/*
 * Copyright (c) 2012, 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package org.graalvm.compiler.hotspot;

import static org.graalvm.compiler.core.GraalCompilerOptions.ExitVMOnBailout;
import static org.graalvm.compiler.core.GraalCompilerOptions.ExitVMOnException;
import static org.graalvm.compiler.core.GraalCompilerOptions.PrintAfterCompilation;
import static org.graalvm.compiler.core.GraalCompilerOptions.PrintBailout;
import static org.graalvm.compiler.core.GraalCompilerOptions.PrintCompilation;
import static org.graalvm.compiler.core.GraalCompilerOptions.PrintFilter;
import static org.graalvm.compiler.core.GraalCompilerOptions.PrintStackTraceOnException;
import static org.graalvm.compiler.core.phases.HighTier.Options.Inline;
import static org.graalvm.compiler.debug.Debug.INFO_LEVEL;
import static org.graalvm.compiler.debug.DelegatingDebugConfig.Feature.DUMP_METHOD;
import static org.graalvm.compiler.debug.DelegatingDebugConfig.Level.DUMP;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.Dump;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.DumpPath;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.ForceDebugEnable;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.PrintCFGFileName;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.PrintGraphFile;
import static org.graalvm.compiler.debug.GraalDebugConfig.Options.PrintGraphFileName;
import static org.graalvm.compiler.java.BytecodeParserOptions.InlineDuringParsing;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.graalvm.compiler.code.CompilationResult;
import org.graalvm.compiler.debug.Debug;
import org.graalvm.compiler.debug.Debug.Scope;
import org.graalvm.compiler.debug.DebugCloseable;
import org.graalvm.compiler.debug.DebugCounter;
import org.graalvm.compiler.debug.DebugDumpHandler;
import org.graalvm.compiler.debug.DebugDumpScope;
import org.graalvm.compiler.debug.DebugRetryableTask;
import org.graalvm.compiler.debug.DebugTimer;
import org.graalvm.compiler.debug.GraalError;
import org.graalvm.compiler.debug.Management;
import org.graalvm.compiler.debug.TTY;
import org.graalvm.compiler.debug.TimeSource;
import org.graalvm.compiler.options.OptionKey;
import org.graalvm.compiler.options.OptionValues;
import org.graalvm.compiler.printer.GraalDebugConfigCustomizer;
import org.graalvm.util.EconomicMap;

import jdk.vm.ci.code.BailoutException;
import jdk.vm.ci.code.CodeCacheProvider;
import jdk.vm.ci.hotspot.EventProvider;
import jdk.vm.ci.hotspot.HotSpotCompilationRequest;
import jdk.vm.ci.hotspot.HotSpotCompilationRequestResult;
import jdk.vm.ci.hotspot.HotSpotCompiledCode;
import jdk.vm.ci.hotspot.HotSpotInstalledCode;
import jdk.vm.ci.hotspot.HotSpotJVMCIRuntimeProvider;
import jdk.vm.ci.hotspot.HotSpotNmethod;
import jdk.vm.ci.hotspot.HotSpotResolvedJavaMethod;
import jdk.vm.ci.runtime.JVMCICompiler;
import jdk.vm.ci.services.JVMCIServiceLocator;

//JaCoCo Exclude

public class CompilationTask {

    private static final DebugCounter BAILOUTS = Debug.counter("Bailouts");

    private static final EventProvider eventProvider;

    static {
        List<EventProvider> providers = JVMCIServiceLocator.getProviders(EventProvider.class);
        if (providers.size() > 1) {
            throw new GraalError("Multiple %s providers found: %s", EventProvider.class.getName(), providers);
        } else if (providers.isEmpty()) {
            eventProvider = EventProvider.createEmptyEventProvider();
        } else {
            eventProvider = providers.get(0);
        }
    }

    private final HotSpotJVMCIRuntimeProvider jvmciRuntime;

    private final HotSpotGraalCompiler compiler;
    private final HotSpotCompilationIdentifier compilationId;

    private HotSpotInstalledCode installedCode;

    /**
     * Specifies whether the compilation result is installed as the
     * {@linkplain HotSpotNmethod#isDefault() default} nmethod for the compiled method.
     */
    private final boolean installAsDefault;

    private final boolean useProfilingInfo;
    private final OptionValues options;

    final class RetryableCompilation extends DebugRetryableTask<HotSpotCompilationRequestResult> {
        private final EventProvider.CompilationEvent compilationEvent;
        CompilationResult result;

        RetryableCompilation(EventProvider.CompilationEvent compilationEvent) {
            this.compilationEvent = compilationEvent;
        }

        @SuppressWarnings("try")
        @Override
        protected HotSpotCompilationRequestResult run(Throwable retryCause) {
            HotSpotResolvedJavaMethod method = getMethod();
            int entryBCI = getEntryBCI();
            final boolean isOSR = entryBCI != JVMCICompiler.INVOCATION_ENTRY_BCI;
            CompilationStatistics stats = CompilationStatistics.create(options, method, isOSR);
            final boolean printCompilation = PrintCompilation.getValue(options) && !TTY.isSuppressed();
            final boolean printAfterCompilation = PrintAfterCompilation.getValue(options) && !TTY.isSuppressed();
            if (printCompilation) {
                TTY.println(getMethodDescription() + "...");
            }

            TTY.Filter filter = new TTY.Filter(PrintFilter.getValue(options), method);
            final long start;
            final long allocatedBytesBefore;
            if (printAfterCompilation || printCompilation) {
                final long threadId = Thread.currentThread().getId();
                start = TimeSource.getTimeNS();
                allocatedBytesBefore = printAfterCompilation || printCompilation ? Lazy.threadMXBean.getThreadAllocatedBytes(threadId) : 0L;
            } else {
                start = 0L;
                allocatedBytesBefore = 0L;
            }

            try (Scope s = Debug.scope("Compiling", new DebugDumpScope(getIdString(), true))) {
                // Begin the compilation event.
                compilationEvent.begin();
                result = compiler.compile(method, entryBCI, useProfilingInfo, compilationId, options);
            } catch (Throwable e) {
                throw Debug.handle(e);
            } finally {
                // End the compilation event.
                compilationEvent.end();

                filter.remove();

                if (printAfterCompilation || printCompilation) {
                    final long threadId = Thread.currentThread().getId();
                    final long stop = TimeSource.getTimeNS();
                    final long duration = (stop - start) / 1000000;
                    final int targetCodeSize = result != null ? result.getTargetCodeSize() : -1;
                    final int bytecodeSize = result != null ? result.getBytecodeSize() : 0;
                    final long allocatedBytesAfter = Lazy.threadMXBean.getThreadAllocatedBytes(threadId);
                    final long allocatedKBytes = (allocatedBytesAfter - allocatedBytesBefore) / 1024;

                    if (printAfterCompilation) {
                        TTY.println(getMethodDescription() + String.format(" | %4dms %5dB %5dB %5dkB", duration, bytecodeSize, targetCodeSize, allocatedKBytes));
                    } else if (printCompilation) {
                        TTY.println(String.format("%-6d JVMCI %-70s %-45s %-50s | %4dms %5dB %5dB %5dkB", getId(), "", "", "", duration, bytecodeSize, targetCodeSize, allocatedKBytes));
                    }
                }
            }

            if (result != null) {
                try (DebugCloseable b = CodeInstallationTime.start()) {
                    installMethod(result);
                }
            }
            stats.finish(method, installedCode);
            if (result != null) {
                return HotSpotCompilationRequestResult.success(result.getBytecodeSize() - method.getCodeSize());
            }
            return null;
        }

        @Override
        protected boolean onRetry(Throwable t) {
            if (t instanceof BailoutException) {
                return false;
            }

            if (!Debug.isEnabled()) {
                TTY.printf("Error while processing %s.%nRe-run with -D%s%s=true to capture graph dumps upon a compilation failure.%n", CompilationTask.this,
                                HotSpotGraalOptionValues.GRAAL_OPTION_PROPERTY_PREFIX, ForceDebugEnable.getName());
                return false;
            }

            if (Dump.hasBeenSet(options)) {
                // If dumping is explicitly enabled, Graal is being debugged
                // so don't interfere with what the user is expecting to see.
                return false;
            }

            String outputDirectory = compiler.getGraalRuntime().getOutputDirectory();
            if (outputDirectory == null) {
                return false;
            }
            String methodFQN = getMethod().format("%H.%n");
            File dumpPath = new File(outputDirectory, methodFQN);
            dumpPath.mkdirs();
            if (!dumpPath.exists()) {
                TTY.println("Warning: could not create dump directory " + dumpPath);
                return false;
            }

            TTY.println("Retrying " + CompilationTask.this);
            retryDumpHandlers = new ArrayList<>();
            retryOptions = new OptionValues(options,
                            PrintGraphFile, true,
                            PrintCFGFileName, methodFQN,
                            PrintGraphFileName, methodFQN,
                            DumpPath, dumpPath.getPath());
            override(DUMP, INFO_LEVEL).enable(DUMP_METHOD);
            new GraalDebugConfigCustomizer().customize(this);
            return true;
        }

        private Collection<DebugDumpHandler> retryDumpHandlers;
        private OptionValues retryOptions;

        @Override
        public Collection<DebugDumpHandler> dumpHandlers() {
            return retryDumpHandlers;
        }

        @Override
        public OptionValues getOptions() {
            return retryOptions;
        }
    }

    static class Lazy {
        /**
         * A {@link com.sun.management.ThreadMXBean} to be able to query some information about the
         * current compiler thread, e.g. total allocated bytes.
         */
        static final com.sun.management.ThreadMXBean threadMXBean = (com.sun.management.ThreadMXBean) Management.getThreadMXBean();
    }

    public CompilationTask(HotSpotJVMCIRuntimeProvider jvmciRuntime, HotSpotGraalCompiler compiler, HotSpotCompilationRequest request, boolean useProfilingInfo, boolean installAsDefault,
                    OptionValues options) {
        this.jvmciRuntime = jvmciRuntime;
        this.compiler = compiler;
        this.compilationId = new HotSpotCompilationIdentifier(request);
        this.useProfilingInfo = useProfilingInfo;
        this.installAsDefault = installAsDefault;

        /*
         * Disable inlining if HotSpot has it disabled unless it's been explicitly set in Graal.
         */
        HotSpotGraalRuntimeProvider graalRuntime = compiler.getGraalRuntime();
        GraalHotSpotVMConfig config = graalRuntime.getVMConfig();
        OptionValues newOptions = options;
        if (!config.inline) {
            EconomicMap<OptionKey<?>, Object> m = OptionValues.newOptionMap();
            if (Inline.getValue(options) && !Inline.hasBeenSet(options)) {
                m.put(Inline, false);
            }
            if (InlineDuringParsing.getValue(options) && !InlineDuringParsing.hasBeenSet(options)) {
                m.put(InlineDuringParsing, false);
            }
            if (!m.isEmpty()) {
                newOptions = new OptionValues(options, m);
            }
        }
        this.options = newOptions;
    }

    public HotSpotResolvedJavaMethod getMethod() {
        return getRequest().getMethod();
    }

    /**
     * Returns the compilation id of this task.
     *
     * @return compile id
     */
    public int getId() {
        return getRequest().getId();
    }

    public int getEntryBCI() {
        return getRequest().getEntryBCI();
    }

    /**
     * @return the compilation id plus a trailing '%' is the compilation is an OSR to match
     *         PrintCompilation style output
     */
    public String getIdString() {
        if (getEntryBCI() != JVMCICompiler.INVOCATION_ENTRY_BCI) {
            return getId() + "%";
        } else {
            return Integer.toString(getId());
        }
    }

    public HotSpotInstalledCode getInstalledCode() {
        return installedCode;
    }

    /**
     * Time spent in compilation.
     */
    private static final DebugTimer CompilationTime = Debug.timer("CompilationTime");

    /**
     * Counts the number of compiled {@linkplain CompilationResult#getBytecodeSize() bytecodes}.
     */
    private static final DebugCounter CompiledBytecodes = Debug.counter("CompiledBytecodes");

    /**
     * Counts the number of compiled {@linkplain CompilationResult#getBytecodeSize() bytecodes} for
     * which {@linkplain CompilationResult#getTargetCode()} code was installed.
     */
    private static final DebugCounter CompiledAndInstalledBytecodes = Debug.counter("CompiledAndInstalledBytecodes");

    /**
     * Counts the number of installed {@linkplain CompilationResult#getTargetCodeSize()} bytes.
     */
    private static final DebugCounter InstalledCodeSize = Debug.counter("InstalledCodeSize");

    /**
     * Time spent in code installation.
     */
    public static final DebugTimer CodeInstallationTime = Debug.timer("CodeInstallation");

    @SuppressWarnings("try")
    public HotSpotCompilationRequestResult runCompilation() {
        HotSpotGraalRuntimeProvider graalRuntime = compiler.getGraalRuntime();
        GraalHotSpotVMConfig config = graalRuntime.getVMConfig();
        int entryBCI = getEntryBCI();
        boolean isOSR = entryBCI != JVMCICompiler.INVOCATION_ENTRY_BCI;
        HotSpotResolvedJavaMethod method = getMethod();

        // register the compilation id in the method metrics
        if (Debug.isMethodMeterEnabled()) {
            if (getEntryBCI() != JVMCICompiler.INVOCATION_ENTRY_BCI) {
                Debug.methodMetrics(method).addToMetric(getId(), "CompilationIdOSR");
            } else {
                Debug.methodMetrics(method).addToMetric(getId(), "CompilationId");
            }
        }

        // Log a compilation event.
        EventProvider.CompilationEvent compilationEvent = eventProvider.newCompilationEvent();

        // If there is already compiled code for this method on our level we simply return.
        // JVMCI compiles are always at the highest compile level, even in non-tiered mode so we
        // only need to check for that value.
        if (method.hasCodeAtLevel(entryBCI, config.compilationLevelFullOptimization)) {
            return null;
        }

        RetryableCompilation compilation = new RetryableCompilation(compilationEvent);
        try (DebugCloseable a = CompilationTime.start()) {
            return compilation.execute();
        } catch (BailoutException bailout) {
            BAILOUTS.increment();
            if (ExitVMOnBailout.getValue(options)) {
                TTY.out.println(method.format("Bailout in %H.%n(%p)"));
                bailout.printStackTrace(TTY.out);
                System.exit(-1);
            } else if (PrintBailout.getValue(options)) {
                TTY.out.println(method.format("Bailout in %H.%n(%p)"));
                bailout.printStackTrace(TTY.out);
            }
            /*
             * Handling of permanent bailouts: Permanent bailouts that can happen for example due to
             * unsupported unstructured control flow in the bytecodes of a method must not be
             * retried. Hotspot compile broker will ensure that no recompilation at the given tier
             * will happen if retry is false.
             */
            final boolean permanentBailout = bailout.isPermanent();
            if (permanentBailout && PrintBailout.getValue(options)) {
                TTY.println("Permanent bailout %s compiling method %s %s.", bailout.getMessage(), HotSpotGraalCompiler.str(method), (isOSR ? "OSR" : ""));
            }
            return HotSpotCompilationRequestResult.failure(bailout.getMessage(), !permanentBailout);
        } catch (Throwable t) {
            // Log a failure event.
            EventProvider.CompilerFailureEvent event = eventProvider.newCompilerFailureEvent();
            if (event.shouldWrite()) {
                event.setCompileId(getId());
                event.setMessage(t.getMessage());
                event.commit();
            }

            handleException(t);
            /*
             * Treat random exceptions from the compiler as indicating a problem compiling this
             * method. Report the result of toString instead of getMessage to ensure that the
             * exception type is included in the output in case there's no detail mesage.
             */
            return HotSpotCompilationRequestResult.failure(t.toString(), false);
        } finally {
            try {
                int compiledBytecodes = 0;
                int codeSize = 0;

                if (compilation.result != null) {
                    compiledBytecodes = compilation.result.getBytecodeSize();
                    CompiledBytecodes.add(compiledBytecodes);
                    if (installedCode != null) {
                        codeSize = installedCode.getSize();
                        CompiledAndInstalledBytecodes.add(compiledBytecodes);
                        InstalledCodeSize.add(codeSize);
                    }
                }

                // Log a compilation event.
                if (compilationEvent.shouldWrite()) {
                    compilationEvent.setMethod(method.format("%H.%n(%p)"));
                    compilationEvent.setCompileId(getId());
                    compilationEvent.setCompileLevel(config.compilationLevelFullOptimization);
                    compilationEvent.setSucceeded(compilation.result != null && installedCode != null);
                    compilationEvent.setIsOsr(isOSR);
                    compilationEvent.setCodeSize(codeSize);
                    compilationEvent.setInlinedBytes(compiledBytecodes);
                    compilationEvent.commit();
                }
            } catch (Throwable t) {
                handleException(t);
            }
        }
    }

    protected void handleException(Throwable t) {
        /*
         * Automatically enable ExitVMOnException during bootstrap or when asserts are enabled but
         * respect ExitVMOnException if it's been explicitly set.
         */
        boolean exitVMOnException = ExitVMOnException.getValue(options);
        if (!ExitVMOnException.hasBeenSet(options)) {
            assert (exitVMOnException = true) == true;
            if (!exitVMOnException) {
                HotSpotGraalRuntimeProvider runtime = compiler.getGraalRuntime();
                if (runtime.isBootstrapping()) {
                    exitVMOnException = true;
                }
            }
        }

        if (PrintStackTraceOnException.getValue(options) || exitVMOnException) {
            try {
                t.printStackTrace(TTY.out);
            } catch (Throwable throwable) {
                // Don't let an exception here change the other control flow
            }
        }

        if (exitVMOnException) {
            System.exit(-1);
        }
    }

    private String getMethodDescription() {
        HotSpotResolvedJavaMethod method = getMethod();
        return String.format("%-6d JVMCI %-70s %-45s %-50s %s", getId(), method.getDeclaringClass().getName(), method.getName(), method.getSignature().toMethodDescriptor(),
                        getEntryBCI() == JVMCICompiler.INVOCATION_ENTRY_BCI ? "" : "(OSR@" + getEntryBCI() + ") ");
    }

    @SuppressWarnings("try")
    private void installMethod(final CompilationResult compResult) {
        final CodeCacheProvider codeCache = jvmciRuntime.getHostJVMCIBackend().getCodeCache();
        installedCode = null;
        Object[] context = {new DebugDumpScope(getIdString(), true), codeCache, getMethod(), compResult};
        try (Scope s = Debug.scope("CodeInstall", context)) {
            HotSpotCompiledCode compiledCode = HotSpotCompiledCodeBuilder.createCompiledCode(codeCache, getRequest().getMethod(), getRequest(), compResult);
            installedCode = (HotSpotInstalledCode) codeCache.installCode(getRequest().getMethod(), compiledCode, null, getRequest().getMethod().getSpeculationLog(), installAsDefault);
        } catch (Throwable e) {
            throw Debug.handle(e);
        }
    }

    @Override
    public String toString() {
        return "Compilation[id=" + getId() + ", " + getMethod().format("%H.%n(%p)") + (getEntryBCI() == JVMCICompiler.INVOCATION_ENTRY_BCI ? "" : "@" + getEntryBCI()) + "]";
    }

    private HotSpotCompilationRequest getRequest() {
        return compilationId.getRequest();
    }
}
