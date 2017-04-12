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
package org.graalvm.compiler.loop;

import static org.graalvm.compiler.core.common.GraalOptions.LoopMaxUnswitch;
import static org.graalvm.compiler.core.common.GraalOptions.MaximumDesiredSize;
import static org.graalvm.compiler.core.common.GraalOptions.MinimumPeelProbability;
import static jdk.vm.ci.meta.DeoptimizationReason.BoundsCheckException;

import java.util.List;

import org.graalvm.compiler.debug.Debug;
import org.graalvm.compiler.debug.DebugCounter;
import org.graalvm.compiler.graph.Node;
import org.graalvm.compiler.graph.NodeBitMap;
import org.graalvm.compiler.nodes.AbstractBeginNode;
import org.graalvm.compiler.nodes.ControlSplitNode;
import org.graalvm.compiler.nodes.DeoptimizeNode;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.FrameState;
import org.graalvm.compiler.nodes.GuardNode;
import org.graalvm.compiler.nodes.LoopBeginNode;
import org.graalvm.compiler.nodes.MergeNode;
import org.graalvm.compiler.nodes.VirtualState;
import org.graalvm.compiler.nodes.VirtualState.VirtualClosure;
import org.graalvm.compiler.nodes.cfg.Block;
import org.graalvm.compiler.nodes.cfg.ControlFlowGraph;
import org.graalvm.compiler.nodes.debug.ControlFlowAnchorNode;
import org.graalvm.compiler.nodes.extended.GuardingNode;
import org.graalvm.compiler.nodes.java.TypeSwitchNode;
import org.graalvm.compiler.nodes.memory.ReadNode;
import org.graalvm.compiler.nodes.memory.WriteNode;
import org.graalvm.compiler.options.Option;
import org.graalvm.compiler.options.OptionType;
import org.graalvm.compiler.options.OptionValues;
import org.graalvm.compiler.options.OptionKey;

import jdk.vm.ci.code.BytecodeFrame;
import jdk.vm.ci.meta.MetaAccessProvider;
import jdk.vm.ci.meta.ConstantReflectionProvider;

public class DefaultLoopPolicies implements LoopPolicies {
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> LoopUnswitchMaxIncrease = new OptionKey<>(500);
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> LoopUnswitchTrivial = new OptionKey<>(10);
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Double> LoopUnswitchFrequencyBoost = new OptionKey<>(10.0);

    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> FullUnrollMaxNodes = new OptionKey<>(300);
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> FullUnrollMaxIterations = new OptionKey<>(600);
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> ExactFullUnrollMaxNodes = new OptionKey<>(1200);

    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Integer> UnrollMaxIterations = new OptionKey<>(16);
    @Option(help = "", type = OptionType.Expert) public static final OptionKey<Boolean> EliminateRangeChecks = new OptionKey<>(true);

    @Override
    public boolean shouldPeel(LoopEx loop, ControlFlowGraph cfg, MetaAccessProvider metaAccess) {
        LoopBeginNode loopBegin = loop.loopBegin();
        double entryProbability = cfg.blockFor(loopBegin.forwardEnd()).probability();
        OptionValues options = cfg.graph.getOptions();
        if (entryProbability > MinimumPeelProbability.getValue(options) && loop.size() + loopBegin.graph().getNodeCount() < MaximumDesiredSize.getValue(options)) {
            // check whether we're allowed to peel this loop
            return loop.canDuplicateLoop();
        } else {
            return false;
        }
    }

    @Override
    public boolean shouldFullUnroll(LoopEx loop) {
        if (!loop.isCounted() || !loop.counted().isConstantMaxTripCount()) {
            return false;
        }
        OptionValues options = loop.entryPoint().getOptions();
        CountedLoopInfo counted = loop.counted();
        long maxTrips = counted.constantMaxTripCount();
        int maxNodes = (counted.isExactTripCount() && counted.isConstantExactTripCount()) ? ExactFullUnrollMaxNodes.getValue(options) : FullUnrollMaxNodes.getValue(options);
        maxNodes = Math.min(maxNodes, Math.max(0, MaximumDesiredSize.getValue(options) - loop.loopBegin().graph().getNodeCount()));
        int size = Math.max(1, loop.size() - 1 - loop.loopBegin().phis().count());
        if (maxTrips <= FullUnrollMaxIterations.getValue(options) && size * (maxTrips - 1) <= maxNodes) {
            // check whether we're allowed to unroll this loop
            return loop.canDuplicateLoop();
        } else {
            return false;
        }
    }

    @Override
    public boolean shouldPartiallyUnroll(LoopEx loop) {
        if (!loop.isCounted()) {
            return false;
        }
        OptionValues options = loop.entryPoint().getOptions();
        CountedLoopInfo counted = loop.counted();
        int maxNodes = (counted.isExactTripCount() && counted.isConstantExactTripCount()) ? ExactFullUnrollMaxNodes.getValue(options) : FullUnrollMaxNodes.getValue(options);
        maxNodes = Math.min(maxNodes, Math.max(0, MaximumDesiredSize.getValue(options) - loop.loopBegin().graph().getNodeCount()));
        int size = Math.max(1, loop.size() - 1 - loop.loopBegin().phis().count());
        int unrollFactor = 1; // fill in with counted data
        if (unrollFactor < UnrollMaxIterations.getValue(options) && size * unrollFactor <= maxNodes) {
            // check whether we're allowed to unroll this loop
            for (Node node : loop.inside().nodes()) {
                if (node instanceof ControlFlowAnchorNode) {
                    return false;
                }
                if (node instanceof FrameState) {
                    FrameState frameState = (FrameState) node;
                    if (frameState.bci == BytecodeFrame.AFTER_EXCEPTION_BCI || frameState.bci == BytecodeFrame.UNWIND_BCI) {
                        return false;
                    }
                }
            }
            return true;
        } else {
            return false;
        }
    }

    @Override
    public boolean shouldEliminateRangeChecks(LoopEx loop, ConstantReflectionProvider constantReflection) {
        if (!loop.isCounted()) {
            return false;
        }
        OptionValues options = loop.entryPoint().getOptions();
        if (EliminateRangeChecks.getValue(options)) {
            // Check if there are any range checks to eliminate.
            // We do not need to worry about loop exits as unswitching has already happened.
            int rangeCheckCount = 0;
            for (Node node : loop.inside().nodes()) {
                if (node instanceof ReadNode) {
                    ReadNode readNode = (ReadNode) node;
                    if (readNode.getGuard() != null) {
                        GuardingNode guarding = readNode.getGuard();
                        if (guarding instanceof GuardNode) {
                            GuardNode guard = (GuardNode) guarding;
                            if (guard.getReason() == BoundsCheckException) {
                                rangeCheckCount++;
                            }
                        }
                    }
                } else if (node instanceof WriteNode) {
                    WriteNode writeNode = (WriteNode) node;
                    if (writeNode.getGuard() != null) {
                        GuardingNode guarding = writeNode.getGuard();
                        if (guarding instanceof GuardNode) {
                            GuardNode guard = (GuardNode) guarding;
                            if (guard.getReason() == BoundsCheckException) {
                                rangeCheckCount++;
                            }
                        }
                    }
                }
            }
            if (rangeCheckCount > 0) {
                return true;
            }
        } else {
            return false;
        }
        return false;
    }

    @Override
    public boolean shouldTryUnswitch(LoopEx loop) {
        LoopBeginNode loopBegin = loop.loopBegin();
        double loopFrequency = loopBegin.loopFrequency();
        if (loopFrequency <= 1.0) {
            return false;
        }
        OptionValues options = loop.entryPoint().getOptions();
        return loopBegin.unswitches() <= LoopMaxUnswitch.getValue(options);
    }

    private static final class CountingClosure implements VirtualClosure {
        int count;

        @Override
        public void apply(VirtualState node) {
            count++;
        }
    }

    private static class IsolatedInitialization {
        static final DebugCounter UNSWITCH_SPLIT_WITH_PHIS = Debug.counter("UnswitchSplitWithPhis");
    }

    @Override
    public boolean shouldUnswitch(LoopEx loop, List<ControlSplitNode> controlSplits) {
        int phis = 0;
        NodeBitMap branchNodes = loop.loopBegin().graph().createNodeBitMap();
        for (ControlSplitNode controlSplit : controlSplits) {
            for (Node successor : controlSplit.successors()) {
                AbstractBeginNode branch = (AbstractBeginNode) successor;
                // this may count twice because of fall-through in switches
                loop.nodesInLoopBranch(branchNodes, branch);
            }
            Block postDomBlock = loop.loopsData().getCFG().blockFor(controlSplit).getPostdominator();
            if (postDomBlock != null) {
                IsolatedInitialization.UNSWITCH_SPLIT_WITH_PHIS.increment();
                phis += ((MergeNode) postDomBlock.getBeginNode()).phis().count();
            }
        }
        int inBranchTotal = branchNodes.count();

        CountingClosure stateNodesCount = new CountingClosure();
        double loopFrequency = loop.loopBegin().loopFrequency();
        OptionValues options = loop.loopBegin().getOptions();
        int maxDiff = LoopUnswitchTrivial.getValue(options) + (int) (LoopUnswitchFrequencyBoost.getValue(options) * (loopFrequency - 1.0 + phis));

        maxDiff = Math.min(maxDiff, LoopUnswitchMaxIncrease.getValue(options));
        int remainingGraphSpace = MaximumDesiredSize.getValue(options) - loop.loopBegin().graph().getNodeCount();
        maxDiff = Math.min(maxDiff, remainingGraphSpace);

        loop.loopBegin().stateAfter().applyToVirtual(stateNodesCount);
        int loopTotal = loop.size() - loop.loopBegin().phis().count() - stateNodesCount.count - 1;
        int actualDiff = (loopTotal - inBranchTotal);
        ControlSplitNode firstSplit = controlSplits.get(0);
        if (firstSplit instanceof TypeSwitchNode) {
            int copies = firstSplit.successors().count() - 1;
            for (Node succ : firstSplit.successors()) {
                FixedNode current = (FixedNode) succ;
                while (current instanceof FixedWithNextNode) {
                    current = ((FixedWithNextNode) current).next();
                }
                if (current instanceof DeoptimizeNode) {
                    copies--;
                }
            }
            actualDiff = actualDiff * copies;
        }

        Debug.log("shouldUnswitch(%s, %s) : delta=%d (%.2f%% inside of branches), max=%d, f=%.2f, phis=%d -> %b", loop, controlSplits, actualDiff, (double) (inBranchTotal) / loopTotal * 100, maxDiff,
                        loopFrequency, phis, actualDiff <= maxDiff);
        if (actualDiff <= maxDiff) {
            // check whether we're allowed to unswitch this loop
            return loop.canDuplicateLoop();
        } else {
            return false;
        }
    }

}
