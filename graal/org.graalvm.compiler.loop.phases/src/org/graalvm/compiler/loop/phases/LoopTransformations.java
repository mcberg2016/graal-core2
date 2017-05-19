/*
 * Copyright (c) 2012, 2012, Oracle and/or its affiliates. All rights reserved.
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
package org.graalvm.compiler.loop.phases;

import static org.graalvm.compiler.core.common.GraalOptions.MaximumDesiredSize;
import static jdk.vm.ci.meta.DeoptimizationReason.BoundsCheckException;
import static jdk.vm.ci.meta.DeoptimizationReason.NullCheckException;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.graalvm.compiler.graph.Graph.Mark;
import org.graalvm.compiler.core.common.RetryableBailoutException;
import org.graalvm.compiler.core.common.type.Stamp;
import org.graalvm.compiler.core.common.type.StampFactory;
import org.graalvm.compiler.graph.Node;
import org.graalvm.compiler.graph.Position;
import org.graalvm.compiler.loop.CountedLoopInfo;
import org.graalvm.compiler.loop.InductionVariable;
import org.graalvm.compiler.loop.InductionVariable.Direction;
import org.graalvm.compiler.loop.BasicInductionVariable;
import org.graalvm.compiler.loop.DerivedInductionVariable;
import static org.graalvm.compiler.loop.MathUtil.add;
import static org.graalvm.compiler.loop.MathUtil.sub;
import org.graalvm.compiler.loop.LoopEx;
import org.graalvm.compiler.loop.LoopFragmentWhole;
import org.graalvm.compiler.loop.LoopFragmentInside;
import org.graalvm.compiler.nodeinfo.InputType;
import org.graalvm.compiler.nodes.AbstractBeginNode;
import org.graalvm.compiler.nodes.AbstractEndNode;
import org.graalvm.compiler.nodes.AbstractMergeNode;
import org.graalvm.compiler.nodes.BeginNode;
import org.graalvm.compiler.nodes.BinaryOpLogicNode;
import org.graalvm.compiler.nodes.ConstantNode;
import org.graalvm.compiler.nodes.ControlSplitNode;
import org.graalvm.compiler.nodes.EndNode;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.FrameState;
import org.graalvm.compiler.nodes.GuardNode;
import org.graalvm.compiler.nodes.IfNode;
import org.graalvm.compiler.nodes.InvokeNode;
import org.graalvm.compiler.nodes.LogicNode;
import org.graalvm.compiler.nodes.LoopBeginNode;
import org.graalvm.compiler.nodes.LoopEndNode;
import org.graalvm.compiler.nodes.LoopExitNode;
import org.graalvm.compiler.nodes.PhiNode;
import org.graalvm.compiler.nodes.PiNode;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.ValueNode;
import org.graalvm.compiler.nodes.ValuePhiNode;
import org.graalvm.compiler.nodes.calc.AddNode;
import org.graalvm.compiler.nodes.calc.BinaryArithmeticNode;
import org.graalvm.compiler.nodes.calc.CompareNode;
import org.graalvm.compiler.nodes.calc.ConditionalNode;
import org.graalvm.compiler.nodes.calc.IntegerBelowNode;
import org.graalvm.compiler.nodes.calc.IntegerEqualsNode;
import org.graalvm.compiler.nodes.calc.IntegerLessThanNode;
import org.graalvm.compiler.nodes.calc.LeftShiftNode;
import org.graalvm.compiler.nodes.calc.RightShiftNode;
import org.graalvm.compiler.nodes.calc.SubNode;
import org.graalvm.compiler.nodes.extended.GuardingNode;
import org.graalvm.compiler.nodes.extended.SwitchNode;
import org.graalvm.compiler.nodes.memory.ReadNode;
import org.graalvm.compiler.nodes.memory.FixedAccessNode;
import org.graalvm.compiler.nodes.memory.MemoryPhiNode;
import org.graalvm.compiler.nodes.memory.address.AddressNode;
import org.graalvm.compiler.nodes.virtual.CommitAllocationNode;
import org.graalvm.compiler.phases.common.CanonicalizerPhase;
import org.graalvm.compiler.phases.tiers.PhaseContext;

import org.graalvm.compiler.options.OptionValues;
import static org.graalvm.compiler.core.common.GraalOptions.BlackBox;

import jdk.vm.ci.meta.JavaKind;

public abstract class LoopTransformations {

    private LoopTransformations() {
        // does not need to be instantiated
    }

    public static void peel(LoopEx loop) {
        loop.inside().duplicate().insertBefore(loop);
        loop.loopBegin().setLoopFrequency(Math.max(0.0, loop.loopBegin().loopFrequency() - 1));
    }

    public static void fullUnroll(LoopEx loop, PhaseContext context, CanonicalizerPhase canonicalizer) {
        // assert loop.isCounted(); //TODO (gd) strengthen : counted with known trip count
        LoopBeginNode loopBegin = loop.loopBegin();
        StructuredGraph graph = loopBegin.graph();
        int initialNodeCount = graph.getNodeCount();
        while (!loopBegin.isDeleted()) {
            Mark mark = graph.getMark();
            peel(loop);
            canonicalizer.applyIncremental(graph, context, mark);
            loop.invalidateFragments();
            if (graph.getNodeCount() > initialNodeCount + MaximumDesiredSize.getValue(graph.getOptions()) * 2) {
                throw new RetryableBailoutException("FullUnroll : Graph seems to grow out of proportion");
            }
        }
    }

    public static void unswitch(LoopEx loop, List<ControlSplitNode> controlSplitNodeSet) {
        ControlSplitNode firstNode = controlSplitNodeSet.iterator().next();
        LoopFragmentWhole originalLoop = loop.whole();
        StructuredGraph graph = firstNode.graph();

        loop.loopBegin().incrementUnswitches();

        // create new control split out of loop
        ControlSplitNode newControlSplit = (ControlSplitNode) firstNode.copyWithInputs();
        originalLoop.entryPoint().replaceAtPredecessor(newControlSplit);

        /*
         * The code below assumes that all of the control split nodes have the same successor
         * structure, which should have been enforced by findUnswitchable.
         */
        Iterator<Position> successors = firstNode.successorPositions().iterator();
        assert successors.hasNext();
        // original loop is used as first successor
        Position firstPosition = successors.next();
        AbstractBeginNode originalLoopBegin = BeginNode.begin(originalLoop.entryPoint());
        firstPosition.set(newControlSplit, originalLoopBegin);

        while (successors.hasNext()) {
            Position position = successors.next();
            // create a new loop duplicate and connect it.
            LoopFragmentWhole duplicateLoop = originalLoop.duplicate();
            AbstractBeginNode newBegin = BeginNode.begin(duplicateLoop.entryPoint());
            position.set(newControlSplit, newBegin);

            // For each cloned ControlSplitNode, simplify the proper path
            for (ControlSplitNode controlSplitNode : controlSplitNodeSet) {
                ControlSplitNode duplicatedControlSplit = duplicateLoop.getDuplicatedNode(controlSplitNode);
                if (duplicatedControlSplit.isAlive()) {
                    AbstractBeginNode survivingSuccessor = (AbstractBeginNode) position.get(duplicatedControlSplit);
                    survivingSuccessor.replaceAtUsages(InputType.Guard, newBegin);
                    graph.removeSplitPropagate(duplicatedControlSplit, survivingSuccessor);
                }
            }
        }
        // original loop is simplified last to avoid deleting controlSplitNode too early
        for (ControlSplitNode controlSplitNode : controlSplitNodeSet) {
            if (controlSplitNode.isAlive()) {
                AbstractBeginNode survivingSuccessor = (AbstractBeginNode) firstPosition.get(controlSplitNode);
                survivingSuccessor.replaceAtUsages(InputType.Guard, originalLoopBegin);
                graph.removeSplitPropagate(controlSplitNode, survivingSuccessor);
            }
        }

        // TODO (gd) probabilities need some amount of fixup.. (probably also in other transforms)
    }

    public static boolean partialUnroll(LoopEx loop, StructuredGraph graph) {
        boolean changed = false;
        CountedLoopInfo mainCounted = loop.counted();
        LoopBeginNode mainLoopBegin = loop.loopBegin();
        InductionVariable iv = mainCounted.getCounter();
        IfNode mainLimit = mainCounted.getLimitTest();
        LogicNode ifTest = mainLimit.condition();
        CompareNode compareNode = (CompareNode) ifTest;
        ValueNode compareBound = null;
        ValueNode curPhi = iv.valueNode();
        if (compareNode.getX() == curPhi) {
            compareBound = compareNode.getY();
        } else if (compareNode.getY() == curPhi) {
            compareBound = compareNode.getX();
        }
        long oldStride = iv.constantStride();
        LoopFragmentInside newSegment = loop.inside().duplicate();
        newSegment.insertWithinAfter(loop);
        ValueNode inductionNode = iv.valueNode();
        Node segmentOrigOp = null;
        Node replacementOp = null;
        Node newStrideNode = null;
        if (inductionNode instanceof PhiNode) {
            PhiNode mainPhiNode = (PhiNode) inductionNode;
            // Rework each phi with a loop carried dependence
            for (Node usage : mainPhiNode.usages()) {
                if (loop.isOutsideLoop(usage) == false) {
                    for (int i = 0; i < mainPhiNode.valueCount(); i++) {
                        ValueNode v = mainPhiNode.valueAt(i);
                        if (v == usage) {
                            Node node = newSegment.getDuplicatedNode(usage);
                            int inputCnt = 0;
                            for (Node input : usage.inputs()) {
                                inputCnt++;
                                if (input == mainPhiNode) {
                                    break;
                                }
                            }
                            int newInputCnt = 0;
                            for (Node input : node.inputs()) {
                                newInputCnt++;
                                if (newInputCnt == inputCnt) {
                                    replacementOp = input;
                                    newStrideNode = node;
                                    // Use this loops induction phi as input to the new stride node
                                    node.replaceFirstInput(input, inductionNode);
                                    segmentOrigOp = usage;
                                    break;
                                }
                            }
                            // Update the induction phi with new stride node
                            mainPhiNode.setValueAt(i, (ValueNode) newStrideNode);
                            changed |= true;
                        }
                    }
                }
                if (newStrideNode != null) {
                    break;
                }
            }
        }

        if (changed) {
            // Patch the new segments induction uses of replacementOp with the old stride node
            if (inductionNode instanceof PhiNode) {
                PhiNode mainPhiNode = (PhiNode) inductionNode;
                for (Node usage : mainPhiNode.usages()) {
                    if (usage == segmentOrigOp) {
                        continue;
                    }
                    if (loop.isOutsideLoop(usage) == false) {
                        Node node = newSegment.getDuplicatedNode(usage);
                        if (node instanceof CompareNode) {
                            continue;
                        }
                        node.replaceFirstInput(replacementOp, segmentOrigOp);
                    }
                }
            }

            // If merge the duplicate code into the loop and remove redundant code
            placeNewSegmentAndCleanup(mainCounted, mainLoopBegin, newSegment);
            int unrollFactor = mainLoopBegin.getUnrollFactor();
            // First restore the old pattern of the loop exit condition so we can update it one way
            if (unrollFactor > 1) {
                if (compareBound instanceof LeftShiftNode) {
                    LeftShiftNode left = (LeftShiftNode) compareBound;
                    RightShiftNode right = (RightShiftNode) left.getX();
                    ValueNode oldcompareBound = right.getX();
                    compareNode.replaceFirstInput(left, oldcompareBound);
                    left.safeDelete();
                    right.safeDelete();
                    compareBound = oldcompareBound;
                }
            }
            unrollFactor *= 2;
            mainLoopBegin.setUnrollFactor(unrollFactor);
            // Reset stride to include new segment in loop control.
            oldStride *= 2;
            // Now update the induction op and the exit condition
            if (iv instanceof BasicInductionVariable) {
                boolean useInt = true;
                ConstantNode newStrideVal = null;
                BasicInductionVariable biv = (BasicInductionVariable) iv;
                BinaryArithmeticNode<?> newOp = (BinaryArithmeticNode<?>) newStrideNode;
                Stamp strideStamp = newOp.stamp();
                if (strideStamp.getStackKind() == JavaKind.Long) {
                    newStrideVal = graph.unique(ConstantNode.forLong(oldStride));
                    useInt = false;
                } else {
                    newStrideVal = graph.unique(ConstantNode.forInt((int) oldStride));
                }
                newOp.setY(newStrideVal);
                biv.setOP(newOp);
                // Now use the current unrollFactor to update the exit condition to power of two
                if (unrollFactor > 1) {
                    ConstantNode shiftVal = null;
                    int[] lookupVal = {0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4};
                    if (useInt) {
                        shiftVal = graph.unique(ConstantNode.forInt(lookupVal[unrollFactor]));
                    } else {
                        shiftVal = graph.unique(ConstantNode.forLong(lookupVal[unrollFactor]));
                    }
                    RightShiftNode right = graph.addWithoutUnique(new RightShiftNode(compareBound, shiftVal));
                    LeftShiftNode left = graph.addWithoutUnique(new LeftShiftNode(right, shiftVal));
                    compareNode.replaceFirstInput(compareBound, left);
                }
                mainLoopBegin.setLoopFrequency(mainLoopBegin.loopFrequency() / 2);
            }
        }
        return changed;
    }

    public static void placeNewSegmentAndCleanup(CountedLoopInfo mainCounted, LoopBeginNode mainLoopBegin, LoopFragmentInside newSegment) {
        // Discard the segment entry and its flow, after if merging it into the loop
        IfNode loopTest = mainCounted.getLimitTest();
        IfNode newSegmentTest = newSegment.getDuplicatedNode(loopTest);
        AbstractBeginNode trueSuccessor = loopTest.trueSuccessor();
        AbstractBeginNode falseSuccessor = loopTest.falseSuccessor();
        FixedNode firstNode = null;
        FixedNode lastNode = null;
        boolean codeInTrueSide = false;
        if (trueSuccessor == mainCounted.getBody()) {
            firstNode = trueSuccessor.next();
            codeInTrueSide = true;
        } else {
            assert (falseSuccessor == mainCounted.getBody());
            firstNode = falseSuccessor.next();
        }
        AbstractBeginNode startBlockNode = null;
        trueSuccessor = newSegmentTest.trueSuccessor();
        falseSuccessor = newSegmentTest.falseSuccessor();
        if (codeInTrueSide) {
            startBlockNode = trueSuccessor;
        } else {
            startBlockNode = falseSuccessor;
        }
        if (startBlockNode != null) {
            FixedWithNextNode node = startBlockNode;
            while (true) {
                if (node == null) {
                    break;
                }
                FixedNode next = node.next();
                if (next instanceof FixedAccessNode) {
                    FixedAccessNode accessNode = (FixedAccessNode) next;
                    Node curGuard = (Node) accessNode.getGuard();
                    accessNode.replaceFirstInput(curGuard, mainLoopBegin);
                }
                if (next instanceof FixedWithNextNode) {
                    node = (FixedWithNextNode) next;
                } else {
                    lastNode = next;
                    break;
                }
            }
            assert (lastNode != null);
            LoopEndNode loopEndNode = getSingleLoopEndFromLoop(mainLoopBegin);
            FixedNode lastCodeNode = (FixedNode) loopEndNode.predecessor();
            FixedNode newSegmentFirstNode = newSegment.getDuplicatedNode(firstNode);
            FixedNode newSegmentLastNode = newSegment.getDuplicatedNode(lastCodeNode);
            newSegmentLastNode.clearSuccessors();
            startBlockNode.setNext(lastNode);
            lastCodeNode.replaceFirstSuccessor(loopEndNode, newSegmentFirstNode);
            newSegmentLastNode.replaceFirstSuccessor(lastNode, loopEndNode);
            FixedWithNextNode oldLastNode = (FixedWithNextNode) lastCodeNode;
            oldLastNode.setNext(newSegmentFirstNode);
            FixedWithNextNode newLastNode = (FixedWithNextNode) newSegmentLastNode;
            newLastNode.setNext(loopEndNode);
            startBlockNode.clearSuccessors();
            lastNode.safeDelete();
            Node newSegmentTestStart = newSegmentTest.predecessor();
            LogicNode newSegmentIfTest = newSegmentTest.condition();
            newSegmentTestStart.clearSuccessors();
            newSegmentTest.safeDelete();
            newSegmentIfTest.safeDelete();
            trueSuccessor.safeDelete();
            falseSuccessor.safeDelete();
            newSegmentTestStart.safeDelete();
        }
    }

    /*
     * @formatter:off
     * This function splits candidate loops into pre, main and post loops,
     * dividing the iteration space to facilitate the majority of iterations
     * being executed in a main loop, which will have RCE implemented upon it.
     * The initial loop form is constrained to single entry/exit, but can have
     * flow.  The translation looks like:
     *
     *       (Simple Loop entry)                   (Pre Loop Entry)
     *                |                                  |
     *         (LoopBeginNode)                    (LoopBeginNode)
     *                |                                  |
     *       (Loop Control Test)<------   ==>  (Loop control Test)<------
     *         /               \       \         /               \       \
     *    (Loop Exit)      (Loop Body) |    (Loop Exit)      (Loop Body) |
     *        |                |       |        |                |       |
     * (continue code)     (Loop End)  |  if (M < length)*   (Loop End)  |
     *                         \       /       /      \           \      /
     *                          ----->        /       |            ----->
     *                                       /  if ( ... )*
     *                                      /     /       \
     *                                     /     /         \
     *                                    /     /           \
     *                                   |     /     (Main Loop Entry)
     *                                   |    |             |
     *                                   |    |      (LoopBeginNode)
     *                                   |    |             |
     *                                   |    |     (Loop Control Test)<------
     *                                   |    |      /               \        \
     *                                   |    |  (Loop Exit)      (Loop Body) |
     *                                    \   \      |                |       |
     *                                     \   \     |            (Loop End)  |
     *                                      \   \    |                \       /
     *                                       \   \   |                 ------>
     *                                        \   \  |
     *                                      (Main Loop Merge)*
     *                                               |
     *                                      (Post Loop Entry)
     *                                               |
     *                                        (LoopBeginNode)
     *                                               |
     *                                       (Loop Control Test)<-----
     *                                        /               \       \
     *                                    (Loop Exit)     (Loop Body) |
     *                                        |               |       |
     *                                 (continue code)    (Loop End)  |
     *                                                         \      /
     *                                                          ----->
     *
     * Key: "*" = optional.
     *
     * The value "M" is the maximal value of the loop trip for the original
     * loop.  The value of "length" is applicable to the number of arrays found
     * in the loop but is reduced if some or all of the arrays are known to be
     * the same length as "M". The maximum number of tests can be equal to the
     * number of arrays in the loop, where multiple instances of an array are
     * subsumed into a single test for that arrays length.
     *
     * If the optional main loop entry tests are absent, the Pre Loop exit
     * connects to the Main loops entry and there is no merge hanging off the
     * main loops exit to converge flow from said tests.  All split use data
     * flow is mitigated through phi(s) in the main merge if present and
     * passed through the main and post loop phi(s) from the originating pre
     * loop with final phi(s) and data flow patched to the "continue code".
     * The pre loop is constrained to one iteration for now and will likely
     * be updated to produce vector alignment if applicable.
     * 
     * @formatter:on
     */

    public static void insertPrePostLoops(LoopEx loop, StructuredGraph graph, OptionValues options) {
        LoopFragmentWhole preLoop = loop.whole();
        CountedLoopInfo preCounted = preLoop.loop().counted();
        IfNode preLimit = preCounted.getLimitTest();
        List<Node> boundsExpressions = null;
        if (BlackBox.getValue(options)) {
            boundsExpressions = new ArrayList<>();
        } else {
            boundsExpressions = findBoundsExpressions(preLoop.loop());
        }
        if (preLimit != null) {
            LoopBeginNode preLoopBegin = loop.loopBegin();
            EndNode preEndNode = getSingleEndFromLoop(preLoopBegin);
            AbstractMergeNode preMergeNode = preEndNode.merge();
            InductionVariable preIv = preCounted.getCounter();
            LoopExitNode preLoopExitNode = getSingleExitFromLoop(preLoopBegin);
            FixedNode continuationNode = preLoopExitNode.next();
            boolean haveBounds = (boundsExpressions.isEmpty() == false);
            boolean arrayLengthTrip = pruneBoundsExpressions(preLimit, preIv, boundsExpressions);

            // Each duplication is inserted after the original, ergo create the post loop first
            LoopFragmentWhole postLoop = preLoop.duplicate();
            LoopFragmentWhole mainLoop = preLoop.duplicate();
            preLoopBegin.incrementSplits();
            preLoopBegin.incrementSplits();
            preLoopBegin.setPreLoop();
            markGuards(loop, mainLoop, postLoop);

            // Handle original code has guards loaded and the old continuation code.
            AbstractMergeNode postMergeNode = preMergeNode;
            LoopBeginNode postLoopBegin = postLoop.getDuplicatedNode(preLoopBegin);
            postLoopBegin.setPostLoop();
            AbstractEndNode postEntryNode = postLoopBegin.forwardEnd();
            EndNode postEndNode = getSingleEndFromLoop(postLoopBegin);
            preMergeNode = postEndNode.merge();
            preMergeNode.clearEnds();
            LoopExitNode postLoopExitNode = getSingleExitFromLoop(postLoopBegin);
            cleanPostLoopExit(postLoopExitNode);
            if (preMergeNode.usages().isEmpty()) {
                preMergeNode.safeDelete();
            } else {
                // Duplicate may have moved some uses onto created merges
                preMergeNode.prepareDelete(postLoopExitNode);
                preMergeNode.safeDelete();
            }

            // Process the main loop and update loop with effect-less guards
            LoopBeginNode mainLoopBegin = mainLoop.getDuplicatedNode(preLoopBegin);
            mainLoopBegin.setMainLoop();
            EndNode mainEndNode = getSingleEndFromLoop(mainLoopBegin);
            ValueNode origLimit = null;

            // Update the main loop phi initialization to carry from the pre loop
            for (PhiNode prePhiNode : preLoopBegin.valuePhis()) {
                PhiNode mainPhiNode = mainLoop.getDuplicatedNode(prePhiNode);
                mainPhiNode.initializeValueAt(0, prePhiNode);
            }

            AbstractMergeNode mainMergeNode = mainEndNode.merge();
            if (boundsExpressions.isEmpty()) {
                // In the case of no Bounds tests, we just flow right into the main loop
                AbstractBeginNode mainLandingNode = BeginNode.begin(postEntryNode);
                LoopExitNode mainLoopExitNode = getSingleExitFromLoop(mainLoopBegin);
                mainLoopExitNode.setNext(mainLandingNode);
                mainMergeNode.clearEnds();
                if (mainMergeNode.usages().isEmpty()) {
                    mainMergeNode.safeDelete();
                } else {
                    mainMergeNode.prepareDelete(mainLandingNode);
                    mainMergeNode.safeDelete();
                }
                preLoopExitNode.setNext(mainLoopBegin.forwardEnd());
            } else {
                AbstractBeginNode mainBeginNode = BeginNode.begin(mainLoopBegin.forwardEnd());
                // Add limit based range checks to guard main loop entry/execution
                mainMergeNode.clearEnds();
                mainMergeNode.addForwardEnd(mainEndNode);
                mainMergeNode.setNext(postEntryNode);
                origLimit = getPreLoopMaxBound(preLimit, preIv, preCounted);
                assert (origLimit != null);
                IfNode firstIf = addEntryTestsForMainLoop(boundsExpressions, mainBeginNode, mainMergeNode, origLimit, arrayLengthTrip);
                assert (firstIf != null);
                preLoopExitNode.setNext(firstIf);
            }

            // Remove bounds checks if we have them
            if (haveBounds) {
                removeChecks(preLoop, mainLoop);
            }

            // Add and update any phi edges as per merge usage as needed and update usages
            processPreLoopPhis(loop, boundsExpressions, mainLoop, postLoop, mainMergeNode, postMergeNode);
            postLoopExitNode.setNext(continuationNode);

            // Clear out any unused EndNodes
            for (EndNode endNode : graph.getNodes().filter(EndNode.class)) {
                if (endNode.merge() == null) {
                    endNode.safeDelete();
                }
            }

            // Change the preLoop to execute one iteration for now
            updatePreLoopLimit(preLimit, preIv, preCounted);
            preLoopBegin.setLoopFrequency(1);
            mainLoopBegin.setLoopFrequency(Math.max(0.0, mainLoopBegin.loopFrequency() - 1));
            postLoopBegin.setLoopFrequency(Math.max(0.0, postLoopBegin.loopFrequency() - 1));
        }
    }

    public static void markGuards(LoopEx loop, LoopFragmentWhole mainLoop, LoopFragmentWhole postLoop) {
        for (GuardNode guard : loop.inside().nodes().filter(GuardNode.class)) {
            if (guard.getReason() == BoundsCheckException) {
                guard.clearMotionable();
                GuardNode mainGuardNode = mainLoop.getDuplicatedNode(guard);
                mainGuardNode.clearMotionable();
                GuardNode postGuardNode = postLoop.getDuplicatedNode(guard);
                postGuardNode.clearMotionable();
            }
        }
    }

    public static void cleanPostLoopExit(LoopExitNode postLoopExitNode) {
        List<Node> workList = new ArrayList<>();
        // Clean up the postLoopExitNode before we move usages from the pre loops exit
        for (Node usage : postLoopExitNode.usages().filter(GuardNode.class)) {
            workList.add(usage);
        }
        for (Node node : workList) {
            if (node.usages().isEmpty()) {
                node.safeDelete();
            }
        }
    }

    public static void processPreLoopPhis(LoopEx loop, List<Node> boundsExpressions, LoopFragmentWhole mainLoop, LoopFragmentWhole postLoop, AbstractMergeNode mainMergeNode,
                    AbstractMergeNode postMergeNode) {
        // process phis for the post loop
        LoopBeginNode preLoopBegin = loop.loopBegin();
        LoopBeginNode postLoopBegin = postLoop.getDuplicatedNode(preLoopBegin);
        StructuredGraph graph = preLoopBegin.graph();
        FrameState mainMergeState = null;
        if (boundsExpressions.isEmpty() == false) {
            mainMergeState = postLoopBegin.stateAfter().duplicateWithVirtualState();
        }
        for (PhiNode prePhiNode : preLoopBegin.valuePhis()) {
            PhiNode postPhiNode = postLoop.getDuplicatedNode(prePhiNode);
            PhiNode mainPhiNode = mainLoop.getDuplicatedNode(prePhiNode);
            ValuePhiNode postMergeIvValues = null;
            if (boundsExpressions.isEmpty()) {
                postPhiNode.initializeValueAt(0, mainPhiNode);
            } else {
                JavaKind elementKind = prePhiNode.getStackKind();
                Stamp postInitValueStamp = StampFactory.forKind(elementKind);
                postMergeIvValues = graph.addWithoutUnique(new ValuePhiNode(postInitValueStamp, mainMergeNode));
                postMergeIvValues.addInput(mainPhiNode);
                for (Node curNode : boundsExpressions) {
                    // Add as many pre phi values to carry as there are bounds (i.e. test paths)
                    if (curNode != null) {
                        postMergeIvValues.addInput(prePhiNode);
                    }
                }
                postPhiNode.initializeValueAt(0, postMergeIvValues);
                for (int i = 0; i < mainMergeState.values().count(); i++) {
                    if (mainMergeState.values().get(i) == postPhiNode) {
                        mainMergeState.values().set(i, postMergeIvValues);
                    }
                }
            }

            // Build a work list to update the pre loop phis to the post loops phis
            List<Node> workList = new ArrayList<>();
            for (Node usage : prePhiNode.usages()) {
                if (usage == mainPhiNode) {
                    continue;
                } else if (usage == postMergeIvValues) {
                    continue;
                } else if (usage instanceof ValuePhiNode) {
                    ValuePhiNode curPhi = (ValuePhiNode) usage;
                    if (curPhi.merge() != postMergeNode) {
                        continue;
                    }
                }
                if (loop.isOutsideLoop(usage)) {
                    workList.add(usage);
                }
            }
            for (Node node : workList) {
                node.replaceFirstInput(prePhiNode, postPhiNode);
            }
        }
        if (boundsExpressions.isEmpty() == false) {
            mainMergeNode.setStateAfter(mainMergeState);
        }

    }

    public static LoopExitNode getSingleExitFromLoop(LoopBeginNode curLoopBegin) {
        return curLoopBegin.loopExits().first();
    }

    public static LoopEndNode getSingleLoopEndFromLoop(LoopBeginNode curLoopBegin) {
        return curLoopBegin.loopEnds().first();
    }

    public static EndNode getSingleEndFromLoop(LoopBeginNode curLoopBegin) {
        EndNode curLoopEndNode = null;
        FixedWithNextNode node = curLoopBegin.loopExits().first();
        FixedNode lastNode = null;
        // Find the last node after the exit blocks starts
        while (true) {
            if (node == null) {
                break;
            }
            FixedNode next = node.next();
            if (next instanceof FixedWithNextNode) {
                node = (FixedWithNextNode) next;
            } else {
                lastNode = next;
                break;
            }
        }
        if (lastNode instanceof EndNode) {
            curLoopEndNode = (EndNode) lastNode;
        }
        return curLoopEndNode;
    }

    public static IfNode addEntryTestsForMainLoop(List<Node> boundsExpressions, AbstractBeginNode mainBeginNode, AbstractMergeNode mainMergeNode, ValueNode origLimit, boolean arrayLengthTrip) {
        IfNode firstIf = null;
        IfNode lastIf = null;
        GuardNode lastGuard = null;
        AbstractBeginNode mainBypassChecks = null;
        StructuredGraph graph = mainBeginNode.graph();

        /*
         * Manually lower the bounds expressions to IfNodes so that the branch side is connected to
         * the post loop and the fall side to either the next bounds check or to the main loop.
         */

        for (Node node : boundsExpressions) {
            if (node instanceof FixedAccessNode) {
                FixedAccessNode accessNode = (FixedAccessNode) node;
                GuardNode guard = (GuardNode) accessNode.getGuard();
                LogicNode condition = guard.getCondition();
                // Use a valid condition to construct main entry and bypass flow
                if (condition instanceof BinaryOpLogicNode) {
                    EndNode postLandingEnd = graph.add(new EndNode());
                    AbstractBeginNode postLandingNode = graph.add(new BeginNode());
                    postLandingNode.setNext(postLandingEnd);
                    mainMergeNode.addForwardEnd(postLandingEnd);
                    BinaryOpLogicNode logicNode = (BinaryOpLogicNode) condition;
                    ValueNode arrayLength = logicNode.getY();
                    if (arrayLength instanceof ReadNode) {
                        ReadNode readNode = (ReadNode) arrayLength;
                        AddressNode addressNode = readNode.getAddress();
                        ValueNode baseNode = addressNode.getBase();
                        // We already check this address above pre loop.
                        if (baseNode instanceof PiNode) {
                            PiNode piNode = (PiNode) baseNode;
                            piNode.setGuard(null);
                        }
                    }
                    // Compare the read length and the calculated limit expression.
                    LogicNode ifTest = graph.addWithoutUnique(new IntegerBelowNode(origLimit, arrayLength));
                    if (arrayLengthTrip) {
                        LogicNode additionalTest = graph.addWithoutUnique(new IntegerEqualsNode(origLimit, arrayLength));
                        ifTest = LogicNode.or(additionalTest, ifTest, 1.0);
                    }
                    AbstractBeginNode trueSuccessor;
                    AbstractBeginNode falseSuccessor;
                    if (guard.isNegated()) {
                        trueSuccessor = postLandingNode;
                        falseSuccessor = mainBeginNode;
                    } else {
                        trueSuccessor = mainBeginNode;
                        falseSuccessor = postLandingNode;
                    }
                    // Fixup lastIf before minting another one so there is no reuse.
                    if (lastIf != null) {
                        mainBypassChecks = graph.add(new BeginNode());
                        if (lastGuard.isNegated()) {
                            lastIf.setFalseSuccessor(mainBypassChecks);
                        } else {
                            lastIf.setTrueSuccessor(mainBypassChecks);
                        }
                    }
                    IfNode ifNode = graph.add(new IfNode(ifTest, trueSuccessor, falseSuccessor, trueSuccessor == mainBeginNode ? 1 : 0));
                    ifNode.setNotSimplifiable();
                    if (lastIf != null) {
                        mainBypassChecks.setNext(ifNode);
                    } else {
                        firstIf = ifNode;
                    }
                    lastGuard = guard;
                    lastIf = ifNode;
                }
            }
        }
        return firstIf;
    }

    public static boolean pruneBoundsExpressions(IfNode preLimit, InductionVariable preIv, List<Node> boundsExpressions) {
        boolean arrayLengthTrip = false;
        if (boundsExpressions.isEmpty() == false) {
            List<Node> workList = new ArrayList<>();
            LogicNode ifTest = preLimit.condition();
            CompareNode compareNode = (CompareNode) ifTest;
            ValueNode checkValue = null;
            ValueNode prePhi = preIv.valueNode();
            if (compareNode.getX() == prePhi) {
                checkValue = compareNode.getY();
            } else if (compareNode.getY() == prePhi) {
                checkValue = compareNode.getX();
            }
            if (checkValue instanceof ReadNode) {
                ReadNode checkRead = (ReadNode) checkValue;
                AddressNode offsetAddress = checkRead.getAddress();
                for (Node node : boundsExpressions) {
                    if (node instanceof FixedAccessNode) {
                        FixedAccessNode accessNode = (FixedAccessNode) node;
                        GuardNode guard = (GuardNode) accessNode.getGuard();
                        LogicNode condition = guard.getCondition();
                        if (condition instanceof BinaryOpLogicNode) {
                            BinaryOpLogicNode logicNode = (BinaryOpLogicNode) condition;
                            ValueNode arrayLength = logicNode.getY();
                            if (arrayLength instanceof ReadNode) {
                                ReadNode readLength = (ReadNode) arrayLength;
                                AddressNode curOffsetAddress = readLength.getAddress();
                                if (curOffsetAddress == offsetAddress) {
                                    workList.add(node);
                                    arrayLengthTrip = true;
                                }
                            }
                        }
                    }
                }
                for (Node node : workList) {
                    boundsExpressions.remove(node);
                }
            }
        }
        return arrayLengthTrip;
    }

    public static ValueNode getPreLoopMaxBound(IfNode preLimit, InductionVariable preIv, CountedLoopInfo preCounted) {
        ValueNode upperBound = null;
        StructuredGraph graph = preLimit.graph();
        LogicNode ifTest = preLimit.condition();
        ValueNode prePhi = preIv.valueNode();
        CompareNode compareNode = (CompareNode) ifTest;
        if (compareNode.getX() == prePhi) {
            upperBound = compareNode.getY();
        } else if (compareNode.getY() == prePhi) {
            upperBound = compareNode.getX();
        }
        ValueNode initIv = preCounted.getStart();
        if (upperBound != null) {
            return graph.unique(new ConditionalNode(graph.unique(new IntegerLessThanNode(initIv, upperBound)), upperBound, initIv));
        } else {
            return null;
        }
    }

    public static void updatePreLoopLimit(IfNode preLimit, InductionVariable preIv, CountedLoopInfo preCounted) {
        // Update the pre loops limit test
        StructuredGraph graph = preLimit.graph();
        LogicNode ifTest = preLimit.condition();
        CompareNode compareNode = (CompareNode) ifTest;
        ValueNode varX = null;
        ValueNode varY = null;
        ValueNode prePhi = preIv.valueNode();
        // Check direction and make new limit one iteration
        ValueNode initIv = preCounted.getStart();
        ValueNode newLimit = null;
        if (preIv.direction() == Direction.Up) {
            newLimit = add(graph, initIv, preIv.strideNode());
        } else {
            newLimit = sub(graph, initIv, preIv.strideNode());
        }
        // Fetch the variable we are not replacing and configure the one we are
        if (compareNode.getX() == prePhi) {
            varX = prePhi;
            varY = newLimit;
        } else if (compareNode.getY() == prePhi) {
            varY = prePhi;
            varX = newLimit;
        }
        // Re-wire the new condition into preLimit
        if (ifTest instanceof IntegerLessThanNode) {
            LogicNode newIfTest = graph.addWithoutUnique(new IntegerLessThanNode(varX, varY));
            ifTest.replaceAndDelete(newIfTest);
        } else if (ifTest instanceof IntegerEqualsNode) {
            LogicNode newIfTest = graph.addWithoutUnique(new IntegerEqualsNode(varX, varY));
            ifTest.replaceAndDelete(newIfTest);
        }
    }

    public static void removeChecks(LoopFragmentWhole origLoop, LoopFragmentWhole targetLoop) {
        LoopBeginNode origLoopBegin = origLoop.loop().loopBegin();
        LoopBeginNode targetLoopBegin = targetLoop.getDuplicatedNode(origLoopBegin);
        List<Node> workList = new ArrayList<>();
        for (Node preNode : origLoop.loop().inside().nodes()) {
            Node node = targetLoop.getDuplicatedNode(preNode);
            if (node instanceof FixedAccessNode) {
                FixedAccessNode accessNode = (FixedAccessNode) node;
                Node guardNode = (Node) accessNode.getGuard();
                if (guardNode instanceof GuardNode) {
                    GuardNode guard = (GuardNode) guardNode;
                    if (guard.getReason() == BoundsCheckException) {
                        accessNode.replaceFirstInput(guard, targetLoopBegin);
                        if (workList.contains(guard) == false) {
                            workList.add(guard);
                        }
                    }
                }
            } else if (node instanceof PiNode) {
                PiNode piNode = (PiNode) node;
                Node guardNode = (Node) piNode.getGuard();
                if (guardNode instanceof GuardNode) {
                    GuardNode guard = (GuardNode) guardNode;
                    if (guard.getReason() == BoundsCheckException) {
                        piNode.replaceFirstInput(guard, targetLoopBegin);
                    }
                }
            }
        }
        for (Node node : workList) {
            GuardNode guard = (GuardNode) node;
            LogicNode condition = guard.getCondition();
            if (guard.hasNoUsages()) {
                guard.safeDelete();
            }
            if (condition.hasNoUsages()) {
                condition.safeDelete();
            }
        }
    }

    public static List<Node> findBoundsExpressions(LoopEx loop) {
        List<Node> boundsExpressions = new ArrayList<>();
        for (Node node : loop.inside().nodes()) {
            if (node instanceof FixedAccessNode) {
                FixedAccessNode accessNode = (FixedAccessNode) node;
                if (accessNode.getGuard() != null) {
                    GuardingNode guarding = accessNode.getGuard();
                    if (guarding instanceof GuardNode) {
                        GuardNode guard = (GuardNode) guarding;
                        if (guard.getReason() == BoundsCheckException) {
                            if (boundsExpressions.isEmpty()) {
                                boundsExpressions.add(node);
                            } else if (isUniqueAddress(node, boundsExpressions) == true) {
                                boundsExpressions.add(node);
                            }
                        }
                    }
                }
            }
        }
        return boundsExpressions;
    }

    public static boolean isUniqueAddress(Node inNode, List<Node> boundsExpressions) {
        boolean isUniqueAddress = true;
        AddressNode offsetAddress = null;
        if (inNode instanceof FixedAccessNode) {
            FixedAccessNode accessInNode = (FixedAccessNode) inNode;
            offsetAddress = accessInNode.getAddress();
            if (offsetAddress != null) {
                for (Node node : boundsExpressions) {
                    if (node instanceof FixedAccessNode) {
                        FixedAccessNode validNode = (FixedAccessNode) node;
                        AddressNode validAddress = validNode.getAddress();
                        // If two addresses have the same base address, they have the same bounds.
                        if (validAddress.getBase() == offsetAddress.getBase()) {
                            isUniqueAddress = false;
                            break;
                        }
                    }
                }
            }
        }
        return isUniqueAddress;
    }

    public static List<ControlSplitNode> findUnswitchable(LoopEx loop) {
        List<ControlSplitNode> controls = null;
        ValueNode invariantValue = null;
        for (IfNode ifNode : loop.whole().nodes().filter(IfNode.class)) {
            if (loop.isOutsideLoop(ifNode.condition())) {
                if (controls == null) {
                    invariantValue = ifNode.condition();
                    controls = new ArrayList<>();
                    controls.add(ifNode);
                } else if (ifNode.condition() == invariantValue) {
                    controls.add(ifNode);
                }
            }
        }
        if (controls == null) {
            SwitchNode firstSwitch = null;
            for (SwitchNode switchNode : loop.whole().nodes().filter(SwitchNode.class)) {
                if (switchNode.successors().count() > 1 && loop.isOutsideLoop(switchNode.value())) {
                    if (controls == null) {
                        firstSwitch = switchNode;
                        invariantValue = switchNode.value();
                        controls = new ArrayList<>();
                        controls.add(switchNode);
                    } else if (switchNode.value() == invariantValue && firstSwitch.structureEquals(switchNode)) {
                        // Only collect switches which test the same values in the same order
                        controls.add(switchNode);
                    }
                }
            }
        }
        return controls;
    }

    public static boolean isQualifyingLoop(LoopEx loop) {
        LoopBeginNode curBeginNode = loop.loopBegin();
        boolean isCanonical = (curBeginNode.loopFrequency() > 2.0 && loop.canDuplicateLoop());
        if (isCanonical) {
            isCanonical = loop.loop().getChildren().isEmpty();
        }
        if (isCanonical) {
            isCanonical = false;
            ValueNode outerLoopPhi = limitTestContainsOuterPhi(loop);
            CountedLoopInfo counted = loop.counted();
            InductionVariable iv = counted.getCounter();
            // Does the original loop have constant stride
            if (iv.isConstantStride()) {
                ValueNode loopPhi = iv.valueNode();
                boolean splittingOk = true;
                // If we have a zero trip loop, we will need to avoid splitting for now.
                if (outerLoopPhi != null) {
                    ValueNode initIv = counted.getStart();
                    if (initIv instanceof ConstantNode) {
                        ValuePhiNode cmpIv = (ValuePhiNode) outerLoopPhi;
                        ValueNode cmpInit = cmpIv.valueAt(0);
                        if (initIv == cmpInit) {
                            splittingOk = false;
                        }
                    }
                }
                // Does this loop have a single exit/single exit?
                if (curBeginNode.loopExits().count() == 1 && curBeginNode.isSingleEntryLoop()) {
                    EndNode endNode = getSingleEndFromLoop(curBeginNode);
                    if (endNode == null) {
                        splittingOk = false;
                    } else {
                        AbstractMergeNode mergeNode = endNode.merge();
                        int loopEndCount = 1;
                        for (int i = 1; i < mergeNode.forwardEndCount(); i++) {
                            EndNode curEnd = mergeNode.forwardEndAt(i);
                            if (curEnd.predecessor() instanceof LoopExitNode) {
                                loopEndCount++;
                            }
                        }
                        // This loop is tied to complex control flow
                        if (loopEndCount > 1) {
                            splittingOk = false;
                        } else if (mergeNode.forwardEndCount() > 2) {
                            splittingOk = false;
                        }
                    }
                    if (splittingOk) {
                        // Look for other kinds of excepting guards, calls or side effects
                        int boundsCount = 0;
                        for (Node node : loop.inside().nodes()) {
                            if (node instanceof GuardNode) {
                                GuardNode guard = (GuardNode) node;
                                if ((guard.getReason() != BoundsCheckException) && (guard.getReason() != NullCheckException)) {
                                    boundsCount = 0;
                                    break;
                                } else if (guard.getReason() == BoundsCheckException) {
                                    if (canEliminateBounds(loopPhi, guard) == false) {
                                        boundsCount = 0;
                                        break;
                                    }
                                    boundsCount++;
                                }
                            } else if (node instanceof CommitAllocationNode) {
                                CommitAllocationNode curNode = (CommitAllocationNode) node;
                                if (curNode.hasLocks()) {
                                    boundsCount = 0;
                                    break;
                                }
                            } else if (node instanceof InvokeNode) {
                                boundsCount = 0;
                                break;
                            }
                        }
                        if (boundsCount > 0) {
                            if (loopHasPhiFrameState(curBeginNode)) {
                                isCanonical = true;
                            }
                        }
                    }
                }
            }
        }
        return isCanonical;
    }

    public static boolean loopHasPhiFrameState(LoopBeginNode curBeginNode) {
        boolean foundPhi = false;
        FrameState curState = curBeginNode.stateAfter();
        for (PhiNode phiNode : curBeginNode.valuePhis()) {
            for (int i = 0; i < curState.values().count(); i++) {
                if (curState.values().get(i) == phiNode) {
                    foundPhi = true;
                    break;
                }
            }
            if (foundPhi) {
                break;
            }
        }
        return foundPhi;
    }

    public static ValueNode limitTestContainsOuterPhi(LoopEx loop) {
        ValueNode parentPhi = null;
        CountedLoopInfo counted = loop.counted();
        IfNode loopLimit = counted.getLimitTest();
        LogicNode ifTest = loopLimit.condition();
        CompareNode compareNode = (CompareNode) ifTest;
        ValueNode varX = compareNode.getX();
        ValueNode varY = compareNode.getY();
        InductionVariable iv = counted.getCounter();
        ValueNode phi = iv.valueNode();
        if (varX instanceof ValuePhiNode && varX != phi) {
            if (phi instanceof ValuePhiNode) {
                if (isParentLoopPhiVar(varX, phi)) {
                    parentPhi = varX;
                }
            }
        } else if (varY instanceof ValuePhiNode && varY != phi) {
            if (phi instanceof ValuePhiNode) {
                if (isParentLoopPhiVar(varY, phi)) {
                    parentPhi = varY;
                }
            }
        }
        return parentPhi;
    }

    public static boolean canEliminateBounds(ValueNode phi, GuardNode guard) {
        boolean boundsOk = false;
        LogicNode condition = guard.getCondition();
        if (condition instanceof IntegerBelowNode) {
            CompareNode compareNode = (CompareNode) condition;
            ValueNode loopVar = compareNode.getX();
            if (loopVar == phi) {
                boundsOk = true;
            } else if (loopVar instanceof AddNode) {
                AddNode node = (AddNode) loopVar;
                ValueNode varX = node.getX();
                ValueNode varY = node.getY();
                if (varX == phi && varY instanceof ConstantNode) {
                    boundsOk = true;
                }
            } else if (loopVar instanceof SubNode) {
                SubNode node = (SubNode) loopVar;
                ValueNode varX = node.getX();
                ValueNode varY = node.getY();
                if (varX == phi && varY instanceof ConstantNode) {
                    boundsOk = true;
                }
            }
        }
        return boundsOk;
    }

    public static boolean isParentLoopPhiVar(ValueNode phi, ValueNode inductionPhi) {
        boolean parentLoopPhi = false;
        ValuePhiNode cmpPhi = (ValuePhiNode) phi;
        ValuePhiNode curPhi = (ValuePhiNode) inductionPhi;
        if (cmpPhi.merge() instanceof LoopBeginNode) {
            if (cmpPhi.merge() != curPhi.merge()) {
                parentLoopPhi = true;
            }
        }
        return parentLoopPhi;
    }

    public static boolean isUnrollableLoop(LoopEx loop) {
        LoopBeginNode curBeginNode = loop.loopBegin();
        boolean isCanonical = false;
        if (curBeginNode.isMainLoop()) {
            // Flow-less loops to partial unroll for now
            if (loop.loop().getBlocks().size() < 3) {
                isCanonical = true;
            }
        }
        if (isCanonical) {
            for (PhiNode phi : curBeginNode.valuePhis()) {
                if (phi instanceof MemoryPhiNode) {
                    continue;
                }
                InductionVariable iv = loop.getInductionVariables().get(phi);
                if (iv instanceof DerivedInductionVariable) {
                    isCanonical = false;
                    break;
                }
                if (iv == null) {
                    // No unclassified derived induction variables
                    isCanonical = false;
                    break;
                }
            }
        }
        return isCanonical;
    }
}
