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
import org.graalvm.compiler.graph.iterators.NodeIterable;
import org.graalvm.compiler.core.common.cfg.Loop;
import org.graalvm.compiler.core.common.RetryableBailoutException;
import org.graalvm.compiler.core.common.type.Stamp;
import org.graalvm.compiler.core.common.type.StampFactory;
import org.graalvm.compiler.debug.Debug;
import org.graalvm.compiler.graph.Node;
import org.graalvm.compiler.graph.Position;
import org.graalvm.compiler.loop.BasicInductionVariable;
import org.graalvm.compiler.loop.CountedLoopInfo;
import org.graalvm.compiler.loop.InductionVariable;
import org.graalvm.compiler.loop.InductionVariable.Direction;
import static org.graalvm.compiler.loop.MathUtil.add;
import static org.graalvm.compiler.loop.MathUtil.sub;
import org.graalvm.compiler.loop.LoopEx;
import org.graalvm.compiler.loop.LoopFragmentWhole;
import org.graalvm.compiler.loop.LoopFragment;
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
import org.graalvm.compiler.nodes.LoopExitNode;
import org.graalvm.compiler.nodes.MergeNode;
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
import org.graalvm.compiler.nodes.calc.SubNode;
import org.graalvm.compiler.nodes.calc.ZeroExtendNode;
import org.graalvm.compiler.nodes.cfg.Block;
import org.graalvm.compiler.nodes.extended.GuardingNode;
import org.graalvm.compiler.nodes.extended.SwitchNode;
import org.graalvm.compiler.nodes.memory.ReadNode;
import org.graalvm.compiler.nodes.memory.WriteNode;
import org.graalvm.compiler.nodes.memory.HeapAccess.BarrierType;
import org.graalvm.compiler.nodes.memory.address.AddressNode;
import org.graalvm.compiler.nodes.memory.address.OffsetAddressNode;
import org.graalvm.compiler.nodes.virtual.CommitAllocationNode;
import org.graalvm.compiler.phases.common.CanonicalizerPhase;
import org.graalvm.compiler.phases.tiers.PhaseContext;

import jdk.vm.ci.meta.JavaConstant;
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

    public static void insertPrePostLoops(LoopEx loop, PhaseContext context, CanonicalizerPhase canonicalizer, StructuredGraph graph) {
        LoopFragmentWhole preLoop = loop.whole();
        CountedLoopInfo preCounted = preLoop.loop().counted();
        IfNode preLimit = preCounted.getLimitTest();
        List<Node> boundsExpressions = findBoundsExpressions(preLoop.loop());
        if (preLimit != null) {
            LoopBeginNode preLoopBegin = loop.loopBegin();
            EndNode preEndNode = getSingleEndFromLoop(preLoopBegin);
            AbstractMergeNode preMergeNode = preEndNode.merge();
            InductionVariable preIv = preCounted.getCounter();
            int phiIndex = 0;
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

            // Handle original code has guards loaded and the old continuation code.
            AbstractMergeNode postMergeNode = preMergeNode;
            LoopBeginNode postLoopBegin = postLoop.getDuplicatedNode(preLoopBegin);
            postLoopBegin.setPostLoop();
            AbstractEndNode postEntryNode = postLoopBegin.forwardEnd();
            EndNode postEndNode = getSingleEndFromLoop(postLoopBegin);
            preMergeNode = postEndNode.merge();
            preMergeNode.clearEnds();
            AbstractBeginNode preLandingNode = graph.add(new BeginNode());
            LoopExitNode postLoopExitNode = getSingleExitFromLoop(postLoopBegin);
            preLoopExitNode.setNext(preLandingNode);
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
            if (haveBounds) {
                removeChecks(preLoop, mainLoop);
            }

            // Update the main loop phi initialization to carry from the pre loop
            for (PhiNode prePhiNode : preLoopBegin.valuePhis()) {
                PhiNode mainPhiNode = mainLoop.getDuplicatedNode(prePhiNode);
                mainPhiNode.initializeValueAt(phiIndex, prePhiNode);
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
                preLandingNode.setNext(mainLoopBegin.forwardEnd());
            } else {
                AbstractBeginNode mainBeginNode = BeginNode.begin(mainLoopBegin.forwardEnd());
                // Add limit based range checks to guard main loop entry/execution
                ValueNode origLimit = getPreLoopMaxBound(preLimit, preIv, preCounted);
                assert (origLimit != null);
                mainMergeNode.clearEnds();
                mainMergeNode.addForwardEnd(mainEndNode);
                mainMergeNode.setNext(postEntryNode);
                IfNode firstIf = addEntryTestsForMainLoop(boundsExpressions, mainBeginNode, mainMergeNode, origLimit, arrayLengthTrip);
                assert (firstIf != null);
                preLandingNode.setNext(firstIf);
            }

            // Add and update any phi edges as per merge usage as needed and update usages
            processPreLoopPhis(loop, boundsExpressions, mainLoop, postLoop, mainMergeNode, postMergeNode);
            postLoopExitNode.setNext(continuationNode);

            // Clear out any unused EndNodes
            for (Node n : graph.getNodes()) {
                if (n instanceof EndNode) {
                    EndNode endNode = (EndNode) n;
                    if (endNode.merge() == null) {
                        endNode.safeDelete();
                    }
                }
            }

            // Change the preLoop to execute one iteration for now
            updatePreLoopLimit(preLimit, preIv, preCounted);
            preLoopBegin.setLoopFrequency(1);
        }
    }

    public static void processPreLoopPhis(LoopEx loop, List<Node> boundsExpressions, LoopFragmentWhole mainLoop, LoopFragmentWhole postLoop, AbstractMergeNode mainMergeNode,
                    AbstractMergeNode postMergeNode) {
        // process phis for the post loop
        int phiIndex = 0;
        LoopBeginNode preLoopBegin = loop.loopBegin();
        LoopBeginNode postLoopBegin = postLoop.getDuplicatedNode(preLoopBegin);
        StructuredGraph graph = preLoopBegin.graph();
        for (PhiNode prePhiNode : preLoopBegin.valuePhis()) {
            PhiNode postPhiNode = postLoop.getDuplicatedNode(prePhiNode);
            PhiNode mainPhiNode = mainLoop.getDuplicatedNode(prePhiNode);
            ValuePhiNode postMergeIvValues = null;
            if (boundsExpressions.isEmpty()) {
                postPhiNode.initializeValueAt(phiIndex, mainPhiNode);
            } else {
                JavaKind elementKind = prePhiNode.getStackKind();
                Stamp postInitValueStamp = StampFactory.forKind(elementKind);
                postMergeIvValues = graph.addWithoutUnique(new ValuePhiNode(postInitValueStamp, mainMergeNode));
                postMergeIvValues.addInput(mainPhiNode);
                for (Node curNode : boundsExpressions) {
                    // Add as many pre phi values to carry as there are bounds (i.e. test paths)
                    postMergeIvValues.addInput(prePhiNode);
                }
                postPhiNode.initializeValueAt(phiIndex, postMergeIvValues);
            }

            // Build a work list to update the pre loop phis to the post loops phis
            List<Node> workList = null;
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
                    if (workList == null) {
                        workList = new ArrayList<>();
                    }
                    workList.add(usage);
                }
            }
            if (workList != null) {
                for (Node node : workList) {
                    node.replaceFirstInput(prePhiNode, postPhiNode);
                }
            }
        }
    }

    public static LoopExitNode getSingleExitFromLoop(LoopBeginNode curLoopBegin) {
        LoopExitNode exitNode = null;
        for (LoopExitNode curLoopExit : curLoopBegin.loopExits()) {
            exitNode = curLoopExit;
            break;
        }
        return exitNode;
    }

    public static EndNode getSingleEndFromLoop(LoopBeginNode curLoopBegin) {
        EndNode curLoopEndNode = null;
        FixedWithNextNode node = null;
        FixedNode lastNode = null;
        for (LoopExitNode curLoopExit : curLoopBegin.loopExits()) {
            node = (FixedWithNextNode) curLoopExit;
            break;
        }
        // Find the last node after the exit blocks starts
        while (true) {
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
            LogicNode condition = null;
            GuardNode guard = null;
            if (node instanceof ReadNode) {
                ReadNode readNode = (ReadNode) node;
                guard = (GuardNode) readNode.getGuard();
                condition = guard.getCondition();
            } else if (node instanceof WriteNode) {
                WriteNode writeNode = (WriteNode) node;
                guard = (GuardNode) writeNode.getGuard();
                condition = guard.getCondition();
            }

            EndNode postLandingEnd = graph.add(new EndNode());
            AbstractBeginNode postLandingNode = graph.add(new BeginNode());
            postLandingNode.setNext(postLandingEnd);
            mainMergeNode.addForwardEnd(postLandingEnd);

            // Use a valid condition to construct main entry and bypass flow
            if (condition != null) {
                if (condition instanceof BinaryOpLogicNode) {
                    BinaryOpLogicNode logicNode = (BinaryOpLogicNode) condition;
                    ValueNode arrayLength = logicNode.getY();
                    // Compare the read length and the calculated limit expression.
                    LogicNode ifTest = (LogicNode) graph.addWithoutUnique(new IntegerBelowNode(origLimit, arrayLength));
                    if (arrayLengthTrip) {
                        LogicNode additionalTest = (LogicNode) graph.addWithoutUnique(new IntegerEqualsNode(origLimit, arrayLength));
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
            List<Node> workList = null;
            StructuredGraph graph = preLimit.graph();
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
                OffsetAddressNode offsetAddress = (OffsetAddressNode) checkRead.getAddress();
                for (Node node : boundsExpressions) {
                    LogicNode condition = null;
                    GuardNode guard = null;
                    if (node instanceof ReadNode) {
                        ReadNode readNode = (ReadNode) node;
                        guard = (GuardNode) readNode.getGuard();
                        condition = guard.getCondition();
                    } else if (node instanceof WriteNode) {
                        WriteNode writeNode = (WriteNode) node;
                        guard = (GuardNode) writeNode.getGuard();
                        condition = guard.getCondition();
                    }
                    if (condition != null) {
                        if (condition instanceof BinaryOpLogicNode) {
                            BinaryOpLogicNode logicNode = (BinaryOpLogicNode) condition;
                            ValueNode arrayLength = logicNode.getY();
                            if (arrayLength instanceof ReadNode) {
                                ReadNode readLength = (ReadNode) arrayLength;
                                OffsetAddressNode curOffsetAddress = (OffsetAddressNode) readLength.getAddress();
                                if (curOffsetAddress.getBase() == offsetAddress.getBase()) {
                                    if (curOffsetAddress.getOffset() == offsetAddress.getOffset()) {
                                        if (workList == null) {
                                            workList = new ArrayList<>();
                                        }
                                        workList.add(node);
                                        arrayLengthTrip = true;
                                    }
                                }
                            }
                        }
                    }
                }
                if (workList != null) {
                    for (Node node : workList) {
                        boundsExpressions.remove(node);
                    }
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
        return graph.unique(new ConditionalNode(graph.unique(new IntegerLessThanNode(initIv, upperBound)), upperBound, initIv));
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
            ifTest.replaceAtUsages(newIfTest);
            ifTest.safeDelete();
        } else if (ifTest instanceof IntegerEqualsNode) {
            LogicNode newIfTest = graph.addWithoutUnique(new IntegerEqualsNode(varX, varY));
            ifTest.replaceAtUsages(newIfTest);
            ifTest.safeDelete();
        }
    }

    public static void removeChecks(LoopFragmentWhole origLoop, LoopFragmentWhole targetLoop) {
        StructuredGraph graph = origLoop.graph();
        NodeIterable<AbstractBeginNode> blocks = LoopFragment.toHirBlocks(origLoop.loop().loop().getBlocks());
        for (AbstractBeginNode origNode : blocks) {
            AbstractBeginNode blockNode = targetLoop.getDuplicatedNode(origNode);
            if (blockNode instanceof LoopExitNode) {
                continue;
            } else if (blockNode instanceof LoopBeginNode) {
                continue;
            } else if (blockNode instanceof AbstractBeginNode) {
                for (Node node : blockNode.getBlockNodes()) {
                    GuardNode newGuard = null;
                    if (node instanceof ReadNode) {
                        ReadNode readNode = (ReadNode) node;
                        GuardNode guard = (GuardNode) readNode.getGuard();
                        if (guard == null) {
                            continue;
                        }
                        if (guard.getReason() == BoundsCheckException) {
                            newGuard = guard;
                        } else if (guard.getReason() == NullCheckException) {
                            newGuard = graph.addWithoutUnique(new GuardNode(guard.getCondition(), blockNode, guard.getReason(), guard.getAction(), guard.isNegated(), guard.getSpeculation()));
                            readNode.setGuard((GuardingNode) newGuard);
                        }
                    } else if (node instanceof WriteNode) {
                        WriteNode writeNode = (WriteNode) node;
                        GuardNode guard = (GuardNode) writeNode.getGuard();
                        if (guard == null) {
                            continue;
                        }
                        if (guard.getReason() == BoundsCheckException) {
                            newGuard = guard;
                        }
                    }
                    if (newGuard != null) {
                        newGuard.clearReason();
                        newGuard.clearAction();
                    }
                }
            }
        }
    }

    public static List<Node> findBoundsExpressions(LoopEx loop) {
        List<Node> boundsExpressions = new ArrayList<>();
        for (Node node : loop.inside().nodes()) {
            boolean foundCandidate = false;
            if (node instanceof ReadNode) {
                ReadNode readNode = (ReadNode) node;
                if (readNode.getGuard() != null) {
                    GuardingNode guarding = readNode.getGuard();
                    if (guarding instanceof GuardNode) {
                        GuardNode guard = (GuardNode) guarding;
                        if (guard.getReason() == BoundsCheckException) {
                            foundCandidate = true;
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
                            foundCandidate = true;
                        }
                    }
                }
            }
            if (foundCandidate) {
                if (boundsExpressions.isEmpty()) {
                    boundsExpressions.add(node);
                } else if (isUniqueAddress(node, boundsExpressions) == true) {
                    boundsExpressions.add(node);
                }
            }
        }
        return boundsExpressions;
    }

    public static boolean isUniqueAddress(Node inNode, List<Node> boundsExpressions) {
        boolean isUniqueAddress = true;
        boolean checkRead = true;
        OffsetAddressNode offsetAddress = null;
        if (inNode instanceof ReadNode) {
            ReadNode readNode = (ReadNode) inNode;
            offsetAddress = (OffsetAddressNode) readNode.getAddress();
        } else if (inNode instanceof WriteNode) {
            WriteNode writeNode = (WriteNode) inNode;
            offsetAddress = (OffsetAddressNode) writeNode.getAddress();
            checkRead = false;
        }
        if (offsetAddress != null) {
            for (Node node : boundsExpressions) {
                if (node instanceof ReadNode) {
                    // Always compare same type
                    if (checkRead == false) {
                        continue;
                    }
                    ReadNode validNode = (ReadNode) node;
                    OffsetAddressNode validOffsetAddress = (OffsetAddressNode) validNode.getAddress();
                    // If two reads have the same base address, they have the same bounds.
                    if (validOffsetAddress.getBase() == offsetAddress.getBase()) {
                        isUniqueAddress = false;
                        break;
                    }
                } else if (node instanceof WriteNode) {
                    // Always compare same type
                    if (checkRead) {
                        continue;
                    }
                    WriteNode validNode = (WriteNode) node;
                    OffsetAddressNode validOffsetAddress = (OffsetAddressNode) validNode.getAddress();
                    // If two writes have the same base address, they have the same bounds.
                    if (validOffsetAddress.getBase() == offsetAddress.getBase()) {
                        isUniqueAddress = false;
                        break;
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
        boolean isCanonical = (curBeginNode.loopFrequency() > 1.0 && loop.canDuplicateLoop());
        Loop<Block> curLoop = loop.loop();
        for (Loop<Block> child : curLoop.getChildren()) {
            isCanonical = false;
            break;
        }
        if (isCanonical) {
            isCanonical = false;
            ValueNode outerLoopPhi = limitTestContainsOuterPhi(loop);
            LoopFragmentWhole origLoop = loop.whole();
            NodeIterable<AbstractBeginNode> blocks = LoopFragment.toHirBlocks(origLoop.loop().loop().getBlocks());
            // TODO - need a cost metric when flow present and need to extend design some
            if (blocks.count() < 20) {
                CountedLoopInfo counted = loop.counted();
                InductionVariable iv = counted.getCounter();
                // Does the original loop have constant stride
                if (iv.isConstantStride()) {
                    ValueNode loopPhi = iv.valueNode();
                    boolean splittingOk = true;
                    // If we have a zero trip loop scenario, we will need to avoid splitting for now.
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
                    // Does this loop have a single exit?
                    if (curBeginNode.loopExits().count() == 1 && splittingOk) {
                        EndNode endNode = getSingleEndFromLoop(curBeginNode);
                        // Loops connected simply for now
                        if (endNode != null) {
                            // Look for other kinds of excepting guards, calls or side effects
                            if (curBeginNode.isSingleEntryLoop()) {
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
                                    isCanonical = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return isCanonical;
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
            if (isParentLoopPhiVar(varX, phi)) {
                parentPhi = varX;
            }
        } else if (varY instanceof ValuePhiNode && varY != phi) {
            if (isParentLoopPhiVar(varY, phi)) {
               parentPhi = varY;
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
}
