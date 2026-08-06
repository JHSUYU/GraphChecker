package edu.uva.liftlab.graphchecker.causynth;

import soot.Body;
import soot.Unit;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.TrapUnitGraph;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Set;

/** Identifies branch units that decide whether a natural loop continues. */
final class CfgLoopControl {
    private CfgLoopControl() {
    }

    /**
     * Returns branches with at least one successor inside a natural loop and
     * at least one successor outside it.  The loops come from dominance-
     * proved CFG backedges, so a semantic branch merely located in a loop is
     * not classified as iteration control.
     */
    static Set<Unit> guards(Body body, UnitGraph graph) {
        if (body == null || graph == null) {
            return Collections.emptySet();
        }
        // BriefUnitGraph makes every catch handler a synthetic CFG head.
        // That breaks dominance for a perfectly reducible loop containing a
        // caught operation (the handler appears to reach the latch without
        // passing the header).  Trap edges restore the real entry path and
        // therefore the natural-loop proof without requiring value/type
        // analysis.
        UnitGraph loopGraph = body.getTraps().isEmpty()
                ? graph : new TrapUnitGraph(body);
        Set<Unit> result = identitySet();
        MHGDominatorsFinder<Unit> dominators =
                new MHGDominatorsFinder<>(loopGraph);
        for (Unit tail : loopGraph) {
            for (Unit header : loopGraph.getSuccsOf(tail)) {
                if (!dominators.isDominatedBy(tail, header)) {
                    continue;
                }
                Set<Unit> loop = naturalLoop(loopGraph, header, tail);
                for (Unit candidate : loop) {
                    CausynthBranchShape shape =
                            CausynthBranchShape.from(body, candidate);
                    if (shape == null || shape.successorCount() < 2) {
                        continue;
                    }
                    boolean continues = false;
                    boolean exits = false;
                    for (Unit successor : shape.successors) {
                        if (loop.contains(successor)) {
                            continues = true;
                        } else {
                            exits = true;
                        }
                    }
                    if (continues && exits) {
                        result.add(candidate);
                    }
                }
            }
        }
        return result;
    }

    private static Set<Unit> naturalLoop(UnitGraph graph, Unit header,
                                         Unit tail) {
        Set<Unit> loop = identitySet();
        loop.add(header);
        loop.add(tail);
        Deque<Unit> work = new ArrayDeque<>();
        if (tail != header) work.add(tail);
        while (!work.isEmpty()) {
            Unit current = work.removeFirst();
            for (Unit predecessor : graph.getPredsOf(current)) {
                if (loop.add(predecessor) && predecessor != header) {
                    work.addLast(predecessor);
                }
            }
        }
        return loop;
    }

    private static Set<Unit> identitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<Unit, Boolean>());
    }
}
