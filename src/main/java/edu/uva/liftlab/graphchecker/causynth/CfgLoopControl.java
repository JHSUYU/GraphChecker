package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import soot.Body;
import soot.Local;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.LengthExpr;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.TrapUnitGraph;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The one CFG a method's loop questions are answered on, and the branch units
 * that decide whether a natural loop continues.
 */
final class CfgLoopControl {
    /**
     * Names the cycles the loop CFG deliberately refuses to call loops, so
     * that dropping them is a stated coverage boundary and not a silent one.
     */
    static final String GAP_EXCEPTION_CYCLE_UNBOUNDED =
            "CONCOLIC_LOOP_EXCEPTION_CYCLE_UNBOUNDED";

    private CfgLoopControl() {
    }

    /**
     * One method's loop CFG.  Backedge discovery, dominance, natural-loop
     * membership, iteration guards, and bound instrumentation all read this
     * one object, so a loop can never be discovered on one graph and
     * instrumented on another.
     *
     * <p>Loop structure -- dominance and natural-loop membership -- is read
     * from the trap-augmented CFG whenever the body has traps.  Without trap
     * edges a handler has no predecessor at all, so
     * {@link soot.toolkits.graph.BriefUnitGraph} presents it as a second CFG
     * entry, and a perfectly reducible loop containing a caught operation
     * loses its dominance proof: the handler appears to reach the latch
     * without passing the header.  The same edges are what put the protected
     * body of a retry loop inside that loop, where it belongs, when the only
     * way back to the latch is through the handler.</p>
     *
     * <p>A backedge, however, is only ever one of the method's ordinary
     * transfers.  A trap edge is not an iteration: it is one abrupt transfer
     * out of a protected range, and the bound pass can install a bound only
     * on a branch target or a fall-through, so no bound could ride on it.
     * The catch-all that javac emits for a {@code synchronized} block or a
     * {@code finally} sits inside the range it protects and would otherwise
     * present the handler as a self-cycle.  Cycles that exist only over trap
     * edges are counted by {@link #exceptionCycles()} and named by
     * {@link #GAP_EXCEPTION_CYCLE_UNBOUNDED}: they are outside the bounded
     * loop model and no iteration count is claimed for them.</p>
     */
    static final class LoopCfg {
        private final Body body;
        private final UnitGraph transfers;
        private final UnitGraph structure;
        private final MHGDominatorsFinder<Unit> dominators;
        private final int exceptionCycles;

        private LoopCfg(Body body, UnitGraph transfers, UnitGraph structure) {
            this.body = body;
            this.transfers = transfers;
            this.structure = structure;
            this.dominators = new MHGDominatorsFinder<>(structure);
            this.exceptionCycles = structure == transfers ? 0
                    : countExceptionCycles();
        }

        Body body() {
            return body;
        }

        Iterable<Unit> units() {
            return transfers;
        }

        /**
         * The ordinary transfers out of {@code unit}: the only edges a
         * backedge can be, and the only ones a bound can be installed on.
         */
        List<Unit> succsOf(Unit unit) {
            return transfers.getSuccsOf(unit);
        }

        /** True when {@code dominator} dominates {@code unit}. */
        boolean isDominatedBy(Unit unit, Unit dominator) {
            return dominators.isDominatedBy(unit, dominator);
        }

        /**
         * The units of the natural loop of {@code header} closed by
         * {@code latches}: everything that reaches a latch without passing
         * the header, over the same edges the dominance proof used.  A
         * protected body whose only way back to the latch is its handler is
         * therefore in the loop, and because the structure graph has one
         * entry, every member is dominated by the header.
         */
        Set<Unit> naturalLoop(Unit header, Collection<Unit> latches) {
            Set<Unit> loop = identitySet();
            loop.add(header);
            Deque<Unit> work = new ArrayDeque<>();
            for (Unit latch : latches) {
                if (loop.add(latch) && latch != header) {
                    work.addLast(latch);
                }
            }
            while (!work.isEmpty()) {
                Unit current = work.removeFirst();
                for (Unit predecessor : structure.getPredsOf(current)) {
                    if (loop.add(predecessor) && predecessor != header) {
                        work.addLast(predecessor);
                    }
                }
            }
            return loop;
        }

        /**
         * Cycles this method has over trap edges only.  They are not loops
         * of the bounded model; the count exists so the boundary can be
         * reported rather than assumed away.
         */
        int exceptionCycles() {
            return exceptionCycles;
        }

        private int countExceptionCycles() {
            int result = 0;
            for (Unit source : structure) {
                for (Unit target : structure.getSuccsOf(source)) {
                    if (dominators.isDominatedBy(source, target)
                            && !transfers.getSuccsOf(source).contains(target)) {
                        result++;
                    }
                }
            }
            return result;
        }
    }

    /**
     * Takes the loop-CFG decision for {@code body} once, on the ordinary
     * transfer graph its caller already uses, and hands back the one object
     * every loop consumer must read.  A trapped body gets the trap-augmented
     * structure explicitly here, at the caller's own graph, instead of one
     * consumer quietly substituting a different CFG for itself.
     *
     * @param transfers the method's unexceptional CFG.  A graph that already
     *                  carries exception edges is rejected: its successors
     *                  are not iteration edges.
     */
    static LoopCfg loopCfg(Body body, UnitGraph transfers) {
        if (body == null || transfers == null) {
            throw new IllegalArgumentException(
                    "a loop CFG needs a body and its transfer graph");
        }
        if (transfers instanceof TrapUnitGraph
                || transfers instanceof ExceptionalUnitGraph) {
            throw new IllegalArgumentException(
                    "LOOP_CFG_TRANSFERS_MUST_BE_UNEXCEPTIONAL: "
                            + transfers.getClass().getName() + " in "
                            + body.getMethod().getSignature());
        }
        return new LoopCfg(body, transfers,
                body.getTraps().isEmpty() ? transfers
                        : new TrapUnitGraph(body));
    }

    /**
     * Returns branches with at least one successor inside a natural loop and
     * at least one successor outside it.  The loops come from the dominance-
     * proved backedges of {@code cfg}, the same ones the bound pass
     * instruments, so a semantic branch merely located in a loop is not
     * classified as iteration control.
     */
    static Set<Unit> guards(LoopCfg cfg) {
        return classify(cfg).keySet();
    }

    /**
     * What kind of loop one iteration guard belongs to.
     *
     * <p>README's loop authority chain starts here: an array-backed indexed
     * {@code for} is {@code FIXED_COUNT_INDEXED} and its slot count comes
     * from the exact cardinality of the array; anything else is
     * {@code CONDITION_BOUNDED} and runs under a declared {@code K_L}.  The
     * classification is published, never re-derived by a later stage.</p>
     */
    static final class LoopKind {
        /** {@code FIXED_COUNT_INDEXED} or {@code CONDITION_BOUNDED}. */
        final String classification;

        private LoopKind(String classification) {
            this.classification = classification;
        }
    }

    /**
     * One retained loop of a method: the iteration guards that decide it,
     * with the one kind the nest classifies as.
     *
     * <p>A retained loop is a natural loop header and the exiting branches
     * of its body.  It is independent of any communication structure: the
     * same loop is retained whether or not the method performs a remote
     * call.</p>
     */
    static final class RetainedLoop {
        /** Dominance-proved natural-loop header used by runtime counters. */
        final Unit header;
        /** Exiting branches of this natural loop, in CFG order. */
        final List<Unit> guards;
        /** {@code FIXED_COUNT_INDEXED} or {@code CONDITION_BOUNDED}. */
        final String classification;
        /** The nest's guards do not all classify the same way. */
        final boolean guardsClassifyDifferently;

        private RetainedLoop(Unit header, List<Unit> guards,
                             String classification,
                             boolean guardsClassifyDifferently) {
            this.header = header;
            this.guards = Collections.unmodifiableList(guards);
            this.classification = classification;
            this.guardsClassifyDifferently = guardsClassifyDifferently;
        }
    }

    /**
     * Every retained loop of {@code cfg}, one per dominance-proved natural
     * loop header.
     *
     * <p>Two backedges onto one header close one loop, so their guards are
     * one retained loop and not two.  A nest of two headers is two retained
     * loops, each with its own bound: claiming one identity for both would
     * make the inner loop's body executions indistinguishable from the
     * outer's.</p>
     */
    static List<RetainedLoop> retainedLoops(LoopCfg cfg) {
        List<RetainedLoop> result = new ArrayList<RetainedLoop>();
        if (cfg == null) return result;
        Map<Unit, LoopKind> kinds = classify(cfg);
        Map<Unit, List<Unit>> latchesByHeader =
                new IdentityHashMap<Unit, List<Unit>>();
        List<Unit> headers = new ArrayList<Unit>();
        for (Unit tail : cfg.units()) {
            for (Unit header : cfg.succsOf(tail)) {
                if (!cfg.isDominatedBy(tail, header)) continue;
                List<Unit> latches = latchesByHeader.get(header);
                if (latches == null) {
                    latches = new ArrayList<Unit>();
                    latchesByHeader.put(header, latches);
                    headers.add(header);
                }
                latches.add(tail);
            }
        }
        for (Unit header : headers) {
            Set<Unit> loop = cfg.naturalLoop(header,
                    latchesByHeader.get(header));
            List<Unit> guards = new ArrayList<Unit>();
            for (Unit unit : cfg.units()) {
                if (loop.contains(unit) && kinds.containsKey(unit)
                        && exitingBranch(cfg.body(), unit, loop)) {
                    guards.add(unit);
                }
            }
            if (guards.isEmpty()) continue;
            int fixed = 0;
            for (Unit guard : guards) {
                LoopKind kind = kinds.get(guard);
                if (LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                        .equals(kind.classification)) {
                    fixed++;
                }
            }
            boolean fixedCount = fixed == guards.size();
            result.add(new RetainedLoop(header, guards, fixedCount
                    ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                    : LoopBoundPolicy.LOOP_CONDITION_BOUNDED,
                    fixed > 0 && !fixedCount));
        }
        return result;
    }

    /** The rule one classification was produced by. */
    static String classificationAuthority(String classification) {
        return LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                .equals(classification)
                ? LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED
                : LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED;
    }

    /**
     * Every iteration guard of {@code cfg}, with the kind of loop it closes.
     *
     * <p>A guard shared by two natural loops takes the weaker kind: a fixed
     * count claimed for one of them says nothing about the body executions
     * the other contributes.</p>
     */
    static Map<Unit, LoopKind> classify(LoopCfg cfg) {
        Map<Unit, LoopKind> result = new IdentityHashMap<Unit, LoopKind>();
        if (cfg == null) {
            return result;
        }
        Set<String> lengthLocals = arrayLengthLocals(cfg.body());
        for (Unit tail : cfg.units()) {
            for (Unit header : cfg.succsOf(tail)) {
                if (!cfg.isDominatedBy(tail, header)) {
                    continue;
                }
                Set<Unit> loop = cfg.naturalLoop(header,
                        Collections.singletonList(tail));
                List<Unit> exits = new ArrayList<Unit>();
                for (Unit candidate : loop) {
                    if (cfg.succsOf(candidate).isEmpty()) {
                        continue;
                    }
                    if (exitingBranch(cfg.body(), candidate, loop)) {
                        exits.add(candidate);
                    }
                }
                boolean indexed = false;
                for (Unit exit : exits) {
                    indexed |= testsArrayLength(exit, lengthLocals);
                }
                // The array cardinality fixes the available iteration
                // slots. A break/return only guards which of those slots a
                // local path reaches; it does not turn the array traversal
                // into a while-loop K_L prefix. The guarded region cases
                // retain that early-exit condition themselves.
                LoopKind kind = new LoopKind(indexed
                        ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                        : LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
                for (Unit exit : exits) {
                    result.put(exit, weaker(result.get(exit), kind));
                }
            }
        }
        return result;
    }

    private static LoopKind weaker(LoopKind held, LoopKind found) {
        if (held == null) {
            return found;
        }
        boolean fixed = LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                .equals(held.classification)
                && LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                .equals(found.classification);
        return new LoopKind(fixed
                ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                : LoopBoundPolicy.LOOP_CONDITION_BOUNDED);
    }

    private static Set<Unit> identitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<Unit, Boolean>());
    }

    private static boolean exitingBranch(Body body, Unit candidate,
                                         Set<Unit> loop) {
        CausynthBranchShape shape = CausynthBranchShape.from(body, candidate);
        if (shape == null || shape.successorCount() < 2) {
            return false;
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
        return continues && exits;
    }

    /**
     * Locals this body only ever assigns {@code lengthof} to.  Jimple states
     * a condition over immediates, so the array length of a
     * {@code for (i = 0; i &lt; a.length; i++)} reaches its test through one
     * of these.  A local that also holds something else proves nothing about
     * the array, so it is not one.
     */
    private static Set<String> arrayLengthLocals(Body body) {
        Set<String> lengths = new LinkedHashSet<String>();
        Set<String> other = new LinkedHashSet<String>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)) {
                continue;
            }
            AssignStmt assignment = (AssignStmt) unit;
            if (!(assignment.getLeftOp() instanceof Local)) {
                continue;
            }
            String name = ((Local) assignment.getLeftOp()).getName();
            if (assignment.getRightOp() instanceof LengthExpr) {
                lengths.add(name);
            } else {
                other.add(name);
            }
        }
        lengths.removeAll(other);
        return lengths;
    }

    private static boolean testsArrayLength(Unit branch,
                                            Set<String> lengthLocals) {
        if (!(branch instanceof IfStmt)) {
            return false;
        }
        for (ValueBox box
                : ((IfStmt) branch).getCondition().getUseBoxes()) {
            Value operand = box.getValue();
            if (operand instanceof LengthExpr
                    || (operand instanceof Local && lengthLocals.contains(
                    ((Local) operand).getName()))) {
                return true;
            }
        }
        return false;
    }

    /**
     * The unique {@code lengthof} definition supplying these loop guards.
     *
     * <p>The definition is the exact runtime cardinality authority: unlike a
     * body counter it observes the available array length even when a guarded
     * case exits the loop early. Ambiguous definitions are refused by the
     * instrumentation caller rather than guessed.</p>
     */
    static AssignStmt arrayLengthAuthority(
            Body body, Collection<Unit> guards) {
        Set<String> lengthLocals = arrayLengthLocals(body);
        Set<String> demanded = new LinkedHashSet<String>();
        for (Unit guard : guards) {
            if (!(guard instanceof IfStmt)) continue;
            for (ValueBox box
                    : ((IfStmt) guard).getCondition().getUseBoxes()) {
                Value operand = box.getValue();
                if (operand instanceof Local && lengthLocals.contains(
                        ((Local) operand).getName())) {
                    demanded.add(((Local) operand).getName());
                }
            }
        }
        if (demanded.size() != 1) return null;
        AssignStmt authority = null;
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof AssignStmt)) continue;
            AssignStmt assignment = (AssignStmt) unit;
            if (!(assignment.getLeftOp() instanceof Local)
                    || !(assignment.getRightOp() instanceof LengthExpr)
                    || !demanded.contains(
                    ((Local) assignment.getLeftOp()).getName())) {
                continue;
            }
            if (authority != null && authority != assignment) return null;
            authority = assignment;
        }
        return authority;
    }
}
