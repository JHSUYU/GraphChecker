package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.d3.plan.LoopBoundPolicy;
import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.ThrowStmt;
import soot.jimple.LengthExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.TrapUnitGraph;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.ToIntFunction;

/**
 * The one CFG a method's loop questions are answered on, and the branch units
 * that decide whether a natural loop continues.
 */
final class CfgLoopControl {
    /** One dominance proof per body, shared by every loop consumer. */
    private static final Map<Body, LoopCfg> BY_BODY =
            Collections.synchronizedMap(new IdentityHashMap<Body, LoopCfg>());

    /** Rejects no unit: only instrumentation names loops by unit index. */
    private static final ToIntFunction<Unit> ANY_UNIT = unit -> 0;

    private CfgLoopControl() {
    }

    /** One method's loop CFG. */
    static final class LoopCfg {
        private final Body body;
        private final UnitGraph transfers;
        private final UnitGraph structure;
        private final MHGDominatorsFinder<Unit> dominators;
        private final long unitChainState;

        private LoopCfg(Body body, UnitGraph transfers, UnitGraph structure) {
            this.body = body;
            this.transfers = transfers;
            this.structure = structure;
            this.dominators = new MHGDominatorsFinder<>(structure);
            this.unitChainState = body.getUnits().getModificationCount();
        }

        /** Whether this proof still describes {@code body}: Soot counts
         *  every write to a unit chain, so a body an instrumenter touched
         *  since the proof was taken is refused rather than reused. */
        private boolean describes(Body candidate) {
            return unitChainState
                    == candidate.getUnits().getModificationCount();
        }

        Body body() {
            return body;
        }

        Iterable<Unit> units() {
            return transfers;
        }

        /** The ordinary transfers out of {@code unit}: the only edges a
         *  backedge can be, and the only ones a bound can sit on. */
        List<Unit> succsOf(Unit unit) {
            return transfers.getSuccsOf(unit);
        }

        /** True when {@code dominator} dominates {@code unit}. */
        boolean isDominatedBy(Unit unit, Unit dominator) {
            return dominators.isDominatedBy(unit, dominator);
        }

        /** The natural loop of {@code header} closed by {@code latches}:
         *  everything reaching a latch without passing the header, over the
         *  same edges the dominance proof used. */
        Set<Unit> naturalLoop(Unit header, Collection<Unit> latches) {
            Set<Unit> loop = StaticProgram.closure(latches,
                    unit -> unit == header
                            ? Collections.<Unit>emptyList()
                            : structure.getPredsOf(unit));
            loop.add(header);
            return loop;
        }
    }


    /** One transfer between two units of a method's loop CFG. */
    static final class Edge {
        final Unit source;
        final Unit target;

        Edge(Unit source, Unit target) {
            this.source = source;
            this.target = target;
        }
    }

    /** One dominance-proved backedge, named by original unit index and
     *  never by position in a rewritten body. */
    static final class Backedge {
        final Unit source;
        final int sourceIndex;
        final Unit target;
        final int targetIndex;

        private Backedge(Unit source, int sourceIndex,
                         Unit target, int targetIndex) {
            this.source = source;
            this.sourceIndex = sourceIndex;
            this.target = target;
            this.targetIndex = targetIndex;
        }

        String identity(SootMethod method) {
            return method.getSignature() + "#backedge:u" + sourceIndex
                    + "->u" + targetIndex;
        }
    }

    /** One natural loop: its dominance-proved header and the backedges that
     *  close it, answered on the loop CFG the header was proved on. */
    static final class NaturalLoop {
        private final LoopCfg cfg;
        final Unit header;
        final int headerIndex;
        final List<Backedge> backedges = new ArrayList<Backedge>();

        private NaturalLoop(LoopCfg cfg, Unit header, int headerIndex) {
            this.cfg = cfg;
            this.header = header;
            this.headerIndex = headerIndex;
        }

        String identity(SootMethod method) {
            return method.getSignature() + "#loop:u" + headerIndex;
        }

        /** Every unit of the loop: the union over its latches. */
        Set<Unit> members() {
            Set<Unit> members = new LinkedHashSet<Unit>();
            for (Backedge backedge : backedges) {
                members.addAll(cfg.naturalLoop(header,
                        Collections.singletonList(backedge.source)));
            }
            return members;
        }

        /** The units this loop's own latch closes, for one backedge. */
        Set<Unit> members(Backedge backedge) {
            return cfg.naturalLoop(header,
                    Collections.singletonList(backedge.source));
        }

        /** True when every structural CFG path to {@code unit} passes
         *  {@code dominator}; this is the same proof used to form the loop. */
        boolean isDominatedBy(Unit unit, Unit dominator) {
            return cfg.isDominatedBy(unit, dominator);
        }

        /** The normal successors recorded in this immutable CFG proof. */
        List<Unit> stableSuccessors(Unit unit) {
            return cfg.succsOf(unit);
        }

        /** Normal transfers ending one dynamic invocation of this loop. */
        List<Edge> exitEdges() {
            Set<Unit> members = members();
            List<Edge> exits = new ArrayList<Edge>();
            for (Unit source : members) {
                for (Unit target : cfg.succsOf(source)) {
                    if (!members.contains(target)) {
                        exits.add(new Edge(source, target));
                    }
                }
            }
            return exits;
        }

        /** Abrupt method terminals inside the loop have no normal exit. */
        List<Unit> terminals() {
            List<Unit> terminals = new ArrayList<Unit>();
            for (Unit unit : members()) {
                if (cfg.succsOf(unit).isEmpty()
                        && (unit instanceof ReturnStmt
                        || unit instanceof ReturnVoidStmt
                        || unit instanceof ThrowStmt)) {
                    terminals.add(unit);
                }
            }
            return terminals;
        }
    }

    /**
     * The one natural-loop grouping: every dominance-proved header of {@code
     * cfg} with the backedges that close it, in first-backedge order. A unit
     * {@code unitIndex} cannot name -- one an earlier pass inserted -- closes
     * no loop this pass may bound, so it is skipped rather than given a
     * positional identity that moves on the next rewrite.
     */
    static List<NaturalLoop> naturalLoops(LoopCfg cfg,
                                          ToIntFunction<Unit> unitIndex) {
        List<NaturalLoop> loops = new ArrayList<NaturalLoop>();
        if (cfg == null) return loops;
        Map<Unit, NaturalLoop> byHeader =
                new IdentityHashMap<Unit, NaturalLoop>();
        for (Unit source : cfg.units()) {
            int sourceIndex = unitIndex.applyAsInt(source);
            if (sourceIndex < 0) continue;
            for (Unit target : cfg.succsOf(source)) {
                int targetIndex = unitIndex.applyAsInt(target);
                if (targetIndex < 0 || !cfg.isDominatedBy(source, target)) {
                    continue;
                }
                NaturalLoop loop = byHeader.get(target);
                if (loop == null) {
                    loop = new NaturalLoop(cfg, target, targetIndex);
                    byHeader.put(target, loop);
                    loops.add(loop);
                }
                loop.backedges.add(new Backedge(source, sourceIndex,
                        target, targetIndex));
            }
        }
        return loops;
    }

    /**
     * The one loop-CFG decision for {@code body}, taken on the transfer graph
     * its caller already uses.
     * @param transfers the method's unexceptional CFG.  One that already
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

    /** Releases every held loop CFG: one analysis run holds them, not one JVM. */
    static void forget() {
        BY_BODY.clear();
    }

    /** The one loop CFG of {@code body}, built on first ask and shared. */
    static LoopCfg loopCfg(Body body) {
        LoopCfg held = BY_BODY.get(body);
        if (held != null && held.describes(body)) {
            return held;
        }
        LoopCfg built = loopCfg(body, new BriefUnitGraph(body));
        BY_BODY.put(body, built);
        return built;
    }

    /** Branches with a successor inside a natural loop and one outside. */
    static Set<Unit> guards(LoopCfg cfg) {
        return classify(cfg).keySet();
    }

    /** One retained loop: its iteration guards and the kind it classifies
     *  as. */
    static final class RetainedLoop {
        /** Dominance-proved natural-loop header used by runtime counters. */
        final Unit header;
        /** Exiting branches of this natural loop, in CFG order. */
        final List<Unit> guards;
        /** {@code FIXED_COUNT_INDEXED} or {@code CONDITION_BOUNDED}. */
        final String classification;
        /** The nest's guards do not all classify the same way. */
        final boolean guardsClassifyDifferently;
        /** The latches (backedge sources) that close this loop. */
        final List<Unit> latches;
        /** Exact CFG members, used to assign a branch to its innermost loop. */
        final Set<Unit> members;

        private RetainedLoop(Unit header, List<Unit> guards,
                             String classification,
                             boolean guardsClassifyDifferently,
                             List<Unit> latches, Set<Unit> members) {
            this.header = header;
            this.guards = Collections.unmodifiableList(guards);
            this.classification = classification;
            this.guardsClassifyDifferently = guardsClassifyDifferently;
            this.latches = Collections.unmodifiableList(latches);
            this.members = Collections.unmodifiableSet(
                    new LinkedHashSet<Unit>(members));
        }
    }

    /** Every retained loop of {@code cfg}, one per proved header. */
    static List<RetainedLoop> retainedLoops(LoopCfg cfg) {
        List<RetainedLoop> result = new ArrayList<RetainedLoop>();
        if (cfg == null) return result;
        Map<Unit, String> kinds = classify(cfg);
        for (NaturalLoop natural : naturalLoops(cfg, ANY_UNIT)) {
            Unit header = natural.header;
            Set<Unit> loop = natural.members();
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
                if (fixedCount(kinds.get(guard))) fixed++;
            }
            boolean fixedCount = fixed == guards.size();
            List<Unit> latches = new ArrayList<Unit>();
            for (Backedge backedge : natural.backedges) {
                latches.add(backedge.source);
            }
            result.add(new RetainedLoop(header, guards,
                    classification(fixedCount), fixed > 0 && !fixedCount,
                    latches, loop));
        }
        return result;
    }

    /** The rule one classification was produced by. */
    static String classificationAuthority(String classification) {
        return fixedCount(classification)
                ? LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED
                : LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED;
    }

    /** True for the {@code FIXED_COUNT_INDEXED} classification. */
    static boolean fixedCount(String classification) {
        return LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                .equals(classification);
    }

    private static String classification(boolean fixedCount) {
        return fixedCount ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                : LoopBoundPolicy.LOOP_CONDITION_BOUNDED;
    }

    /**
     * Every iteration guard of {@code cfg}, with the classification of the
     * loop it closes.  README's loop authority chain starts here: an
     * array-backed indexed {@code for} is {@code FIXED_COUNT_INDEXED} and its
     * slot count comes from the exact cardinality of the array; anything else
     * is {@code CONDITION_BOUNDED} and runs under a declared {@code K_L}.
     */
    static Map<Unit, String> classify(LoopCfg cfg) {
        Map<Unit, String> result = new IdentityHashMap<Unit, String>();
        if (cfg == null) {
            return result;
        }
        Set<String> lengthLocals = arrayLengthLocals(cfg.body());
        for (NaturalLoop natural : naturalLoops(cfg, ANY_UNIT)) {
            // One guard kind per latch: a nest closed by several backedges
            // classifies each of its own iteration edges.
            for (Backedge backedge : natural.backedges) {
                Set<Unit> loop = natural.members(backedge);
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
                // The array cardinality fixes the available iteration slots.
                for (Unit exit : exits) {
                    String held = result.get(exit);
                    result.put(exit, held == null ? classification(indexed)
                            : classification(fixedCount(held) && indexed));
                }
            }
        }
        return result;
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

    /** Locals this body only ever assigns {@code lengthof} to. */
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

    /** The unique {@code lengthof} definition supplying these loop guards. */
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
