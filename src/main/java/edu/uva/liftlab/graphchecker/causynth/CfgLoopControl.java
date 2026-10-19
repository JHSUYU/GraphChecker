package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.LengthExpr;
import soot.toolkits.graph.BriefUnitGraph;
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

final class CfgLoopControl {
    private static final Map<Body, LoopCfg> BY_BODY =
            Collections.synchronizedMap(new IdentityHashMap<Body, LoopCfg>());

    private static final ToIntFunction<Unit> ANY_UNIT = unit -> 0;

    private CfgLoopControl() {
    }

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

        List<Unit> succsOf(Unit unit) {
            return transfers.getSuccsOf(unit);
        }

        boolean isDominatedBy(Unit unit, Unit dominator) {
            return dominators.isDominatedBy(unit, dominator);
        }

        Set<Unit> naturalLoop(Unit header, Collection<Unit> latches) {
            Set<Unit> loop = StaticProgram.closure(latches,
                    unit -> unit == header
                            ? Collections.<Unit>emptyList()
                            : structure.getPredsOf(unit));
            loop.add(header);
            return loop;
        }
    }


    static final class Edge {
        final Unit source;
        final Unit target;

        Edge(Unit source, Unit target) {
            this.source = source;
            this.target = target;
        }
    }

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

        Set<Unit> members() {
            Set<Unit> members = new LinkedHashSet<Unit>();
            for (Backedge backedge : backedges) {
                members.addAll(cfg.naturalLoop(header,
                        Collections.singletonList(backedge.source)));
            }
            return members;
        }

        Set<Unit> members(Backedge backedge) {
            return cfg.naturalLoop(header,
                    Collections.singletonList(backedge.source));
        }

        boolean isDominatedBy(Unit unit, Unit dominator) {
            return cfg.isDominatedBy(unit, dominator);
        }

        List<Unit> stableSuccessors(Unit unit) {
            return cfg.succsOf(unit);
        }

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

    }

    static final class BodyEntry {
        final Unit target;
        final List<Edge> edges;

        BodyEntry(Unit target, List<Edge> edges) {
            this.target = target;
            this.edges = Collections.unmodifiableList(edges);
        }
    }

    static BodyEntry bodyEntry(NaturalLoop loop, Collection<Unit> controls,
                               Unit demanded) {
        Set<Unit> members = loop.members();
        if (demanded == null || !members.contains(demanded)
                || !loop.isDominatedBy(demanded, loop.header)) {
            return null;
        }
        List<Unit> targets = new ArrayList<Unit>();
        Map<Unit, List<Edge>> into = new IdentityHashMap<Unit, List<Edge>>();
        for (Unit control : controls) {
            for (Unit successor : loop.stableSuccessors(control)) {
                if (!members.contains(successor)
                        || !loop.isDominatedBy(demanded, successor)) {
                    continue;
                }
                List<Edge> edges = into.get(successor);
                if (edges == null) {
                    edges = new ArrayList<Edge>();
                    into.put(successor, edges);
                    targets.add(successor);
                }
                if (!holds(edges, control, successor)) {
                    edges.add(new Edge(control, successor));
                }
            }
        }
        if (targets.isEmpty()) {
            return loop.backedges.isEmpty() ? null : new BodyEntry(
                    loop.header, Collections.singletonList(new Edge(
                    loop.backedges.get(0).source, loop.header)));
        }
        Unit outermost = null;
        for (Unit candidate : targets) {
            boolean nested = false;
            for (Unit other : targets) {
                if (candidate != other
                        && loop.isDominatedBy(candidate, other)) {
                    nested = true;
                    break;
                }
            }
            if (nested) continue;
            if (outermost != null) return null;
            outermost = candidate;
        }
        return new BodyEntry(outermost, into.get(outermost));
    }

    private static boolean holds(List<Edge> edges, Unit source, Unit target) {
        for (Edge edge : edges) {
            if (edge.source == source && edge.target == target) return true;
        }
        return false;
    }

    static List<NaturalLoop> naturalLoops(LoopCfg cfg,
                                          ToIntFunction<Unit> unitIndex) {
        List<NaturalLoop> loops = new ArrayList<NaturalLoop>();
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

    static void forget() {
        BY_BODY.clear();
    }

    static LoopCfg loopCfg(Body body) {
        LoopCfg held = BY_BODY.get(body);
        if (held != null && held.describes(body)) {
            return held;
        }
        UnitGraph transfers = new BriefUnitGraph(body);
        LoopCfg built = new LoopCfg(body, transfers,
                body.getTraps().isEmpty() ? transfers
                        : new TrapUnitGraph(body));
        BY_BODY.put(body, built);
        return built;
    }

    static final class RetainedLoop {
        final Unit header;
        final List<Unit> guards;
        final String classification;
        final boolean guardsClassifyDifferently;
        final List<Unit> latches;
        final Set<Unit> members;

        final NaturalLoop natural;

        private RetainedLoop(NaturalLoop natural, List<Unit> guards,
                             String classification,
                             boolean guardsClassifyDifferently,
                             List<Unit> latches, Set<Unit> members) {
            this.natural = natural;
            this.header = natural.header;
            this.guards = Collections.unmodifiableList(guards);
            this.classification = classification;
            this.guardsClassifyDifferently = guardsClassifyDifferently;
            this.latches = Collections.unmodifiableList(latches);
            this.members = Collections.unmodifiableSet(
                    new LinkedHashSet<Unit>(members));
        }
    }

    static List<RetainedLoop> retainedLoops(LoopCfg cfg) {
        List<RetainedLoop> result = new ArrayList<RetainedLoop>();
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
            result.add(new RetainedLoop(natural, guards,
                    classification(fixedCount), fixed > 0 && !fixedCount,
                    latches, loop));
        }
        return result;
    }

    static String classificationAuthority(String classification) {
        return fixedCount(classification)
                ? LoopBoundPolicy.LOOP_CLASSIFIED_ARRAY_INDEXED
                : LoopBoundPolicy.LOOP_CLASSIFIED_CONDITION_CONTROLLED;
    }

    static boolean fixedCount(String classification) {
        return LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                .equals(classification);
    }

    private static String classification(boolean fixedCount) {
        return fixedCount ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                : LoopBoundPolicy.LOOP_CONDITION_BOUNDED;
    }

    private static Map<Unit, String> classify(LoopCfg cfg) {
        Map<Unit, String> result = new IdentityHashMap<Unit, String>();
        Set<String> lengthLocals = arrayLengthLocals(cfg.body());
        for (NaturalLoop natural : naturalLoops(cfg, ANY_UNIT)) {
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
}
