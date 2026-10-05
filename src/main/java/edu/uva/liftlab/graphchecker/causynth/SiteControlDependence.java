package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import soot.Body;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The guard set of a site: the branches it is control-dependent on.  The one
 * guard computation in the engine.
 *
 * <p>SYMBOL-SCOPE §3: site {@code t} is control-dependent on branch {@code b}
 * when some successor of {@code b} is post-dominated by {@code t} and {@code
 * b} is not.  Unlike a may-reach rule, this keeps a branch both of whose arms
 * can reach the site but only one makes it unavoidable -- and so NAMES that
 * arm ({@link StaticScopeMap.Guard#outcome()}).</p>
 *
 * <p>The CFG is {@link BriefUnitGraph}: an exception edge would leave almost
 * nothing post-dominated.  The one exception it adds is a door fault a
 * handler catches ({@link FaultPropagation}): a call that can leave one to a
 * handler is a fault branch over the CFG with that edge, deciding the sites
 * only one of its exits reaches, with no boolean arm (its guard's outcome is
 * null) and no decision ever recorded at it -- a fault is flipped at its
 * marker ({@link MethodGuards}).  A door woven into the method itself (a
 * door at calls) throws to the handler from its marker branch, which is a
 * fault branch too, on its arm: otherwise the handler, now reached from
 * every exit of the calls before it, would be decided by nothing.</p>
 *
 * <p>Every index is the ORIGINAL one ({@link
 * CausynthPipeline#originalUnitIndex}), the numbering of every published site
 * id.  Trap: a woven body's POSITION is shifted by the inserted hooks; a woven
 * unit has no original index and is never a guard.</p>
 */
public final class SiteControlDependence {
    private SiteControlDependence() {
    }

    /**
     * The guard sets of the given sites, from the live Scene.  A site with no
     * body or unit answers empty, read as "no branch stated", not "unguarded".
     */
    public static StaticScopeMap.Guards over(Collection<String> siteIds) {
        Map<String, MethodGuards> byMethod =
                new LinkedHashMap<String, MethodGuards>();
        final Map<String, MethodGuards> bySite =
                new LinkedHashMap<String, MethodGuards>();
        for (String siteId : siteIds == null
                ? Collections.<String>emptyList() : siteIds) {
            String method = SiteId.methodOf(siteId);
            if (method.isEmpty()) continue;
            MethodGuards computed = byMethod.get(method);
            if (computed == null) {
                computed = MethodGuards.of(method);
                byMethod.put(method, computed);
            }
            bySite.put(siteId, computed);
        }
        final Map<String, MethodGuards> callers = byMethod;
        return new StaticScopeMap.Guards() {
            private CallSites calls;

            @Override
            public List<StaticScopeMap.Guard> of(String siteId) {
                MethodGuards computed = bySite.get(siteId);
                return computed == null
                        ? Collections.<StaticScopeMap.Guard>emptyList()
                        : computed.at(SiteId.unitIndexOf(siteId));
            }

            @Override
            public List<StaticScopeMap.Guard> callsInto(
                    String method, Predicate<String> walked) {
                List<StaticScopeMap.Guard> found =
                        new ArrayList<StaticScopeMap.Guard>();
                Set<String> named = new LinkedHashSet<String>();
                for (String call : callSitesInto(method, walked)) {
                    String caller = SiteId.methodOf(call);
                    MethodGuards guards = callers.get(caller);
                    if (guards == null) {
                        guards = MethodGuards.of(caller);
                        callers.put(caller, guards);
                    }
                    // The call's guards and theirs: in `if (a || b) return;
                    // call();` the call is control-dependent on b alone, and
                    // b on a.
                    int unit = SiteId.unitIndexOf(call);
                    List<StaticScopeMap.Guard> deciding =
                            new ArrayList<StaticScopeMap.Guard>(
                                    guards.at(unit));
                    deciding.addAll(guards.chain(unit));
                    for (StaticScopeMap.Guard guard : deciding) {
                        if (named.add(guard.siteId())) found.add(guard);
                    }
                }
                return found;
            }

            @Override
            public List<String> callersOf(String method) {
                Set<String> found = new LinkedHashSet<String>();
                for (String call : callSitesInto(method, caller -> true)) {
                    found.add(SiteId.methodOf(call));
                }
                return new ArrayList<String>(found);
            }

            /** The call sites that run {@code method}, {@link #CALL_DEPTH}
             *  calls up, but none into a method {@code walked} refuses. */
            private List<String> callSitesInto(String method,
                                               Predicate<String> walked) {
                if (calls == null) calls = CallSites.ofApplication();
                List<String> found = new ArrayList<String>();
                Set<String> visited = new LinkedHashSet<String>();
                List<String> level = Collections.singletonList(method);
                for (int depth = 0; depth < CALL_DEPTH && !level.isEmpty();
                     depth++) {
                    List<String> next = new ArrayList<String>();
                    for (String callee : level) {
                        if (!visited.add(callee) || !walked.test(callee)) {
                            continue;
                        }
                        for (String call : calls.into(callee)) {
                            found.add(call);
                            next.add(SiteId.methodOf(call));
                        }
                    }
                    level = next;
                }
                return found;
            }

            @Override
            public List<StaticScopeMap.Guard> chainOf(String siteId) {
                MethodGuards computed = bySite.get(siteId);
                return computed == null
                        ? Collections.<StaticScopeMap.Guard>emptyList()
                        : computed.chain(SiteId.unitIndexOf(siteId));
            }
        };
    }

    /** How many calls up the calls-into guards reach (the slice's
     *  SeedBackwardStaticAnalyzer#ACTIVATION_DEPTH). */
    private static final int CALL_DEPTH = 3;

    /**
     * Where each method of the analysed program is called from: the call
     * site ids, by callee, a virtual call counting for every override the
     * hierarchy dispatches it to.
     */
    private static final class CallSites {
        private final Map<String, List<String>> byCallee;

        private CallSites(Map<String, List<String>> byCallee) {
            this.byCallee = byCallee;
        }

        static CallSites ofApplication() {
            Map<String, List<String>> byCallee =
                    new LinkedHashMap<String, List<String>>();
            for (soot.SootClass owner : new ArrayList<soot.SootClass>(
                    soot.Scene.v().getApplicationClasses())) {
                for (soot.SootMethod method
                        : new ArrayList<soot.SootMethod>(owner.getMethods())) {
                    Body body = method.isConcrete()
                            ? CausynthStaticFacts.activeBody(method) : null;
                    if (body == null) continue;
                    for (Unit unit : body.getUnits()) {
                        soot.jimple.Stmt stmt = (soot.jimple.Stmt) unit;
                        if (!stmt.containsInvokeExpr()) continue;
                        String site = SiteId.of(method.getSignature(),
                                originalIndex(body, unit));
                        for (soot.SootMethod callee
                                : targets(stmt.getInvokeExpr())) {
                            byCallee.computeIfAbsent(callee.getSignature(),
                                    key -> new ArrayList<String>()).add(site);
                        }
                    }
                }
            }
            return new CallSites(byCallee);
        }

        /** The methods one call may run; none when the hierarchy cannot
         *  resolve it (a phantom supertype). */
        private static Collection<soot.SootMethod> targets(
                soot.jimple.InvokeExpr call) {
            try {
                soot.SootMethod declared = call.getMethod();
                if (call instanceof soot.jimple.StaticInvokeExpr
                        || call instanceof soot.jimple.SpecialInvokeExpr) {
                    return Collections.singletonList(declared);
                }
                return soot.Scene.v().getOrMakeFastHierarchy()
                        .resolveAbstractDispatch(declared.getDeclaringClass(),
                                declared);
            } catch (RuntimeException unresolved) {
                return Collections.<soot.SootMethod>emptyList();
            }
        }

        List<String> into(String callee) {
            List<String> sites = byCallee.get(callee);
            return sites == null ? Collections.<String>emptyList() : sites;
        }
    }

    /** One unit's original index in its body ({@link
     *  CausynthPipeline#originalUnitIndex}), or its position in a body never
     *  woven. */
    static int originalIndex(Body body, Unit unit) {
        List<Unit> units = new ArrayList<Unit>(body.getUnits());
        return tagged(units) ? CausynthPipeline.originalUnitIndex(unit)
                : units.indexOf(unit);
    }

    /** Whether a weave tagged these units; an untagged body was never woven,
     *  so its positions are the original indices. */
    private static boolean tagged(List<Unit> units) {
        for (Unit unit : units) {
            if (CausynthPipeline.originalUnitIndex(unit) >= 0) return true;
        }
        return false;
    }

    /** {@link BriefUnitGraph}'s edges and the door faults' handler edges. */
    private static final class FaultGraph extends UnitGraph {
        FaultGraph(Body body, String method, FaultPropagation faults) {
            super(body);
            unitToSuccs = new LinkedHashMap<Unit, List<Unit>>();
            unitToPreds = new LinkedHashMap<Unit, List<Unit>>();
            buildUnexceptionalEdges(unitToSuccs, unitToPreds);
            for (Unit unit : body.getUnits()) {
                for (Unit handler : faults.handlers(method, unit)) {
                    addEdge(unitToSuccs, unitToPreds, unit, handler);
                }
            }
            buildHeadsAndTails();
        }
    }

    /** One CFG's post-dominance over some of its branches. */
    private static final class Relation {
        final UnitGraph cfg;
        final MHGPostDominatorsFinder<Unit> post;
        final List<Unit> branches;

        Relation(UnitGraph cfg, List<Unit> branches) {
            this.cfg = cfg;
            this.post = new MHGPostDominatorsFinder<Unit>(cfg);
            this.branches = branches;
        }

        /** The branches one of whose arms makes {@code site} run and which
         *  {@code site} does not post-dominate. */
        List<Unit> deciding(Unit site) {
            List<Unit> found = new ArrayList<Unit>();
            for (Unit branch : branches) {
                if (post.isDominatedBy(branch, site)) continue;
                for (Unit successor : cfg.getSuccsOf(branch)) {
                    if (post.isDominatedBy(successor, site)) {
                        found.add(branch);
                        break;
                    }
                }
            }
            return found;
        }

        /** The branches {@code site} is reachable from, by a proper subset
         *  of their successors when {@code controllingOnly}. */
        List<Unit> reaching(Unit site, boolean controllingOnly) {
            List<Unit> found = new ArrayList<Unit>();
            for (Unit branch : branches) {
                List<Unit> successors = cfg.getSuccsOf(branch);
                int reaching = 0;
                for (Unit successor : successors) {
                    if (reachesWithoutRevisiting(successor, site, branch)) {
                        reaching++;
                    }
                }
                if (reaching == 0) continue;
                if (controllingOnly && reaching == successors.size()) {
                    continue;
                }
                found.add(branch);
            }
            return found;
        }

        /** Reachability within one occurrence: the branch is a barrier. */
        private boolean reachesWithoutRevisiting(Unit start, Unit site,
                                                 Unit branch) {
            Set<Unit> seen = new LinkedHashSet<Unit>();
            Deque<Unit> work = new ArrayDeque<Unit>();
            work.add(start);
            while (!work.isEmpty()) {
                Unit current = work.removeFirst();
                if (current == site) return true;
                if (current == branch || !seen.add(current)) continue;
                work.addAll(cfg.getSuccsOf(current));
            }
            return false;
        }
    }

    /**
     * One method's control dependence, built once; callers keep it.  Two
     * relations: the branches' over {@link BriefUnitGraph}, and, when a call
     * of the method can leave a door fault to a handler, the fault branches'
     * over the {@link FaultGraph}.  A fault branch adds to a site's guards,
     * never takes a branch's place: the branches deciding the call decide
     * the site through it, so a recorded branch is never hidden behind a
     * call no decision is recorded at.
     */
    public static final class MethodGuards {
        private final String method;
        private final Map<Unit, Integer> original;
        private final Map<Integer, Unit> byIndex;
        private final Relation plain;
        /** Null when no call of the method leaves a fault to a handler. */
        private final Relation faults;
        private final Map<Integer, List<StaticScopeMap.Guard>> cache =
                new LinkedHashMap<Integer, List<StaticScopeMap.Guard>>();
        private final Map<String, List<Integer>> reachingCache =
                new LinkedHashMap<String, List<Integer>>();

        private MethodGuards(String method, Relation plain, Relation faults,
                             Map<Unit, Integer> original,
                             Map<Integer, Unit> byIndex) {
            this.method = method;
            this.plain = plain;
            this.faults = faults;
            this.original = original;
            this.byIndex = byIndex;
        }

        /** The relation of one method, or an empty one with no body. */
        public static MethodGuards of(String method) {
            return of(method, FaultPropagation.current());
        }

        /** The relation of one method over a fault model: the slice's, or
         *  the root demand's latent one. */
        static MethodGuards of(String method, FaultPropagation raised) {
            Body body = CausynthStaticFacts.activeBody(
                    CausynthStaticFacts.method(method));
            if (body == null) {
                return new MethodGuards(method, null, null,
                        Collections.<Unit, Integer>emptyMap(),
                        Collections.<Integer, Unit>emptyMap());
            }
            List<Unit> units = new ArrayList<Unit>(body.getUnits());
            boolean tagged = tagged(units);
            Map<Unit, Integer> original = new LinkedHashMap<Unit, Integer>();
            Map<Integer, Unit> byIndex = new LinkedHashMap<Integer, Unit>();
            for (int position = 0; position < units.size(); position++) {
                Unit unit = units.get(position);
                int index = tagged
                        ? CausynthPipeline.originalUnitIndex(unit) : position;
                original.put(unit, Integer.valueOf(index));
                if (index >= 0 && !byIndex.containsKey(index)) {
                    byIndex.put(Integer.valueOf(index), unit);
                }
            }
            UnitGraph cfg = new BriefUnitGraph(body);
            List<Unit> branches = new ArrayList<Unit>();
            // A call that can leave a door fault to a handler of the method,
            // and the branch an in-method throw one catches stands on (a
            // woven throw's marker, a failing result's test): its arm
            // reaches the handler only over the fault graph.
            List<Unit> faultBranches = new ArrayList<Unit>();
            for (Unit unit : units) {
                if (original.get(unit).intValue() < 0) continue;
                if (cfg.getSuccsOf(unit).size() > 1) branches.add(unit);
                if (raised.handlers(method, unit).isEmpty()) continue;
                FaultPropagation.Raise raise = raised.raise(method, unit);
                Unit branch = unit.fallsThrough() ? unit
                        : raise == null ? null : raise.branch;
                if (branch != null && !faultBranches.contains(branch)) {
                    faultBranches.add(branch);
                }
            }
            return new MethodGuards(method, new Relation(cfg, branches),
                    faultBranches.isEmpty() ? null : new Relation(
                            new FaultGraph(body, method, raised),
                            faultBranches),
                    original, byIndex);
        }

        /** The unit at an ORIGINAL index, or null. */
        Unit unit(int unitIndex) {
            return byIndex.get(Integer.valueOf(unitIndex));
        }

        /** Whether a fault caught by one of {@code handlers} makes the unit
         *  at {@code unitIndex} unavoidable, over the fault graph. */
        boolean caughtLeadsTo(Collection<Unit> handlers, int unitIndex) {
            Unit site = unit(unitIndex);
            if (faults == null || site == null) return false;
            for (Unit handler : handlers) {
                if (faults.post.isDominatedBy(handler, site)) return true;
            }
            return false;
        }

        /** The branches the unit at this ORIGINAL index depends on. */
        public List<StaticScopeMap.Guard> at(int unitIndex) {
            List<StaticScopeMap.Guard> cached = cache.get(
                    Integer.valueOf(unitIndex));
            if (cached != null) return cached;
            List<StaticScopeMap.Guard> computed = compute(unitIndex);
            cache.put(Integer.valueOf(unitIndex), computed);
            return computed;
        }

        /**
         * The guards of the unit's guards, and theirs, each on its arm toward
         * the guard it controls: every decision an occurrence takes on its way
         * to the unit, outermost last, the unit's own guards excluded.  A
         * guard met twice (a loop's) is named once.
         */
        public List<StaticScopeMap.Guard> chain(int unitIndex) {
            List<StaticScopeMap.Guard> direct = at(unitIndex);
            Set<String> named = new LinkedHashSet<String>();
            for (StaticScopeMap.Guard guard : direct) named.add(guard.siteId());
            List<StaticScopeMap.Guard> chain =
                    new ArrayList<StaticScopeMap.Guard>();
            Deque<StaticScopeMap.Guard> work =
                    new ArrayDeque<StaticScopeMap.Guard>(direct);
            while (!work.isEmpty()) {
                StaticScopeMap.Guard guard = work.removeFirst();
                for (StaticScopeMap.Guard outer
                        : at(SiteId.unitIndexOf(guard.siteId()))) {
                    if (named.add(outer.siteId())) {
                        chain.add(outer);
                        work.add(outer);
                    }
                }
            }
            return Collections.unmodifiableList(chain);
        }

        /**
         * Every branch from which the unit at this ORIGINAL index is
         * reachable, and every fault branch with the branches it is
         * reachable from.  SCOPE for widening the slice, not a guard set: it
         * names no arm and decides nothing.
         *
         * @param controllingOnly keep a branch only when a proper subset of
         *                        its successors reaches the site
         */
        public List<Integer> reaching(int unitIndex,
                                      boolean controllingOnly) {
            String key = unitIndex + (controllingOnly ? "|c" : "|r");
            List<Integer> cached = reachingCache.get(key);
            if (cached != null) return cached;
            Unit site = byIndex.get(Integer.valueOf(unitIndex));
            Set<Integer> found = new LinkedHashSet<Integer>();
            if (site != null && plain != null) {
                for (Unit branch : plain.reaching(site, controllingOnly)) {
                    found.add(original.get(branch));
                }
                for (Unit branch : faultClosure(site, controllingOnly)) {
                    found.add(original.get(branch));
                    for (Unit outer : plain.reaching(branch,
                            controllingOnly)) {
                        found.add(original.get(outer));
                    }
                }
            }
            List<Integer> computed = Collections.unmodifiableList(
                    new ArrayList<Integer>(found));
            reachingCache.put(key, computed);
            return computed;
        }

        private List<StaticScopeMap.Guard> compute(int unitIndex) {
            Unit site = byIndex.get(Integer.valueOf(unitIndex));
            if (site == null || plain == null) {
                return Collections.<StaticScopeMap.Guard>emptyList();
            }
            Set<String> named = new LinkedHashSet<String>();
            List<StaticScopeMap.Guard> found =
                    new ArrayList<StaticScopeMap.Guard>();
            addGuards(site, named, found);
            for (Unit branch : faultClosure(site, null)) {
                // A call has no arm; a marker branch its arm toward the
                // handler, over the fault graph.
                if (named.add(siteOf(branch))) {
                    found.add(new StaticScopeMap.Guard(siteOf(branch),
                            reachingArm(faults, branch, site)));
                }
                addGuards(branch, named, found);
            }
            return Collections.unmodifiableList(found);
        }

        /** The plain relation's guards of {@code site}, each on its arm. */
        private void addGuards(Unit site, Set<String> named,
                               List<StaticScopeMap.Guard> found) {
            for (Unit branch : plain.deciding(site)) {
                Boolean arm = reachingArm(plain, branch, site);
                if (named.add(siteOf(branch))) {
                    found.add(new StaticScopeMap.Guard(siteOf(branch), arm,
                            arm == null
                                    ? Collections.<StaticScopeMap.Guard>emptyList()
                                    : BooleanReturns.deciders(
                                            plain.cfg.getBody(), branch)));
                }
            }
        }

        /**
         * The fault branches {@code site} depends on, and theirs: deciding
         * it (post-dominance, {@code controllingOnly} null) or reaching it.
         */
        private List<Unit> faultClosure(Unit site, Boolean controllingOnly) {
            List<Unit> closure = new ArrayList<Unit>();
            if (faults == null) return closure;
            Set<Unit> seen = new LinkedHashSet<Unit>();
            Deque<Unit> work = new ArrayDeque<Unit>();
            work.add(site);
            while (!work.isEmpty()) {
                Unit unit = work.removeFirst();
                for (Unit call : controllingOnly == null
                        ? faults.deciding(unit)
                        : faults.reaching(unit, controllingOnly)) {
                    if (seen.add(call)) {
                        closure.add(call);
                        work.add(call);
                    }
                }
            }
            return closure;
        }

        private String siteOf(Unit unit) {
            return SiteId.of(method, original.get(unit).intValue());
        }

        /** The arm of an if that makes {@code site} unavoidable over the
         *  relation's graph, or null. */
        private static Boolean reachingArm(Relation relation, Unit branch,
                                           Unit site) {
            if (!(branch instanceof IfStmt)) return null;
            IfStmt conditional = (IfStmt) branch;
            Unit taken = conditional.getTarget();
            boolean takenForces = taken != null
                    && relation.post.isDominatedBy(taken, site);
            boolean fallsThroughForces = false;
            for (Unit successor : relation.cfg.getSuccsOf(branch)) {
                if (successor == taken) continue;
                fallsThroughForces |= relation.post.isDominatedBy(successor,
                        site);
            }
            if (takenForces == fallsThroughForces) return null;
            return Boolean.valueOf(takenForces);
        }
    }

}
