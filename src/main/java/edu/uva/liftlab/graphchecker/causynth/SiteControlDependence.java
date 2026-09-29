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

/**
 * The guard set of a site: the branches it is control-dependent on.  The one
 * guard computation in the engine.
 *
 * <p>CLOSURE-V2 SS1: site {@code t} is control-dependent on branch {@code b}
 * when some successor of {@code b} is post-dominated by {@code t} and {@code
 * b} is not.  Unlike a may-reach rule, this keeps a branch both of whose arms
 * can reach the site but only one makes it unavoidable -- and so NAMES that
 * arm ({@link StaticScopeMap.Guard#outcome()}).</p>
 *
 * <p>The CFG is {@link BriefUnitGraph} (no exception edges: they would leave
 * almost nothing post-dominated, and a throw is no flippable branch).</p>
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
            public List<StaticScopeMap.Guard> callsInto(String method) {
                if (calls == null) calls = CallSites.ofApplication();
                List<StaticScopeMap.Guard> found =
                        new ArrayList<StaticScopeMap.Guard>();
                Set<String> named = new LinkedHashSet<String>();
                Set<String> visited = new LinkedHashSet<String>();
                List<String> level = Collections.singletonList(method);
                for (int depth = 0; depth < CALL_DEPTH && !level.isEmpty();
                     depth++) {
                    List<String> next = new ArrayList<String>();
                    for (String callee : level) {
                        if (!visited.add(callee)) continue;
                        for (String call : calls.into(callee)) {
                            String caller = SiteId.methodOf(call);
                            MethodGuards guards = callers.get(caller);
                            if (guards == null) {
                                guards = MethodGuards.of(caller);
                                callers.put(caller, guards);
                            }
                            for (StaticScopeMap.Guard guard
                                    : guards.at(SiteId.unitIndexOf(call))) {
                                if (named.add(guard.siteId())) found.add(guard);
                            }
                            next.add(caller);
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

    /** How many calls up a store's calls-into guards reach. */
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

    /** One method's post-dominance relation, built once; callers keep it. */
    public static final class MethodGuards {
        private final String method;
        /** The multi-successor units that have an original index. */
        private final List<Unit> branches;
        private final Map<Unit, Integer> original;
        private final Map<Integer, Unit> byIndex;
        private final MHGPostDominatorsFinder<Unit> post;
        private final UnitGraph cfg;
        private final Map<Integer, List<StaticScopeMap.Guard>> cache =
                new LinkedHashMap<Integer, List<StaticScopeMap.Guard>>();
        private final Map<String, List<Integer>> reachingCache =
                new LinkedHashMap<String, List<Integer>>();

        private MethodGuards(String method, UnitGraph cfg,
                             MHGPostDominatorsFinder<Unit> post,
                             List<Unit> branches,
                             Map<Unit, Integer> original,
                             Map<Integer, Unit> byIndex) {
            this.method = method;
            this.cfg = cfg;
            this.post = post;
            this.branches = branches;
            this.original = original;
            this.byIndex = byIndex;
        }

        /** The relation of one method, or an empty one with no body. */
        public static MethodGuards of(String method) {
            Body body = CausynthStaticFacts.activeBody(
                    CausynthStaticFacts.method(method));
            if (body == null) {
                return new MethodGuards(method, null, null,
                        Collections.<Unit>emptyList(),
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
            MHGPostDominatorsFinder<Unit> post =
                    new MHGPostDominatorsFinder<Unit>(cfg);
            List<Unit> branches = new ArrayList<Unit>();
            for (Unit unit : units) {
                if (cfg.getSuccsOf(unit).size() > 1
                        && original.get(unit).intValue() >= 0) {
                    branches.add(unit);
                }
            }
            return new MethodGuards(method, cfg, post, branches, original,
                    byIndex);
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
         * reachable.  SCOPE for widening the slice, not a guard set: it
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
            List<Integer> computed = computeReaching(unitIndex,
                    controllingOnly);
            reachingCache.put(key, computed);
            return computed;
        }

        private List<Integer> computeReaching(int unitIndex,
                                              boolean controllingOnly) {
            Unit site = byIndex.get(Integer.valueOf(unitIndex));
            if (site == null || cfg == null) {
                return Collections.<Integer>emptyList();
            }
            List<Integer> found = new ArrayList<Integer>();
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
                found.add(original.get(branch));
            }
            return Collections.unmodifiableList(found);
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

        private List<StaticScopeMap.Guard> compute(int unitIndex) {
            Unit site = byIndex.get(Integer.valueOf(unitIndex));
            if (site == null || cfg == null) {
                return Collections.<StaticScopeMap.Guard>emptyList();
            }
            Set<String> named = new LinkedHashSet<String>();
            List<StaticScopeMap.Guard> found =
                    new ArrayList<StaticScopeMap.Guard>();
            for (Unit branch : branches) {
                if (post.isDominatedBy(branch, site)) continue;
                Boolean arm = reachingArm(branch, site);
                if (arm == null && !reaches(branch, site)) continue;
                String guardSite = SiteId.of(method,
                        original.get(branch).intValue());
                if (named.add(guardSite)) {
                    found.add(new StaticScopeMap.Guard(guardSite, arm,
                            arm == null ? null : BooleanReturns.decider(
                                    cfg.getBody(), branch, arm)));
                }
            }
            return Collections.unmodifiableList(found);
        }

        /** True when one arm of {@code branch} makes {@code site} run. */
        private boolean reaches(Unit branch, Unit site) {
            for (Unit successor : cfg.getSuccsOf(branch)) {
                if (post.isDominatedBy(successor, site)) return true;
            }
            return false;
        }

        /** The arm of an if that makes {@code site} unavoidable, or null. */
        private Boolean reachingArm(Unit branch, Unit site) {
            if (!(branch instanceof IfStmt)) return null;
            IfStmt conditional = (IfStmt) branch;
            Unit taken = conditional.getTarget();
            boolean takenForces = taken != null
                    && post.isDominatedBy(taken, site);
            boolean fallsThroughForces = false;
            for (Unit successor : cfg.getSuccsOf(branch)) {
                if (successor == taken) continue;
                fallsThroughForces |= post.isDominatedBy(successor, site);
            }
            if (takenForces == fallsThroughForces) return null;
            return Boolean.valueOf(takenForces);
        }
    }

}
