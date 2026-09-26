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
        final Map<String, List<StaticScopeMap.Guard>> guards =
                new LinkedHashMap<String, List<StaticScopeMap.Guard>>();
        for (String siteId : siteIds == null
                ? Collections.<String>emptyList() : siteIds) {
            String method = SiteId.methodOf(siteId);
            if (method.isEmpty()) continue;
            MethodGuards computed = byMethod.get(method);
            if (computed == null) {
                computed = MethodGuards.of(method);
                byMethod.put(method, computed);
            }
            guards.put(siteId, computed.at(SiteId.unitIndexOf(siteId)));
        }
        return new StaticScopeMap.Guards() {
            @Override
            public List<StaticScopeMap.Guard> of(String siteId) {
                List<StaticScopeMap.Guard> found = guards.get(siteId);
                return found == null
                        ? Collections.<StaticScopeMap.Guard>emptyList()
                        : found;
            }
        };
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
