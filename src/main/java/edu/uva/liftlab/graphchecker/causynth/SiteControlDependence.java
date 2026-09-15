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
 * <p>CLOSURE-V2 SS1 states the rule and this is it, textually: site {@code t}
 * is control-dependent on branch {@code b} when some successor of {@code b}
 * is post-dominated by {@code t} and {@code b} itself is not.  Under that
 * rule the counter decrement of 17960's {@code deleteSnapshot} is guarded by
 * BOTH the ordered-deletion marker branch (whose false arm runs it directly)
 * and the earliest-snapshot branch (whose other arm returns), which is what
 * makes the marker a flip candidate of that occurrence.</p>
 *
 * <p>It replaced a second, MAY-reach rule -- keep a branch when SOME
 * successor reaches the site and not all do -- which the backward slice used
 * to compute for itself and publish as {@code path_guard_dependency},
 * {@code heap_mutation_path_guard}, {@code receiver_field_effect_path_guard}
 * and {@code activation_path_guard} edges.  The marker branch fails that test
 * -- both of its arms can reach the decrement -- while post-dominance keeps
 * it, because the decrement is unavoidable on one arm and avoidable on the
 * other.  There is now one rule, computed here, and its answer reaches the
 * slice, the static scope map and the task plan from this file alone.</p>
 *
 * <p>Because post-dominance keeps a branch only when exactly one arm makes
 * the site unavoidable, the kept branch also NAMES that arm: {@link
 * StaticScopeMap.Guard#outcome()} is the outcome a replay must decide to
 * reach the site, and for the annotated throw it is phi's fatal polarity.</p>
 *
 * <p>The CFG is {@link BriefUnitGraph}: normal control flow only.  Exception
 * edges leave almost nothing post-dominating anything, and an exception is
 * not a branch a flip can take -- the annotated throw is the target, not a
 * guard of it.</p>
 *
 * <p>Every index here is the ORIGINAL one
 * ({@link CausynthPipeline#originalUnitIndex}), which is the numbering every
 * published site id is in: the graph's write sites, the plan's branches and
 * the branch sites INSTRUMENT weaves are all {@code <method>#u<original>}.
 * Read off a woven body by POSITION instead, a guard id is shifted by
 * however many units the hooks before it added -- 17960's target guard came
 * out {@code #u63} for the branch the replay decides as {@code #u61}, and
 * nothing in the session was ever decided at a published guard id.  A woven
 * unit has no original index and so can never BE a guard: it is a CFG node
 * like any other, and no DecisionRow can stand at a site no plan named.</p>
 */
public final class SiteControlDependence {
    private SiteControlDependence() {
    }

    /**
     * The guard sets of the given sites, computed from the live Scene.
     *
     * <p>A site whose method has no retrievable body, or whose unit index is
     * not in it, answers with no guards: the map then publishes a site with
     * an empty guard set, which exploration reads as "this map states no
     * branch for it" rather than as "nothing guards it".</p>
     */
    public static StaticScopeMap.Guards over(Collection<String> siteIds) {
        Map<String, MethodGuards> byMethod =
                new LinkedHashMap<String, MethodGuards>();
        final Map<String, List<StaticScopeMap.Guard>> guards =
                new LinkedHashMap<String, List<StaticScopeMap.Guard>>();
        for (String siteId : siteIds == null
                ? Collections.<String>emptyList() : siteIds) {
            String method = methodOf(siteId);
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

    /**
     * One method's post-dominance relation, built once and asked about any
     * unit in it.
     *
     * <p>The relation costs a CFG and a post-dominator walk per method, and
     * the backward slice asks about many sites of the same method, so the
     * caller keeps this object rather than the answer.</p>
     */
    public static final class MethodGuards {
        private final String method;
        /** Branch unit -> the arm that makes each post-dominated unit run. */
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
            // The original index of each unit, by which every site id is
            // spelled.  An untagged body was never woven, and there its
            // position IS its original index; a body with tags has them on
            // exactly its original units.
            boolean tagged = false;
            for (Unit unit : units) {
                tagged |= CausynthPipeline.originalUnitIndex(unit) >= 0;
            }
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
         * reachable, as original indices.
         *
         * <p>SCOPE, not a guard set: it names no arm, is published as no
         * edge member and decides nothing.  It is what the root-dependence
         * slice is widened by, so that a value deciding a branch on SOME
         * path to a demanded site is in the slice -- SiteControlDependence's
         * own note says a may-reach set "is the right admission rule for
         * instrumenting a path to a target and the wrong one for naming what
         * decides a write", and these are those two answers, from one CFG
         * and one owner.</p>
         *
         * @param controllingOnly keep a branch only when a proper subset of
         *                        its successors reaches the site, which is
         *                        control dependence in the may-reach sense;
         *                        false keeps every branch that can reach it
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

        /**
         * Reachability within the current dynamic occurrence of the branch:
         * the branch itself is a barrier, so a path that loops back through
         * it is a later occurrence and not this one.
         */
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
                    found.add(new StaticScopeMap.Guard(guardSite, arm));
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

        /**
         * Which arm of a binary branch makes {@code site} unavoidable, or
         * null when the branch is not binary or both arms answer alike.
         */
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

    /** The method one site id names, or "" when it names no unit. */
    private static String methodOf(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf("#u");
        return marker < 0 || SiteId.unitIndexOf(siteId) < 0 ? ""
                : siteId.substring(0, marker);
    }
}
