package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import soot.Body;
import soot.Unit;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.MHGPostDominatorsFinder;
import soot.toolkits.graph.UnitGraph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The guard set of a site: the branches it is control-dependent on.
 *
 * <p>CLOSURE-V2 SS1 states the rule and this is it, textually: site {@code t}
 * is control-dependent on branch {@code b} when some successor of {@code b}
 * is post-dominated by {@code t} and {@code b} itself is not.  Under that
 * rule the counter decrement of 17960's {@code deleteSnapshot} is guarded by
 * BOTH the ordered-deletion marker branch (whose false arm runs it directly)
 * and the earliest-snapshot branch (whose other arm returns), which is what
 * makes the marker a flip candidate of that occurrence.</p>
 *
 * <p>Deliberately not the graph's {@code heap_mutation_path_guard} edges:
 * those keep a branch when SOME successor reaches the site and not all do
 * ({@code SeedBackwardStaticAnalyzer.branchGuards}), which is a MAY-reach
 * test.  The marker branch fails it -- both of its arms can reach the
 * decrement -- while post-dominance keeps it, because the decrement is
 * unavoidable on one arm and avoidable on the other.  A may-reach guard set
 * is the right admission rule for instrumenting a path to a target and the
 * wrong one for naming what decides a write.</p>
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
        Map<String, List<String>> byMethod =
                new LinkedHashMap<String, List<String>>();
        for (String siteId : siteIds == null
                ? Collections.<String>emptyList() : siteIds) {
            String method = methodOf(siteId);
            if (method.isEmpty()) continue;
            List<String> sites = byMethod.get(method);
            if (sites == null) {
                sites = new ArrayList<String>();
                byMethod.put(method, sites);
            }
            sites.add(siteId);
        }
        final Map<String, List<String>> guards =
                new LinkedHashMap<String, List<String>>();
        for (Map.Entry<String, List<String>> entry : byMethod.entrySet()) {
            guards.putAll(guardsOf(entry.getKey(), entry.getValue()));
        }
        return new StaticScopeMap.Guards() {
            @Override
            public List<String> of(String siteId) {
                List<String> found = guards.get(siteId);
                return found == null ? Collections.<String>emptyList() : found;
            }
        };
    }

    private static Map<String, List<String>> guardsOf(String method,
                                                      List<String> siteIds) {
        Map<String, List<String>> guards =
                new LinkedHashMap<String, List<String>>();
        Body body = CausynthStaticFacts.activeBody(
                CausynthStaticFacts.method(method));
        if (body == null) return guards;
        List<Unit> units = new ArrayList<Unit>(body.getUnits());
        // The original index of each unit, by which every site id is spelled.
        // An untagged body was never woven, and there its position IS its
        // original index; a body with tags has them on exactly its original
        // units.
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
        for (String siteId : siteIds) {
            Unit site = byIndex.get(
                    Integer.valueOf(SiteId.unitIndexOf(siteId)));
            if (site == null) continue;
            Set<String> found = new LinkedHashSet<String>();
            for (Unit branch : branches) {
                if (post.isDominatedBy(branch, site)) continue;
                for (Unit successor : cfg.getSuccsOf(branch)) {
                    if (post.isDominatedBy(successor, site)) {
                        found.add(SiteId.of(method,
                                original.get(branch).intValue()));
                        break;
                    }
                }
            }
            guards.put(siteId, new ArrayList<String>(found));
        }
        return guards;
    }

    /** The method one site id names, or "" when it names no unit. */
    private static String methodOf(String siteId) {
        int marker = siteId == null ? -1 : siteId.lastIndexOf("#u");
        return marker < 0 || SiteId.unitIndexOf(siteId) < 0 ? ""
                : siteId.substring(0, marker);
    }
}
