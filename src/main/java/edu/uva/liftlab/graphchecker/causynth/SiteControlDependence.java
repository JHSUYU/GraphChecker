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
        UnitGraph cfg = new BriefUnitGraph(body);
        MHGPostDominatorsFinder<Unit> post =
                new MHGPostDominatorsFinder<Unit>(cfg);
        List<Integer> branches = new ArrayList<Integer>();
        for (int index = 0; index < units.size(); index++) {
            if (cfg.getSuccsOf(units.get(index)).size() > 1) {
                branches.add(Integer.valueOf(index));
            }
        }
        for (String siteId : siteIds) {
            int unitIndex = SiteId.unitIndexOf(siteId);
            if (unitIndex < 0 || unitIndex >= units.size()) continue;
            Unit site = units.get(unitIndex);
            Set<String> found = new LinkedHashSet<String>();
            for (Integer index : branches) {
                Unit branch = units.get(index.intValue());
                if (post.isDominatedBy(branch, site)) continue;
                for (Unit successor : cfg.getSuccsOf(branch)) {
                    if (post.isDominatedBy(successor, site)) {
                        found.add(SiteId.of(method, index.intValue()));
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
