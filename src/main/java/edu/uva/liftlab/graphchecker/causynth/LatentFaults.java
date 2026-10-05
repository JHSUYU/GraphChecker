package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import soot.Body;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.Stmt;
import soot.toolkits.graph.BriefUnitGraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Where a local file fault could stand on what the root demand found
 * (SYMBOL-SCOPE §4.6), over the latent model ({@link
 * FaultPropagation#latent}): from a demanded site down the calls a fault
 * escapes, to the call of a demanded door's anchor it comes from, or to the
 * call into the system outside the scope that may hold one.
 */
final class LatentFaults implements RootDemand.Faults {
    private final FaultPropagation model;
    private final Map<String, SiteControlDependence.MethodGuards> guards =
            new HashMap<>();
    private final Map<String, BriefUnitGraph> graphs = new HashMap<>();
    private final Predicate<String> held;

    /**
     * @param systemClass whether a class is the system's own
     * @param held        whether a region holds a method: a door's marker
     *                    is read in the regions holding its demanded site
     */
    LatentFaults(Predicate<String> systemClass, Predicate<String> held) {
        this.model = FaultPropagation.latent(systemClass);
        this.held = held;
    }

    @Override
    public RootDemand.Candidate valued(String siteId, String callee) {
        LibraryCatalog.Door door = LibraryCatalog.demandedDoor(callee);
        String method = SiteId.methodOf(siteId);
        Unit unit = method.isEmpty() ? null
                : guards(method).unit(SiteId.unitIndexOf(siteId));
        if (door == null || door.result == LibraryCatalog.Result.NONE
                || !(unit instanceof AssignStmt)
                || !((Stmt) unit).containsInvokeExpr()) {
            return null;
        }
        return candidate(Collections.singletonList(method), (Stmt) unit, 0,
                RootDemand.VALUE);
    }

    @Override
    public List<RootDemand.Candidate> latent(Map<String, Integer> demanded,
                                             Map<String, Integer> stores,
                                             Set<String> path) {
        Map<String, RootDemand.Candidate> found = new LinkedHashMap<>();
        // A fault escaping before a demanded store skips it.
        for (Map.Entry<String, Integer> store : stores.entrySet()) {
            String method = SiteId.methodOf(store.getKey());
            Unit site = method.isEmpty() ? null : guards(method).unit(
                    SiteId.unitIndexOf(store.getKey()));
            if (site == null) continue;
            for (FaultPropagation.Raise raise : model.escapes(method)) {
                if (raise.unit != site && reaches(method, raise.unit, site)) {
                    descend(method, raise, store.getValue() + 1,
                            RootDemand.ESCAPE, found);
                }
            }
        }
        // A fault a handler catches decides the sites the handler's arm
        // does; a site on the target's path only where it leads there.
        Map<String, Integer> decided = new LinkedHashMap<>(demanded);
        for (Map.Entry<String, Integer> store : stores.entrySet()) {
            decided.merge(store.getKey(), store.getValue(), Math::min);
        }
        for (String site : path) decided.put(site, 0);
        for (Map.Entry<String, Integer> site : decided.entrySet()) {
            String method = SiteId.methodOf(site.getKey());
            if (method.isEmpty()) continue;
            int index = SiteId.unitIndexOf(site.getKey());
            SiteControlDependence.MethodGuards relation = guards(method);
            for (StaticScopeMap.Guard guard : relation.at(index)) {
                Unit branch = relation.unit(SiteId.unitIndexOf(
                        guard.siteId()));
                if (branch == null) continue;
                for (FaultPropagation.Raise raise
                        : model.decidedBy(method, branch)) {
                    Set<Unit> handlers = model.handlers(method, raise.unit);
                    if (handlers.isEmpty() || path.contains(site.getKey())
                            && !relation.caughtLeadsTo(handlers, index)) {
                        continue;
                    }
                    descend(method, raise, site.getValue() + 1,
                            RootDemand.HANDLER, found);
                }
            }
        }
        return new ArrayList<>(found.values());
    }

    @Override
    public String site(DemandedDoors.Site door) {
        Body body = CausynthStaticFacts.activeBody(
                CausynthStaticFacts.method(door.caller));
        Stmt call = body == null ? null
                : DoorWeave.call(body, door.callee, door.ordinal);
        return call == null ? "" : SiteId.of(door.caller,
                SiteControlDependence.originalIndex(body, call));
    }

    /**
     * From a raise of {@code method} down to where its fault comes from:
     * the call where a door could stand, the call into the system outside
     * the scope, and through each callee it escapes, one edge further each,
     * the chain of methods walked kept as the door's {@code via}.
     */
    private void descend(String method, FaultPropagation.Raise start,
                         int distance, String reach,
                         Map<String, RootDemand.Candidate> found) {
        Deque<Object[]> work = new ArrayDeque<>();
        Set<FaultPropagation.Raise> seen =
                Collections.newSetFromMap(new IdentityHashMap<>());
        work.add(new Object[]{Collections.singletonList(method), start,
                distance});
        while (!work.isEmpty()) {
            Object[] next = work.removeFirst();
            @SuppressWarnings("unchecked")
            List<String> via = (List<String>) next[0];
            String at = via.get(via.size() - 1);
            FaultPropagation.Raise raise = (FaultPropagation.Raise) next[1];
            int hops = (Integer) next[2];
            if (hops > RootDemand.DISTANCE || !seen.add(raise)) continue;
            if (raise.latent != null) {
                keep(found, candidate(via, raise.latent, hops, reach));
            }
            if (raise.frontier != null) {
                keep(found, new RootDemand.Candidate(siteOf(at, raise.unit),
                        raise.frontier, at, 0, hops, reach, true, via,
                        true));
            }
            for (FaultPropagation.Raise origin : raise.origins) {
                work.add(new Object[]{via, origin, hops});
            }
            for (String cell : raise.callees) {
                String callee = cell.substring(0,
                        cell.length() - FaultPropagation.THROWS.length());
                List<String> deeper = new ArrayList<>(via);
                deeper.add(callee);
                for (FaultPropagation.Raise inner : model.escapes(callee)) {
                    work.add(new Object[]{deeper, inner, hops + 1});
                }
            }
        }
    }

    /** The nearer of two findings of one call. */
    private static void keep(Map<String, RootDemand.Candidate> found,
                             RootDemand.Candidate candidate) {
        String key = (candidate.frontier ? "F|" : "D|") + candidate.siteId
                + "|" + candidate.callee;
        RootDemand.Candidate known = found.get(key);
        if (known == null || candidate.distance < known.distance) {
            found.put(key, candidate);
        }
    }

    /** A door at {@code call} in the last method of {@code via}, read
     *  where the first runs. */
    private RootDemand.Candidate candidate(List<String> via, Stmt call,
                                           int distance, String reach) {
        String method = via.get(via.size() - 1);
        Body body = CausynthStaticFacts.activeBody(
                CausynthStaticFacts.method(method));
        return new RootDemand.Candidate(siteOf(method, call),
                call.getInvokeExpr().getMethodRef().getSignature(), method,
                DoorWeave.ordinal(body, call), distance, reach, false, via,
                held.test(via.get(0)));
    }

    private String siteOf(String method, Unit unit) {
        Body body = CausynthStaticFacts.activeBody(
                CausynthStaticFacts.method(method));
        return SiteId.render(method,
                SiteControlDependence.originalIndex(body, unit));
    }

    /** Whether {@code site} runs after {@code from} on some normal path. */
    private boolean reaches(String method, Unit from, Unit site) {
        BriefUnitGraph cfg = graphs.computeIfAbsent(method,
                key -> new BriefUnitGraph(CausynthStaticFacts.activeBody(
                        CausynthStaticFacts.method(key))));
        Set<Unit> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<Unit> work = new ArrayDeque<>(cfg.getSuccsOf(from));
        while (!work.isEmpty()) {
            Unit unit = work.removeFirst();
            if (unit == site) return true;
            if (seen.add(unit)) work.addAll(cfg.getSuccsOf(unit));
        }
        return false;
    }

    private SiteControlDependence.MethodGuards guards(String method) {
        return guards.computeIfAbsent(method,
                key -> SiteControlDependence.MethodGuards.of(key, model));
    }
}
