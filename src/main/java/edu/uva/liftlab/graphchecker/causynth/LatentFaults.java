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

final class LatentFaults implements RootDemand.Faults {
    private final FaultPropagation model;
    private final Map<String, SiteControlDependence.MethodGuards> guards =
            new HashMap<>();
    private final Map<String, BriefUnitGraph> graphs = new HashMap<>();
    private final Predicate<String> held;

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

    private static void keep(Map<String, RootDemand.Candidate> found,
                             RootDemand.Candidate candidate) {
        String key = (candidate.frontier ? "F|" : "D|") + candidate.siteId
                + "|" + candidate.callee;
        RootDemand.Candidate known = found.get(key);
        if (known == null || candidate.distance < known.distance) {
            found.put(key, candidate);
        }
    }

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
