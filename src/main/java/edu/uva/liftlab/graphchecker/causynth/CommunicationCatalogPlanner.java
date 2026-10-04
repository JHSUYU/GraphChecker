package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import soot.Body;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;
import soot.jimple.SwitchStmt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

/** The static communication and loop catalog of one target-selected slice. */
final class CommunicationCatalogPlanner {
    private CommunicationCatalogPlanner() {
    }

    static final class Result {
        final List<Map<String, Object>> callSites = new ArrayList<>();
        final List<Map<String, Object>> loops = new ArrayList<>();
        final List<Map<String, Object>> gaps = new ArrayList<>();
        /** Communication-boundary callees: where a demand walk stops. */
        final Set<String> callSiteCallees = new LinkedHashSet<>();
    }

    /**
     * Publishes the wire ports and the loops of the selected slice; seeding a
     * port's captures selected their methods.  A port with no capture on one
     * side carries nothing.
     */
    static Result plan(Collection<String> selectedMethods,
                       Function<String, Body> bodies,
                       List<WireFlowCatalog.WireFlow> flows,
                       DeclaredLoopBodyBounds bounds) {
        Result result = new Result();
        List<String> ordered = new ArrayList<>(new TreeSet<>(
                selectedMethods));
        for (WireFlowCatalog.WireFlow flow : flows) {
            if (flow.producers.isEmpty() || flow.consumers.isEmpty()) continue;
            result.callSites.add(flow.row());
            List<WireFlowCatalog.CaptureSite> captures =
                    new ArrayList<>(flow.producers);
            captures.addAll(flow.consumers);
            for (WireFlowCatalog.CaptureSite capture : captures) {
                if (!capture.callee.isEmpty()) {
                    result.callSiteCallees.add(capture.callee);
                }
            }
        }

        // Loops of every selected method, communicating or not.
        for (String method : ordered) {
            Body body = body(bodies, method);
            if (body == null) continue;
            catalogLoops(method, body, bounds, result);
        }
        return result;
    }

    /** Publishes one row per retained loop of {@code method}. */
    private static void catalogLoops(String method, Body body,
                                     DeclaredLoopBodyBounds bounds,
                                     Result result) {
        List<CfgLoopControl.RetainedLoop> retained =
                CfgLoopControl.retainedLoops(CfgLoopControl.loopCfg(body));
        if (retained.isEmpty()) return;
        Map<Unit, Integer> unitIndices = new LinkedHashMap<>();
        int index = -1;
        for (Unit unit : body.getUnits()) {
            unitIndices.put(unit, Integer.valueOf(++index));
        }
        Map<Unit, CfgLoopControl.RetainedLoop> innermostByBranch =
                innermostLoopsByBranch(body, retained);
        for (CfgLoopControl.RetainedLoop loop : retained) {
            Integer headerPosition = unitIndices.get(loop.header);
            if (headerPosition == null) continue;
            List<String> controlSites = new ArrayList<>();
            for (Unit guard : loop.guards) {
                Integer position = unitIndices.get(guard);
                if (position == null) continue;
                controlSites.add(SiteId.of(method,
                        position.intValue()));
            }
            if (controlSites.isEmpty()) continue;
            String loopSiteId = LoopBoundPolicy.loopSiteId(controlSites);
            boolean fixedCount = CfgLoopControl.fixedCount(
                    loop.classification);
            if (loop.guardsClassifyDifferently) {
                result.gaps.add(gap(
                        GapKind.BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT,
                        GapClass.DIAGNOSTIC,
                        "LOOP_NEST_GUARDS_CLASSIFY_DIFFERENTLY", method,
                        loopSiteId, controlSites.toString()));
            }
            int declaredBound = bounds.bound(controlSites);
            if (!fixedCount && declaredBound == 0) {
                // Runs under the inherited K_L: a prefix nobody stated.
                result.gaps.add(gap(
                        GapKind.BOUNDED_LOOP_BODY_BOUND_UNDECLARED,
                        GapClass.DIAGNOSTIC,
                        "INHERITED_K_L_"
                                + LoopBoundPolicy.declaredDefault(),
                        method, loopSiteId, controlSites.toString()));
            } else if (fixedCount && declaredBound == 0) {
                // Named, not demanded: the trip count is the array length,
                // observed exactly, so a declared K_L would only weaken it.
                result.gaps.add(gap(
                        GapKind.BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED,
                        GapClass.DIAGNOSTIC,
                        "EXACT_ARRAY_CARDINALITY_EXPECTED",
                        method, loopSiteId, controlSites.toString()));
            }
            Map<String, Object> row = newRow(LOOP_ROW_KIND);
            row.put("enclosingMethod", method);
            row.put(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                    method + "#loop:u" + headerPosition.intValue());
            row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controlSites);
            List<String> memberBranches = new ArrayList<>();
            for (Unit unit : body.getUnits()) {
                if (innermostByBranch.get(unit) != loop) continue;
                Integer position = unitIndices.get(unit);
                if (position != null) {
                    memberBranches.add(SiteId.of(
                            method, position.intValue()));
                }
            }
            row.put(LoopBoundPolicy.LOOP_INNERMOST_BRANCH_SITE_IDS,
                    memberBranches);
            List<Map<String, Object>> exitDecisions = new ArrayList<>();
            for (Unit guard : loop.guards) {
                Integer position = unitIndices.get(guard);
                CausynthBranchShape shape = CausynthBranchShape.from(
                        body, guard);
                if (position == null || shape == null) continue;
                String site = SiteId.of(method,
                        position.intValue());
                // One row per exiting guard.
                if (loop.members.containsAll(shape.successors)) continue;
                Map<String, Object> exit = newRow("LOOP_EXIT_DECISION");
                exit.put("siteId", site);
                exitDecisions.add(exit);
            }
            row.put(LoopBoundPolicy.LOOP_EXIT_DECISIONS, exitDecisions);
            int latchIndex = headerPosition.intValue();
            for (Unit latch : loop.latches) {
                Integer position = unitIndices.get(latch);
                if (position != null) {
                    latchIndex = Math.max(latchIndex, position.intValue());
                }
            }
            row.put(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, latchIndex);
            List<Integer> entries = new ArrayList<>();
            for (Unit unit : body.getUnits()) {
                Integer position = unitIndices.get(unit);
                if (position != null && unit instanceof Stmt
                        && ((Stmt) unit).containsInvokeExpr()
                        && CfgLoopControl.bodyEntry(loop.natural,
                        loop.guards, unit) != null) {
                    entries.add(position);
                }
            }
            row.put(LoopBoundPolicy.BODY_ENTRY_CALL_UNITS, entries);
            row.put(LoopBoundPolicy.LOOP_CLASSIFICATION, loop.classification);
            row.put(LoopBoundPolicy.LOOP_CLASSIFICATION_AUTHORITY,
                    CfgLoopControl.classificationAuthority(
                            loop.classification));
            if (declaredBound > 0) {
                row.put(LoopBoundPolicy.LOOP_BODY_BOUND, declaredBound);
            }
            result.loops.add(row);
        }
    }

    /** Exact, unambiguous innermost natural-loop owner of every branch. */
    private static Map<Unit, CfgLoopControl.RetainedLoop>
            innermostLoopsByBranch(
            Body body, List<CfgLoopControl.RetainedLoop> loops) {
        Map<Unit, CfgLoopControl.RetainedLoop> result =
                new IdentityHashMap<>();
        for (Unit unit : body.getUnits()) {
            if (!(unit instanceof IfStmt) && !(unit instanceof SwitchStmt)) {
                continue;
            }
            List<CfgLoopControl.RetainedLoop> owners = new ArrayList<>();
            for (CfgLoopControl.RetainedLoop candidate : loops) {
                if (candidate.members.contains(unit)) owners.add(candidate);
            }
            CfgLoopControl.RetainedLoop selected = null;
            for (CfgLoopControl.RetainedLoop candidate : owners) {
                boolean insideEveryOther = true;
                for (CfgLoopControl.RetainedLoop other : owners) {
                    if (other == candidate) continue;
                    if (!other.members.containsAll(candidate.members)
                            || candidate.members.containsAll(other.members)) {
                        insideEveryOther = false;
                        break;
                    }
                }
                if (insideEveryOther) {
                    if (selected != null) {
                        selected = null;
                        break;
                    }
                    selected = candidate;
                }
            }
            // Equal or overlapping bodies: no unique innermost owner.
            if (selected != null) result.put(unit, selected);
        }
        return result;
    }

    static final String LOOP_ROW_KIND = "RETAINED_LOOP";


    /** One schema-stamped catalog row of {@code kind}. */
    static Map<String, Object> newRow(String kind) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                CommunicationCatalogContract.SCHEMA_VERSION);
        row.put(CommunicationCatalogContract.KIND, kind);
        return row;
    }

    /**
     * One catalog gap stating its own kind and class, like a {@link
     * edu.uva.liftlab.graphchecker.contract.GapRow}; no later stage overrules.
     */
    static Map<String, Object> gap(GapKind kind, GapClass cls, String reason,
                                   String method, String siteId,
                                   String detail) {
        Map<String, Object> row = newRow(kind.name());
        row.put(CommunicationCatalogContract.GAP_CLASS, cls.name());
        row.put(CommunicationCatalogContract.GAP_REASON, reason);
        row.put(CommunicationCatalogContract.GAP_METHOD, method);
        row.put(CommunicationCatalogContract.GAP_SITE_ID, siteId);
        row.put(CommunicationCatalogContract.GAP_DETAIL, detail);
        return row;
    }

    private static Body body(Function<String, Body> bodies, String method) {
        try {
            return bodies.apply(method);
        } catch (RuntimeException unavailable) {
            return null;
        }
    }
}
