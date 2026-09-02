package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import soot.Body;
import soot.Unit;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

/** The static communication and loop catalog of one target-selected slice. */
final class CommunicationCatalogPlanner {
    private CommunicationCatalogPlanner() {
    }

    /** Static discovery output for one analysis run. */
    static final class Result {
        final List<Map<String, Object>> callSites = new ArrayList<>();
        /** One row per retained loop of a selected method. */
        final List<Map<String, Object>> loops = new ArrayList<>();
        final List<Map<String, Object>> gaps = new ArrayList<>();
        /**
         * Declared callees that are communication boundaries in the selected
         * slice.  This is the authority for where a demand walk stops.
         */
        final Set<String> callSiteCallees = new LinkedHashSet<>();
    }

    /** Publishes declared wire flows and loops in the selected slice. */
    static Result plan(Collection<String> selectedMethods,
                       Function<String, Body> bodies,
                       List<WireFlowCatalog.WireFlow> flows,
                       DeclaredLoopBodyBounds loopBodyBounds) {
        Result result = new Result();
        if (selectedMethods == null || bodies == null || flows == null) {
            return result;
        }
        DeclaredLoopBodyBounds bounds = loopBodyBounds == null
                ? DeclaredLoopBodyBounds.none() : loopBodyBounds;
        List<String> ordered = new ArrayList<>(new TreeSet<>(
                selectedMethods));
        Set<String> selected = new LinkedHashSet<>(ordered);
        for (WireFlowCatalog.WireFlow flow : flows) {
            if (!selected.contains(flow.producer.method)
                    || !selected.contains(flow.consumer.method)) continue;
            result.callSites.add(flow.row());
            for (WireFlowCatalog.CaptureSite endpoint
                    : new WireFlowCatalog.CaptureSite[]{
                    flow.producer, flow.consumer}) {
                if (!endpoint.callee.isEmpty()) {
                    result.callSiteCallees.add(endpoint.callee);
                }
            }
        }

        // Loop discovery is independent of communication: every selected
        // production method may retain loops whether or not it communicates.
        for (String method : ordered) {
            Body body = body(bodies, method);
            if (body == null) continue;
            catalogLoops(method, body, bounds, result);
        }
        return result;
    }

    /**
     * Publishes one row per retained loop of {@code method}: its stable {@code
     * loopSiteId}, its control sites, its kind, the rule that decided the
     * kind, and {@code K_L} where the campaign declared one.
     */
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
        for (CfgLoopControl.RetainedLoop loop : retained) {
            Integer headerPosition = unitIndices.get(loop.header);
            if (headerPosition == null) continue;
            List<String> controlSites = new ArrayList<>();
            for (Unit guard : loop.guards) {
                Integer position = unitIndices.get(guard);
                if (position == null) continue;
                controlSites.add(CommunicationCatalogContract.siteId(method,
                        position.intValue()));
            }
            if (controlSites.isEmpty()) continue;
            String loopSiteId = LoopBoundPolicy.loopSiteId(controlSites);
            boolean fixedCount = CfgLoopControl.fixedCount(
                    loop.classification);
            if (loop.guardsClassifyDifferently) {
                result.gaps.add(gap(
                        LoopBoundPolicy.GAP_LOOP_CLASSIFICATION_INCONSISTENT,
                        "LOOP_NEST_GUARDS_CLASSIFY_DIFFERENTLY", method,
                        loopSiteId, controlSites.toString()));
            }
            int declaredBound = bounds.bound(controlSites);
            if (!fixedCount && declaredBound == 0) {
                // The loop still runs under the inherited K_L, and the model
                // it produces is a prefix nobody stated for this workload.
                result.gaps.add(gap("BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
                        "INHERITED_K_L_"
                                + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
                        method, loopSiteId, controlSites.toString()));
            }
            Map<String, Object> row = newRow(LOOP_ROW_KIND);
            row.put("enclosingMethod", method);
            row.put(LoopBoundPolicy.LOOP_SITE_ID, loopSiteId);
            row.put(LoopBoundPolicy.RUNTIME_LOOP_ID,
                    method + "#loop:u" + headerPosition.intValue());
            row.put(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS, controlSites);
            int latchIndex = headerPosition.intValue();
            for (Unit latch : loop.latches) {
                Integer position = unitIndices.get(latch);
                if (position != null) {
                    latchIndex = Math.max(latchIndex, position.intValue());
                }
            }
            row.put(LoopBoundPolicy.LOOP_LATCH_UNIT_INDEX, latchIndex);
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

    /** {@code kind} of one retained-loop catalog row. */
    static final String LOOP_ROW_KIND = "RETAINED_LOOP";


    /** One schema-stamped catalog row of {@code kind}. */
    static Map<String, Object> newRow(String kind) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                CommunicationCatalogContract.SCHEMA_VERSION);
        row.put(CommunicationCatalogContract.KIND, kind);
        return row;
    }

    static Map<String, Object> gap(String kind, String reason,
                                   String method, String siteId,
                                   String detail) {
        Map<String, Object> row = newRow(
                CommunicationCatalogContract.GAP_ROW_KIND);
        row.put(CommunicationCatalogContract.GAP_KIND, kind);
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
