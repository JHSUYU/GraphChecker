package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import soot.Body;
import soot.Unit;
import soot.jimple.IfStmt;
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
                        LoopBoundPolicy.GAP_LOOP_CLASSIFICATION_INCONSISTENT,
                        "LOOP_NEST_GUARDS_CLASSIFY_DIFFERENTLY", method,
                        loopSiteId, controlSites.toString()));
            }
            int declaredBound = bounds.bound(controlSites);
            if (declaredBound == 0) {
                // The loop still runs under the inherited K_L, and the model
                // it produces is a prefix nobody stated for this workload.
                //
                // FIXED_COUNT_INDEXED used to be exempt here, on the reading
                // that an array-indexed for is bounded by its array. It is
                // not: the cardinality that would bound it is a runtime
                // observation, and when the replay publishes no exact
                // cardinality vector the loop runs at the same inherited
                // ceiling every other undeclared loop runs at -- on
                // hdfs-11741 that was 4 of 7 retained loops, every one of
                // them at loopBodyBound NONE and none of them named. So the
                // exemption is gone and the classification is reported
                // instead, the way guardsClassifyDifferently above already
                // reports its finding.
                result.gaps.add(gap("BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
                        (fixedCount
                                ? LoopBoundPolicy.LOOP_FIXED_COUNT_INDEXED
                                        + "_INHERITED_K_L_"
                                : "INHERITED_K_L_")
                                + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS,
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
                for (int successor = 0;
                     successor < shape.successors.size(); successor++) {
                    if (loop.members.contains(
                            shape.successors.get(successor))) continue;
                    Map<String, Object> exit = newRow("LOOP_EXIT_DECISION");
                    exit.put("siteId", site);
                    exit.put("decisionToken", shape.isSwitch()
                            ? ExactConcreteBranchObservation
                            .switchDecisionToken(shape.kind, shape.caseKeys,
                                    successor)
                            : ExactConcreteBranchObservation
                            .binaryDecisionToken(successor == 1));
                    exitDecisions.add(exit);
                }
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
            // Equal or overlapping loop bodies have no unique innermost
            // owner. Their branches retain exact ordinals.
            if (selected != null) result.put(unit, selected);
        }
        return result;
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
