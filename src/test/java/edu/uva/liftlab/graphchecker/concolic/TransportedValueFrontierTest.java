package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Whether a transported structure carrier extends the value frontier.
 *
 * <p>The carrier is concrete <em>as a value</em>: a transported object
 * reference is not a value, and symbolizing it would state nothing.  So the
 * consuming input action is deliberately {@code CONCRETE} with role
 * {@code CONCRETE_STRUCTURE_CARRIER}.  But the carrier is the transport for
 * the leaves the demand actually reads, and transport-for-value is a producer
 * relationship - so frontier membership consults the role the incoming edge
 * states, not only the mode of the consuming action.</p>
 *
 * <p>Reading the mode alone left the exporting occurrence unscheduled while
 * recorded deliveries named it, which in turn left the export with no
 * symbolic source.  These tests pin the rule so it is not simplified back.</p>
 */
public class TransportedValueFrontierTest {

    private static final String EXCHANGE =
            "XCH.aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee";
    private static final String RESPONSE_PORT = EXCHANGE + ".resp";
    private static final String LATER_RESPONSE_PORT =
            "XCH.ffffffff-eeee-dddd-cccc-bbbbbbbbbbbb.resp";
    private static final String HEAP_PORT = "REGION.P.out.h";
    private static final String HEAP_INPUT = "REGION.P.in.a";
    private static final String TARGET_INPUT = "REGION.T.in.k";
    private static final String REMOTE_INPUT = "REGION.R.in.s";
    private static final String PRODUCER_OCCURRENCE =
            "cluster/client#epoch0/region/REGION.P#1";
    private static final String TARGET_OCCURRENCE =
            "cluster/target#epoch0/region/REGION.T#1";
    private static final String REMOTE_OCCURRENCE =
            "cluster/remote#epoch0/region/REGION.R#1";
    private static final String CLIENT_METHOD = "<C: void call()>";
    private static final String REMOTE_METHOD = "<R: Object serve()>";
    private static final String HEAP_EDGE = "RF.heap";
    private static final String DELIVERY_EDGE = "RPC.delivery";
    private static final String ANCHORED_OCCURRENCE =
            "cluster/remote#epoch0/region/REGION.R#1";
    private static final String ACAUSAL_OCCURRENCE =
            "cluster/remote#epoch0/region/REGION.R#2";
    private static final String ANCHORED_EDGE =
            "RPC.11111111-1111-1111-1111-111111111111";
    private static final String ACAUSAL_EDGE =
            "RPC.ffffffff-ffff-ffff-ffff-ffffffffffff";
    /** Sorts after {@link #EARLIER_GOAL} in the identity order. */
    private static final String LATER_GOAL = "GOAL.OUTPUT_RELATION.r-zzz";
    private static final String EARLIER_GOAL = "GOAL.OUTPUT_RELATION.r-aaa";

    /**
     * The demanded write reads a transported structure whose incoming edge
     * states {@code VALUE_FRONTIER}.  The exporting occurrence is scheduled
     * even though the consuming action stays concrete.
     */
    @Test
    public void aTransportedValueFrontierSchedulesItsRemoteProducer()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), targetRow(),
                        remoteRow(REMOTE_OCCURRENCE, DELIVERY_EDGE,
                                "VALUE_FRONTIER")),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());

        assertEquals(describe(workflow), 2,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow,
                REMOTE_OCCURRENCE));
    }

    /**
     * The same transported carrier without the value role keeps today's
     * behaviour: a concrete carrier does not extend the frontier on its
     * transport alone.
     */
    @Test
    public void aTransportedCarrierWithoutTheValueRoleIsNotFollowed()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), targetRow(),
                        remoteRow(REMOTE_OCCURRENCE, DELIVERY_EDGE,
                                "CONCRETE_STRUCTURE_CARRIER")),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());

        assertEquals(describe(workflow), 1,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), !scheduled(workflow,
                REMOTE_OCCURRENCE));
    }

    @Test
    public void requestPrefixKeepsOnlyReadyObservedValueTransactions()
            throws Exception {
        String request = "cluster/client#epoch0/request/fetch#1";
        JsonObject target = requestTargetRow(request, 100L);
        JsonObject selected = requestRemoteRow(
                "cluster/remote#epoch0/region/REGION.R#2",
                "RPC.prefix.selected", request, "VALUE_FRONTIER",
                60L, 70L);
        JsonObject anotherRequest = requestRemoteRow(
                "cluster/remote#epoch0/region/REGION.R#3",
                "RPC.prefix.other", request + ".other", "VALUE_FRONTIER",
                61L, 71L);
        JsonObject afterFailure = requestRemoteRow(
                "cluster/remote#epoch0/region/REGION.R#4",
                "RPC.prefix.late", request, "VALUE_FRONTIER",
                90L, 101L);
        JsonObject carrier = requestRemoteRow(
                "cluster/remote#epoch0/region/REGION.R#5",
                "RPC.prefix.carrier", request,
                "CONCRETE_STRUCTURE_CARRIER", 62L, 72L);
        JsonObject targetRequest = targetRequestConsumer(request,
                "RPC.prefix.target-out", 80L, 90L);

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), target, selected, anotherRequest,
                        afterFailure, carrier, targetRequest),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertEquals(describe(workflow), 2,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow,
                "cluster/remote#epoch0/region/REGION.R#2"));
        assertTrue(describe(workflow), !scheduled(workflow,
                "cluster/remote#epoch0/region/REGION.R#3"));
        assertTrue(describe(workflow), !scheduled(workflow,
                "cluster/remote#epoch0/region/REGION.R#4"));
        assertTrue(describe(workflow), !scheduled(workflow,
                "cluster/remote#epoch0/region/REGION.R#5"));

        RuntimeWorkflowDiscovery.Selection targetSelection =
                workflow.selections().get(0);
        assertTrue(targetSelection.targetEdgeIds.contains(
                "RPC.prefix.target-out"));
        JsonArray merged = ConcolicScheduler.mergeTargetPrefixBindings(
                new JsonArray(), targetSelection.targetPrefixBindings);
        assertEquals(1, merged.size());
        assertEquals("RPC.prefix.target-out", merged.get(0)
                .getAsJsonObject().get("edgeId").getAsString());
    }

    /** A concrete heap receiver is replay structure, not a symbolic writer. */
    @Test
    public void aConcreteHeapCarrierDoesNotScheduleItsWriter()
            throws Exception {
        JsonObject producer = producerRow();
        JsonObject edge = sharedStateEdge(REMOTE_OCCURRENCE,
                DELIVERY_EDGE);
        JsonObject goal = producer.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject();
        goal.getAsJsonArray("edgeBindings").add(edge.deepCopy());
        goal.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("causalEdgeIds").add(DELIVERY_EDGE);
        JsonObject remote = remoteRow(REMOTE_OCCURRENCE, DELIVERY_EDGE,
                "CONCRETE_STRUCTURE_CARRIER");
        remote.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .add("edgeBindings", one(edge));

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producer, targetRow(), remote),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());

        assertEquals(describe(workflow), 1,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), !scheduled(workflow,
                REMOTE_OCCURRENCE));
    }

    @Test
    public void unselectedFailureInputDoesNotDemandItsProducer()
            throws Exception {
        try {
            RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                    producerRow(), targetRow()),
                    (region, action) -> !TARGET_INPUT.equals(
                            action.get("symbol").getAsString()), (regionId, closure) -> Collections.<String>emptySet());
            fail("an unselected target input must not retain its writer");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("no executable producer path"));
        }
    }

    @Test
    public void finalizerAdmittedSharedInputDemandsItsExactWriter()
            throws Exception {
        String location = "T#state";
        JsonObject producer = producerRow();
        producer.addProperty("admissionBasis",
                "SHARED_LOCATION_DEMAND_V1");
        JsonArray consumers = new JsonArray();
        consumers.add("REGION.T");
        producer.add("demandedByRegionIds", consumers);
        JsonArray locations = new JsonArray();
        locations.add(location);
        producer.add("demandedSharedLocations", locations);
        markExactSharedLocation(producer, location);

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producer, targetRow()),
                        (region, action) -> false,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertEquals(describe(workflow), 1,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow,
                PRODUCER_OCCURRENCE));
    }

    /**
     * Two remote executions may deliver the same declared response port to
     * one coarse client occurrence.  The demanded output member records which
     * delivery preceded that output; endpoint-only ranking must not replace it
     * with the lexically earlier occurrence.
     */
    @Test
    public void selectedMemberKeepsItsExactDeliveryOccurrence()
            throws Exception {
        String olderOccurrence =
                "cluster/remote#epoch0/region/REGION.R#1";
        String selectedOccurrence =
                "cluster/remote#epoch0/region/REGION.R#2";
        String olderEdge = "RPC.11111111-1111-1111-1111-111111111111";
        String selectedEdge = "RPC.ffffffff-ffff-ffff-ffff-ffffffffffff";

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRowSelecting(selectedOccurrence,
                                selectedEdge),
                        targetRow(),
                        remoteRow(olderOccurrence, olderEdge,
                                "VALUE_FRONTIER"),
                        remoteRow(selectedOccurrence, selectedEdge,
                                "VALUE_FRONTIER")),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());

        assertEquals(describe(workflow), 2,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), !scheduled(workflow,
                olderOccurrence));
        assertTrue(describe(workflow), scheduled(workflow,
                selectedOccurrence));
        assertTrue(describe(workflow), selectedEdges(workflow,
                selectedOccurrence).contains(selectedEdge));
        assertTrue(describe(workflow), !selectedEdges(workflow,
                selectedOccurrence).contains(olderEdge));
    }

    /** Folded heap versions retain a union catalog, but predecessor discovery
     * follows only the input/edge scope of the selected writer event. */
    @Test
    public void selectedHeapVersionDoesNotDemandAnOlderVersionsInput()
            throws Exception {
        JsonObject producer = producerRow();
        JsonObject goal = producer.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject();
        JsonObject early = deliveryEdge(ANCHORED_OCCURRENCE,
                ANCHORED_EDGE, "VALUE_FRONTIER", RESPONSE_PORT);
        JsonObject late = deliveryEdge(ACAUSAL_OCCURRENCE,
                ACAUSAL_EDGE, "VALUE_FRONTIER", LATER_RESPONSE_PORT);
        goal.getAsJsonArray("edgeBindings").add(early.deepCopy());
        goal.getAsJsonArray("edgeBindings").add(late.deepCopy());
        JsonObject slice = goal.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice");
        slice.getAsJsonArray("inputPorts").add(LATER_RESPONSE_PORT);
        slice.getAsJsonArray("causalEdgeIds").add(ANCHORED_EDGE);
        slice.getAsJsonArray("causalEdgeIds").add(ACAUSAL_EDGE);

        JsonArray versions = new JsonArray();
        versions.add(versionScope(10L, RESPONSE_PORT, HEAP_EDGE));
        versions.add(versionScope(30L, LATER_RESPONSE_PORT, ACAUSAL_EDGE));
        slice.add("boundedVersionScopes", versions);

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producer, targetRow(),
                        remoteRow(ANCHORED_OCCURRENCE, ANCHORED_EDGE,
                                "VALUE_FRONTIER", RESPONSE_PORT),
                        remoteRow(ACAUSAL_OCCURRENCE, ACAUSAL_EDGE,
                                "VALUE_FRONTIER", LATER_RESPONSE_PORT)),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertTrue(describe(workflow), scheduled(workflow,
                ANCHORED_OCCURRENCE));
        assertTrue(describe(workflow), !scheduled(workflow,
                ACAUSAL_OCCURRENCE));
    }

    @Test
    public void writerEventNumberDoesNotReplaceMissingCausalEdgeIdentity()
            throws Exception {
        JsonObject producer = producerRow();
        JsonObject slice = producer.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject().getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice");
        JsonObject oldVersion = versionScope(10L, HEAP_INPUT, HEAP_EDGE);
        oldVersion.add("causalEdgeIds", new JsonArray());
        JsonArray versions = new JsonArray();
        versions.add(oldVersion);
        slice.add("boundedVersionScopes", versions);

        try {
            RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                            producer, targetRow()),
                    (region, action) -> true,
                    (regionId, closure) ->
                            Collections.<String>emptySet());
            fail("event-sequence equality must not revive an old edge");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "no bounded writer version"));
        }
    }

    /** Equivalent target calls on opposite sides of a state write select the
     * changed writer, then the first call that observed that writer. */
    @Test
    public void targetRankingKeepsTopologyChangeButDropsLaterStutter()
            throws Exception {
        JsonObject producer = producerRow();
        JsonObject firstTarget = targetRow();
        JsonObject firstEvidence = new JsonObject();
        firstEvidence.addProperty("rootCallId", 20L);
        firstTarget.add("traceEvidence", firstEvidence);

        String changedOccurrence =
                "cluster/target#epoch0/region/REGION.T#2";
        JsonObject changedEdge = heapEdge();
        changedEdge.addProperty("edgeId", "RF.heap.changed");
        changedEdge.addProperty("toOccurrenceId", changedOccurrence);
        changedEdge.addProperty("writerEventSeq", 30L);
        changedEdge.addProperty("readerEventSeq", 40L);
        JsonObject changedTarget = targetRow(changedOccurrence,
                "GOAL.TARGET_REACH.changed", changedEdge, 40L);

        String stutterOccurrence =
                "cluster/target#epoch0/region/REGION.T#3";
        JsonObject stutterEdge = changedEdge.deepCopy();
        stutterEdge.addProperty("edgeId", "RF.heap.stutter");
        stutterEdge.addProperty("toOccurrenceId", stutterOccurrence);
        stutterEdge.addProperty("readerEventSeq", 50L);
        JsonObject stutterTarget = targetRow(stutterOccurrence,
                "GOAL.TARGET_REACH.stutter", stutterEdge, 50L);

        JsonArray producerEdges = producer.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject().getAsJsonArray("edgeBindings");
        producerEdges.add(changedEdge.deepCopy());
        producerEdges.add(stutterEdge.deepCopy());

        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producer, firstTarget, changedTarget, stutterTarget),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertEquals(changedOccurrence,
                workflow.selections().get(0).occurrenceId);
    }

    /**
     * Two remote executions deliver the same declared response port to one
     * coarse client occurrence, and the member pins neither.  The client
     * produced the demanded value at event 10; one delivery arrived at 5 and
     * the other at 50.  Only the first can have been read, so it is the one
     * addressed -- even though the identity order below would have taken the
     * other.  The occurrence is addressed by the exchange it carries.
     */
    @Test
    public void theOccurrenceCarryingTheDemandedExchangeIsAddressed()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), targetRow(),
                        arrivingRemoteRow(ANCHORED_OCCURRENCE,
                                ANCHORED_EDGE, LATER_GOAL, 5L),
                        arrivingRemoteRow(ACAUSAL_OCCURRENCE,
                                ACAUSAL_EDGE, EARLIER_GOAL, 50L)),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertTrue(describe(workflow), scheduled(workflow,
                ANCHORED_OCCURRENCE));
        assertTrue(describe(workflow), !scheduled(workflow,
                ACAUSAL_OCCURRENCE));
        assertTrue(describe(workflow), selectedEdges(workflow,
                ANCHORED_OCCURRENCE).contains(ANCHORED_EDGE));
    }

    /**
     * FAIL-CLOSED: the same two deliveries with no recorded arrival anchor
     * nothing, and the selection is exactly the identity order it always
     * was.  An occurrence the trace did not time is never promoted on a
     * guess.
     */
    @Test
    public void anUnrecordedArrivalKeepsTodaysOccurrenceOrder()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), targetRow(),
                        goalRemoteRow(ANCHORED_OCCURRENCE,
                                ANCHORED_EDGE, LATER_GOAL),
                        goalRemoteRow(ACAUSAL_OCCURRENCE,
                                ACAUSAL_EDGE, EARLIER_GOAL)),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertTrue(describe(workflow), scheduled(workflow,
                ACAUSAL_OCCURRENCE));
        assertTrue(describe(workflow), !scheduled(workflow,
                ANCHORED_OCCURRENCE));
    }

    /**
     * NO OVER-APPROXIMATION: both deliveries arrived after the client had
     * already produced the demanded value, so neither can explain it.  A late
     * arrival is refused rather than stretched into an anchor, and the
     * identity order stands exactly as it did before this key existed.
     */
    @Test
    public void anArrivalAfterTheProductionAnchorsNothing()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(), targetRow(),
                        arrivingRemoteRow(ANCHORED_OCCURRENCE,
                                ANCHORED_EDGE, LATER_GOAL, 50L),
                        arrivingRemoteRow(ACAUSAL_OCCURRENCE,
                                ACAUSAL_EDGE, EARLIER_GOAL, 60L)),
                        (region, action) -> true,
                        (regionId, closure) ->
                                Collections.<String>emptySet());

        assertTrue(describe(workflow), scheduled(workflow,
                ACAUSAL_OCCURRENCE));
        assertTrue(describe(workflow), !scheduled(workflow,
                ANCHORED_OCCURRENCE));
    }

    // ---------------------------------------------------------------
    // Fixture: a client fragment whose demanded write reads a transported
    // response, the target that demands that write, and the remote fragment
    // that exported the response.
    // ---------------------------------------------------------------

    /** A remote fragment whose delivery states when it reached the client. */
    private static JsonObject arrivingRemoteRow(String occurrenceId,
                                                String edgeId, String goalId,
                                                long arrivalEventSeq) {
        JsonObject row = goalRemoteRow(occurrenceId, edgeId, goalId);
        for (com.google.gson.JsonElement binding
                : row.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .getAsJsonArray("edgeBindings")) {
            binding.getAsJsonObject().addProperty("senderEventSeq",
                    arrivalEventSeq - 1L);
            binding.getAsJsonObject().addProperty("receiverEventSeq",
                    arrivalEventSeq);
        }
        return row;
    }

    /** The same remote fragment under a stated goal identity. */
    private static JsonObject goalRemoteRow(String occurrenceId,
                                            String edgeId, String goalId) {
        JsonObject row = remoteRow(occurrenceId, edgeId, "VALUE_FRONTIER");
        row.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .addProperty("goalId", goalId);
        return row;
    }

    private static String describe(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow) {
        StringBuilder text = new StringBuilder();
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            text.append(group.occurrenceId).append(' ');
        }
        return text.toString();
    }

    private static boolean scheduled(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            String occurrenceId) {
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            if (occurrenceId.equals(group.occurrenceId)) return true;
        }
        return false;
    }

    private static java.util.Set<String> selectedEdges(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            String occurrenceId) throws Exception {
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            if (occurrenceId.equals(group.occurrenceId)) {
                return group.edgeIds();
            }
        }
        return java.util.Collections.emptySet();
    }

    private static JsonObject producerRowSelecting(
            String remoteOccurrence, String edgeId) {
        JsonObject row = producerRow();
        JsonObject goal = row.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject();
        goal.getAsJsonArray("edgeBindings").add(
                deliveryEdge(remoteOccurrence, edgeId,
                        "VALUE_FRONTIER"));
        goal.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("causalEdgeIds").add(edgeId);
        return row;
    }

    private static JsonObject producerRow() {
        JsonObject row = planRow("cluster/client#epoch0",
                PRODUCER_OCCURRENCE, "REGION.P",
                "cluster/client/relation/REGION.P/segment/SEG.p#0");

        JsonObject goal = goalRow("GOAL.OUTPUT_RELATION.p",
                "OUTPUT_RELATION_CLOSURE", CLIENT_METHOD);
        JsonArray symbolize = new JsonArray();
        symbolize.add(valueAction(HEAP_INPUT));
        // The transported carrier: concrete as a value, on purpose.
        symbolize.add(carrierAction(RESPONSE_PORT));
        goal.add("symbolize", symbolize);
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        goal.add("edgeBindings", bindings);
        goal.add("outputClosure", clientClosure());
        attach(row, goal);
        return row;
    }

    private static JsonObject targetRow() {
        JsonObject row = planRow("cluster/target#epoch0",
                TARGET_OCCURRENCE, "REGION.T",
                "cluster/target/relation/REGION.T/segment/SEG.t#0");

        JsonObject goal = goalRow("GOAL.TARGET_REACH.t",
                "TARGET_REACH_CLOSURE", "<T: void handle()>");
        JsonArray symbolize = new JsonArray();
        symbolize.add(valueAction(TARGET_INPUT));
        goal.add("symbolize", symbolize);
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        goal.add("edgeBindings", bindings);
        attach(row, goal);
        return row;
    }

    private static JsonObject requestTargetRow(String requestKey,
                                               long failureEvent) {
        JsonObject row = targetRow();
        row.addProperty("requestKey", requestKey);
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", "<T: void handle()>#u1");
        branch.addProperty("method", "<T: void handle()>");
        branch.addProperty("failureTarget", true);
        branch.addProperty("loopControlGuard", false);
        branch.addProperty("observed", true);
        branch.addProperty("requiredOutcome", false);
        branch.addProperty("selectedRuntimeEventSeq", failureEvent);
        row.getAsJsonArray("closureGoals").get(0).getAsJsonObject()
                .getAsJsonArray("branches").add(branch);
        return row;
    }

    private static JsonObject requestRemoteRow(
            String occurrence, String edgeId, String requestKey,
            String role, long sent, long received) {
        JsonObject row = remoteRow(occurrence, edgeId, role);
        row.addProperty("requestKey", requestKey);
        JsonObject edge = row.getAsJsonArray("closureGoals").get(0)
                .getAsJsonObject().getAsJsonArray("edgeBindings")
                .get(0).getAsJsonObject();
        edge.addProperty("requestKey", requestKey);
        edge.addProperty("senderEventSeq", sent);
        edge.addProperty("receiverEventSeq", received);
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("toRegion", "REGION.prefix-consumer");
        edge.addProperty("toOccurrenceId",
                "cluster/client#epoch0/region/REGION.prefix-consumer#1");
        return row;
    }

    private static JsonObject targetRequestConsumer(
            String requestKey, String edgeId, long sent, long received) {
        String port = "XCH.12345678-1234-3234-8234-123456789abc.req";
        JsonObject edge = deliveryEdge(TARGET_OCCURRENCE, edgeId,
                "VALUE_FRONTIER", port);
        edge.addProperty("requestKey", requestKey);
        edge.addProperty("senderEventSeq", sent);
        edge.addProperty("receiverEventSeq", received);
        edge.addProperty("direction", "REQUEST");
        edge.addProperty("fromRegion", "REGION.T");
        edge.addProperty("toRegion", "REGION.server");
        edge.addProperty("toOccurrenceId",
                "cluster/server#epoch0/region/REGION.server#1");

        JsonObject row = planRow("cluster/server#epoch0",
                "cluster/server#epoch0/region/REGION.server#1",
                "REGION.server", "cluster/server/relation/REGION.server");
        row.addProperty("requestKey", requestKey);
        JsonObject goal = goalRow("GOAL.OUTPUT_RELATION.server",
                "OUTPUT_RELATION_CLOSURE", "<S: void serve()>");
        goal.getAsJsonObject("admission").addProperty("state",
                "DISCOVERED");
        goal.add("symbolize", new JsonArray());
        goal.add("edgeBindings", one(edge));
        attach(row, goal);
        return row;
    }

    private static JsonObject targetRow(String occurrenceId, String goalId,
                                        JsonObject edge, long rootCallId) {
        JsonObject row = planRow("cluster/target#epoch0", occurrenceId,
                "REGION.T",
                "cluster/target/relation/REGION.T/segment/SEG.t#0");
        JsonObject evidence = new JsonObject();
        evidence.addProperty("rootCallId", rootCallId);
        row.add("traceEvidence", evidence);
        JsonObject goal = goalRow(goalId, "TARGET_REACH_CLOSURE",
                "<T: void handle()>");
        JsonArray symbolize = new JsonArray();
        symbolize.add(valueAction(TARGET_INPUT));
        goal.add("symbolize", symbolize);
        JsonArray bindings = new JsonArray();
        bindings.add(edge.deepCopy());
        goal.add("edgeBindings", bindings);
        attach(row, goal);
        return row;
    }

    private static void markExactSharedLocation(JsonObject producer,
                                                String location) {
        JsonObject edge = producer.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject().getAsJsonArray("edgeBindings")
                .get(0).getAsJsonObject();
        edge.addProperty("transportKind", "HEAP");
        edge.addProperty("readFromField", location);
        edge.addProperty("valueObjectId", 8L);
    }

    private static JsonObject remoteRow(String occurrenceId, String edgeId,
                                        String role) {
        return remoteRow(occurrenceId, edgeId, role, RESPONSE_PORT);
    }

    private static JsonObject remoteRow(String occurrenceId, String edgeId,
                                        String role, String responsePort) {
        JsonObject row = planRow("cluster/remote#epoch0", occurrenceId,
                "REGION.R", "cluster/remote/relation/REGION.R/segment/SEG.r#0");

        JsonObject goal = goalRow("GOAL.OUTPUT_RELATION.r",
                "OUTPUT_RELATION_CLOSURE", REMOTE_METHOD);
        JsonArray symbolize = new JsonArray();
        symbolize.add(valueAction(REMOTE_INPUT));
        goal.add("symbolize", symbolize);
        JsonArray bindings = new JsonArray();
        bindings.add(deliveryEdge(occurrenceId, edgeId, role,
                responsePort));
        goal.add("edgeBindings", bindings);
        goal.add("outputClosure", remoteClosure(responsePort));
        attach(row, goal);
        return row;
    }

    private static JsonObject planRow(String sourceKey, String occurrenceId,
                                      String regionId, String relationKey) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", sourceKey);
        row.addProperty("occurrenceId", occurrenceId);
        row.addProperty("regionId", regionId);
        row.addProperty("relationKey", relationKey);
        return row;
    }

    private static JsonObject goalRow(String goalId, String kind,
                                      String method) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", goalId);
        goal.addProperty("kind", kind);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.addProperty("mode", "RUNTIME_FAILURE_CLOSURE");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);
        JsonArray methods = new JsonArray();
        methods.add(method);
        goal.add("runtimeDefinitionMethods", methods);
        goal.add("branches", new JsonArray());
        return goal;
    }

    private static void attach(JsonObject row, JsonObject goal) {
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
    }

    private static JsonObject valueAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        return action;
    }

    /** A transported object reference: concrete, and correctly so. */
    private static JsonObject carrierAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "CONCRETE");
        action.addProperty("dependencyRole", "CONCRETE_STRUCTURE_CARRIER");
        return action;
    }

    private static JsonObject heapEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("transportKind", "HEAP");
        edge.addProperty("readFromField", "T#state");
        edge.addProperty("edgeId", HEAP_EDGE);
        edge.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("fromSegmentKey", "SEG.p");
        edge.addProperty("fromSemanticOccurrenceId", 0);
        edge.addProperty("fromOutputPort", HEAP_PORT);
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        edge.addProperty("toSegmentKey", "SEG.t");
        edge.addProperty("toSemanticOccurrenceId", 0);
        edge.addProperty("toInputPort", TARGET_INPUT);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty("receiverObjectId", 7);
        edge.addProperty("writerEventSeq", 10);
        edge.addProperty("readerEventSeq", 20);
        edge.addProperty("writerLaneId", "1");
        edge.addProperty("readerLaneId", "2");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    /** The recorded delivery that carried the response to the client. */
    private static JsonObject deliveryEdge(String remoteOccurrence,
                                           String edgeId, String role) {
        return deliveryEdge(remoteOccurrence, edgeId, role, RESPONSE_PORT);
    }

    private static JsonObject deliveryEdge(String remoteOccurrence,
                                           String edgeId, String role,
                                           String responsePort) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("state", "CANDIDATE_TRACED_RPC_EXCHANGE");
        edge.addProperty("evidenceState", "APPROXIMATE");
        edge.addProperty("evidenceKind",
                "TRACED_RPC_EXCHANGE_CORRELATION_V1");
        edge.addProperty("correlationAuthority",
                "TRACED_RPC_EXCHANGE_CORRELATION_V1");
        edge.addProperty("transportKind", "HADOOP_IPC");
        edge.addProperty("fromRegion", "REGION.R");
        edge.addProperty("fromOccurrenceId", remoteOccurrence);
        edge.addProperty("fromOutputPort", responsePort);
        edge.addProperty("toRegion", "REGION.P");
        edge.addProperty("toOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("toInputPort", responsePort);
        edge.addProperty("dependencyRole", role);
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject sharedStateEdge(
            String remoteOccurrence, String edgeId) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("evidenceKind",
                "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("transportKind", "HEAP");
        edge.addProperty("fromRegion", "REGION.R");
        edge.addProperty("fromOccurrenceId", remoteOccurrence);
        edge.addProperty("fromOutputPort", RESPONSE_PORT);
        edge.addProperty("toRegion", "REGION.P");
        edge.addProperty("toOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("toInputPort", RESPONSE_PORT);
        edge.addProperty("dependencyRole",
                "CONCRETE_STRUCTURE_CARRIER");
        edge.addProperty("receiverObjectId", 7);
        edge.addProperty("valueObjectId", 8);
        edge.addProperty("writerEventSeq", 10);
        edge.addProperty("readerEventSeq", 20);
        edge.addProperty("writerLaneId", "1");
        edge.addProperty("readerLaneId", "2");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonArray one(JsonObject row) {
        JsonArray rows = new JsonArray();
        rows.add(row.deepCopy());
        return rows;
    }

    private static JsonObject clientClosure() {
        JsonArray inputs = new JsonArray();
        inputs.add(HEAP_INPUT);
        inputs.add(RESPONSE_PORT);
        return closure("REGION.P",
                "cluster/client/relation/REGION.P/segment/SEG.p#0", null,
                member(HEAP_PORT, "<C: int state>", "state", "int", "I",
                        inputs, HEAP_INPUT, CLIENT_METHOD));
    }

    /**
     * The remote fragment declares the response port by name, because the
     * port the exchange minted is not one this region minted itself.
     */
    private static JsonObject remoteClosure() {
        return remoteClosure(RESPONSE_PORT);
    }

    private static JsonObject remoteClosure(String responsePort) {
        return closure("REGION.R",
                "cluster/remote/relation/REGION.R/segment/SEG.r#0",
                responsePort,
                remoteMember(responsePort));
    }

    private static JsonObject remoteMember() {
        return remoteMember(RESPONSE_PORT);
    }

    private static JsonObject remoteMember(String responsePort) {
        JsonArray inputs = new JsonArray();
        inputs.add(REMOTE_INPUT);
        return member(responsePort, "<R: int served>", "served", "int", "I",
                inputs, REMOTE_INPUT, REMOTE_METHOD);
    }

    private static JsonObject versionScope(long eventSeq, String inputPort,
                                           String edgeId) {
        JsonObject scope = new JsonObject();
        scope.addProperty("selectedRuntimeEventSeq", eventSeq);
        JsonArray inputs = new JsonArray();
        inputs.add(HEAP_INPUT);
        inputs.add(inputPort);
        scope.add("inputPorts", inputs);
        JsonArray edges = new JsonArray();
        edges.add(edgeId);
        scope.add("causalEdgeIds", edges);
        return scope;
    }

    private static JsonObject closure(String regionId, String relationKey,
                                      String declaredPort,
                                      JsonObject member) {
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", relationKey);
        producer.addProperty("regionId", regionId);
        if (declaredPort != null) {
            JsonArray declared = new JsonArray();
            declared.add(declaredPort);
            producer.add("declaredOutputPorts", declared);
        }

        JsonArray members = new JsonArray();
        members.add(member);

        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject member(String portId, String cell,
                                     String fieldName, String javaType,
                                     String descriptor, JsonArray inputs,
                                     String accessRoot, String method) {
        JsonObject output = new JsonObject();
        output.addProperty("portId", portId);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", descriptor);

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + portId);
        capture.addProperty("captureKind", "REGION_EXIT_FIELD");
        capture.addProperty("outputPort", portId);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add(fieldName);
        capture.add("fieldPath", fieldPath);
        capture.addProperty("javaType", javaType);
        if (!accessRoot.isEmpty()) {
            capture.addProperty("accessRootInputPort", accessRoot);
        }

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", portId);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", inputs);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(method);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject encoded = new JsonObject();
        encoded.add("output", output);
        encoded.add("slice", slice);
        return encoded;
    }

    /** The plan rows this fixture states, decoded the way the artifact does. */
    private static java.util.List<RegionInstancePlan> plans(
            JsonObject... rows) {
        java.util.List<RegionInstancePlan> decoded =
                new java.util.ArrayList<>();
        for (JsonObject row : rows) {
            decoded.add(RegionInstancePlan.decode(row));
        }
        return decoded;
    }

}
