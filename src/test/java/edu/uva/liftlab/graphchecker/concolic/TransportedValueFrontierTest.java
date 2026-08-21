package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

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

    /**
     * The demanded write reads a transported structure whose incoming edge
     * states {@code VALUE_FRONTIER}.  The exporting occurrence is scheduled
     * even though the consuming action stays concrete.
     */
    @Test
    public void aTransportedValueFrontierSchedulesItsRemoteProducer()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producerRow(), targetRow(),
                        remoteRow(REMOTE_OCCURRENCE, DELIVERY_EDGE,
                                "VALUE_FRONTIER")),
                        (region, action) -> true);

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
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producerRow(), targetRow(),
                        remoteRow(REMOTE_OCCURRENCE, DELIVERY_EDGE,
                                "CONCRETE_STRUCTURE_CARRIER")),
                        (region, action) -> true);

        assertEquals(describe(workflow), 1,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), !scheduled(workflow,
                REMOTE_OCCURRENCE));
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
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producer, targetRow(), remote),
                        (region, action) -> true);

        assertEquals(describe(workflow), 1,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), !scheduled(workflow,
                REMOTE_OCCURRENCE));
    }

    /**
     * An exact reference field that the finalizer identifies as carrying a
     * configured VM component does retain its writer.  The consuming action
     * remains concrete; only the marked edge extends the scheduling frontier.
     */
    @Test
    public void anExactVmComponentCarrierSchedulesItsHeapWriter()
            throws Exception {
        JsonObject producer = producerRow();
        JsonObject edge = sharedStateEdge(REMOTE_OCCURRENCE,
                DELIVERY_EDGE);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty(
                AutomaticRegionEdge.TRANSPORTED_VALUE_FRONTIER_FIELD,
                AutomaticRegionEdge.TRANSPORTED_VALUE_FRONTIER_AUTHORITY);
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
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producer, targetRow(), remote),
                        (region, action) -> true);

        assertEquals(describe(workflow), 2,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow,
                REMOTE_OCCURRENCE));
    }

    @Test
    public void unselectedFailureInputDoesNotDemandItsProducer()
            throws Exception {
        try {
            RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                    producerRow(), targetRow()),
                    (region, action) -> !TARGET_INPUT.equals(
                            action.get("symbol").getAsString()));
            fail("an unselected target input must not retain its writer");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("no executable producer path"));
        }
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
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        producerRowSelecting(selectedOccurrence,
                                selectedEdge),
                        targetRow(),
                        remoteRow(olderOccurrence, olderEdge,
                                "VALUE_FRONTIER"),
                        remoteRow(selectedOccurrence, selectedEdge,
                                "VALUE_FRONTIER")),
                        (region, action) -> true);

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

    // ---------------------------------------------------------------
    // Fixture: a client fragment whose demanded write reads a transported
    // response, the target that demands that write, and the remote fragment
    // that exported the response.
    // ---------------------------------------------------------------

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

    private static JsonObject remoteRow(String occurrenceId, String edgeId,
                                        String role) {
        JsonObject row = planRow("cluster/remote#epoch0", occurrenceId,
                "REGION.R", "cluster/remote/relation/REGION.R/segment/SEG.r#0");

        JsonObject goal = goalRow("GOAL.OUTPUT_RELATION.r",
                "OUTPUT_RELATION_CLOSURE", REMOTE_METHOD);
        JsonArray symbolize = new JsonArray();
        symbolize.add(valueAction(REMOTE_INPUT));
        goal.add("symbolize", symbolize);
        JsonArray bindings = new JsonArray();
        bindings.add(deliveryEdge(occurrenceId, edgeId, role));
        goal.add("edgeBindings", bindings);
        goal.add("outputClosure", remoteClosure());
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
        edge.addProperty("fromOutputPort", RESPONSE_PORT);
        edge.addProperty("toRegion", "REGION.P");
        edge.addProperty("toOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("toInputPort", RESPONSE_PORT);
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
        return closure("REGION.R",
                "cluster/remote/relation/REGION.R/segment/SEG.r#0",
                RESPONSE_PORT,
                remoteMember());
    }

    private static JsonObject remoteMember() {
        JsonArray inputs = new JsonArray();
        inputs.add(REMOTE_INPUT);
        return member(RESPONSE_PORT, "<R: int served>", "served", "int", "I",
                inputs, REMOTE_INPUT, REMOTE_METHOD);
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
}
