package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A client prefix keeps the request it hands to its own declared cut.
 *
 * <p>README section 3 states a client prefix as {@code T_C0(Input, Live_out,
 * Req_out)}.  The target-first projection narrows a producer relation to the
 * members some selected downstream edge reads, and on a workflow that
 * schedules nothing on the far side of the cut that set contains only the
 * fragment's heap outputs.  {@code Req_out} was then dropped - and with it
 * every input port only its slice demanded - so the scheduled prefix declared
 * no boundary at the cut it exists for.  At replay such a fragment symbolizes
 * nothing, exports nothing, seals its segment on the enclosing method's plain
 * return with an empty path-condition window, and can only end when the
 * long-lived root it sits on is cut, which the import refuses.</p>
 *
 * <p>The exchanges the plan row declares are the bounded answer to which
 * members belong to the fragment whatever any consumer asked for, so the
 * projection stays target-directed: no call graph is walked and no port of
 * another occurrence is admitted.</p>
 */
public class DeclaredCutExportProjectionTest {

    private static final String EXCHANGE =
            "XCH.11111111-2222-3333-4444-555555555555";
    private static final String REQUEST_PORT = EXCHANGE + ".req.arg0";
    private static final String RESPONSE_PORT = EXCHANGE + ".resp";
    private static final String HEAP_PORT = "REGION.P.out.h";
    private static final String HEAP_INPUT = "REGION.P.in.a";
    private static final String REQUEST_INPUT = "REGION.P.in.b";
    private static final String TARGET_INPUT = "REGION.T.in.k";
    private static final String PRODUCER_OCCURRENCE =
            "cluster/client#epoch0/region/REGION.P#1";
    private static final String TARGET_OCCURRENCE =
            "cluster/target#epoch0/region/REGION.T#1";
    private static final String CONSUMER_OCCURRENCE =
            "cluster/server#epoch0/region/REGION.S#1";
    private static final String CLIENT_METHOD = "<C: void call()>";
    private static final String HEAP_EDGE = "RF.heap";
    private static final String REQUEST_EDGE = "RD.request";

    /**
     * The demanded heap output is projected, and so is the cut's own request:
     * one is what a consumer asked for, the other is what the fragment is.
     */
    @Test
    public void aPrefixProjectionKeepsItsOwnRequestOutput() throws Exception {
        Set<String> outputs = producerOutputPorts();

        assertTrue(outputs.toString(), outputs.contains(HEAP_PORT));
        assertTrue(outputs.toString(), outputs.contains(REQUEST_PORT));
        assertEquals(outputs.toString(), 2, outputs.size());
    }

    /**
     * The retained member's own live-ins travel with it.  A projection that
     * kept the port but not its inputs would state a demand set the closure
     * does not have, and the scheduled task is refused for exactly that.
     */
    @Test
    public void theRetainedRequestBringsItsOwnInputs() throws Exception {
        Set<String> inputs = producerInputPorts();

        assertTrue(inputs.toString(), inputs.contains(HEAP_INPUT));
        assertTrue(inputs.toString(), inputs.contains(REQUEST_INPUT));
        assertTrue(inputs.toString(), inputs.contains(RESPONSE_PORT));
    }

    /**
     * The edge the retained member is stated over travels with it too, so
     * the projected closure never names a boundary with no recorded delivery
     * behind it.
     */
    @Test
    public void theRetainedRequestBringsItsDeliveryEdge() throws Exception {
        Set<String> edges = producerEdgeIds();

        assertTrue(edges.toString(), edges.contains(HEAP_EDGE));
        assertTrue(edges.toString(), edges.contains(REQUEST_EDGE));
    }

    @Test
    public void selectedPhasePromotesOnlyItsExactContinuation() {
        JsonObject row = producerRow();
        JsonArray members = row.getAsJsonArray("closureGoals").get(0)
                .getAsJsonObject().getAsJsonObject("outputClosure")
                .getAsJsonArray("members");
        members.get(0).getAsJsonObject().getAsJsonObject("slice")
                .add(ExecutionTask.REPLAY_ENTRY,
                        replayEntry("<C: void heartbeat()>", "C"));
        members.get(1).getAsJsonObject().getAsJsonObject("slice")
                .add(ExecutionTask.REPLAY_ENTRY,
                        replayEntry("<C: void registration()>", "C"));
        RegionInstancePlan.Goal goal =
                RegionInstancePlan.decode(row).goals().get(0);
        OutputClosureContract selected = OutputClosureCodec.project(
                goal.outputClosure(),
                java.util.Collections.singleton(HEAP_PORT));

        ExecutionTask task = ExecutionTask.create(goal, "TASK.SEED.CUT",
                new JsonArray(), new JsonArray(), new JsonArray(),
                LoopBoundPolicy.cfgBackedges(
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS),
                true, selected);

        assertEquals("<C: void heartbeat()>", task.json()
                .getAsJsonObject(ExecutionTask.REPLAY_ENTRY)
                .get("method").getAsString());
    }

    // ---------------------------------------------------------------
    // Fixture.
    // ---------------------------------------------------------------

    private static RuntimeWorkflowDiscovery.ProducerGroup producerGroup()
            throws Exception {
        List<RuntimeWorkflowDiscovery.ProducerGroup> groups =
                RuntimeWorkflowDiscovery.rankedWorkflow(
                        plans(producerRow(), targetRow()),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet())
                        .producerGroups();
        assertEquals(String.valueOf(groups.size()), 1, groups.size());
        return groups.get(0);
    }

    private static Set<String> producerOutputPorts() throws Exception {
        return producerGroup().outputPorts();
    }

    private static Set<String> producerInputPorts() throws Exception {
        return producerGroup().inputPorts();
    }

    private static Set<String> producerEdgeIds() throws Exception {
        return producerGroup().edgeIds();
    }

    private static JsonObject producerRow() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", "cluster/client#epoch0");
        row.addProperty("occurrenceId", PRODUCER_OCCURRENCE);
        row.addProperty("regionId", "REGION.P");
        row.addProperty("relationKey",
                "cluster/client/relation/REGION.P/segment/SEG.p#0");
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.OUTPUT_RELATION.p");
        goal.addProperty("kind", "OUTPUT_RELATION_CLOSURE");
        goal.add("admission", admission("READY"));
        JsonArray methods = new JsonArray();
        methods.add(CLIENT_METHOD);
        goal.add("runtimeDefinitionMethods", methods);
        JsonArray symbolize = new JsonArray();
        symbolize.add(inputAction(HEAP_INPUT));
        symbolize.add(inputAction(REQUEST_INPUT));
        goal.add("symbolize", symbolize);
        goal.add("branches", new JsonArray());
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        bindings.add(requestEdge());
        goal.add("edgeBindings", bindings);
        goal.add("outputClosure", outputClosure());
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
        return row;
    }

    private static JsonObject targetRow() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", "cluster/target#epoch0");
        row.addProperty("occurrenceId", TARGET_OCCURRENCE);
        row.addProperty("regionId", "REGION.T");
        row.addProperty("relationKey",
                "cluster/target/relation/REGION.T/segment/SEG.t#0");

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.TARGET_REACH.t");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        goal.add("admission", admission("READY"));
        JsonArray methods = new JsonArray();
        methods.add("<T: void handle()>");
        goal.add("runtimeDefinitionMethods", methods);
        JsonArray symbolize = new JsonArray();
        symbolize.add(inputAction(TARGET_INPUT));
        goal.add("symbolize", symbolize);
        goal.add("branches", new JsonArray());
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        goal.add("edgeBindings", bindings);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
        return row;
    }

    private static JsonObject admission(String state) {
        JsonObject admission = new JsonObject();
        admission.addProperty("state", state);
        admission.addProperty("mode", "RUNTIME_FAILURE_CLOSURE");
        admission.add("blockers", new JsonArray());
        return admission;
    }

    private static JsonObject inputAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        return action;
    }

    /** The exact runtime read-from the target's input is demanded through. */
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

    /**
     * The recorded delivery of the cut's own request.  Its consumer is not on
     * this plan, so nothing downstream can demand the port: this is the run
     * that used to lose {@code Req_out}.
     */
    private static JsonObject requestEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("edgeId", REQUEST_EDGE);
        edge.addProperty("correlationAuthority",
                "TRACED_RPC_EXCHANGE_CORRELATION_V1");
        edge.addProperty("evidenceKind",
                "TRACED_RPC_EXCHANGE_CORRELATION_V1");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("fromSegmentKey", "SEG.p");
        edge.addProperty("fromSemanticOccurrenceId", 0);
        edge.addProperty("fromOutputPort", REQUEST_PORT);
        edge.addProperty("toOccurrenceId", CONSUMER_OCCURRENCE);
        edge.addProperty("toInputPort", REQUEST_PORT);
        edge.addProperty("direction",
                CommunicationCatalogContract.DIRECTION_REQUEST);
        edge.addProperty(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                EXCHANGE);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject outputClosure() {
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey",
                "cluster/client/relation/REGION.P/segment/SEG.p#0");
        producer.addProperty("regionId", "REGION.P");
        JsonArray declared = new JsonArray();
        declared.add(REQUEST_PORT);
        producer.add("declaredOutputPorts", declared);

        JsonArray members = new JsonArray();
        members.add(heapMember());
        members.add(requestMember());

        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject heapMember() {
        String cell = "<C: int state>";
        JsonObject output = new JsonObject();
        output.addProperty("portId", HEAP_PORT);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.heap");
        capture.addProperty("captureKind", "REGION_EXIT_FIELD");
        capture.addProperty("outputPort", HEAP_PORT);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("state");
        capture.add("fieldPath", fieldPath);
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", HEAP_INPUT);

        JsonObject slice = slice(HEAP_PORT, cell, capture, HEAP_INPUT);
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        return member;
    }

    private static JsonObject requestMember() {
        String cell = CLIENT_METHOD + "::r1";
        JsonObject output = new JsonObject();
        output.addProperty("portId", REQUEST_PORT);
        output.addProperty("cell", cell);
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("javaTypeDescriptor", "Lorg/example/Req;");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.request");
        capture.addProperty("captureKind", "CALL_ARGUMENT");
        capture.addProperty("outputPort", REQUEST_PORT);
        capture.addProperty("outputCell", cell);
        capture.addProperty("javaType", "org.example.Req");
        capture.addProperty("definitionMethod", CLIENT_METHOD);
        capture.addProperty("definitionUnitIndex", 4);
        capture.addProperty("argumentIndex", 0);
        capture.addProperty("declaredCallee",
                "<T: org.example.Resp send(org.example.Req)>");

        JsonObject slice = slice(REQUEST_PORT, cell, capture,
                REQUEST_INPUT, RESPONSE_PORT);
        JsonArray edges = new JsonArray();
        edges.add(REQUEST_EDGE);
        slice.add("causalEdgeIds", edges);
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        return member;
    }

    private static JsonObject slice(String port, String cell,
                                    JsonObject capture,
                                    String... inputPorts) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        JsonArray inputs = new JsonArray();
        for (String input : inputPorts) inputs.add(input);
        slice.add("inputPorts", inputs);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(CLIENT_METHOD);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray bindings = new JsonArray();
        bindings.add(capture);
        slice.add("captureBindings", bindings);
        slice.add("captureBindingIssues", new JsonArray());
        return slice;
    }

    private static JsonObject replayEntry(
            String method, String receiverClass) {
        JsonObject entry = new JsonObject();
        entry.addProperty("method", method);
        entry.addProperty("receiverClass", receiverClass);
        return entry;
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
