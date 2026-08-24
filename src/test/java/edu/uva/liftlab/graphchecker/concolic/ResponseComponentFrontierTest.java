package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Exact component delivery behind a concrete structured response input. */
public class ResponseComponentFrontierTest {

    private static final String EXCHANGE =
            "XCH.12345678-1234-3234-8234-123456789abc";
    private static final String RESPONSE = EXCHANGE + ".resp";
    private static final String COMPONENT = RESPONSE + ".keyId";
    private static final String HEAP_INPUT = "REGION.C.in.state";
    private static final String HEAP_OUTPUT = "REGION.C.out.state";
    private static final String TARGET_INPUT = "REGION.T.in.state";
    private static final String CONSUMER =
            "node/client#epoch0/region/REGION.C#1";
    private static final String TARGET =
            "node/target#epoch0/region/REGION.T#1";
    private static final String SELECTED =
            "node/server#epoch0/region/REGION.R#2";
    private static final String UNRELATED =
            "node/server#epoch0/region/REGION.R#1";
    private static final String SELECTED_EDGE = "RPC.selected";
    private static final String UNRELATED_EDGE = "RPC.unrelated";
    private static final String HEAP_EDGE = "RF.consumer-target";
    private static final String KEYS_INPUT = "REGION.R.in.keys";
    private static final String GUARD_INPUT = "REGION.R.in.guard";
    private static final String STATS_INPUT = "REGION.R.in.stats";
    private static final String KEYS_OUTPUT = "REGION.K.out.keys";
    private static final String GUARD_OUTPUT = "REGION.G.out.guard";
    private static final String STATS_OUTPUT = "REGION.S.out.stats";
    private static final String KEYS_WRITER =
            "node/keys#epoch0/region/REGION.K#1";
    private static final String GUARD_WRITER =
            "node/guard#epoch0/region/REGION.G#1";
    private static final String STATS_WRITER =
            "node/stats#epoch0/region/REGION.S#1";
    private static final String KEYS_EDGE = "RF.keys";
    private static final String GUARD_EDGE = "RF.guard";
    private static final String STATS_EDGE = "RF.stats";
    private static final String SOURCE_EDGE = "RF.source";
    private static final String SOURCE_OUTPUT = "REGION.R.out.source";
    private static final String SOURCE_INPUT = "REGION.R.in.sourceRoot";
    private static final String SOURCE_CELL = "<Server: int state>";
    private static final String SOURCE_ROOT_OUTPUT =
            "REGION.P.out.sourceRoot";
    private static final String SOURCE_WRITER =
            "node/source#epoch0/region/REGION.P#1";

    /**
     * A heap write may read the concrete parent response even though the VM
     * attaches only one configured component of it.  That component extends
     * the value frontier.  The output member's exact delivery id still picks
     * one dynamic server occurrence when the exchange site ran repeatedly.
     */
    @Test
    public void parentResponseSliceSchedulesItsExactAttachedComponent()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        consumerRow(), targetRow(),
                        remoteRow(UNRELATED, UNRELATED_EDGE),
                        remoteRow(SELECTED, SELECTED_EDGE)),
                        (region, action) -> true);

        assertEquals(describe(workflow), 2,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow, CONSUMER));
        assertTrue(describe(workflow), scheduled(workflow, SELECTED));
        assertFalse(describe(workflow), scheduled(workflow, UNRELATED));
        assertEquals(java.util.Collections.singleton(SELECTED_EDGE),
                edges(workflow, SELECTED));
    }

    /** The narrowed component frontier schedules keys and its guard only. */
    @Test
    public void componentFrontierDoesNotScheduleUnrelatedStatsProducer()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        consumerRow(), targetRow(),
                        remoteRowWithFrontier(false),
                        stateProducerRow(KEYS_WRITER, "REGION.K",
                                KEYS_OUTPUT, KEYS_EDGE, KEYS_INPUT),
                        stateProducerRow(GUARD_WRITER, "REGION.G",
                                GUARD_OUTPUT, GUARD_EDGE, GUARD_INPUT),
                        stateProducerRow(STATS_WRITER, "REGION.S",
                                STATS_OUTPUT, STATS_EDGE, STATS_INPUT)),
                        (region, action) -> true);

        assertTrue(describe(workflow), scheduled(workflow, KEYS_WRITER));
        assertTrue(describe(workflow), scheduled(workflow, GUARD_WRITER));
        assertFalse(describe(workflow), scheduled(workflow, STATS_WRITER));
        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                SELECTED_EDGE, KEYS_EDGE, GUARD_EDGE)),
                edges(workflow, SELECTED));
    }

    /** Negative control: a stats input demanded by the slice is retained. */
    @Test
    public void componentFrontierKeepsStatsWhenParentSliceDemandsIt()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        consumerRow(), targetRow(),
                        remoteRowWithFrontier(true),
                        stateProducerRow(KEYS_WRITER, "REGION.K",
                                KEYS_OUTPUT, KEYS_EDGE, KEYS_INPUT),
                        stateProducerRow(GUARD_WRITER, "REGION.G",
                                GUARD_OUTPUT, GUARD_EDGE, GUARD_INPUT),
                        stateProducerRow(STATS_WRITER, "REGION.S",
                                STATS_OUTPUT, STATS_EDGE, STATS_INPUT)),
                        (region, action) -> true);

        assertTrue(describe(workflow), scheduled(workflow, STATS_WRITER));
        assertTrue(edges(workflow, SELECTED).contains(STATS_EDGE));
    }

    /** Source outputs augment the chosen producer without changing ranking. */
    @Test
    public void configuredSourceOutputAugmentsOnlyTheRankedOccurrence()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        consumerRow(), targetRow(),
                        remoteRow(UNRELATED, UNRELATED_EDGE),
                        remoteRowWithSourceOutput()),
                        (region, action) -> true,
                        (region, closure) -> "REGION.R".equals(region)
                                ? java.util.Collections.singleton(SOURCE_CELL)
                                : java.util.Collections.emptySet());

        // The already-ranked component and the newly configured source
        // output are distinct replay phases of the same exact occurrence.
        assertEquals(describe(workflow), 3,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow, SELECTED));
        assertFalse(describe(workflow), scheduled(workflow, UNRELATED));
        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                COMPONENT, SOURCE_OUTPUT)), outputs(workflow, SELECTED));
    }

    /** Source-only members participate in predecessor closure before split. */
    @Test
    public void configuredSourceOutputClosesItsExactPriorProducer()
            throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        consumerRow(), targetRow(),
                        remoteRow(UNRELATED, UNRELATED_EDGE),
                        remoteRowWithSourceOutput(true),
                        stateProducerRow(SOURCE_WRITER, "REGION.P",
                                SOURCE_ROOT_OUTPUT, SOURCE_EDGE,
                                SOURCE_INPUT)),
                        (region, action) -> true,
                        (region, closure) -> "REGION.R".equals(region)
                                ? java.util.Collections.singleton(SOURCE_CELL)
                                : java.util.Collections.emptySet());

        assertEquals(describe(workflow), 4,
                workflow.producerGroups().size());
        assertTrue(describe(workflow), scheduled(workflow, SELECTED));
        assertTrue(describe(workflow), scheduled(workflow, SOURCE_WRITER));
        assertFalse(describe(workflow), scheduled(workflow, UNRELATED));
        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                COMPONENT, SOURCE_OUTPUT)), outputs(workflow, SELECTED));
    }

    private static JsonObject consumerRow() {
        JsonObject row = plan("node/client#epoch0", CONSUMER,
                "REGION.C", "node/client/relation/REGION.C");
        JsonArray handoffs = new JsonArray();
        handoffs.add(componentHandoff("ATTACH"));
        row.add("communicationHandoffs", handoffs);

        JsonObject goal = goal("GOAL.consumer",
                "OUTPUT_RELATION_CLOSURE", "<Client: void update()>");
        JsonArray actions = new JsonArray();
        actions.add(valueAction(HEAP_INPUT));
        actions.add(carrierAction(RESPONSE));
        goal.add("symbolize", actions);
        JsonArray bindings = one(heapEdge());
        bindings.add(delivery(SELECTED, SELECTED_EDGE));
        goal.add("edgeBindings", bindings);
        JsonArray inputs = new JsonArray();
        inputs.add(HEAP_INPUT);
        inputs.add(RESPONSE);
        inputs.add(COMPONENT);
        JsonArray causalEdges = new JsonArray();
        causalEdges.add(SELECTED_EDGE);
        goal.add("outputClosure", closure("REGION.C",
                "node/client/relation/REGION.C", member(HEAP_OUTPUT,
                        "<Client: int state>", inputs, HEAP_INPUT,
                        "<Client: void update()>", causalEdges)));
        attach(row, goal);
        return row;
    }

    private static JsonObject targetRow() {
        JsonObject row = plan("node/target#epoch0", TARGET,
                "REGION.T", "node/target/relation/REGION.T");
        JsonObject goal = goal("GOAL.target", "TARGET_REACH_CLOSURE",
                "<Target: void fail()>");
        JsonArray actions = new JsonArray();
        actions.add(valueAction(TARGET_INPUT));
        goal.add("symbolize", actions);
        goal.add("edgeBindings", one(heapEdge()));
        attach(row, goal);
        return row;
    }

    private static JsonObject remoteRow(String occurrence, String edgeId) {
        JsonObject row = plan("node/server#epoch0", occurrence,
                "REGION.R", "node/server/relation/REGION.R");
        JsonArray handoffs = new JsonArray();
        handoffs.add(componentHandoff("EXPORT"));
        row.add("communicationHandoffs", handoffs);

        JsonObject goal = goal("GOAL.remote", "OUTPUT_RELATION_CLOSURE",
                "<Server: Response reply()>");
        goal.add("symbolize", new JsonArray());
        goal.add("edgeBindings", one(delivery(occurrence, edgeId)));
        JsonArray inputs = new JsonArray();
        goal.add("outputClosure", closure("REGION.R",
                "node/server/relation/REGION.R", member(COMPONENT,
                        COMPONENT, inputs, "",
                        "<Server: Response reply()>", new JsonArray())));
        attach(row, goal);
        return row;
    }

    private static JsonObject remoteRowWithFrontier(boolean includeStats) {
        JsonObject row = plan("node/server#epoch0", SELECTED,
                "REGION.R", "node/server/relation/REGION.R");
        JsonArray handoffs = new JsonArray();
        handoffs.add(componentHandoff("EXPORT"));
        row.add("communicationHandoffs", handoffs);

        JsonObject goal = goal("GOAL.remote", "OUTPUT_RELATION_CLOSURE",
                "<Server: Response reply()>");
        JsonArray actions = new JsonArray();
        actions.add(valueAction(KEYS_INPUT));
        actions.add(valueAction(GUARD_INPUT));
        if (includeStats) actions.add(valueAction(STATS_INPUT));
        goal.add("symbolize", actions);
        JsonArray bindings = one(delivery(SELECTED, SELECTED_EDGE));
        bindings.add(sharedStateEdge(KEYS_WRITER, "REGION.K",
                KEYS_OUTPUT, KEYS_EDGE, KEYS_INPUT));
        bindings.add(sharedStateEdge(GUARD_WRITER, "REGION.G",
                GUARD_OUTPUT, GUARD_EDGE, GUARD_INPUT));
        if (includeStats) {
            bindings.add(sharedStateEdge(STATS_WRITER, "REGION.S",
                    STATS_OUTPUT, STATS_EDGE, STATS_INPUT));
        }
        goal.add("edgeBindings", bindings);

        JsonArray inputs = new JsonArray();
        inputs.add(KEYS_INPUT);
        inputs.add(GUARD_INPUT);
        JsonArray causalEdges = new JsonArray();
        causalEdges.add(SELECTED_EDGE);
        causalEdges.add(KEYS_EDGE);
        causalEdges.add(GUARD_EDGE);
        if (includeStats) {
            inputs.add(STATS_INPUT);
            causalEdges.add(STATS_EDGE);
        }
        goal.add("outputClosure", closure("REGION.R",
                "node/server/relation/REGION.R", member(COMPONENT,
                        COMPONENT, inputs, "",
                        "<Server: Response reply()>", causalEdges)));
        attach(row, goal);
        return row;
    }

    private static JsonObject remoteRowWithSourceOutput() {
        return remoteRowWithSourceOutput(false);
    }

    private static JsonObject remoteRowWithSourceOutput(
            boolean bindSourcePredecessor) {
        JsonObject row = remoteRow(SELECTED, SELECTED_EDGE);
        JsonObject goal = row.getAsJsonArray("closureGoals").get(0)
                .getAsJsonObject();
        goal.getAsJsonArray("symbolize").add(valueAction(SOURCE_INPUT));
        if (bindSourcePredecessor) {
            goal.getAsJsonArray("edgeBindings").add(sharedStateEdge(
                    SOURCE_WRITER, "REGION.P", SOURCE_ROOT_OUTPUT,
                    SOURCE_EDGE, SOURCE_INPUT));
        }
        JsonObject closure = goal.getAsJsonObject("outputClosure");
        JsonArray inputs = new JsonArray();
        inputs.add(SOURCE_INPUT);
        JsonArray sourceEdges = new JsonArray();
        sourceEdges.add(SOURCE_EDGE);
        closure.getAsJsonArray("members").add(member(SOURCE_OUTPUT,
                SOURCE_CELL, inputs, SOURCE_INPUT,
                "<Server: Response reply()>", sourceEdges));
        return row;
    }

    private static JsonObject stateProducerRow(
            String occurrence, String region, String outputPort,
            String edgeId, String downstreamInput) {
        String method = "<Writer" + region + ": int value()>";
        JsonObject row = plan(occurrence.substring(0,
                occurrence.indexOf("/region/")), occurrence, region,
                occurrence.substring(0, occurrence.indexOf("#epoch0"))
                        + "/relation/" + region);
        JsonObject goal = goal("GOAL." + region,
                "OUTPUT_RELATION_CLOSURE", method);
        String accessRoot = region + ".in.root";
        JsonArray actions = new JsonArray();
        actions.add(carrierAction(accessRoot));
        goal.add("symbolize", actions);
        goal.add("edgeBindings", one(sharedStateEdge(occurrence, region,
                outputPort, edgeId, downstreamInput)));
        JsonArray inputs = new JsonArray();
        inputs.add(accessRoot);
        goal.add("outputClosure", closure(region,
                row.get("relationKey").getAsString(), member(outputPort,
                        "<Writer" + region + ": int state>", inputs,
                        accessRoot, method,
                        new JsonArray())));
        attach(row, goal);
        return row;
    }

    private static JsonObject sharedStateEdge(
            String producer, String producerRegion, String outputPort,
            String edgeId, String downstreamInput) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("fromRegion", producerRegion);
        edge.addProperty("fromOccurrenceId", producer);
        edge.addProperty("fromOutputPort", outputPort);
        edge.addProperty("toRegion", "REGION.R");
        edge.addProperty("toOccurrenceId", SELECTED);
        edge.addProperty("toInputPort", downstreamInput);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty("receiverObjectId", 19);
        edge.addProperty("writerEventSeq", 10);
        edge.addProperty("readerEventSeq", 20);
        edge.addProperty("writerLaneId", "1");
        edge.addProperty("readerLaneId", "2");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject componentHandoff(String role) {
        JsonObject handoff = new JsonObject();
        handoff.addProperty("schemaVersion", 2);
        handoff.addProperty("kind", "COMMUNICATION_HANDOFF_SITE");
        handoff.addProperty("portId", COMPONENT);
        handoff.addProperty("handoffLeafPath", "resp/keyId");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("exchangeSiteKey", EXCHANGE);
        handoff.addProperty("componentOfPortId", RESPONSE);
        handoff.addProperty("encodingAuthority", "TEST_RESPONSE_PATH_V1");
        handoff.addProperty("javaType", "int");
        handoff.addProperty("role", role);
        handoff.addProperty("definitionMethod", role.equals("ATTACH")
                ? "<Client: void update()>" : "<Server: Response reply()>");
        JsonObject step = new JsonObject();
        step.addProperty("kind", "FIELD");
        step.addProperty("declaration", "<Response: int keyId>");
        JsonArray path = new JsonArray();
        path.add(step);
        handoff.add("handoffPath", path);
        return handoff;
    }

    private static JsonObject delivery(String producer, String edgeId) {
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
        edge.addProperty("exchangeSiteKey", EXCHANGE);
        edge.addProperty("handoffLeafPath", "resp/keyId");
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("componentOfPortId", RESPONSE);
        edge.addProperty("fromRegion", "REGION.R");
        edge.addProperty("fromOccurrenceId", producer);
        edge.addProperty("fromOutputPort", COMPONENT);
        edge.addProperty("toRegion", "REGION.C");
        edge.addProperty("toOccurrenceId", CONSUMER);
        edge.addProperty("toInputPort", COMPONENT);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject heapEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("edgeId", HEAP_EDGE);
        edge.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("fromRegion", "REGION.C");
        edge.addProperty("fromOccurrenceId", CONSUMER);
        edge.addProperty("fromOutputPort", HEAP_OUTPUT);
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toOccurrenceId", TARGET);
        edge.addProperty("toInputPort", TARGET_INPUT);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty("receiverObjectId", 17);
        edge.addProperty("writerEventSeq", 10);
        edge.addProperty("readerEventSeq", 20);
        edge.addProperty("writerLaneId", "1");
        edge.addProperty("readerLaneId", "2");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject plan(String source, String occurrence,
                                   String region, String relation) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", source);
        row.addProperty("occurrenceId", occurrence);
        row.addProperty("regionId", region);
        row.addProperty("relationKey", relation);
        return row;
    }

    private static JsonObject goal(String id, String kind, String method) {
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", id);
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

    private static JsonObject valueAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        return action;
    }

    private static JsonObject carrierAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "CONCRETE");
        action.addProperty("dependencyRole", "CONCRETE_STRUCTURE_CARRIER");
        return action;
    }

    private static JsonObject closure(String region, String relation,
                                      JsonObject... selectedMembers) {
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", region);
        producer.addProperty("relationKey", relation);
        if (selectedMembers.length == 1 && COMPONENT.equals(
                selectedMembers[0].getAsJsonObject("output")
                .get("portId").getAsString())) {
            JsonArray ports = new JsonArray();
            ports.add(COMPONENT);
            producer.add("declaredOutputPorts", ports);
        }
        JsonArray members = new JsonArray();
        for (JsonObject member : selectedMembers) members.add(member);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject member(String port, String cell,
                                     JsonArray inputs, String accessRoot,
                                     String method, JsonArray causalEdges) {
        JsonObject output = new JsonObject();
        output.addProperty("portId", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + port);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("javaType", "int");
        if (COMPONENT.equals(port)) {
            capture.addProperty("captureKind", "HANDOFF_BOUND_LEAF");
            capture.addProperty("componentOfPortId", RESPONSE);
            capture.addProperty("encodingAuthority",
                    "TEST_RESPONSE_PATH_V1");
            capture.addProperty("exchangeSiteKey", EXCHANGE);
            capture.addProperty("leafPath", "resp/keyId");
            capture.addProperty("direction", "RESPONSE");
        } else {
            capture.addProperty("captureKind", "REGION_EXIT_FIELD");
            capture.addProperty("fieldSignature", cell);
            JsonArray fieldPath = new JsonArray();
            fieldPath.add("state");
            capture.add("fieldPath", fieldPath);
            capture.addProperty("accessRootInputPort", accessRoot);
        }

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", inputs);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(method);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", causalEdges);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        return member;
    }

    private static JsonArray one(JsonObject value) {
        JsonArray array = new JsonArray();
        array.add(value.deepCopy());
        return array;
    }

    private static void attach(JsonObject row, JsonObject goal) {
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
    }

    private static boolean scheduled(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            String occurrence) {
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            if (occurrence.equals(group.occurrenceId)) return true;
        }
        return false;
    }

    private static java.util.Set<String> edges(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            String occurrence) throws Exception {
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            if (occurrence.equals(group.occurrenceId)) {
                return group.edgeIds();
            }
        }
        return java.util.Collections.emptySet();
    }

    private static java.util.Set<String> outputs(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow,
            String occurrence) throws Exception {
        java.util.Set<String> outputs = new java.util.LinkedHashSet<>();
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            if (occurrence.equals(group.occurrenceId)) {
                outputs.addAll(group.outputPorts());
            }
        }
        return outputs;
    }

    private static String describe(
            RuntimeWorkflowDiscovery.RankedWorkflow workflow) {
        StringBuilder result = new StringBuilder();
        for (RuntimeWorkflowDiscovery.ProducerGroup group
                : workflow.producerGroups()) {
            result.append(group.occurrenceId).append(' ');
        }
        return result.toString();
    }
}
