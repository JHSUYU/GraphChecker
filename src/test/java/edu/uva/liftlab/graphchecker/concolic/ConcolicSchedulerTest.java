package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSchedulerTest {
    private static final String ROOT = "<example.Server: void receive()>";
    private static final String CALLBACK = "<example.Callback: void handle()>";
    private static final String TARGET = "<example.Manager: byte[] lookup(int)>#u8";
    private static final String USERNAME = CALLBACK + "::$r4";
    private static final String ALL_KEYS =
            "<example.Manager: java.util.Map allKeys>";
    private static final String CURRENT_KEY_ID =
            "<example.Manager: example.BlockKey currentKey>#field:keyId";

    @Test
    public void containerTraversalReferenceReturnIsConcreteStructure() {
        assertTrue(ConcolicScheduler.structuralContainerReferenceReturn(
                callReturn("<java.util.Iterator: java.lang.Object next()>"
                        + ".return", "java.lang.Object")));
        assertTrue(ConcolicScheduler.structuralContainerReferenceReturn(
                callReturn("<java.util.Map: java.lang.Object "
                        + "get(java.lang.Object)>.return",
                        "java.lang.Object")));
        assertFalse(ConcolicScheduler.structuralContainerReferenceReturn(
                callReturn("<java.util.Iterator: boolean hasNext()>.return",
                        "boolean")));
        assertFalse(ConcolicScheduler.structuralContainerReferenceReturn(
                callReturn("<example.Service: java.lang.Object load()>"
                        + ".return", "java.lang.Object")));
    }









    @Test
    public void captureOnlySchedulesOutputClosureWithoutBranchTarget()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath());
            JsonObject activation = singletonOutputActivation();
            Files.write(fixture.regionPlan,
                    (activation + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--region-plan", fixture.regionPlan.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-instance-id",
                            "REGION.11@test#call7"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.executionTasks.size());
            JsonObject scheduled = result.executionTasks.get(0);
            assertFalse(scheduled.has("activationId"));
            assertEquals("REGION.11@test#call7",
                    scheduled.get("regionInstanceId").getAsString());
            assertEquals("GOAL.OUTPUT.MAP",
                    scheduled.get("goalId").getAsString());
            assertTrue(scheduled.get("taskId").getAsString().startsWith(
                    "TASK.SEED."));
            assertFalse(scheduled.has("scheduleId"));
            assertFalse(scheduled.has("bundle"));
            assertEquals(1, scheduled.getAsJsonObject("admission").size());
            assertFalse(scheduled.has("executionPhase"));
            assertEquals("OUTPUT_RELATION_CLOSURE",
                    scheduled.get("goalKind").getAsString());
            assertFalse(scheduled.has("runtimeDefinitionMethods"));
            assertEquals(0, result.queries.size());
            assertTrue(Files.isRegularFile(fixture.output.resolve(
                    "execution_task_plan.jsonl")));
            assertFalse(Files.exists(fixture.output.resolve(
                    "scheduled_activation_plan.jsonl")));
            assertTrue(scheduled.has(OutputClosureContract.FIELD));
            assertFalse(scheduled.has("requestedOutput"));

            JsonObject observedMapPrestate = activation.deepCopy();
            JsonObject mapInput = new JsonObject();
            mapInput.addProperty("symbol", "REGION.11.in.map");
            mapInput.addProperty("cell", ALL_KEYS);
            mapInput.addProperty("field", ALL_KEYS);
            mapInput.addProperty("sourceKind", "SHARED_HEAP");
            mapInput.addProperty("location", "HEAP_OBJECT_FIELD");
            mapInput.addProperty("javaType", "java.util.Map");
            mapInput.addProperty("observed", true);
            JsonArray mapInputs = new JsonArray();
            mapInputs.add(mapInput);
            onlyGoal(observedMapPrestate).add("symbolize", mapInputs);
            Files.write(fixture.regionPlan,
                    (observedMapPrestate + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result mapState =
                    ConcolicScheduler.schedule(arguments);
            JsonObject mapBinding = mapState.executionTasks.get(0)
                    .getAsJsonArray("inputActions").get(0)
                    .getAsJsonObject();
            assertEquals("FIELD_ACCESS",
                    mapBinding.get("bindingMode").getAsString());
            assertFalse(mapBinding.has("mapStateObservationOnly"));
            assertFalse(mapBinding.has("modelControllable"));
            assertFalse(mapBinding.has("mapStateRequestedOutputCell"));

            JsonObject incompleteSlice = activation.deepCopy();
            onlyGoal(incompleteSlice).getAsJsonObject(
                    OutputClosureContract.FIELD)
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .addProperty("complete", false);
            addAdmission(onlyGoal(incompleteSlice), "DISCOVERED",
                    "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
            Files.write(fixture.regionPlan,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result blocked =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(blocked.executionTasks.isEmpty());

            onlyGoal(incompleteSlice).remove(OutputClosureContract.FIELD);
            Files.write(fixture.regionPlan,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result missingNestedSlice =
                    ConcolicScheduler.schedule(arguments);
            assertEquals(0, missingNestedSlice.executionTasks.size());

            JsonObject deferred = activation.deepCopy();
            JsonObject environment = new JsonObject();
            environment.addProperty("symbol", "REGION.11.in.env");
            environment.addProperty("cell",
                    "<example.Clock: long now()>.return");
            environment.addProperty("location", "ENVIRONMENT_MODEL");
            JsonArray environmentInputs = new JsonArray();
            environmentInputs.add(environment);
            onlyGoal(deferred).add("symbolize", environmentInputs);
            onlyGoal(deferred).getAsJsonObject(OutputClosureContract.FIELD)
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice").add("inputPorts",
                    strings("REGION.11.in.env"));
            Files.write(fixture.regionPlan,
                    (deferred + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result deferredClosure =
                    ConcolicScheduler.schedule(arguments);
            assertEquals("EXECUTABLE", admissionState(
                    deferredClosure.executionTasks.get(0)));
            JsonObject fallback = deferredClosure.executionTasks.get(0)
                    .getAsJsonArray("inputActions").get(0)
                    .getAsJsonObject();
            assertEquals("CONCRETE",
                    fallback.get("mode").getAsString());
            assertTrue(fallback.has("symbol"));
        } finally {
            folder.delete();
        }
    }
















    @Test
    public void scheduledExplicitJointClosureNeverPersistsLegacyMirrors()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath());
            Files.write(fixture.regionPlan,
                    (asEnvelope(explicitJointActivation()) + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--region-plan", fixture.regionPlan.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.1"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.executionTasks.size());
            JsonObject scheduled = result.executionTasks.get(0);
            assertTrue(scheduled.has(OutputClosureContract.FIELD));
            assertFalse(scheduled.has("runtimeDefinitionMethods"));
            assertFalse(scheduled.has("requestedOutput"));
            assertEquals(2, OutputClosureCodec.decode(scheduled)
                    .members().size());
            assertFalse(scheduled.has("requestedOutputSlice"));
            assertFalse(scheduled.has("requestedOutputCapture"));
            assertFalse(scheduled.has("outputs"));
            assertEquals(2, scheduled.getAsJsonArray("inputActions").size());
            assertEquals(2, scheduled.getAsJsonArray("branches").size());

        } finally {
            folder.delete();
        }
    }

    @Test
    public void canonicalTargetSummaryNeedsNoRetiredExecutionKind()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath());
            Path summaries = folder.getRoot().toPath().resolve(
                    "summaries.jsonl");
            JsonObject summary = new JsonObject();
            summary.addProperty("goalId", "GOAL.TARGET.0");
            summary.addProperty("regionId", "REGION.0");
            summary.addProperty("regionInstanceId",
                    "REGION.0@testMiniDfs#call7");
            ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(summary);
            summary.addProperty("relationallyComplete", true);
            summary.addProperty("summaryId", "SUMMARY.CANONICAL");
            Files.write(summaries, (summary + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--region-plan",
                            fixture.regionPlan.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--summaries", summaries.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--max-jobs", "1"}));

            assertEquals(1, result.executionTasks.size());
            assertEquals(1, result.queries.size());
            JsonObject query = result.queries.get(0);
            assertFalse(query.has("activationId"));
            assertEquals("REGION.0@testMiniDfs#call7",
                    query.get("regionInstanceId").getAsString());
            assertEquals("GOAL.TARGET.0",
                    query.get("goalId").getAsString());
            assertFalse(summary.has("executionKind"));
        } finally {
            folder.delete();
        }
    }

    private static JsonObject explicitJointActivation() {
        OutputClosureContract x = OutputClosureCodec.decode(
                completeCanonicalMember("REGION.1.out.x",
                        "<example.Producer: int x>",
                        "REGION.1.in.x", "B.x", 2));
        OutputClosureContract y = OutputClosureCodec.decode(
                completeCanonicalMember("REGION.1.out.y",
                        "<example.Producer: int y>",
                        "REGION.1.in.y", "B.y", 3));
        OutputClosureContract joint = OutputClosureCodec.merge(
                Arrays.asList(y, x));

        JsonObject activation = new JsonObject();
        activation.addProperty("regionId", "REGION.1");
        activation.addProperty("regionInstanceId",
                "REGION.1@test#call7");
        activation.addProperty("rootCallId", 7);
        activation.addProperty("test", "jointOutput");
        activation.addProperty("rootMethod",
                "<example.Producer: void produce(int,int)>");
        activation.addProperty("goalId", "GOAL.OUTPUT.JOINT");
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(activation);
        addAdmission(activation, "READY",
                "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        activation.add("runtimeDefinitionMethods", new JsonArray());
        JsonArray symbolize = new JsonArray();
        symbolize.add(fieldPrestateAction("REGION.1.in.x",
                "<example.Producer: int x>"));
        symbolize.add(fieldPrestateAction("REGION.1.in.y",
                "<example.Producer: int y>"));
        activation.add("symbolize", symbolize);
        JsonArray branches = new JsonArray();
        branches.add(branch("B.x"));
        branches.add(branch("B.y"));
        activation.add("branches", branches);
        OutputClosureCodec.writeTo(activation, joint);
        return activation;
    }

    private static JsonObject completeCanonicalMember(
            String port, String cell, String input, String branch,
            int unitIndex) {
        JsonObject activation = new JsonObject();
        activation.addProperty("regionId", "REGION.1");
        activation.addProperty("regionInstanceId",
                "REGION.1@test#call7");
        activation.addProperty("rootCallId", 7);
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", port + ".capture");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("accessRootInputPort", input);
        capture.add("fieldPath", strings(
                cell.contains(" x>") ? "x" : "y"));
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("javaType", "int");
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.addProperty("complete", true);
        slice.add("captureBindingIssues", new JsonArray());
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        slice.add("inputPorts", inputs);
        JsonArray sites = new JsonArray();
        sites.add(branch);
        slice.add("sites", sites);
        slice.add("staticSites", sites.deepCopy());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        slice.add("captureBindings", captures.deepCopy());
        OutputClosureCodec.writeTo(activation, OutputClosureCodec.singleton(
                "REGION.1", "REGION.1@test#call7", 7,
                port, cell, "REGION_OUTPUT", "I", slice));
        return activation;
    }

    private static JsonObject singletonOutputActivation() {
        JsonObject envelope = new JsonObject();
        envelope.addProperty("regionId", "REGION.11");
        envelope.addProperty("regionInstanceId",
                "REGION.11@test#call7");
        envelope.addProperty("rootCallId", 7);
        envelope.addProperty("test", "testMiniDfs");
        envelope.addProperty("rootMethod",
                "<example.Updater: void run()>");
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.OUTPUT.MAP");
        goal.addProperty("kind", "OUTPUT_RELATION_CLOSURE");
        goal.add("runtimeDefinitionMethods", strings(
                "<example.Updater: void run()>"));
        envelope.addProperty("invocationOrdinal", 1);
        addAdmission(goal, "READY",
                "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        goal.add("edgeBindings", new JsonArray());
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.11.out.0");
        slice.addProperty("outputCell", ALL_KEYS);
        slice.addProperty("complete", true);
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("inputPorts", strings("REGION.11.in.map"));
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings("<example.Updater: void run()>"));
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("causalEdges", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        OutputClosureCodec.writeTo(goal, OutputClosureCodec.singleton(
                "REGION.11", "REGION.11@test#call7", 7,
                "REGION.11.out.0", ALL_KEYS, "HEAP_STATE",
                "Ljava/util/Map;", slice));
        JsonArray goals = new JsonArray();
        goals.add(goal);
        envelope.add("closureGoals", goals);
        return envelope;
    }

    private static JsonObject asEnvelope(JsonObject task) {
        JsonObject envelope = task.deepCopy();
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", string(task, "goalId"));
        goal.addProperty("kind", string(task, "goalKind"));
        for (String field : new String[]{
                "runtimeDefinitionMethods", "admission", "symbolize",
                "branches", "edgeBindings", OutputClosureContract.FIELD}) {
            if (task.has(field)) {
                goal.add(field, task.get(field).deepCopy());
                envelope.remove(field);
            }
        }
        envelope.remove("goalId");
        envelope.remove("goalKind");
        JsonArray goals = new JsonArray();
        goals.add(goal);
        envelope.add("closureGoals", goals);
        return envelope;
    }

    private static JsonObject onlyGoal(JsonObject envelope) {
        return envelope.getAsJsonArray("closureGoals")
                .get(0).getAsJsonObject();
    }

    private static String string(JsonObject object, String field) {
        return object.get(field).getAsString();
    }

    private static JsonObject argumentAction(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("location", "ARGUMENT");
        return action;
    }

    private static JsonObject callReturn(String cell, String javaType) {
        JsonObject action = new JsonObject();
        action.addProperty("cell", cell);
        action.addProperty("sourceKind", "OPAQUE_CALL");
        action.addProperty("location", "CALL_RETURN");
        action.addProperty("javaType", javaType);
        return action;
    }

    private static JsonObject fieldPrestateAction(
            String symbol, String field) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", field);
        action.addProperty("sourceKind", "HEAP_PRESTATE");
        action.addProperty("location", "RECEIVER_FIELD");
        action.addProperty("leafFieldSignature", field);
        action.add("fieldPath", strings("state",
                field.contains(" x>") ? "x" : "y"));
        return action;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static JsonObject branch(String siteId) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", siteId);
        return branch;
    }

    private static void addAdmission(JsonObject activation, String state,
                                     String mode) {
        JsonObject admission = new JsonObject();
        admission.addProperty("state", state);
        admission.addProperty("mode", mode);
        admission.add("blockers", new JsonArray());
        activation.add("admission", admission);
    }

    private static String admissionState(JsonObject activation) {
        return activation.getAsJsonObject("admission")
                .get("state").getAsString();
    }

    private static Fixture fixture(Path root)
            throws Exception {
        Fixture result = new Fixture(root);
        String regions = "{\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                + ROOT + "\",\"symbolicInputs\":["
                + "{\"portId\":\"REGION.0.in.0\",\"cell\":\""
                + USERNAME + "\"},"
                + "{\"portId\":\"REGION.0.in.1\",\"cell\":\""
                + ALL_KEYS + "\"},"
                + "{\"portId\":\"REGION.0.in.2\",\"cell\":\""
                + CURRENT_KEY_ID + "\"}],\"outputs\":[]}\n"
                + "{\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.1\",\"rootMethod\":"
                + "\"<example.Client: void send()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.1.out.0\","
                + "\"cell\":\"client.userName\"}]}\n"
                + "{\"schemaVersion\":2,"
                + "\"regionId\":\"REGION.11\",\"rootMethod\":"
                + "\"<example.Updater: void run()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.11.out.0\","
                + "\"cell\":\"" + ALL_KEYS + "\"}]}\n";
        Files.write(result.regions, regions.getBytes(StandardCharsets.UTF_8));

        String activation = "{\"regionId\":\"REGION.0\","
                + "\"regionInstanceId\":\"REGION.0@testMiniDfs#call7\","
                + "\"rootCallId\":7,\"test\":\"testMiniDfs\","
                + "\"rootMethod\":\"" + ROOT + "\","
                + "\"closureGoals\":[{"
                + "\"goalId\":\"GOAL.TARGET.0\","
                + "\"kind\":\"TARGET_REACH_CLOSURE\","
                + "\"runtimeDefinitionMethods\":[\"" + ROOT + "\","
                + "\"" + CALLBACK + "\","
                + "\"<example.Manager: byte[] lookup(int)>\"],"
                + "\"receiverType\":\"example.Server\","
                + "\"receiverRuntimeClass\":\"example.Server\","
                + "\"threadName\":\"rpc-handler\","
                + "\"threadIdSelectionUsed\":false,"
                + "\"invocationOrdinalWithinContext\":1,"
                + "\"rootContextSelectionAuthority\":"
                + "\"TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                + "THREAD_NAME_CONTEXT_ORDINAL_V1\","
                + "\"invocationOrdinal\":1,\"admission\":{"
                + "\"state\":\"DISCOVERED\","
                + "\"mode\":\"RUNTIME_SELECTED_ROOT_REPLAY\","
                + "\"blockers\":[{\"kind\":"
                + "\"SYMBOLIC_BOUNDARY_NOT_READY\"}]},"
                + "\"symbolize\":["
                + "{\"symbol\":\"REGION.0.in.0\",\"cell\":\""
                + USERNAME + "\",\"location\":\"REGION_LIVE_IN\"},"
                + "{\"symbol\":\"REGION.0.in.1\",\"cell\":\""
                + ALL_KEYS + "\",\"location\":\"HEAP_OBJECT_FIELD\"},"
                + "{\"symbol\":\"REGION.0.in.2\",\"cell\":\""
                + CURRENT_KEY_ID
                + "\",\"location\":\"HEAP_OBJECT_FIELD\"}],"
                + "\"branches\":[{\"siteId\":\"" + TARGET + "\","
                + "\"policy\":\"PATH_ASSUMPTION\",\"observed\":true,"
                + "\"observedOutcome\":true,\"requiredOutcome\":false,"
                + "\"matchesRequiredOutcome\":false,"
                + "\"selectedOccurrence\":1,\"occurrences\":["
                + "{\"occurrence\":1,\"seq\":8,\"outcome\":true,"
                + "\"matchesRequiredOutcome\":false}]}]}]}\n";
        Files.write(result.regionPlan,
                activation.getBytes(StandardCharsets.UTF_8));

        String edges = "{\"schemaVersion\":2,"
                + "\"kind\":\"RUNTIME_REGION_EDGE_EVIDENCE\","
                + "\"edgeId\":\"E.SASL\","
                + "\"fromRegion\":\"REGION.1\","
                + "\"toRegion\":\"REGION.0\","
                + "\"fromPort\":\"client.userName\","
                + "\"toPort\":\"" + USERNAME + "\","
                + "\"transportKind\":\"SASL_TRANSFER\","
                + "\"state\":\"CONFIRMED_RUNTIME_VALUE_EQUALITY\","
                + "\"bindings\":[{"
                + "\"fromRegionInstance\":\"REGION.1@test#call1\","
                + "\"toRegionInstance\":"
                + "\"REGION.0@testMiniDfs#call7\","
                + "\"evidenceKind\":\"COMPLETE_VALUE_EQUALITY_V1\","
                + "\"valueFingerprint\":\"sha256:fixture\","
                + "\"writerEventSeq\":10,\"readerEventSeq\":20}]}\n"
                + "{\"schemaVersion\":2,"
                + "\"kind\":\"RUNTIME_REGION_EDGE_EVIDENCE\","
                + "\"edgeId\":\"E.STATE\","
                + "\"fromRegion\":\"REGION.11\","
                + "\"toRegion\":\"REGION.0\","
                + "\"fromPort\":\"" + ALL_KEYS + "\","
                + "\"toPort\":\"" + ALL_KEYS + "\","
                + "\"transportKind\":\"SHARED_STATE\","
                + "\"requiresOrder\":true,"
                + "\"requiresObjectIdentity\":true,"
                + "\"state\":\"CONFIRMED_READ_FROM\","
                + "\"bindings\":[{"
                + "\"evidenceKind\":\"FIELD_ASSIGNMENT_READ_FROM_V1\","
                + "\"writerEventSeq\":1,\"readerEventSeq\":2,"
                + "\"receiverObjectId\":7}]}\n";
        Files.write(result.edges, edges.getBytes(StandardCharsets.UTF_8));

        String staticGraph = "{\"schemaVersion\":2,"
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"id\":\"DF.DEF\",\"toCell\":\""
                + USERNAME + "\",\"method\":\"" + CALLBACK
                + "\",\"unitIndex\":36,\"unit\":\"$r4 = "
                + "virtualinvoke r12.<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>()\"}\n"
                + "{\"schemaVersion\":2,"
                + "\"semanticMode\":\"ASSERTABLE\","
                + "\"id\":\"DF.MAP\",\"kind\":\"map_lookup_state\","
                + "\"method\":\""
                + "<example.Manager: byte[] lookup(int)>\","
                + "\"unitIndex\":6,\"siteId\":\""
                + "<example.Manager: byte[] lookup(int)>#u6\","
                + "\"invoke\":\"<java.util.Map: java.lang.Object "
                + "get(java.lang.Object)>\",\"unit\":\"$r3 = "
                + "interfaceinvoke $r1.<java.util.Map: java.lang.Object "
                + "get(java.lang.Object)>($r2)\"}\n";
        Files.write(result.staticGraph,
                staticGraph.getBytes(StandardCharsets.UTF_8));

        return result;
    }

    private static final class Fixture {
        private final Path regions;
        private final Path regionPlan;
        private final Path edges;
        private final Path staticGraph;
        private final Path output;

        private Fixture(Path root) {
            this.regions = root.resolve("regions.jsonl");
            this.regionPlan = root.resolve("region_plan.jsonl");
            this.edges = root.resolve("edges.jsonl");
            this.staticGraph = root.resolve("static.jsonl");
            this.output = root.resolve("schedule");
        }
    }
}
