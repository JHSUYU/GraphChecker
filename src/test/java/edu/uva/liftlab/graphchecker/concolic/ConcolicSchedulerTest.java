package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
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
    public void captureOnlySchedulesOutputClosureWithoutBranchTarget()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath());
            JsonObject activation = singletonOutputActivation();
            Files.write(fixture.activations,
                    (activation + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.scheduledPrimaryCount);
            JsonObject scheduled = result.scheduledActivations.get(0);
            assertEquals("CAPTURE_OUTPUT_PATH", scheduled
                    .get("executionPhase").getAsString());
            assertEquals("OUTPUT_CLOSURE", scheduled
                    .getAsJsonObject("captureGoal").get("kind")
                    .getAsString());
            assertEquals(0, result.queries.size());
            assertEquals(1, result.summary.get("upstreamCaptureJobCount")
                    .getAsInt());
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
            observedMapPrestate.add("symbolize", mapInputs);
            Files.write(fixture.activations,
                    (observedMapPrestate + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result mapState =
                    ConcolicScheduler.schedule(arguments);
            JsonObject mapBinding = mapState.scheduledActivations.get(0)
                    .getAsJsonArray("materializations").get(0)
                    .getAsJsonObject();
            assertEquals("MAP_STATE_INPUT_OBSERVATION",
                    mapBinding.get("bindingMode").getAsString());
            assertTrue(mapBinding.get("mapStateObservationOnly")
                    .getAsBoolean());
            assertFalse(mapBinding.get("modelControllable")
                    .getAsBoolean());
            assertEquals(ALL_KEYS,
                    mapBinding.get("mapStateRequestedOutputCell")
                            .getAsString());

            JsonObject incompleteSlice = activation.deepCopy();
            incompleteSlice.getAsJsonObject(OutputClosureContract.FIELD)
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .addProperty("complete", false);
            Files.write(fixture.activations,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result blocked =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(blocked.scheduledActivations.get(0)
                    .get("schedulerReady")
                    .getAsBoolean());

            incompleteSlice.remove(OutputClosureContract.FIELD);
            Files.write(fixture.activations,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result missingNestedSlice =
                    ConcolicScheduler.schedule(arguments);
            assertEquals(0, missingNestedSlice.scheduledPrimaryCount);
            assertFalse(blocked.scheduledActivations.get(0)
                    .get("schedulerReady").getAsBoolean());

            JsonObject deferred = activation.deepCopy();
            JsonObject environment = new JsonObject();
            environment.addProperty("symbol", "REGION.11.in.env");
            environment.addProperty("cell",
                    "<example.Clock: long now()>.return");
            environment.addProperty("location", "ENVIRONMENT_MODEL");
            JsonArray environmentInputs = new JsonArray();
            environmentInputs.add(environment);
            deferred.add("symbolize", environmentInputs);
            deferred.getAsJsonObject(OutputClosureContract.FIELD)
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice").add("inputPorts",
                    strings("REGION.11.in.env"));
            Files.write(fixture.activations,
                    (deferred + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result deferredClosure =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(deferredClosure.scheduledActivations.get(0)
                    .get("schedulerReady")
                    .getAsBoolean());
            assertEquals(1, deferredClosure.scheduledActivations.get(0)
                    .getAsJsonArray("concreteFallbacks").size());
        } finally {
            folder.delete();
        }
    }
















    @Test
    public void explicitJointOutputClosureCompilesOnlyMemberUnion() {
        JsonObject activation = explicitJointActivation();

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation, Collections.<JsonObject>emptyList());

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertTrue(prepared.get("outputCaptureReady").getAsBoolean());
        assertTrue(prepared.has(OutputClosureContract.FIELD));
        assertFalse(prepared.has("requestedOutput"));
        assertFalse(prepared.has("requestedOutputSlice"));
        assertFalse(prepared.has("requestedOutputCapture"));
        assertFalse(prepared.has("outputs"));
        assertEquals(2, prepared.getAsJsonArray("symbolize").size());
        assertEquals("REGION.1.in.x", prepared.getAsJsonArray("symbolize")
                .get(0).getAsJsonObject().get("symbol").getAsString());
        assertEquals("REGION.1.in.y", prepared.getAsJsonArray("symbolize")
                .get(1).getAsJsonObject().get("symbol").getAsString());
        assertEquals(2, prepared.getAsJsonArray("branches").size());
        assertEquals(2, prepared.getAsJsonArray("materializations").size());
    }

    @Test
    public void explicitEmptyExecutionUnionNeverFallsBackToWholeRegion() {
        JsonObject activation = explicitJointActivation();
        JsonObject envelope = activation.getAsJsonObject(
                OutputClosureContract.FIELD);
        for (JsonElement element : envelope.getAsJsonArray("members")) {
            JsonObject slice = element.getAsJsonObject()
                    .getAsJsonObject("slice");
            slice.add("inputPorts", new JsonArray());
            slice.add("sites", new JsonArray());
            slice.add("staticSites", new JsonArray());
            slice.add("methods", new JsonArray());
            slice.add("causalEdgeIds", new JsonArray());
        }

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation, Collections.<JsonObject>emptyList());

        assertTrue(prepared.get("schedulerReady").getAsBoolean());
        assertEquals(0, prepared.getAsJsonArray("symbolize").size());
        assertEquals(0, prepared.getAsJsonArray("branches").size());
        assertEquals(0, prepared.getAsJsonArray("materializations").size());
    }

    @Test
    public void oneIncompleteJointMemberClosesWholeActivation() {
        JsonObject activation = explicitJointActivation();
        activation.getAsJsonObject(OutputClosureContract.FIELD)
                .getAsJsonArray("members").get(1).getAsJsonObject()
                .getAsJsonObject("slice").addProperty("complete", false);

        JsonObject prepared = ConcolicScheduler.prepareOutputCapture(
                activation, Collections.<JsonObject>emptyList());

        assertFalse(prepared.get("outputCaptureReady").getAsBoolean());
        assertFalse(prepared.get("schedulerReady").getAsBoolean());
        assertEquals(2, prepared.getAsJsonObject(
                OutputClosureContract.FIELD).getAsJsonArray("members")
                .size());
    }



    @Test
    public void scheduledExplicitJointClosureNeverPersistsLegacyMirrors()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath());
            Files.write(fixture.activations,
                    (explicitJointActivation() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments arguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan", fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--region-id", "REGION.1",
                            "--capture-only"});

            ConcolicScheduler.Result result =
                    ConcolicScheduler.schedule(arguments);

            assertEquals(1, result.scheduledPrimaryCount);
            JsonObject scheduled = result.scheduledActivations.get(0);
            assertTrue(scheduled.has(OutputClosureContract.FIELD));
            assertFalse(scheduled.has("requestedOutput"));
            assertEquals(2, OutputClosureCodec.decode(scheduled)
                    .members().size());
            assertFalse(scheduled.has("requestedOutputSlice"));
            assertFalse(scheduled.has("requestedOutputCapture"));
            assertFalse(scheduled.has("outputs"));
            assertEquals(2, scheduled.getAsJsonArray("symbolize").size());
            assertEquals(2, scheduled.getAsJsonArray("branches").size());
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
        activation.addProperty("activationId", "ACT.JOINT");
        activation.addProperty("regionId", "REGION.1");
        activation.addProperty("regionInstanceId",
                "REGION.1@test#call7");
        activation.addProperty("rootCallId", 7);
        activation.addProperty("test", "jointOutput");
        activation.addProperty("rootMethod",
                "<example.Producer: void produce(int,int)>");
        activation.addProperty("replayable", true);
        activation.add("runtimeDefinitionMethods", new JsonArray());
        RegionCaptureGoal.outputClosure().writeTo(activation);
        JsonArray symbolize = new JsonArray();
        symbolize.add(argumentAction("REGION.1.in.x", "int x"));
        symbolize.add(argumentAction("REGION.1.in.debug",
                "int debug"));
        symbolize.add(argumentAction("REGION.1.in.y", "int y"));
        activation.add("symbolize", symbolize);
        JsonArray branches = new JsonArray();
        branches.add(branch("B.x"));
        branches.add(branch("B.debug"));
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
        String method = "<example.Producer: void produce(int,int)>";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId", port + ".capture");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("method", method);
        capture.addProperty("siteId", method + "#u" + unitIndex);
        capture.addProperty("unitIndex", unitIndex);
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("occurrence", 1);
        capture.addProperty("occurrenceAuthority",
                "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                        + "LAST_WRITE_OCCURRENCE");
        capture.addProperty("runtimeEventSeq", 10 + unitIndex);
        capture.addProperty("runtimeCallId", 7);
        capture.addProperty("runtimeFieldOwnerObjectId", 99);
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.addProperty("complete", true);
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        slice.add("inputPorts", inputs);
        JsonArray sites = new JsonArray();
        sites.add(branch);
        slice.add("sites", sites);
        slice.add("staticSites", sites.deepCopy());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", captures.deepCopy());
        OutputClosureCodec.writeTo(activation, OutputClosureCodec.singleton(
                "REGION.1", "REGION.1@test#call7", 7,
                port, cell, "REGION_OUTPUT", "TEST_EXACT_OUTPUT", slice));
        return activation;
    }

    private static JsonObject singletonOutputActivation() {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.PRODUCER.0");
        activation.addProperty("regionId", "REGION.11");
        activation.addProperty("regionInstanceId",
                "REGION.11@test#call7");
        activation.addProperty("rootCallId", 7);
        activation.addProperty("test", "testMiniDfs");
        activation.addProperty("rootMethod",
                "<example.Updater: void run()>");
        activation.add("runtimeDefinitionMethods", strings(
                "<example.Updater: void run()>"));
        activation.addProperty("invocationOrdinal", 1);
        activation.addProperty("replayable", true);
        activation.addProperty("symbolicReady", true);
        RegionCaptureGoal.outputClosure().writeTo(activation);
        activation.add("edgeBindings", new JsonArray());
        activation.add("symbolize", new JsonArray());
        activation.add("branches", new JsonArray());

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.11.out.0");
        slice.addProperty("outputCell", ALL_KEYS);
        slice.addProperty("complete", true);
        slice.addProperty("captureBindingsRequired", false);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("inputPorts", strings("REGION.11.in.map"));
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings("<example.Updater: void run()>"));
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        OutputClosureCodec.writeTo(activation, OutputClosureCodec.singleton(
                "REGION.11", "REGION.11@test#call7", 7,
                "REGION.11.out.0", ALL_KEYS, "HEAP_STATE",
                "TEST_EXACT_OUTPUT", slice));
        return activation;
    }

    private static JsonObject argumentAction(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("location", "ARGUMENT");
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

    private static Fixture fixture(Path root)
            throws Exception {
        Fixture result = new Fixture(root);
        String regions = "{\"schemaVersion\":1,"
                + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                + ROOT + "\",\"symbolicInputs\":["
                + "{\"portId\":\"REGION.0.in.0\",\"cell\":\""
                + USERNAME + "\"},"
                + "{\"portId\":\"REGION.0.in.1\",\"cell\":\""
                + ALL_KEYS + "\"},"
                + "{\"portId\":\"REGION.0.in.2\",\"cell\":\""
                + CURRENT_KEY_ID + "\"}],\"outputs\":[]}\n"
                + "{\"schemaVersion\":1,"
                + "\"regionId\":\"REGION.1\",\"rootMethod\":"
                + "\"<example.Client: void send()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.1.out.0\","
                + "\"cell\":\"client.userName\"}]}\n"
                + "{\"schemaVersion\":1,"
                + "\"regionId\":\"REGION.11\",\"rootMethod\":"
                + "\"<example.Updater: void run()>\",\"symbolicInputs\":[],"
                + "\"outputs\":[{\"portId\":\"REGION.11.out.0\","
                + "\"cell\":\"" + ALL_KEYS + "\"}]}\n";
        Files.write(result.regions, regions.getBytes(StandardCharsets.UTF_8));

        String activation = "{\"activationId\":\"ACT.0\","
                + "\"regionId\":\"REGION.0\","
                + "\"regionInstanceId\":\"REGION.0@testMiniDfs#call7\","
                + "\"rootCallId\":7,\"test\":\"testMiniDfs\","
                + "\"rootMethod\":\"" + ROOT + "\","
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
                + "\"invocationOrdinal\":1,\"replayable\":true,"
                + "\"captureGoal\":{\"kind\":\"TARGET_BRANCH\","
                + "\"scope\":\"ONE_DIRECTED_BRANCH\"},"
                + "\"symbolicReady\":false,\"symbolize\":["
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
                + "\"matchesRequiredOutcome\":false}]}]}\n";
        Files.write(result.activations,
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
                + "\"discoveredExecutionId\":\"EXEC.fixture\","
                + "\"valueEqualityObserved\":true,"
                + "\"valueEqualityAuthority\":"
                + "\"RUNTIME_COMPLETE_VALUE_FINGERPRINT\","
                + "\"valueFingerprint\":\"sha256:fixture\","
                + "\"endpointOrderAuthority\":"
                + "\"GLOBAL_TRACE_ENDPOINT_SEQUENCE\","
                + "\"fromEndpointSeq\":10,\"toEndpointSeq\":20,"
                + "\"orderConfirmed\":true}]}\n"
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
                + "\"writeEvidenceKind\":\"FIELD_ASSIGNMENT\","
                + "\"writeEvidenceAuthority\":"
                + "\"RUNTIME_EXACT_FIELD_WRITE_EVENT_V1\","
                + "\"orderAuthority\":"
                + "\"GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1\","
                + "\"writeSeq\":1,\"readSeq\":2,"
                + "\"receiverObjectId\":7,"
                + "\"fieldReceiverIdentityConfirmed\":true,"
                + "\"orderConfirmed\":true}]}\n";
        Files.write(result.edges, edges.getBytes(StandardCharsets.UTF_8));

        String staticGraph = "{\"schemaVersion\":1,"
                + "\"id\":\"DF.DEF\",\"toCell\":\""
                + USERNAME + "\",\"method\":\"" + CALLBACK
                + "\",\"unitIndex\":36,\"unit\":\"$r4 = "
                + "virtualinvoke r12.<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>()\"}\n"
                + "{\"schemaVersion\":1,"
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
        private final Path activations;
        private final Path edges;
        private final Path staticGraph;
        private final Path output;

        private Fixture(Path root) {
            this.regions = root.resolve("regions.jsonl");
            this.activations = root.resolve("activations.jsonl");
            this.edges = root.resolve("edges.jsonl");
            this.staticGraph = root.resolve("static.jsonl");
            this.output = root.resolve("schedule");
        }
    }
}
