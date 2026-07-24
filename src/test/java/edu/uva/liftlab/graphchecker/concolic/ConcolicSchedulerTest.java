package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String activation = "{\"activationId\":\"ACT.PRODUCER.0\","
                    + "\"regionInstanceId\":\"REGION.11@test#call7\","
                    + "\"regionId\":\"REGION.11\","
                    + "\"test\":\"testMiniDfs\","
                    + "\"rootMethod\":\"<example.Updater: void run()>\","
                    + "\"runtimeDefinitionMethods\":["
                    + "\"<example.Updater: void run()>\"],"
                    + "\"invocationOrdinal\":1,\"replayable\":true,"
                    + "\"symbolicReady\":true,"
                    + "\"captureGoal\":{\"kind\":\"OUTPUT_CLOSURE\","
                    + "\"scope\":\"BOUNDED_OUTPUT_RELEVANT_PATHS\"},"
                    + "\"requestedOutputSlice\":{\"complete\":true},"
                    + "\"requestedOutputCaptureRequired\":false,"
                    + "\"requestedOutputCaptureComplete\":true,"
                    + "\"requestedOutputCapture\":[],"
                    + "\"requestedOutput\":{"
                    + "\"portId\":\"REGION.11.out.0\","
                    + "\"cell\":\"" + ALL_KEYS + "\","
                    + "\"kind\":\"HEAP_STATE\"},"
                    + "\"edgeBindings\":[{"
                    + "\"edgeId\":\"E.STATE\","
                    + "\"writerEventSeq\":10,\"readerEventSeq\":20}],"
                    + "\"symbolize\":[],\"outputs\":[],\"branches\":[]}\n";
            activation = completeLegacyClosureJson(activation);
            Files.write(fixture.activations,
                    activation.getBytes(StandardCharsets.UTF_8));
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

            assertEquals(1, result.jobs.size());
            assertEquals("CAPTURE_OUTPUT_PATH", result.jobs.get(0)
                    .get("phase").getAsString());
            assertEquals("OUTPUT_CLOSURE", result.jobs.get(0)
                    .getAsJsonObject("captureGoal").get("kind")
                    .getAsString());
            assertEquals(0, result.queries.size());
            assertEquals(1, result.summary.get("upstreamCaptureJobCount")
                    .getAsInt());
            assertTrue(result.jobs.get(0).has("requestedOutput"));
            assertFalse(result.jobs.get(0).has(
                    OutputClosureContract.FIELD));
            assertTrue(result.scheduledActivations.get(0)
                    .has("requestedOutput"));
            assertFalse(result.scheduledActivations.get(0).has(
                    OutputClosureContract.FIELD));

            String observedMapPrestate = activation.replace(
                    "\"symbolize\":[]",
                    "\"symbolize\":[{\"symbol\":\"REGION.11.in.map\","
                            + "\"cell\":\"" + ALL_KEYS + "\","
                            + "\"field\":\"" + ALL_KEYS + "\","
                            + "\"sourceKind\":\"SHARED_HEAP\","
                            + "\"location\":\"HEAP_OBJECT_FIELD\","
                            + "\"javaType\":\"java.util.Map\","
                            + "\"observed\":true}]");
            Files.write(fixture.activations,
                    observedMapPrestate.getBytes(StandardCharsets.UTF_8));
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

            JsonObject incompleteSlice = JsonParser.parseString(activation)
                    .getAsJsonObject();
            incompleteSlice.addProperty("requestedOutputSliceComplete", true);
            incompleteSlice.getAsJsonObject("requestedOutputSlice")
                    .addProperty("complete", false);
            Files.write(fixture.activations,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result blocked =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(blocked.jobs.get(0).get("captureReady")
                    .getAsBoolean());

            incompleteSlice.remove("requestedOutputSlice");
            Files.write(fixture.activations,
                    (incompleteSlice.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            ConcolicScheduler.Result missingNestedSlice =
                    ConcolicScheduler.schedule(arguments);
            assertFalse(missingNestedSlice.jobs.get(0).get("captureReady")
                    .getAsBoolean());
            assertFalse(blocked.scheduledActivations.get(0)
                    .get("schedulerReady").getAsBoolean());
            assertFalse(blocked.jobs.get(0).get("captureReady")
                    .getAsBoolean());

            JsonObject autoCapture = JsonParser.parseString(activation)
                    .getAsJsonObject();
            autoCapture.addProperty("requestedOutputCaptureRequired", true);
            autoCapture.addProperty("requestedOutputCaptureComplete", false);
            JsonArray captureTemplates = new JsonArray();
            JsonObject encryptedCapture = new JsonObject();
            encryptedCapture.addProperty("captureKind",
                    "FIELD_ASSIGNMENT_RHS");
            encryptedCapture.addProperty("captureBindingId", "CAP.0");
            encryptedCapture.addProperty("outputPort",
                    "REGION.11.out.0");
            encryptedCapture.addProperty("outputCell", ALL_KEYS);
            encryptedCapture.addProperty("siteId",
                    "<example.Client: void encrypted()>#u7");
            encryptedCapture.addProperty("callerMethod",
                    "<example.Client: void encrypted()>");
            encryptedCapture.addProperty("method",
                    "<example.Client: void encrypted()>");
            encryptedCapture.addProperty("unitIndex", 7);
            encryptedCapture.addProperty("fieldSignature", ALL_KEYS);
            encryptedCapture.addProperty("occurrence", 0);
            captureTemplates.add(encryptedCapture);
            JsonObject plainCapture = new JsonObject();
            plainCapture.addProperty("captureKind",
                    "FIELD_ASSIGNMENT_RHS");
            plainCapture.addProperty("captureBindingId", "CAP.1");
            plainCapture.addProperty("outputPort",
                    "REGION.11.out.0");
            plainCapture.addProperty("outputCell", ALL_KEYS);
            plainCapture.addProperty("siteId",
                    "<example.Client: void plain()>#u9");
            plainCapture.addProperty("callerMethod",
                    "<example.Client: void plain()>");
            plainCapture.addProperty("method",
                    "<example.Client: void plain()>");
            plainCapture.addProperty("unitIndex", 9);
            plainCapture.addProperty("fieldSignature", ALL_KEYS);
            plainCapture.addProperty("occurrence", 0);
            captureTemplates.add(plainCapture);
            autoCapture.add("requestedOutputCapture", captureTemplates);
            autoCapture.getAsJsonObject("requestedOutputSlice")
                    .addProperty("captureBindingsRequired", true);
            autoCapture.getAsJsonObject("requestedOutputSlice")
                    .add("captureBindings", captureTemplates.deepCopy());
            autoCapture.getAsJsonObject("requestedOutputSlice")
                    .addProperty("captureBindingsComplete", false);
            JsonArray observedMethods = new JsonArray();
            observedMethods.add("<example.Client: void encrypted()>");
            autoCapture.add("observedMethods", observedMethods);
            Files.write(fixture.activations,
                    (autoCapture + "\n").getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Arguments autoCaptureArguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan",
                            fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only"});
            JsonObject automaticallyRefined = ConcolicScheduler.schedule(
                    autoCaptureArguments).scheduledActivations.get(0);
            JsonObject automaticCapture = automaticallyRefined
                    .getAsJsonArray("requestedOutputCapture").get(0)
                    .getAsJsonObject();
            assertEquals("<example.Client: void encrypted()>#u7",
                    automaticCapture.get("siteId").getAsString());
            assertEquals(1, automaticCapture.get("occurrence").getAsInt());
            assertEquals("UNIQUE_OBSERVED_CAPTURE_METHOD_FIRST_"
                            + "OCCURRENCE_APPROXIMATION_V1",
                    automaticCapture.get("occurrenceAuthority")
                            .getAsString());
            assertTrue(automaticallyRefined.get(
                    "requestedOutputCaptureComplete").getAsBoolean());

            ConcolicScheduler.Arguments explicitCaptureArguments =
                    ConcolicScheduler.Arguments.parse(new String[]{
                            "--regions", fixture.regions.toString(),
                            "--activation-plan",
                            fixture.activations.toString(),
                            "--edge-validations", fixture.edges.toString(),
                            "--static-graph", fixture.staticGraph.toString(),
                            "--output-dir", fixture.output.toString(),
                            "--activation-id", "ACT.PRODUCER.0",
                            "--capture-only",
                            "--requested-output-capture-site",
                            "<example.Client: void plain()>#u9",
                            "--requested-output-capture-occurrence", "3"});
            JsonObject explicitlyRefined = ConcolicScheduler.schedule(
                    explicitCaptureArguments).scheduledActivations.get(0);
            JsonObject explicitCapture = explicitlyRefined.getAsJsonArray(
                    "requestedOutputCapture").get(0).getAsJsonObject();
            assertEquals("<example.Client: void plain()>#u9",
                    explicitCapture.get("siteId").getAsString());
            assertEquals(3, explicitCapture.get("occurrence").getAsInt());
            assertEquals("CONFIGURED_EXACT_CAPTURE_SITE_AND_OCCURRENCE_V1",
                    explicitCapture.get("selectionAuthority")
                            .getAsString());

            String deferred = activation.replace("\"symbolize\":[]",
                    "\"symbolize\":[{\"symbol\":\"REGION.11.in.env\","
                            + "\"cell\":\"<example.Clock: long now()>.return\","
                            + "\"location\":\"ENVIRONMENT_MODEL\"}]");
            Files.write(fixture.activations,
                    deferred.getBytes(StandardCharsets.UTF_8));
            ConcolicScheduler.Result deferredClosure =
                    ConcolicScheduler.schedule(arguments);
            assertTrue(deferredClosure.jobs.get(0).get("captureReady")
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
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
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

            assertEquals(1, result.jobs.size());
            assertTrue(result.jobs.get(0).has(OutputClosureContract.FIELD));
            assertFalse(result.jobs.get(0).has("requestedOutput"));
            assertEquals(2, OutputClosureCodec.decode(result.jobs.get(0))
                    .members().size());
            JsonObject scheduled = result.scheduledActivations.get(0);
            assertTrue(scheduled.has(OutputClosureContract.FIELD));
            assertFalse(scheduled.has("requestedOutput"));
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
                completeLegacyMember("REGION.1.out.x",
                        "<example.Producer: int x>",
                        "REGION.1.in.x", "B.x", 2));
        OutputClosureContract y = OutputClosureCodec.decode(
                completeLegacyMember("REGION.1.out.y",
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

    private static JsonObject completeLegacyMember(
            String port, String cell, String input, String branch,
            int unitIndex) {
        JsonObject activation = new JsonObject();
        activation.addProperty("regionId", "REGION.1");
        activation.addProperty("regionInstanceId",
                "REGION.1@test#call7");
        activation.addProperty("rootCallId", 7);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", port);
        requested.addProperty("cell", cell);
        requested.addProperty("kind", "REGION_OUTPUT");
        requested.addProperty("selectionAuthority", "TEST_EXACT_OUTPUT");
        activation.add("requestedOutput", requested);
        JsonObject output = new JsonObject();
        output.addProperty("symbol", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        activation.add("outputs", outputs);

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
        activation.add("requestedOutputCapture", captures);
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);

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
        activation.add("requestedOutputSlice", slice);
        return activation;
    }

    private static String completeLegacyClosureJson(String encoded) {
        JsonObject activation = JsonParser.parseString(encoded)
                .getAsJsonObject();
        if (!activation.has("rootCallId")) {
            String instance = activation.get("regionInstanceId").getAsString();
            activation.addProperty("rootCallId", Integer.parseInt(
                    instance.substring(instance.lastIndexOf("#call") + 5)));
        }
        JsonObject requested = activation.getAsJsonObject(
                "requestedOutput");
        if ("VALUE".equals(requested.get("kind").getAsString())) {
            requested.addProperty("kind", "REGION_OUTPUT");
        }
        requested.addProperty("selectionAuthority",
                "TEST_COMPLETE_LEGACY_OUTPUT");
        String port = requested.get("portId").getAsString();
        String cell = requested.get("cell").getAsString();
        if ("client.userName".equals(cell)) {
            requested.addProperty("javaTypeDescriptor",
                    "Ljava/lang/String;");
        }
        if (!activation.has("requestedOutputCapture")) {
            activation.add("requestedOutputCapture", new JsonArray());
        }
        if (!activation.has("requestedOutputCaptureRequired")) {
            activation.addProperty("requestedOutputCaptureRequired", false);
        }
        if (!activation.has("requestedOutputCaptureComplete")) {
            activation.addProperty("requestedOutputCaptureComplete", true);
        }
        JsonObject slice = activation.getAsJsonObject(
                "requestedOutputSlice");
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        JsonArray inputs = new JsonArray();
        for (JsonElement element : activation.getAsJsonArray("symbolize")) {
            if (element.isJsonObject()) {
                inputs.add(element.getAsJsonObject()
                        .get("symbol").getAsString());
            }
        }
        slice.add("inputPorts", inputs);
        if (!slice.has("sites")) slice.add("sites", new JsonArray());
        slice.add("staticSites",
                slice.getAsJsonArray("sites").deepCopy());
        slice.add("methods", activation.has("requestedOutputMethods")
                ? activation.getAsJsonArray("requestedOutputMethods")
                .deepCopy() : new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.addProperty("captureBindingsRequired", activation.get(
                "requestedOutputCaptureRequired").getAsBoolean());
        slice.addProperty("captureBindingsComplete", activation.get(
                "requestedOutputCaptureComplete").getAsBoolean());
        slice.add("captureBindings", activation.getAsJsonArray(
                "requestedOutputCapture").deepCopy());

        JsonObject output = new JsonObject();
        output.addProperty("symbol", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", requested.get("kind").getAsString());
        output.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        if (requested.has("javaTypeDescriptor")) {
            output.add("javaTypeDescriptor",
                    requested.get("javaTypeDescriptor").deepCopy());
        }
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        activation.add("outputs", outputs);
        return activation + "\n";
    }

    private static JsonObject argumentAction(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("location", "ARGUMENT");
        return action;
    }

    private static JsonObject branch(String siteId) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", siteId);
        return branch;
    }

    private static JsonObject arrayFieldCaptureActivation(JsonObject action) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.ARRAY.FIELD");
        activation.addProperty("regionId", "REGION.ARRAY");
        RegionCaptureGoal.outputClosure().writeTo(activation);
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        activation.add("requestedOutputSlice", slice);
        activation.addProperty("requestedOutputCaptureRequired", false);
        activation.addProperty("requestedOutputCaptureComplete", true);
        activation.add("requestedOutputCapture", new JsonArray());
        JsonArray symbolize = new JsonArray();
        symbolize.add(action);
        activation.add("symbolize", symbolize);
        return activation;
    }

    private static JsonObject exactArrayFieldAction(String method) {
        String signature =
                "<example.ArrayState: example.Value[] values>";
        JsonObject action = new JsonObject();
        action.addProperty("symbol", "REGION.ARRAY.in.0");
        action.addProperty("cell", signature);
        action.addProperty("field", signature);
        action.addProperty("javaType", "example.Value[]");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("consumedFieldBindingComplete", true);
        action.addProperty("consumedFieldMethod", method);
        action.addProperty("consumedFieldUnitIndex", 7);
        action.addProperty("consumedFieldSiteId", method + "#u7");
        action.addProperty("consumedFieldSiteAuthority",
                "RUNTIME_UNIQUE_STATIC_LEAF_GETFIELD_SITE_AND_"
                        + "OWNER_WITHIN_REGION_INSTANCE_V1");
        action.addProperty("consumedFieldRootAuthority",
                "DIRECT_EXACT_LEAF_GETFIELD_BASE_IS_INPUT_OWNER_V1");
        action.addProperty("consumedFieldOccurrence", 1);
        action.addProperty("consumedFieldOccurrenceAuthority",
                "UNIQUE_CONTAINED_RUNTIME_FIELD_READ_V1");
        return action;
    }

    private static JsonObject pendingArrayCallReturnAction(
            String method, String returned) {
        JsonObject action = exactArrayFieldAction(method);
        action.addProperty("cell", returned);
        action.addProperty("location", "CALL_RETURN");
        action.add("fieldPath", JsonParser.parseString("[\"values\"]"));
        action.addProperty("consumedFieldBindingComplete", false);
        action.addProperty("consumedFieldSiteBindingComplete", true);
        action.addProperty("consumedFieldBindingIssue",
                "LOCAL_ROOT_DEFINITION_PENDING_SCHEDULER");
        action.addProperty("consumedFieldRootAuthority",
                "LOCAL_DEFINITION_ROOT_PENDING_AUTHORITATIVE_"
                        + "SCHEDULER_DEFINITION_INDEX_V1");
        action.addProperty("consumedFieldPendingRootKind",
                "CALL_RETURN_DEFINITION");
        return action;
    }

    private static JsonObject callReturnDefinition(String returned,
                                                   String method,
                                                   String local,
                                                   int unitIndex) {
        JsonObject definition = new JsonObject();
        definition.addProperty("fromCell", returned);
        definition.addProperty("toCell", method + "::" + local);
        definition.addProperty("method", method);
        definition.addProperty("unitIndex", unitIndex);
        definition.addProperty("siteId", method + "#u" + unitIndex);
        definition.addProperty("unit", local + " = source()");
        return definition;
    }


    private static void setSaslEqualityEvidence(Fixture fixture,
                                                long writer,
                                                long reader)
            throws Exception {
        List<String> rows = Files.readAllLines(fixture.edges,
                StandardCharsets.UTF_8);
        JsonArray rewritten = new JsonArray();
        boolean found = false;
        for (String row : rows) {
            if (row.trim().isEmpty()) continue;
            JsonObject edge = JsonParser.parseString(row).getAsJsonObject();
            if ("E.SASL".equals(edge.get("edgeId").getAsString())) {
                JsonObject evidence = edge.getAsJsonArray(
                        "bindings")
                        .get(0).getAsJsonObject().deepCopy();
                evidence.addProperty("fromRegionInstance",
                        "REGION.1@test#call1");
                evidence.addProperty("toRegionInstance",
                        "REGION.0@testMiniDfs#call7");
                evidence.addProperty("fromEndpointSeq", writer);
                evidence.addProperty("toEndpointSeq", reader);
                evidence.addProperty("orderConfirmed", writer < reader);
                JsonArray singleton = new JsonArray();
                singleton.add(evidence);
                edge.add("bindings", singleton);
                found = true;
            }
            rewritten.add(edge);
        }
        assertTrue(found);
        StringBuilder content = new StringBuilder();
        for (JsonElement element : rewritten) {
            content.append(element).append('\n');
        }
        Files.write(fixture.edges,
                content.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static void prependSaslEqualityEvidence(Fixture fixture,
                                                    long writer,
                                                    long reader)
            throws Exception {
        List<String> rows = Files.readAllLines(fixture.edges,
                StandardCharsets.UTF_8);
        StringBuilder content = new StringBuilder();
        boolean found = false;
        for (String row : rows) {
            if (row.trim().isEmpty()) continue;
            JsonObject edge = JsonParser.parseString(row).getAsJsonObject();
            if ("E.SASL".equals(edge.get("edgeId").getAsString())) {
                JsonArray current = edge.getAsJsonArray(
                        "bindings");
                JsonObject duplicate = current.get(0).getAsJsonObject()
                        .deepCopy();
                duplicate.addProperty("fromEndpointSeq", writer);
                duplicate.addProperty("toEndpointSeq", reader);
                duplicate.addProperty("orderConfirmed", writer < reader);
                JsonArray repeated = new JsonArray();
                repeated.add(duplicate);
                for (JsonElement element : current) {
                    repeated.add(element.deepCopy());
                }
                edge.add("bindings", repeated);
                found = true;
            }
            content.append(edge).append('\n');
        }
        assertTrue(found);
        Files.write(fixture.edges,
                content.toString().getBytes(StandardCharsets.UTF_8));
    }

    private static void assertCompactScheduledActivation(JsonObject row) {
        assertFalse(row.has("symbolicReady"));
    }

    private static void assertRuntimeEqualityBinding(JsonObject binding) {
        assertEquals("E.SASL", binding.get("edgeId").getAsString());
        assertEquals("EQUALITY", binding.get("relationKind").getAsString());
        assertEquals("RUNTIME_CONFIRMED_VALUE_EQUALITY", binding.get(
                "selectionAuthority").getAsString());
        assertEquals("REGION.1@test#call1", binding.get(
                "fromRegionInstance").getAsString());
        assertEquals("REGION.0@testMiniDfs#call7", binding.get(
                "toRegionInstance").getAsString());
        assertEquals("REGION.1.out.0", binding.get(
                "fromOutputPort").getAsString());
        assertEquals("REGION.0.in.0", binding.get(
                "toInputPort").getAsString());
        assertEquals(10, binding.get("writerEventSeq").getAsInt());
        assertEquals(20, binding.get("readerEventSeq").getAsInt());
        assertTrue(binding.get("orderConfirmed").getAsBoolean());
        assertTrue(binding.get("valueEqualityObserved").getAsBoolean());
        assertEquals("RUNTIME_COMPLETE_VALUE_FINGERPRINT", binding.get(
                "valueEqualityAuthority").getAsString());
        assertEquals("GLOBAL_TRACE_ENDPOINT_SEQUENCE", binding.get(
                "endpointOrderAuthority").getAsString());
        assertEquals("EXEC.fixture", binding.get(
                "discoveredExecutionId").getAsString());
        assertEquals("sha256:fixture", binding.get(
                "valueFingerprint").getAsString());
        assertFalse(binding.get("objectIdentityRequired").getAsBoolean());
        assertFalse(binding.has("receiverObjectId"));
        assertFalse(binding.has("objectIdentityConfirmed"));
    }

    private static JsonObject condition(String operator) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", operator);
        return result;
    }

    private static String accessorInputProof(String edgeId, String fromCell,
                                             String toCell) {
        String getter = "<javax.security.auth.callback.NameCallback: "
                + "java.lang.String getDefaultName()>";
        return "{\"schemaVersion\":1,\"id\":\"" + edgeId + "\","
                + "\"kind\":\"accessor_field_return\","
                + "\"transferKind\":\"HEAP_READ\","
                + "\"relation\":\"value_flow\","
                + "\"direction\":\"backward_provenance\","
                + "\"mappingOnly\":false,"
                + "\"semanticAssertionsAllowed\":true,"
                + "\"eligibleForAutomaticDerivation\":true,"
                + "\"eligibleForAutomaticSmt\":true,"
                + "\"fromCell\":\"" + fromCell + "\","
                + "\"toCell\":\"" + toCell + "\","
                + "\"invoke\":\"" + getter + "\","
                + "\"declaredFieldSignature\":\"" + fromCell + "\","
                + "\"declaredFieldOwner\":"
                + "\"javax.security.auth.callback.NameCallback\","
                + "\"declaredFieldType\":\"java.lang.String\","
                + "\"declaredFieldName\":\"defaultName\","
                + "\"declaredFieldAuthority\":"
                + "\"SOOT_RESOLVED_DECLARATION_HIERARCHY\","
                + "\"accessorImplementationMethod\":\"" + getter + "\","
                + "\"accessorImplementationAuthority\":"
                + "\"SOOT_RESOLVED_METHOD_DECLARATION_HIERARCHY\"}\n";
    }

    private static Fixture fixture(Path root, boolean includeSummary)
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

        if (includeSummary) {
            JsonObject summary = new JsonObject();
            summary.addProperty("summaryId", "SUMMARY.REGION.0.SEED");
            summary.addProperty("activationId", "ACT.0");
            summary.addProperty("regionId", "REGION.0");
            summary.addProperty("regionInstanceId",
                    "REGION.0@testMiniDfs#call7");
            summary.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            summary.addProperty("relationallyComplete", true);
            summary.addProperty("executionKind", "UNFORCED_SEED");

            JsonObject prefixCondition = JsonParser.parseString(
                    "{\"_type\":\"BinaryExpression\",\"_op\":\">\"}")
                    .getAsJsonObject();
            JsonObject relation = JsonParser.parseString(
                    "{\"_type\":\"MethodExpression\","
                            + "\"_name\":\"java/util/HashMap get\","
                            + "\"_param_list\":["
                            + "{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"MAP\"},"
                            + "{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"KEY\"}],"
                            + "\"_res_exp\":{\"_type\":"
                            + "\"SymbolExpression\",\"_exp\":\"RESULT\"}}")
                    .getAsJsonObject();
            JsonObject targetCondition = JsonParser.parseString(
                    "{\"_type\":\"BinaryExpression\",\"_op\":\"!=\","
                            + "\"_left\":{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"RESULT\"},"
                            + "\"_right\":{\"_type\":\"SymbolExpression\","
                            + "\"_exp\":\"N\"}}")
                    .getAsJsonObject();
            JsonArray path = new JsonArray();
            path.add(prefixCondition);
            path.add(relation);
            path.add(targetCondition);
            summary.add("pathCondition", path);

            JsonObject prefixEvent = new JsonObject();
            prefixEvent.addProperty("eventId", 1);
            prefixEvent.addProperty("contextId", 7);
            BranchWitness prefixWitness = BranchWitness.vmPc(
                    "<example.Manager: byte[] lookup(int)>#u1",
                    "<example.Manager: byte[] lookup(int)>", 1, 1, true,
                    prefixCondition, 0, prefixEvent);
            JsonObject targetEvent = new JsonObject();
            targetEvent.addProperty("eventId", 2);
            targetEvent.addProperty("contextId", 7);
            BranchWitness targetWitness = BranchWitness.vmPc(TARGET,
                    "<example.Manager: byte[] lookup(int)>", 8, 1, true,
                    targetCondition, 2, targetEvent);
            JsonObject prefixMapping = SummaryBranchMapping.witnessed(
                    prefixWitness, 0,
                    SummaryBranchMapping.Policy.PATH_ASSUMPTION).toJson();
            JsonObject targetMapping = SummaryBranchMapping.witnessed(
                    targetWitness, 2,
                    SummaryBranchMapping.Policy.EXPLORE).toJson();
            JsonArray mappings = new JsonArray();
            mappings.add(prefixMapping);
            mappings.add(targetMapping);
            summary.add("branchMappings", mappings);
            Files.write(result.summaries,
                    (summary + "\n").getBytes(StandardCharsets.UTF_8));
        }
        return result;
    }

    private static final class Fixture {
        private final Path regions;
        private final Path activations;
        private final Path edges;
        private final Path staticGraph;
        private final Path summaries;
        private final Path output;

        private Fixture(Path root) {
            this.regions = root.resolve("regions.jsonl");
            this.activations = root.resolve("activations.jsonl");
            this.edges = root.resolve("edges.jsonl");
            this.staticGraph = root.resolve("static.jsonl");
            this.summaries = root.resolve("summaries.jsonl");
            this.output = root.resolve("schedule");
        }
    }
}
