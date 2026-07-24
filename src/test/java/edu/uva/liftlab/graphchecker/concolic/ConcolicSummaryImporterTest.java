package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicSummaryImporterTest {




    private static JsonObject valueRefWitnessRecord(boolean certified) {
        JsonObject record = new JsonObject();
        record.addProperty("valueExpressionAuthority",
                "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1");
        record.addProperty("objectTokenScope", "ACT.P");
        record.addProperty("valueObjectToken", 103L);
        record.addProperty("valueExpressionWitnessSchemaVersion", 1);
        record.addProperty("valueExpressionWitnessKind",
                "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS");
        record.addProperty("valueExpressionWitnessObjectToken", 103L);
        record.addProperty("valueExpressionWitnessObjectTokenScope", "ACT.P");
        record.addProperty("valueExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103");
        record.add("valueExpression", expression);
        if (certified) {
            record.addProperty("valueExpressionWitnessCertified", true);
            record.addProperty("valueExpressionWitnessCertificationAuthority",
                    "IMPORTER_EXACT_ACTIVATION_TOKEN_AND_"
                            + "DYNAMIC_FIELD_OWNER_JOIN_V1");
            record.addProperty(
                    "valueExpressionWitnessCertifiedObjectToken", 103L);
            record.addProperty(
                    "valueExpressionWitnessCertifiedObjectTokenScope", "ACT.P");
        }
        return record;
    }

    private static JsonObject mapRefWitnessRecord() {
        JsonObject record = new JsonObject();
        record.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        record.addProperty("objectTokenScope", "ACT.P");
        record.addProperty("backingMapObjectToken", 101L);
        record.addProperty("mapExpressionWitnessSchemaVersion", 1);
        record.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        record.addProperty("mapExpressionWitnessObjectToken", 101L);
        record.addProperty("mapExpressionWitnessObjectTokenScope", "ACT.P");
        record.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T101");
        record.add("mapExpression", expression);
        return record;
    }

    @Test
    public void validatesRegionSummaryWithNestedPathConditionPause()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path root = folder.getRoot().toPath();
            Path activations = root.resolve("activation.jsonl");
            Path regions = root.resolve("regions.jsonl");
            Path results = root.resolve("results.jsonl");
            Path output = root.resolve("summaries.jsonl");
            Path diagnostics = root.resolve("diagnostics.jsonl");
            String method = "<example.Handler: void handle()>";
            write(activations, "{\"activationId\":\"ACT.0\","
                    + "\"regionId\":\"REGION.0\",\"rootMethod\":\""
                    + method + "\","
                    + "\"captureGoal\":"
                    + RegionCaptureGoal.outputClosure().toJson() + ","
                    + "\"receiverType\":\"Handler\","
                    + "\"symbolize\":[{\"symbol\":\"REGION.0.in.0\"}],"
                    + "\"materializations\":[],"
                    + "\"outputs\":[{\"symbol\":\"REGION.0.out.0\","
                    + "\"location\":\"THROW_OR_BRANCH\"}]}\n");
            write(regions, "{\"regionId\":\"REGION.0\","
                    + "\"rootMethod\":\"" + method + "\","
                    + "\"methods\":[\"" + method + "\"]}\n");
            // The observation boundary and finish-time bookkeeping each hold
            // a pause, so a real custom-Zero result can legitimately report 2.
            write(results, "{\"event\":\"CONCOLIC_REGION_RESULT\","
                    + "\"activationId\":\"ACT.0\",\"regionId\":\"REGION.0\","
                    + "\"exitKind\":\"THROW\",\"exceptionType\":\"InvalidToken\","
                    + "\"unresolvedInputs\":[],"
                    + "\"rootOutputExpression\":{\"kind\":\"SYMBOLIC_OBJECT\"},"
                    + "\"engineSummary\":{\"active\":true,"
                    + "\"engine\":\"openjdk8-zero-concolic\","
                    + "\"regionId\":\"REGION.0\",\"activationId\":\"ACT.0\","
                    + "\"pathConditionRecordingPaused\":true,"
                    + "\"pathConditionPauseDepth\":2,"
                    + "\"pathCondition\":[{\"_type\":\"BinaryExpression\","
                    + "\"_op\":\"==\",\"_code_position\":"
                    + "\"virtual void example.Handler.handle():12\"}]}}\n");

            ConcolicSummaryImporter.ImportResult imported =
                    ConcolicSummaryImporter.importSummaries(results, activations,
                            regions, output, diagnostics);

            assertEquals(1, imported.rawResultCount);
            assertEquals(1, imported.validSummaryCount);
            String summary = new String(Files.readAllBytes(output),
                    StandardCharsets.UTF_8);
            assertTrue(summary.contains("InvalidToken"));
            JsonObject importedSummary = JsonParser.parseString(
                    summary.trim()).getAsJsonObject();
            assertEquals("UNFORCED_SEED",
                    importedSummary.get("executionKind").getAsString());
            assertEquals(0, importedSummary.getAsJsonArray(
                    "symbolicInputs").size());
        } finally {
            folder.delete();
        }
    }


























    @Test
    public void outputClosureAdmitsOnlyRequestedOutputSliceMethods()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            JsonObject map = symbol(
                    "M_L_field_REGION.P.in.0_example/Store", "L");
            JsonArray path = new JsonArray();
            path.add(methodExpression("java/util/Map put", 10,
                    symbolCopy(map), symbol("key1", "I"),
                    symbol("value1", "example/Value")));
            path.add(methodExpressionAt("java/util/Map put",
                    "example.Unrelated.touch()", 20, symbolCopy(map),
                    symbol("key2", "I"),
                    symbol("value2", "example/Value")));

            MapFixture imported = importMapFixture(
                    folder.getRoot().toPath(), path);
            assertEquals(1, imported.summary.getAsJsonArray(
                    "pathCondition").size());
            assertEquals(1, imported.summary.getAsJsonArray(
                    "heapEffects").size());
            assertTrue(imported.diagnostics.contains(
                    "FILTERED_NON_SEMANTIC_PATH_CONDITIONS"));
        } finally {
            folder.delete();
        }
    }




















    @Test
    public void importsJointOutputsFromOneAtomicRuntimeResult()
            throws Exception {
        TemporaryFolder complete = new TemporaryFolder();
        complete.create();
        TemporaryFolder partial = new TemporaryFolder();
        partial.create();
        TemporaryFolder wrongGoal = new TemporaryFolder();
        wrongGoal.create();
        TemporaryFolder missingContract = new TemporaryFolder();
        missingContract.create();
        try {
            JsonObject summary = importJointOutputCaptureFixture(
                    complete.getRoot().toPath(), false, false);
            assertTrue(summary.get("relationallyComplete").getAsBoolean());
            assertTrue(summary.has("outputClosure"));
            assertFalse(summary.has("requestedOutput"));
            assertEquals(2, summary.getAsJsonObject("outputExpressions")
                    .size());

            JsonObject missing = importJointOutputCaptureFixture(
                    partial.getRoot().toPath(), true, false);
            assertFalse(missing.get("relationallyComplete").getAsBoolean());
            assertEquals(1, missing.getAsJsonObject("outputExpressions")
                    .size());

            JsonObject rejected = importJointOutputCaptureFixture(
                    wrongGoal.getRoot().toPath(), false, true);
            assertEquals(0, rejected.size());

            Path missingRoot = missingContract.getRoot().toPath();
            importJointOutputCaptureFixture(missingRoot, false, false);
            JsonObject activation = readObject(
                    missingRoot.resolve("activation.jsonl"));
            activation.remove(OutputClosureContract.FIELD);
            writeVerbatim(missingRoot.resolve("activation.jsonl"),
                    activation + "\n");
            ConcolicSummaryImporter.ImportResult missingContractResult =
                    ConcolicSummaryImporter.importSummaries(
                            missingRoot.resolve("results.jsonl"),
                            missingRoot.resolve("activation.jsonl"),
                            missingRoot.resolve("regions.jsonl"),
                            missingRoot.resolve("missing-summary.jsonl"),
                            missingRoot.resolve("missing-diagnostics.jsonl"));
            assertEquals(0, missingContractResult.validSummaryCount);
            assertTrue(readOptional(missingRoot.resolve(
                    "missing-diagnostics.jsonl")).contains(
                    "canonical outputClosure is required"));
        } finally {
            complete.delete();
            partial.delete();
            wrongGoal.delete();
            missingContract.delete();
        }
    }

    @Test
    public void validatesEveryFieldMemberInsteadOfOnlyFirstOutput()
            throws Exception {
        TemporaryFolder complete = new TemporaryFolder();
        complete.create();
        TemporaryFolder malformed = new TemporaryFolder();
        malformed.create();
        try {
            JsonObject summary = importJointFieldOutputCaptureFixture(
                    complete.getRoot().toPath(), false);

            assertTrue(summary.get("relationallyComplete").getAsBoolean());
            assertEquals(2, summary.getAsJsonObject("outputExpressions")
                    .size());
            assertTrue(summary.has("outputClosure"));
            for (Map.Entry<String, JsonElement> output
                    : summary.getAsJsonObject(
                    "outputExpressions").entrySet()) {
                assertTrue(output.getKey(),
                        output.getValue().getAsJsonObject().has("_exp"));
                assertFalse(output.getKey(),
                        output.getValue().getAsJsonObject().has("kind"));
            }

            JsonObject rejected = importJointFieldOutputCaptureFixture(
                    malformed.getRoot().toPath(), true);
            assertFalse(rejected.get("relationallyComplete").getAsBoolean());
        } finally {
            complete.delete();
            malformed.delete();
        }
    }


    @Test
    public void importsExactFieldAssignmentRhsAsHeapStateOutput()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            MapFixture imported = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath(), "NORMAL", true, true,
                    symbol("M_L_field_REGION.FIELD.in.0_java/lang/String",
                            "L"));

            assertTrue(imported.diagnostics, imported.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertEquals("M_L_field_REGION.FIELD.in.0_java/lang/String",
                    imported.summary.getAsJsonObject("outputExpressions")
                            .getAsJsonObject("REGION.FIELD.out.0")
                            .get("_exp").getAsString());
            assertFalse(imported.summary.has("outputExpressionAdmission"));

            MapFixture projected = importExactFieldAssignmentCaptureFixture(
                    folder.getRoot().toPath().resolve("projected"),
                    "NORMAL", true, true, JsonNull.INSTANCE);
            assertTrue(projected.diagnostics, projected.summary.get(
                    "relationallyComplete").getAsBoolean());
            JsonObject projectedExpression = projected.summary
                    .getAsJsonObject("outputExpressions")
                    .getAsJsonObject("REGION.FIELD.out.0");
            assertEquals("SymbolExpression", projectedExpression.get(
                    "_type").getAsString());
            assertEquals("REGION.FIELD.in.0", projectedExpression.get(
                    "_causynth_projection_input_port").getAsString());
            assertEquals("[\"value\"]", projectedExpression.getAsJsonArray(
                    "_causynth_projection_field_path").toString());
            assertFalse(projected.summary.has(
                    "ignoredRuntimeHeapEvidence"));

            MapFixture causalGuardObservation =
                    importExactFieldAssignmentCaptureFixture(
                            folder.getRoot().toPath().resolve(
                                    "causal-map-observation"),
                            "NORMAL", true, true,
                            "<example.State: java.lang.String value>",
                            JsonNull.INSTANCE, "CAUSAL_MAP_OBSERVATION");
            assertFalse(causalGuardObservation.summary.get(
                    "relationallyComplete").getAsBoolean());
            assertFalse(causalGuardObservation.summary.has(
                    "ignoredRuntimeHeapEvidence"));
            assertTrue(causalGuardObservation.diagnostics,
                    causalGuardObservation.diagnostics.contains(
                            "INCOMPLETE_RUNTIME_HEAP_OBSERVATION"));

            Object[][] containerCases = {
                    {"one", 1, new int[]{0}, "NORMAL", true},
                    {"sparse", 5, new int[]{1, 4}, "NORMAL", true},
                    {"duplicate-load", 1, new int[]{0},
                            "DUPLICATE_LOAD", true},
                    {"wrong-site", 1, new int[]{0}, "SITE", false},
                    {"wrong-value", 1, new int[]{0}, "VALUE", false},
                    {"snapshot-value", 1, new int[]{0},
                            "SNAPSHOT_VALUE", false},
                    {"mixed-residual", 1, new int[]{0},
                            "MIXED_RESIDUAL", false},
                    {"missing-effect", 5, new int[]{1, 4},
                            "MISSING_EFFECT", false}
            };
            for (Object[] testCase : containerCases) {
                String name = (String) testCase[0];
                MapFixture container = importContainerMutationFixture(
                        folder.getRoot().toPath().resolve(name),
                        (Integer) testCase[1], (int[]) testCase[2],
                        (String) testCase[3]);
                assertEquals(name + ": " + container.diagnostics,
                        testCase[4], container.summary.get(
                        "relationallyComplete").getAsBoolean());
                if ("mixed-residual".equals(name)) {
                    assertFalse(container.diagnostics,
                            container.diagnostics.contains("#u17"));
                    assertTrue(container.diagnostics,
                            container.diagnostics.contains("#u90"));
                }
            }
        } finally {
            folder.delete();
        }
    }
















    private static void assertPlaceholderRejected(
            PlaceholderFixture rejected, String diagnostic) {
        assertFalse(rejected.summary.get("relationallyComplete")
                .getAsBoolean());
        assertEquals(0, rejected.summary.getAsJsonArray(
                "vmIntrinsicPlaceholderBindings").size());
        assertEquals(0, rejected.summary.getAsJsonArray(
                "unforcedEnvironmentValidationRequirements").size());
        assertTrue(rejected.diagnostics.contains(diagnostic));
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence)
            throws Exception {
        return importPlaceholderFixture(root, materialization, evidence,
                false);
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence,
            boolean falselyReportSymbolized) throws Exception {
        return importPlaceholderFixture(root, materialization, evidence,
                falselyReportSymbolized,
                "<java.lang.System: long currentTimeMillis()>.return");
    }

    private static PlaceholderFixture importPlaceholderFixture(
            Path root, JsonObject materialization, JsonElement evidence,
            boolean falselyReportSymbolized, String environmentCell)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.TimeHandler: long handle()>";
        String inputPort = "REGION.TIME.in.0";

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.TIME");
        activation.addProperty("regionId", "REGION.TIME");
        activation.addProperty("regionInstanceId",
                "REGION.TIME@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", "REGION.TIME.out.0");
        slice.add("inputPorts", singletonString(inputPort));
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject declared = new JsonObject();
        declared.addProperty("symbol", inputPort);
        declared.addProperty("cell", environmentCell);
        declared.addProperty("sourceKind", "ENVIRONMENT");
        declared.addProperty("location", "ENVIRONMENT_MODEL");
        JsonArray symbolize = new JsonArray();
        symbolize.add(declared);
        activation.add("symbolize", symbolize);
        JsonArray materializations = new JsonArray();
        if (materialization != null) {
            materializations.add(materialization.deepCopy());
        }
        activation.add("materializations", materializations);
        JsonObject requestedOutput = new JsonObject();
        requestedOutput.addProperty("portId", "REGION.TIME.out.0");
        requestedOutput.addProperty("kind", "PRIMITIVE");
        activation.add("requestedOutput", requestedOutput);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.TIME.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(outputAction);
        activation.add("outputs", outputs);
        if (evidence.isJsonObject()
                && "BinaryExpression".equals(evidence.getAsJsonObject()
                .has("_type") ? evidence.getAsJsonObject().get("_type")
                .getAsString() : "")) {
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", method + "#u0");
            branch.addProperty("policy", "EXPLORE");
            activation.add("branches", singletonObject(branch));
        }
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.TIME");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        region.add("branchPolicies", activation.has("branches")
                ? activation.getAsJsonArray("branches").deepCopy()
                : new JsonArray());
        write(regions, region + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.TIME");
        raw.addProperty("regionId", "REGION.TIME");
        raw.addProperty("exitKind", "NORMAL");
        JsonArray symbolizedInputs = new JsonArray();
        if (falselyReportSymbolized) {
            symbolizedInputs.add(inputPort);
        }
        raw.add("symbolizedInputs", symbolizedInputs);
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("rootOutputExpression", constant("Y_J_1", "J"));
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.TIME");
        engine.addProperty("activationId", "ACT.TIME");
        JsonArray path = new JsonArray();
        path.add(evidence.deepCopy());
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        if (evidence.isJsonObject()
                && evidence.getAsJsonObject().has("_type")
                && "BinaryExpression".equals(evidence.getAsJsonObject()
                .get("_type").getAsString())) {
            JsonObject mapping = branchMapping(method, 0, 1, true,
                    evidence);
            mapping.addProperty("conditionIndex", 0);
            mapping.addProperty("rawConditionIndex", 0);
            mapping.addProperty("engineConditionIndex", 0);
            mapping.add("rawCondition", evidence.deepCopy());
            raw.add("branchMappings", authorizeRawBranchMappingsForTest(
                    singletonObject(mapping), path));
        }
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics);
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new PlaceholderFixture(summary, readOptional(diagnostics));
    }

    private static JsonObject exactCurrentTimePlaceholderMaterialization() {
        return exactCurrentTimePlaceholderMaterialization(
                "<java.lang.System: long currentTimeMillis()>.return");
    }

    private static JsonObject exactCurrentTimePlaceholderMaterialization(
            String environmentCell) {
        JsonObject result = new JsonObject();
        result.addProperty("symbol", "REGION.TIME.in.0");
        result.addProperty("cell", environmentCell);
        result.addProperty("sourceKind", "ENVIRONMENT");
        result.addProperty("location", "ENVIRONMENT_MODEL");
        result.addProperty("bindingMode", "VM_INTRINSIC_PLACEHOLDER");
        result.addProperty("placeholderFunction", "currentTimeMills");
        result.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        result.addProperty("modelControllable", false);
        result.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        return result;
    }

    private static JsonObject placeholderExpression(String function,
                                                    int count) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "PlaceholderExpression");
        result.addProperty("_java_type", "J");
        result.addProperty("_place_holder_func", function);
        result.addProperty("_count", count);
        return result;
    }

    private static JsonObject placeholderCondition(JsonElement placeholder) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.addProperty("_op", ">");
        result.add("_left", placeholder.deepCopy());
        result.add("_right", constant("Y_J_0", "J"));
        result.addProperty("_code_position",
                "virtual long example.TimeHandler.handle():12");
        return result;
    }

    private static MapFixture importGuardedNoRemoveFixture(
            Path root, JsonElement observations, JsonArray symbolize,
            JsonElement fieldObservations) throws Exception {
        String prune = "<example.Store: void prune()>";
        JsonArray canonicalFields = new JsonArray();
        JsonArray dynamicBindings = new JsonArray();
        JsonArray mappings = readGuardMappings(prune);
        if (observations != null && observations.isJsonArray()) {
            JsonObject read = null;
            for (JsonElement element : observations.getAsJsonArray()) {
                if (element.isJsonObject()
                        && "MAP_ENTRY_READ".equals(element.getAsJsonObject()
                        .get("kind").getAsString())) {
                    read = element.getAsJsonObject();
                    break;
                }
            }
            if (read != null) {
                String site = prune + "#u3";
                String dynamic = dynamicFieldSymbol(
                        "REGION.P.in.1", site, 1);
                long leafToken = read.get("valueObjectToken").getAsLong();
                if (fieldObservations != null
                        && fieldObservations.isJsonArray()
                        && fieldObservations.getAsJsonArray().size() == 1
                        && fieldObservations.getAsJsonArray().get(0)
                        .isJsonObject()
                        && fieldObservations.getAsJsonArray().get(0)
                        .getAsJsonObject().has("leafOwnerObjectToken")) {
                    leafToken = fieldObservations.getAsJsonArray().get(0)
                            .getAsJsonObject().get("leafOwnerObjectToken")
                            .getAsLong();
                }
                dynamicBindings.add(dynamicFieldBinding(dynamic, site, 1,
                        leafToken, read, read.getAsJsonObject(
                        "keyExpression")));
                canonicalFields.add(dynamicFieldObservation(dynamic, site,
                        1, leafToken, read));
                mappings = new JsonArray();
                mappings.add(branchMapping(prune, 4, 1, true,
                        symbol("M_J_field_" + dynamic
                                + "_example/Value", "J")));
            }
        }
        return importMapFixture(root, new JsonArray(), true,
                new JsonArray(), singletonString(prune),
                guardedWriteEdges(prune), observations,
                symbolize, mappings, canonicalFields, dynamicBindings);
    }

    private static JsonObject mapInputExpression() {
        return symbol("M_L_field_REGION.P.in.0_example/Store", "L");
    }

    private static JsonArray singletonString(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonInteger(int value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonObject(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray guardedWriteEdges(String method) {
        JsonArray edges = new JsonArray();
        edges.add(causalEdge("DF.WRITE.READ", method, method + "#u5",
                "HEAP_WRITE", "field_mutation"));
        edges.add(guardedMutationEdge("DF.GUARD.READ", method,
                4, 5, false));
        return edges;
    }

    private static JsonArray readGuardMappings(String method) {
        JsonArray mappings = new JsonArray();
        mappings.add(branchMapping(method, 4, 1, true,
                symbol("M_J_field_REGION.P.in.1_expiry", "J")));
        return mappings;
    }

    private static JsonArray defaultReadSymbolize() {
        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction("REGION.P.in.1", "expiry"));
        return actions;
    }

    private static JsonArray tokenFieldObservations(long ownerToken) {
        JsonObject observation = fieldObservation(
                "REGION.P.in.1", "expiry", 42);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("leafOwnerObjectToken", ownerToken);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerClass", "example.Value");
        JsonArray result = new JsonArray();
        result.add(observation);
        return result;
    }

    private static JsonObject dynamicFieldBinding(
            String dynamicSymbol, String siteId, int occurrence,
            long ownerToken, JsonObject entryRead, JsonObject keyExpression) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        binding.addProperty("baseInputSymbol", "REGION.P.in.1");
        binding.addProperty("dynamicFieldSymbol", dynamicSymbol);
        binding.addProperty("materializationSiteId", siteId);
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        binding.add("fieldPath", path);
        binding.addProperty("leafOwnerObjectToken", ownerToken);
        binding.addProperty("entryValueOwnerObjectToken",
                entryRead.get("valueObjectToken").getAsLong());
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.P");
        binding.addProperty("entryReadObservationId",
                entryRead.get("observationId").getAsString());
        binding.add("keyExpression", keyExpression.deepCopy());
        binding.addProperty("keyExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        binding.addProperty("complete", true);
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        return binding;
    }

    private static JsonObject dynamicFieldObservation(
            String dynamicSymbol, String siteId, int occurrence,
            long ownerToken, JsonObject entryRead) {
        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", dynamicSymbol);
        observation.addProperty("baseInputSymbol", "REGION.P.in.1");
        observation.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicSymbol);
        observation.addProperty("dynamicFieldSymbol", dynamicSymbol);
        observation.addProperty("materializationSiteId", siteId);
        observation.addProperty("materializationOccurrence", occurrence);
        observation.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray path = new JsonArray();
        path.add("expiry");
        observation.add("fieldPath", path.deepCopy());
        observation.add("path", path.deepCopy());
        observation.addProperty("phase", "AT_MATERIALIZATION");
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerObjectToken", ownerToken);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("accessOwnerObjectToken",
                entryRead.get("valueObjectToken").getAsLong());
        observation.addProperty("accessOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerClass", "example.Value");
        observation.addProperty("entryReadObservationId",
                entryRead.get("observationId").getAsString());
        JsonArray readIds = new JsonArray();
        readIds.add(entryRead.get("observationId").getAsString());
        observation.add("entryReadObservationIds", readIds);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("dynamicFieldBindingAuthority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        observation.addProperty("dynamicFieldBindingComplete", true);
        observation.addProperty("complete", true);
        return observation;
    }

    private static MapFixture importNonMutatingDynamicMapReadFixture(
            Path root, String mode) throws Exception {
        String method = "<example.Store: void prune()>";
        String base = "REGION.P.in.1";
        String materializationSite = method + "#u8";
        String dependencyCell =
                "<example.State: example.Guard state>"
                        + "#field:guard#field:expiry";
        String dynamic = dynamicFieldSymbol(base, materializationSite, 1);
        JsonObject key = constant("Y_I_7", "I");
        JsonObject witness = mapRefWitnessRecord();
        JsonObject read = runtimeMapEntryRead(witness.get("mapExpression"),
                key, method, 4, 0, 1, 1);
        for (java.util.Map.Entry<String, JsonElement> entry
                : witness.entrySet()) {
            read.add(entry.getKey(), entry.getValue().deepCopy());
        }
        JsonArray observations = new JsonArray();
        observations.add(read);

        JsonArray deepPath = strings("state", "guard", "expiry");
        JsonObject dynamicBinding = dynamicFieldBinding(dynamic,
                materializationSite, 1, 105L, read, key);
        dynamicBinding.add("fieldPath", deepPath.deepCopy());
        JsonArray dynamicBindings = new JsonArray();
        dynamicBindings.add(dynamicBinding);
        JsonObject fieldObservation = dynamicFieldObservation(dynamic,
                materializationSite, 1, 105L, read);
        fieldObservation.add("fieldPath", deepPath.deepCopy());
        fieldObservation.add("path", deepPath.deepCopy());
        JsonArray fieldObservations = new JsonArray();
        fieldObservations.add(fieldObservation);

        JsonObject action = fieldAccessAction(base, "expiry");
        action.addProperty("cell", dependencyCell);
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("accessMethod", method);
        action.addProperty("accessSiteId", materializationSite);
        action.addProperty("fieldPathAuthority",
                "STATIC_UNIQUE_EXACT_DIRECT_GETFIELD_CHAIN_V1");
        action.addProperty("leafFieldSignature",
                "<example.Value: long expiry>");
        action.add("fieldPath", deepPath.deepCopy());
        JsonArray actions = new JsonArray();
        actions.add(action);

        JsonObject expression = symbol("M_J_field_" + dynamic
                + "_example/Value", "J");
        JsonObject condition = binaryCondition(
                "virtual void example.Store.prune():11", ">",
                expression, constant("Y_J_0", "J"));
        JsonArray path = new JsonArray();
        path.add(condition.deepCopy());
        JsonObject mapping = branchMapping(method, 11, 1, true,
                condition);
        mapping.addProperty("vmOccurrence", 1);
        mapping.addProperty("conditionIndex", 0);
        mapping.addProperty("rawConditionIndex", 0);
        mapping.addProperty("engineConditionIndex", 0);
        mapping.addProperty("pathConditionBaseline", 0);
        mapping.addProperty("rawPathConditionBaseline", 0);
        mapping.addProperty("enginePathConditionBaseline", 0);
        mapping.addProperty("pathConditionSize", 1);
        mapping.addProperty("rawPathConditionSize", 1);
        mapping.addProperty("enginePathConditionSize", 1);
        mapping.addProperty("mappingPolicy",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
        mapping.addProperty("conditionAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
        mapping.addProperty("vmBranchEventExpected", true);
        mapping.addProperty("vmBranchEventValidated",
                !"INVALID_VM_MAPPING".equals(mode));
        mapping.addProperty("vmBranchEventId", 1);
        mapping.addProperty("vmBranchEventAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
        mapping.addProperty("vmThreadContextId", 2);
        mapping.addProperty("vmOwnerJavaThreadId", 3);
        mapping.addProperty("vmOwnerOsThreadId", 4);
        mapping.add("vmConditionIndices", singletonInteger(0));
        mapping.add("rawCondition", condition.deepCopy());
        mapping.add("condition", condition.deepCopy());
        if (!"INVALID_VM_MAPPING".equals(mode)) {
            JsonObject vmEvent = new JsonObject();
            vmEvent.addProperty("authority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
            vmEvent.addProperty("contextId", 2L);
            vmEvent.addProperty("eventId", 1L);
            vmEvent.addProperty("opcode", 153);
            vmEvent.addProperty("ownerJavaThreadId", 3L);
            vmEvent.addProperty("ownerOsThreadId", 4L);
            vmEvent.addProperty("codePosition",
                    condition.get("_code_position").getAsString());
            vmEvent.addProperty("predicateNormalization", "IDENTITY");
            mapping.add("witness", BranchWitness.vmPc(
                    method + "#u11", method, 11, 1, true,
                    condition, 0, vmEvent).toJson());
        }
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        if ("DUPLICATE_VM_MAPPING".equals(mode)) {
            JsonObject duplicate = mapping.deepCopy();
            duplicate.addProperty("vmBranchEventId", 2);
            mappings.add(duplicate);
        }

        JsonObject inputBinding = new JsonObject();
        inputBinding.addProperty("dependencyCell", dependencyCell);
        inputBinding.addProperty("inputPort", base);
        inputBinding.addProperty("bindingAuthority",
                "INVALID_SLICE_BINDING".equals(mode)
                        ? "ALIAS_HEURISTIC" : "EXACT_CELL_IDENTITY");
        inputBinding.add("dependencyMethods", singletonString(method));
        JsonObject slice = new JsonObject();
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);
        slice.add("inputBindings", singletonObject(inputBinding));
        slice.add("sites", strings(method + "#u4", materializationSite,
                method + "#u11"));
        slice.addProperty("_fixtureRequestedOutputCell",
                "<example.Output: int result>");

        JsonArray causalEdges = new JsonArray();
        causalEdges.add(causalEdge("DF.READ.NON_MUTATING", method,
                materializationSite, "HEAP_READ", "field_read"));

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(method), causalEdges,
                observations, actions, mappings, fieldObservations,
                dynamicBindings, slice, new JsonArray());
    }

    private static MapFixture importRawExpiryFallbackFixture(
            Path root, String mutation) throws Exception {
        String prune = "<example.Store: void prune()>";
        String site = "<example.Value: long getExpiry()>#u1";
        JsonObject map = mapInputExpression();
        JsonObject firstKey = symbol("entryKey1", "I");
        JsonObject secondKey = symbol("entryKey2", "I");
        JsonObject firstRead = runtimeMapEntryRead(map, firstKey, prune,
                3, 1, 1, 1);
        JsonObject secondRead = runtimeMapEntryRead(map, secondKey, prune,
                3, "DUPLICATE_RAW".equals(mutation) ? 1 : 2, 2, 2);
        secondRead.addProperty("keyObjectToken", 202L);
        secondRead.addProperty("valueObjectToken", 203L);
        secondRead.addProperty("entryObjectToken", 204L);
        JsonArray reads = new JsonArray();
        reads.add(firstRead);
        reads.add(secondRead);

        String firstDynamic = dynamicFieldSymbol("REGION.P.in.1", site, 1);
        String secondDynamic = dynamicFieldSymbol("REGION.P.in.1", site, 2);
        JsonArray bindings = new JsonArray();
        JsonObject firstBinding = dynamicFieldBinding(firstDynamic, site, 1,
                103L, firstRead, firstKey);
        bindings.add(firstBinding);
        bindings.add(dynamicFieldBinding(secondDynamic, site, 2, 203L,
                secondRead, secondKey));
        if ("DUPLICATE_DYNAMIC".equals(mutation)) {
            bindings.add(firstBinding.deepCopy());
        } else if ("WRONG_ENTRY_VALUE_OWNER".equals(mutation)) {
            firstBinding.addProperty("entryValueOwnerObjectToken", 999L);
        }
        JsonArray fields = new JsonArray();
        fields.add(dynamicFieldObservation(firstDynamic, site, 1, 103L,
                firstRead));
        fields.add(dynamicFieldObservation(secondDynamic, site, 2, 203L,
                secondRead));

        JsonObject firstExpression = symbol(
                "M_J_field_" + firstDynamic + "_example/Value", "J");
        JsonObject secondExpression = symbol(
                "M_J_field_" + secondDynamic + "_example/Value", "J");
        JsonObject candidate = binaryCondition(
                "virtual void example.Store.prune():187", ">",
                firstExpression, "DUPLICATE_RAW".equals(mutation)
                        ? secondExpression : constant("Y_J_0", "J"));
        String siblingDynamic = "DUPLICATE_RAW".equals(mutation)
                ? dynamicFieldSymbol("REGION.P.in.1", site, 3)
                : secondDynamic;
        JsonObject siblingRaw = binaryCondition(
                "virtual void example.Store.prune():187", ">",
                symbol("M_J_field_" + siblingDynamic
                        + "_example/Value", "J"), constant("Y_J_0", "J"));
        JsonObject siblingSemantic = siblingRaw.deepCopy();
        siblingSemantic.addProperty("_op",
                "MALFORMED_OPERATOR".equals(mutation) ? "" : ">=");
        JsonArray path = new JsonArray();
        path.add(binaryCondition(
                "virtual void example.Store.prune():185", "!=",
                symbol("hasNext", "Z"), constant("Y_I_0", "I")));
        path.add(candidate);
        path.add(siblingRaw);

        JsonArray mappings = new JsonArray();
        mappings.add(unmappedBranchMapping(prune, 4, 1, 0, 2));
        if ("DUPLICATE_RAW".equals(mutation)) {
            mappings.add(unmappedBranchMapping(prune, 4, 2, 0, 2));
        }
        JsonObject sibling = branchMapping(prune, 4,
                "DUPLICATE_RAW".equals(mutation) ? 3 : 2,
                true, siblingSemantic);
        sibling.addProperty("conditionIndex", 2);
        sibling.addProperty("rawConditionIndex", 2);
        sibling.addProperty("engineConditionIndex", 2);
        sibling.add("rawCondition", siblingRaw.deepCopy());
        sibling.addProperty("conditionCodePosition",
                "virtual void example.Store.prune():187");
        sibling.addProperty("conditionNormalization",
                "JVM_CMP_TRICHOTOMY_TO_JIMPLE_BRANCH_PREDICATE");
        mappings.add(sibling);

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(prune), guardedWriteEdges(prune),
                reads, defaultReadSymbolize(), mappings,
                fields, bindings);
    }

    private static JsonObject unmappedBranchMapping(
            String method, int unit, int occurrence,
            int baseline, int boundary) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", method + "#u" + unit);
        mapping.addProperty("method", method);
        mapping.addProperty("unitIndex", unit);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        mapping.addProperty("observedOutcome", true);
        mapping.addProperty("conditionIndex", -1);
        mapping.addProperty("rawConditionIndex", -1);
        mapping.addProperty("rawPathConditionBaseline", baseline);
        mapping.addProperty("enginePathConditionBaseline", baseline);
        mapping.addProperty("rawPathConditionSize", boundary);
        mapping.addProperty("enginePathConditionSize", boundary);
        return mapping;
    }

    private static JsonObject binaryCondition(
            String codePosition, String operator,
            JsonElement left, JsonElement right) {
        JsonObject condition = new JsonObject();
        condition.addProperty("_code_position", codePosition);
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_op", operator);
        condition.add("_left", left.deepCopy());
        condition.add("_right", right.deepCopy());
        return condition;
    }

    private static String dynamicFieldSymbol(String base, String siteId,
                                             int occurrence)
            throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] bytes = digest.digest(siteId.getBytes(StandardCharsets.UTF_8));
        StringBuilder hash = new StringBuilder();
        for (byte item : bytes) {
            hash.append(String.format("%02x", item & 0xff));
        }
        return base + ".field." + hash.substring(0, 12) + ".occ."
                + occurrence;
    }

    private static MapFixture importContainerDynamicFixture(
            Path root, String mutation) throws Exception {
        String base = "REGION.P.in.1";
        String containerPort = "REGION.P.in.2";
        String field = "<example.Value: long expiry>";
        String containerCell =
                "<example.Envelope: example.Value[] values>";
        String site = "<example.Store: void update()>#u6";
        int occurrence = 1;
        int elementIndex = 2;
        String dynamic = dynamicFieldSymbol(base, site, occurrence);

        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction(base, "expiry"));
        JsonObject containerAction = new JsonObject();
        containerAction.addProperty("symbol", containerPort);
        containerAction.addProperty("bindingMode", "FIELD_ACCESS");
        containerAction.addProperty("field", containerCell);
        containerAction.addProperty("cell", containerCell);
        containerAction.add("fieldPath",
                JsonParser.parseString("[\"values\"]"));
        actions.add(containerAction);

        boolean discovery = "VALID_DISCOVERY".equals(mutation);
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", "CONTAINER.FIELD.0");
        declaration.addProperty("baseInputSymbol", base);
        declaration.addProperty("containerInputPort", containerPort);
        declaration.addProperty("containerInputCell", containerCell);
        declaration.addProperty("selectorAuthority", discovery
                ? "DISCOVER_UNIQUE_IDENTITY_INDEX" : "EXACT_ARRAY_INDEX");
        declaration.addProperty("elementIndex",
                discovery ? -1 : elementIndex);
        declaration.addProperty("elementOccurrence",
                discovery ? -1 : occurrence);
        declaration.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        declaration.addProperty("fieldMaterializationSiteId", site);
        declaration.addProperty("declaredFieldOwnerClass",
                "example.Value");
        declaration.addProperty("declaredFieldType", "long");
        JsonArray declarations = singletonObject(declaration);

        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "CONTAINER.FIELD.0");
        selector.addProperty("containerInputPort", containerPort);
        selector.addProperty("containerInputCell", containerCell);
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority", discovery
                ? "DISCOVER_UNIQUE_IDENTITY_INDEX" : "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", elementIndex);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("containerObjectToken", 201L);
        selector.addProperty("elementObjectToken", 202L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.P");
        selector.addProperty("containerObservationLocation",
                "FIELD_ACCESS");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);

        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        binding.addProperty("baseInputSymbol", base);
        binding.addProperty("dynamicFieldSymbol", dynamic);
        binding.addProperty("materializationSiteId", site);
        binding.addProperty("materializationOccurrence", occurrence);
        addContainerSiteBridge(binding, site, occurrence,
                "CONTAINER.FIELD.0", 202L);
        binding.addProperty("fieldSignature", field);
        binding.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        binding.addProperty("leafOwnerObjectToken", 202L);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope", "ACT.P");
        binding.add("containerSelector", selector.deepCopy());
        addContainerSelectorFlatFields(binding, selector);
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                        + "AND_STABLE_FIELD_SITE_OCCURRENCE");
        binding.addProperty("complete", true);
        JsonArray bindings = singletonObject(binding);

        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", dynamic);
        observation.addProperty("phase", "AT_MATERIALIZATION");
        observation.add("path",
                JsonParser.parseString("[\"expiry\"]"));
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerObjectToken", 202L);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("baseInputSymbol", base);
        observation.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        observation.addProperty("dynamicFieldSymbol", dynamic);
        observation.addProperty("materializationSiteId", site);
        observation.addProperty("materializationOccurrence", occurrence);
        addContainerSiteBridge(observation, site, occurrence,
                "CONTAINER.FIELD.0", 202L);
        observation.addProperty("dynamicFieldBindingSchemaVersion", 2);
        observation.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        observation.addProperty("fieldSignature", field);
        observation.add("fieldPath",
                JsonParser.parseString("[\"expiry\"]"));
        observation.add("containerSelector", selector.deepCopy());
        addContainerSelectorFlatFields(observation, selector);
        observation.addProperty("dynamicFieldBindingAuthority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                        + "AND_STABLE_FIELD_SITE_OCCURRENCE");
        observation.addProperty("dynamicFieldBindingComplete", true);
        observation.addProperty("complete", true);
        JsonArray observations = singletonObject(observation);

        JsonArray mappings = new JsonArray();
        JsonObject consumerKey = symbol(
                "M_J_field_" + dynamic + "_example/Value", "J");
        JsonArray semanticPath = new JsonArray();
        semanticPath.add(methodExpression("java/util/HashMap put", 19,
                mapInputExpression(), consumerKey.deepCopy(),
                symbol("putValue", "example/Value")));
        mappings.add(branchMapping("<example.Store: void update()>", 6,
                occurrence, true, symbol(
                        "M_J_field_" + dynamic + "_expiry", "J")));

        if ("WRONG_DECLARATION".equals(mutation)) {
            declaration.remove("fieldMaterializationSiteId");
        } else if ("WRONG_INDEX".equals(mutation)) {
            binding.getAsJsonObject("containerSelector").addProperty(
                    "elementIndex", elementIndex + 1);
        } else if ("WRONG_CELL".equals(mutation)) {
            declaration.addProperty("containerInputCell",
                    "<example.Envelope: example.Value[] other>");
        } else if ("WRONG_TOKEN".equals(mutation)) {
            binding.addProperty("leafOwnerObjectToken", 999L);
        } else if ("WRONG_SCOPE".equals(mutation)) {
            binding.addProperty("objectTokenScope", "ACT.OTHER");
        } else if ("DUPLICATE".equals(mutation)) {
            bindings.add(binding.deepCopy());
        } else if ("MIXED_MAP_SELECTOR".equals(mutation)) {
            binding.addProperty("entryReadObservationId", "MAP.READ.0");
            binding.add("keyExpression", symbol("entryKey", "I"));
        } else if ("MISSING_OBSERVATION".equals(mutation)) {
            observations = new JsonArray();
        } else if ("MISSING_MAP_PUT_CONSUMER".equals(mutation)) {
            semanticPath = new JsonArray();
        } else if ("WRONG_BRIDGE_AUTHORITY".equals(mutation)) {
            binding.addProperty("materializationSiteBridgeAuthority",
                    "UNTRUSTED_BRIDGE");
        } else if ("WRONG_ACTUAL_HOOK_SITE".equals(mutation)) {
            binding.addProperty("actualHookSiteId", "not-a-hook-site");
        } else if ("AMBIGUOUS_MAP_PUT_CONSUMER".equals(mutation)) {
            semanticPath.add(methodExpression("java/util/HashMap put", 20,
                    mapInputExpression(), consumerKey.deepCopy(),
                    symbol("putValue2", "example/Value")));
        }

        return importMapFixture(root, semanticPath, true,
                new JsonArray(), new JsonArray(), new JsonArray(), null,
                actions, mappings, observations, bindings, null,
                new JsonArray(), declarations);
    }

    private static void addContainerSiteBridge(
            JsonObject target, String effectiveSite,
            int effectiveOccurrence, String bindingId,
            long elementObjectToken) {
        target.addProperty("actualHookSiteId", effectiveSite);
        target.addProperty("actualHookOccurrence", effectiveOccurrence);
        target.addProperty("effectiveMaterializationSiteId",
                effectiveSite);
        target.addProperty("effectiveMaterializationOccurrence",
                effectiveOccurrence);
        target.addProperty("materializationSiteBridgeAuthority",
                "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_"
                        + "ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1");
        target.addProperty("materializationSiteBridgeBindingId", bindingId);
        target.addProperty(
                "materializationSiteBridgeElementObjectToken",
                elementObjectToken);
        target.addProperty("materializationSiteBridgeObjectTokenScope",
                "ACT.P");
    }

    private static void addContainerSelectorFlatFields(
            JsonObject target, JsonObject selector) {
        target.addProperty("containerBindingId",
                selector.get("bindingId").getAsString());
        target.addProperty("containerInputPort",
                selector.get("containerInputPort").getAsString());
        target.addProperty("containerInputCell",
                selector.get("containerInputCell").getAsString());
        target.addProperty("selectorAuthority",
                selector.get("selectorAuthority").getAsString());
        target.addProperty("resolvedFromSelectorAuthority",
                selector.get("resolvedFromSelectorAuthority").getAsString());
        target.addProperty("elementIndex",
                selector.get("elementIndex").getAsInt());
        target.addProperty("elementOccurrence",
                selector.get("elementOccurrence").getAsInt());
        target.addProperty("declaredFieldOwnerClass",
                selector.get("declaredFieldOwnerClass").getAsString());
        target.addProperty("declaredFieldType",
                selector.get("declaredFieldType").getAsString());
    }

    private static JsonObject inputAction(String symbol, String cell) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("field", cell);
        return action;
    }

    private static JsonObject runtimeMapEntryRead(
            JsonElement mapExpression, JsonElement keyExpression,
            String originMethod, int originUnitIndex, int pcBoundary,
            int occurrence, long eventSequence) {
        String siteId = originMethod + "#u" + originUnitIndex;
        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("operation", "java.util.Iterator.next");
        observation.addProperty("observationId",
                "MAP_ENTRY_READ:" + siteId + "#" + occurrence);
        observation.addProperty("eventSequence", eventSequence);
        observation.addProperty("occurrence", occurrence);
        observation.addProperty("originMethod", originMethod);
        observation.addProperty("originUnitIndex", originUnitIndex);
        observation.addProperty("siteId", siteId);
        observation.addProperty("viewKind", "ENTRY_SET");
        observation.addProperty("rawPathConditionBoundary", pcBoundary);
        observation.addProperty("pcBoundary", pcBoundary);
        observation.addProperty("provenanceAuthority",
                "ACTIVATION_LOCAL_BACKED_ENTRY_SET_IDENTITY_AT_NEXT");
        observation.addProperty("mapBindingAuthority",
                "BOUND_ENTRY_SET_VIEW_BACKING_MAP_IDENTITY");
        observation.addProperty("entryBindingAuthority",
                "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT");
        observation.addProperty("keyBindingAuthority",
                "SAME_MAP_ENTRY_GET_KEY_AT_NEXT");
        observation.addProperty("valueBindingAuthority",
                "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT");
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("expressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        observation.addProperty("keyExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT");
        observation.addProperty("valueExpressionAuthority",
                "AFTER_MATCHED_FIELD_SYMBOLIZATION");
        observation.addProperty("backingMapObjectToken", 101L);
        observation.addProperty("backingMapObjectTokenKnown", true);
        observation.addProperty("entryObjectToken", 104L);
        observation.addProperty("entryObjectTokenKnown", true);
        observation.addProperty("entryWasNull", false);
        observation.addProperty("keyObjectToken", 102L);
        observation.addProperty("keyObjectTokenKnown", true);
        observation.addProperty("keyWasNull", false);
        observation.addProperty("valueObjectToken", 103L);
        observation.addProperty("valueObjectTokenKnown", true);
        observation.addProperty("valueWasNull", false);
        observation.add("mapExpression", mapExpression.deepCopy());
        observation.add("keyExpression", keyExpression.deepCopy());
        observation.add("valueExpression",
                symbol("expiredValue", "example/Value"));
        observation.addProperty("entryBindingComplete", true);
        observation.addProperty("expressionBindingComplete", true);
        observation.addProperty("objectTokenBindingComplete", true);
        observation.addProperty("bindingAuthorityComplete", true);
        observation.addProperty("runtimeProvenanceComplete", true);
        observation.addProperty("complete", true);
        return observation;
    }

    private static JsonObject runtimeFiniteMapEntrySnapshot(
            JsonElement mapExpression, JsonElement keyExpression,
            String originMethod, int originUnitIndex, int occurrence,
            long eventSequence) {
        String siteId = originMethod + "#u" + originUnitIndex;
        JsonObject valueExpression = new JsonObject();
        valueExpression.addProperty("_type", "SymbolExpression");
        valueExpression.addProperty("_java_type", "L");
        valueExpression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103");
        JsonObject entry = new JsonObject();
        entry.addProperty("index", 0);
        entry.add("keyExpression", keyExpression.deepCopy());
        entry.addProperty("keyObjectToken", 102L);
        entry.add("valueExpression", valueExpression.deepCopy());
        entry.addProperty("valueObjectToken", 103L);
        entry.addProperty("valueWasNull", false);
        entry.addProperty("valueExpressionAuthority",
                "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1");

        JsonObject snapshot = new JsonObject();
        snapshot.addProperty("schemaVersion", 1);
        snapshot.addProperty("kind", "FINITE_MAP_ENTRY_SNAPSHOT");
        snapshot.addProperty("operation", "java.util.Map.entrySet");
        snapshot.addProperty("observationId",
                "FINITE_MAP_ENTRY_SNAPSHOT:" + siteId + "#" + occurrence);
        snapshot.addProperty("eventSequence", eventSequence);
        snapshot.addProperty("eventSequenceAuthority",
                "SAME_ITERATOR_NEXT_AS_MAP_ENTRY_READ");
        snapshot.addProperty("originMethod", originMethod);
        snapshot.addProperty("originUnitIndex", originUnitIndex);
        snapshot.addProperty("siteId", siteId);
        snapshot.addProperty("viewKind", "ENTRY_SET");
        snapshot.addProperty("viewOriginSiteId", originMethod + "#u1");
        snapshot.addProperty("iteratorOriginSiteId", originMethod + "#u2");
        snapshot.addProperty("mapImplementationClass",
                "java.util.HashMap");
        snapshot.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        snapshot.addProperty("mapObjectToken", 101L);
        snapshot.addProperty("backingMapObjectToken", 101L);
        snapshot.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        snapshot.addProperty("objectTokenScope", "ACT.P");
        snapshot.add("mapExpression", mapExpression.deepCopy());
        snapshot.addProperty("mapExpressionAuthority",
                "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_FIRST_ENTRY_SET_NEXT");
        snapshot.addProperty("entryCount", 1);
        snapshot.addProperty("finiteEntryBound", 4096);
        snapshot.addProperty("sizeBefore", 1);
        snapshot.addProperty("entrySetSizeBefore", 1);
        snapshot.addProperty("sizeAfter", 1);
        snapshot.addProperty("entrySetSizeAfter", 1);
        JsonArray keys = new JsonArray();
        keys.add(keyExpression.deepCopy());
        snapshot.add("keyExpressions", keys);
        JsonArray keyTokens = new JsonArray();
        keyTokens.add(102L);
        snapshot.add("keyObjectTokens", keyTokens);
        snapshot.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEYS_AT_SAME_EXECUTION_"
                        + "ENTRY_SET_SNAPSHOT");
        JsonArray valueTokens = new JsonArray();
        valueTokens.add(103L);
        snapshot.add("valueObjectTokens", valueTokens);
        JsonArray values = new JsonArray();
        values.add(valueExpression.deepCopy());
        snapshot.add("valueExpressions", values);
        snapshot.addProperty("valueExpressionAuthority",
                "PER_ENTRY_EXACT_RUNTIME_NULL_OR_ACTIVATION_LOCAL_OBJECT_"
                        + "TOKEN_REF_WITNESS_V1");
        JsonArray entries = new JsonArray();
        entries.add(entry);
        snapshot.add("entries", entries);
        snapshot.addProperty("keysDistinct", true);
        snapshot.addProperty("firstIteratorEntryMatched", true);
        snapshot.addProperty("sizeStable", true);
        snapshot.addProperty("entrySetStable", true);
        snapshot.addProperty("authority",
                "FIRST_BOUND_ENTRY_SET_ITERATOR_NEXT_EXACT_HASHMAP_OR_"
                        + "LINKEDHASHMAP_SAME_EXECUTION_AT_ITERATOR_NEXT_"
                        + "STABLE_SIZE_"
                        + "AND_ENTRY_SET_DISTINCT_IMMUTABLE_KEYS_V1");
        snapshot.addProperty("complete", true);
        return snapshot;
    }

    private static MapFixture importMapFixture(Path root, JsonArray path)
            throws Exception {
        return importMapFixture(root, path, true, new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, new JsonArray(), new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                null, new JsonArray(), null, null, null,
                null, new JsonArray(), null, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                null, additionalSymbolize, branchMappings,
                fieldObservations, null, null, new JsonArray(), null,
                null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, null, new JsonArray());
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, sliceMetadata,
                omittedSymbolizedInputs, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs,
                                               JsonElement containerBindings)
            throws Exception {
        return importMapFixture(root, path, existingMapInput,
                heapInitializers, sliceMethods, causalEdges,
                runtimeHeapObservations,
                additionalSymbolize, branchMappings, fieldObservations,
                dynamicFieldBindings, sliceMetadata,
                omittedSymbolizedInputs, containerBindings, null);
    }

    private static MapFixture importMapFixture(Path root, JsonArray path,
                                               boolean existingMapInput,
                                               JsonArray heapInitializers,
                                               JsonArray sliceMethods,
                                               JsonArray causalEdges,
                                               JsonElement runtimeHeapObservations,
                                               JsonArray additionalSymbolize,
                                               JsonElement branchMappings,
                                               JsonElement fieldObservations,
                                               JsonElement dynamicFieldBindings,
                                               JsonObject sliceMetadata,
                                               JsonArray omittedSymbolizedInputs,
                                               JsonElement containerBindings,
                                               JsonElement engineArrayBindings)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.Store: void update()>";
        String cell = "<example.Store: java.util.Map data>";
        JsonElement authorizedBranchMappings =
                authorizeRawBranchMappingsForTest(branchMappings, path);
        if (sliceMetadata != null
                && sliceMetadata.has("_fixtureRequestedOutputCell")) {
            cell = sliceMetadata.get("_fixtureRequestedOutputCell")
                    .getAsString();
        }
        if (sliceMetadata != null
                && sliceMetadata.has(
                "captureDischargedByHeapEffectTransformer")
                && sliceMetadata.get(
                "captureDischargedByHeapEffectTransformer")
                .getAsBoolean()
                && sliceMetadata.has("captureDischargeOutputCell")) {
            cell = sliceMetadata.get("captureDischargeOutputCell")
                    .getAsString();
        }

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P");
        activation.addProperty("regionId", "REGION.P");
        activation.addProperty("regionInstanceId",
                "REGION.P@fixture#call10");
        activation.addProperty("rootCallId", 10);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("rootMethod", method);
        JsonArray requestedOutputMethods = new JsonArray();
        requestedOutputMethods.add(method);
        for (JsonElement sliceMethod : sliceMethods) {
            if (sliceMethod.isJsonPrimitive()
                    && !containsString(requestedOutputMethods,
                    sliceMethod.getAsString())) {
                requestedOutputMethods.add(sliceMethod.getAsString());
            }
        }
        activation.add("requestedOutputMethods", requestedOutputMethods);
        JsonArray symbolize = new JsonArray();
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.P.in.0");
        input.addProperty("cell", cell);
        input.addProperty("field", cell);
        if (existingMapInput) {
            symbolize.add(input);
        }
        for (JsonElement action : additionalSymbolize) {
            symbolize.add(action.deepCopy());
        }
        if (containerBindings != null) {
            // Production plans retain the raw static actions in symbolize
            // and publish the runtime-executable FIELD_ACCESS refinements in
            // materializations.  The importer must mirror the runtime's
            // prefer-refined contract instead of inspecting the raw action.
            activation.add("materializations", symbolize.deepCopy());
            JsonArray rawSymbolize = symbolize.deepCopy();
            for (JsonElement element : rawSymbolize) {
                if (element.isJsonObject()) {
                    element.getAsJsonObject().remove("bindingMode");
                }
            }
            activation.add("symbolize", rawSymbolize);
            activation.add("containerElementFieldBindings",
                    containerBindings.deepCopy());
        } else {
            activation.add("symbolize", symbolize);
        }
        JsonArray outputs = new JsonArray();
        JsonObject outputPort = new JsonObject();
        outputPort.addProperty("symbol", "REGION.P.out.0");
        outputPort.addProperty("cell", cell);
        outputPort.addProperty("kind", "HEAP_STATE");
        outputPort.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        outputs.add(outputPort);
        activation.add("outputs", outputs);
        JsonObject requestedOutput = new JsonObject();
        requestedOutput.addProperty("portId", "REGION.P.out.0");
        requestedOutput.addProperty("cell", cell);
        requestedOutput.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requestedOutput);
        if (sliceMetadata != null && sliceMetadata.has(
                "captureDischargedByHeapEffectTransformer")
                && sliceMetadata.get(
                "captureDischargedByHeapEffectTransformer")
                .getAsBoolean()) {
            activation.addProperty("requestedOutputCaptureRequired", false);
            activation.addProperty("requestedOutputCaptureComplete", true);
            activation.add("requestedOutputCapture", new JsonArray());
            JsonObject heapBinding = new JsonObject();
            heapBinding.addProperty("inputPort", "REGION.P.in.0");
            heapBinding.addProperty("outputPort", "REGION.P.out.0");
            heapBinding.addProperty("cell", cell);
            heapBinding.addProperty("bindingAuthority",
                    "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM");
            JsonArray heapBindings = new JsonArray();
            heapBindings.add(heapBinding);
            activation.add("heapStateBindings", heapBindings);
        }
        JsonObject requestedOutputSlice = new JsonObject();
        requestedOutputSlice.addProperty("outputPort", "REGION.P.out.0");
        requestedOutputSlice.addProperty("outputCell", cell);
        requestedOutputSlice.addProperty("complete", true);
        JsonArray sliceInputs = new JsonArray();
        if (existingMapInput) sliceInputs.add("REGION.P.in.0");
        for (JsonElement action : additionalSymbolize) {
            if (action.isJsonObject()
                    && action.getAsJsonObject().has("symbol")) {
                sliceInputs.add(action.getAsJsonObject().get("symbol")
                        .getAsString());
            }
        }
        requestedOutputSlice.add("inputPorts", sliceInputs);
        requestedOutputSlice.add("heapInitializers",
                heapInitializers.deepCopy());
        if (sliceMethods.size() > 0) {
            requestedOutputSlice.add("methods", sliceMethods.deepCopy());
        }
        if (causalEdges.size() > 0) {
            requestedOutputSlice.add("causalEdges", causalEdges.deepCopy());
        }
        if (sliceMetadata != null) {
            for (java.util.Map.Entry<String, JsonElement> entry
                    : sliceMetadata.entrySet()) {
                if (entry.getKey().startsWith("_fixture")) continue;
                requestedOutputSlice.add(entry.getKey(),
                        entry.getValue().deepCopy());
            }
        }
        if (containerBindings != null
                && containerBindings.isJsonArray()) {
            requestedOutputSlice.add("containerElementFieldBindings",
                    containerBindings.deepCopy());
        }
        activation.add("requestedOutputSlice", requestedOutputSlice);
        activation.add("branches", branchPoliciesForTest(
                authorizedBranchMappings));
        JsonArray edgeBindings = new JsonArray();
        JsonObject edgeBinding = new JsonObject();
        edgeBinding.addProperty("edgeId", "EDGE.P");
        edgeBinding.addProperty("writerEventSeq", 10);
        edgeBinding.addProperty("readerEventSeq", 20);
        edgeBindings.add(edgeBinding);
        activation.add("edgeBindings", edgeBindings);
        write(activations, activation.toString() + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.P");
        region.addProperty("rootMethod", method);
        JsonArray methods = new JsonArray();
        methods.add(method);
        methods.add("<example.Unrelated: void touch()>");
        region.add("methods", methods);
        region.add("branchPolicies", branchPoliciesForTest(
                authorizedBranchMappings));
        write(regions, region.toString() + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.P");
        raw.addProperty("regionId", "REGION.P");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        JsonArray symbolizedInputs = new JsonArray();
        if (existingMapInput && !containsString(omittedSymbolizedInputs,
                "REGION.P.in.0")) {
            symbolizedInputs.add("REGION.P.in.0.selectedField");
        }
        for (JsonElement action : additionalSymbolize) {
            if (action.isJsonObject()
                    && action.getAsJsonObject().has("symbol")) {
                String symbol = action.getAsJsonObject().get("symbol")
                        .getAsString();
                if (!containsString(omittedSymbolizedInputs, symbol)) {
                    symbolizedInputs.add(symbol);
                }
            }
        }
        raw.add("symbolizedInputs", symbolizedInputs);
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.P");
        engine.addProperty("activationId", "ACT.P");
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        if (runtimeHeapObservations != null) {
            raw.add("runtimeHeapObservations",
                    runtimeHeapObservations.deepCopy());
        }
        if (authorizedBranchMappings != null) {
            raw.add("branchMappings",
                    authorizedBranchMappings.deepCopy());
        }
        if (fieldObservations != null) {
            raw.add("fieldObservations", fieldObservations.deepCopy());
        }
        if (dynamicFieldBindings != null) {
            raw.add("dynamicFieldBindings",
                    dynamicFieldBindings.deepCopy());
        }
        if (engineArrayBindings != null) {
            raw.add("engineArrayInputBindings",
                    engineArrayBindings.deepCopy());
        }
        write(results, raw.toString() + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics);
        String summaryRows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = summaryRows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(summaryRows).getAsJsonObject();
        String diagnosticRows = readOptional(diagnostics);
        return new MapFixture(summary, diagnosticRows);
    }

    private static boolean containsString(JsonArray values, String value) {
        if (values == null) {
            return false;
        }
        for (JsonElement element : values) {
            if (element.isJsonPrimitive()
                    && value.equals(element.getAsString())) {
                return true;
            }
        }
        return false;
    }

    private static MapFixture importObservedMapStateFixture(
            Path root, boolean identityComplete, boolean snapshotComplete)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.Store: void update()>";
        String site = method + "#u5";
        String mapCell = "<example.Store: java.util.Map data>";
        String containerCell = "<example.Batch: example.Value[] values>";
        String authority =
                "FIRST_MATCHING_CONTAINER_INSTANCE_APPROXIMATION_V1";

        JsonObject mapAction = observedContainerAction("REGION.P.in.0",
                mapCell, "MAP_STATE_INPUT_OBSERVATION", authority);
        JsonObject containerAction = observedContainerAction(
                "REGION.P.in.1", containerCell,
                "CONTAINER_INPUT_OBSERVATION", authority);
        JsonArray actions = new JsonArray();
        actions.add(mapAction);
        actions.add(containerAction);

        JsonObject edge = causalEdge("DF.MAP.WRITE", method, site,
                "HEAP_WRITE", "field_mutation");
        edge.addProperty("invoke",
                "<java.util.Map: java.lang.Object put(java.lang.Object,"
                        + "java.lang.Object)>");
        edge.addProperty("fromCell", method + "::$r1");
        edge.addProperty("toCell", mapCell);
        JsonObject obligation = exactTransformerObligation(
                "DF.MAP.WRITE", method, site, mapCell);
        JsonObject slice = exactTransformerSliceMetadata(mapCell,
                singletonObject(obligation), new JsonArray());
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.P.out.0");
        slice.addProperty("outputPort", "REGION.P.out.0");
        slice.addProperty("outputCell", mapCell);
        JsonArray inputPorts = new JsonArray();
        inputPorts.add("REGION.P.in.0");
        inputPorts.add("REGION.P.in.1");
        slice.add("inputPorts", inputPorts);
        slice.add("causalEdges", singletonObject(edge));
        slice.add("causalEdgeIds", singletonString("DF.MAP.WRITE"));
        slice.add("methods", singletonString(method));
        slice.add("staticSites", singletonString(site));
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);
        slice.addProperty("complete", true);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.P");
        activation.addProperty("regionId", "REGION.P");
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.add("requestedOutputMethods", singletonString(method));
        activation.add("materializations", actions);
        activation.add("symbolize", actions.deepCopy());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        requested.addProperty("cell", mapCell);
        requested.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.P.out.0");
        outputAction.addProperty("cell", mapCell);
        outputAction.addProperty("kind", "HEAP_STATE");
        activation.add("outputs", singletonObject(outputAction));
        JsonObject heapBinding = new JsonObject();
        heapBinding.addProperty("inputPort", "REGION.P.in.0");
        heapBinding.addProperty("outputPort", "REGION.P.out.0");
        heapBinding.addProperty("cell", mapCell);
        heapBinding.addProperty("bindingAuthority",
                "STATIC_CELL_IDENTITY_PLUS_RUNTIME_READ_FROM");
        activation.add("heapStateBindings", singletonObject(heapBinding));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.P");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        write(regions, region + "\n");

        JsonObject mapObservation = observedEmptyMapState(
                mapAction, method + "#u1", authority,
                identityComplete, snapshotComplete);
        JsonArray approximations = new JsonArray();
        approximations.add(firstContainerEvidence("REGION.P.in.0",
                mapCell, method + "#u1", authority, 2));
        approximations.add(firstContainerEvidence("REGION.P.in.1",
                containerCell, "<example.Batch: example.Value[] get()>#u1",
                authority, 5));
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.P");
        raw.addProperty("regionId", "REGION.P");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("symbolizedInputs", new JsonArray());
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("runtimeApproximations", approximations);
        raw.add("runtimeHeapObservations",
                singletonObject(mapObservation));
        raw.add("finalFieldObservations", singletonObject(
                observedMapAtExit(mapObservation)));
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.P");
        engine.addProperty("activationId", "ACT.P");
        JsonArray path = new JsonArray();
        path.add(methodExpression("java/util/HashMap put", 42,
                symbol("M_L'java/util/HashMap'_25", "java/util/HashMap"),
                symbol("key", "I"), symbol("value", "example/Value")));
        engine.add("pathCondition", path);
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics);
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new MapFixture(summary, readOptional(diagnostics));
    }

    private static MapFixture importObservedMapMutationFixture(
            Path root, JsonObject mutation, String invoke,
            boolean duplicateCausalEdge) throws Exception {
        importObservedMapStateFixture(root, true, true);

        Path activations = root.resolve("activation.jsonl");
        JsonObject activation = JsonParser.parseString(new String(
                Files.readAllBytes(activations), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        JsonArray causalEdges = activation.getAsJsonObject(
                "requestedOutputSlice").getAsJsonArray("causalEdges");
        JsonObject edge = causalEdges.get(0).getAsJsonObject();
        if (invoke == null) {
            edge.remove("invoke");
        } else {
            edge.addProperty("invoke", invoke);
        }
        if (duplicateCausalEdge) {
            causalEdges.add(edge.deepCopy());
        }
        write(activations, activation + "\n");

        Path results = root.resolve("results.jsonl");
        JsonObject raw = JsonParser.parseString(new String(
                Files.readAllBytes(results), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        raw.getAsJsonObject("engineSummary").add("pathCondition",
                singletonObject(mutation));
        write(results, raw + "\n");

        Path output = root.resolve("mutation-summaries.jsonl");
        Path diagnostics = root.resolve("mutation-diagnostics.jsonl");
        ConcolicSummaryImporter.importSummaries(results, activations,
                root.resolve("regions.jsonl"), output, diagnostics);
        JsonObject summary = JsonParser.parseString(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        return new MapFixture(summary, readOptional(diagnostics));
    }

    private static JsonObject observedContainerAction(
            String symbol, String cell, String mode, String authority) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("cell", cell);
        action.addProperty("field", cell);
        action.addProperty("observed", true);
        action.addProperty("bindingMode", mode);
        action.addProperty("modelControllable", false);
        action.addProperty("containerObservationAuthority", authority);
        return action;
    }

    private static JsonObject firstContainerEvidence(
            String symbol, String cell, String site, String authority,
            long token) {
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind",
                "BOUNDED_CONTAINER_INPUT_OBSERVATION");
        evidence.addProperty("authority", authority);
        evidence.addProperty("inputSymbol", symbol);
        evidence.addProperty("inputCell", cell);
        evidence.addProperty("siteId", site);
        evidence.addProperty("outcome",
                "FIRST_MATCHING_CONTAINER_SELECTED");
        evidence.addProperty("selectedObjectToken", token);
        evidence.addProperty("complete", true);
        return evidence;
    }

    private static JsonObject observedEmptyMapState(
            JsonObject action, String site, String authority,
            boolean identityComplete, boolean snapshotComplete) {
        JsonObject observation = new JsonObject();
        String symbol = action.get("symbol").getAsString();
        String cell = action.get("cell").getAsString();
        int marker = site.lastIndexOf("#u");
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_STATE_INPUT_OBSERVATION");
        observation.addProperty("symbol", symbol);
        observation.addProperty("phase", "AT_MAP_STATE_INPUT");
        observation.add("path", singletonString("data"));
        observation.addProperty("available", true);
        observation.addProperty("accessOwnerObjectToken", 3);
        observation.addProperty("accessOwnerObjectTokenKnown", true);
        observation.addProperty("leafOwnerObjectToken", 3);
        observation.addProperty("leafOwnerObjectTokenKnown", true);
        observation.addProperty("valueClass", "java.util.HashMap");
        observation.addProperty("valueObjectToken", 2);
        observation.addProperty("valueObjectTokenKnown", true);
        observation.addProperty("collectionSize", 0);
        observation.addProperty("observationId",
                "MAP_STATE_INPUT:" + site + "#" + symbol);
        observation.addProperty("eventSequence", 1);
        observation.addProperty("originMethod", site.substring(0, marker));
        observation.addProperty("originUnitIndex", Integer.parseInt(
                site.substring(marker + 2)));
        observation.addProperty("siteId", site);
        observation.addProperty("inputSymbol", symbol);
        observation.addProperty("inputCell", cell);
        observation.addProperty("bindingMode",
                "MAP_STATE_INPUT_OBSERVATION");
        observation.addProperty("selectionAuthority", authority);
        observation.addProperty("modelControllable", false);
        observation.addProperty("vmReferenceSymbolized", false);
        observation.addProperty("mapImplementationClass",
                "java.util.HashMap");
        observation.addProperty("mapObjectToken", 2);
        observation.addProperty("backingMapObjectToken", 2);
        observation.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observation.addProperty("objectTokenScope", "ACT.P");
        observation.addProperty("identityBindingComplete",
                identityComplete);
        observation.addProperty("entryCount", 0);
        observation.addProperty("finiteEntryBound", 4096);
        observation.add("keyExpressions", new JsonArray());
        observation.add("valueObjectTokens", new JsonArray());
        observation.add("entries", new JsonArray());
        observation.addProperty("snapshotComplete", snapshotComplete);
        observation.addProperty("snapshotAuthority",
                "SAME_FIELD_HOOK_STABLE_BOUNDED_ENTRY_SET_SNAPSHOT_V1");
        observation.addProperty("complete", true);
        observation.addProperty("mapStateInputSymbol", symbol);
        observation.addProperty("mapStateInputCell", cell);
        observation.addProperty("mapStateInputObservationId",
                observation.get("observationId").getAsString());
        observation.addProperty("mapStateInputObjectToken", 2);
        observation.addProperty("mapStateInputBindingAuthority", authority);
        observation.addProperty("mapStateInputBindingComplete", true);
        return observation;
    }

    private static JsonObject observedMapAtExit(JsonObject input) {
        JsonObject exit = new JsonObject();
        exit.addProperty("symbol", input.get("symbol").getAsString());
        exit.addProperty("phase", "AT_REGION_EXIT");
        exit.add("path", input.get("path").deepCopy());
        exit.addProperty("available", true);
        exit.addProperty("leafOwnerObjectToken", 3);
        exit.addProperty("leafOwnerObjectTokenKnown", true);
        exit.addProperty("valueClass", "java.util.HashMap");
        exit.addProperty("valueObjectToken", 2);
        exit.addProperty("valueObjectTokenKnown", true);
        exit.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        exit.addProperty("objectTokenScope", "ACT.P");
        return exit;
    }

    private static JsonObject incompleteMapEntryObservation(String siteId) {
        int marker = siteId.lastIndexOf("#u");
        JsonObject observation = new JsonObject();
        observation.addProperty("schemaVersion", 1);
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("operation", "java.util.Iterator.next");
        observation.addProperty("originMethod", siteId.substring(0, marker));
        observation.addProperty("originUnitIndex", Integer.parseInt(
                siteId.substring(marker + 2)));
        observation.addProperty("siteId", siteId);
        observation.addProperty("occurrence", 1);
        observation.addProperty("observationId",
                "MAP_ENTRY_READ:" + siteId + "#1");
        observation.addProperty("pcBoundary", 0);
        observation.addProperty("rawPathConditionBoundary", 0);
        observation.addProperty("complete", false);
        observation.addProperty("unresolvedReason",
                "symbolic expressions unavailable for [map]");
        return observation;
    }

    private static JsonObject causalEdge(String edgeId, String method,
                                         String siteId, String transferKind,
                                         String kind) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("method", method);
        edge.addProperty("siteId", siteId);
        edge.addProperty("transferKind", transferKind);
        edge.addProperty("kind", kind);
        return edge;
    }

    private static JsonObject exactProjectedInputBinding(
            String dependencyCell, String authority, String sinkSite) {
        JsonObject binding = new JsonObject();
        binding.addProperty("dependencyCell", dependencyCell);
        binding.addProperty("inputPort", "REGION.FIELD.in.0");
        binding.addProperty("bindingAuthority", authority);
        binding.add("dependencyMethods", singletonString(
                "<example.Heartbeat: void install(example.Snapshot)>"));
        binding.add("requestedStateTransformerSinkSites",
                singletonString(sinkSite));
        binding.add("requestedStateTransformerGuardSites", new JsonArray());
        binding.addProperty(
                "requestedStateTransformerSinkClosureComplete", true);
        binding.addProperty("requestedStateTransformerSinkExclusive", true);
        binding.add("requestedStateTransformerUnclassifiedEdgeIds",
                new JsonArray());
        binding.addProperty("requestedStateTransformerSinkAuthority",
                "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                        + "REQUESTED_STATE_TRANSFORMERS");
        return binding;
    }

    private static JsonObject exactTransformerSliceMetadata(
            String outputCell, JsonArray obligations,
            JsonArray inputBindings) {
        JsonObject metadata = new JsonObject();
        metadata.add("inputBindings", inputBindings.deepCopy());
        metadata.addProperty("requestedStateTransformerContractVersion", 1);
        metadata.addProperty(
                "requestedStateTransformerContractApplicable", true);
        metadata.addProperty(
                "requestedStateTransformerContractOutputPort",
                "REGION.P.out.0");
        metadata.addProperty(
                "requestedStateTransformerContractOutputCell", outputCell);
        metadata.add("requestedStateTransformerObligations",
                obligations.deepCopy());
        metadata.addProperty("requestedStateTransformerObligationCount",
                obligations.size());
        metadata.add("requestedStateTransformerContractIssues",
                new JsonArray());
        metadata.addProperty(
                "requestedStateTransformerContractComplete", true);
        metadata.addProperty(
                "requestedStateTransformerContractAuthority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL_V1");
        return metadata;
    }

    private static void addHeapEffectCaptureDischarge(
            JsonObject metadata, String outputCell, String inputPort) {
        metadata.addProperty(
                "captureDischargedByHeapEffectTransformer", true);
        metadata.addProperty("captureDischargeInputPort", inputPort);
        metadata.addProperty("captureDischargeOutputPort",
                "REGION.P.out.0");
        metadata.addProperty("captureDischargeOutputCell", outputCell);
        metadata.addProperty("captureDischargeAuthority",
                "HEAP_EFFECT_STATE_TRANSFORMER");
        metadata.add("captureBindings", new JsonArray());
        metadata.addProperty("captureBindingsRequired", false);
        metadata.addProperty("captureBindingsComplete", true);
        metadata.add("captureBindingIssues", new JsonArray());
    }

    private static JsonObject exactTransformerObligation(
            String edgeId, String method, String siteId,
            String outputCell) {
        JsonObject obligation = new JsonObject();
        obligation.addProperty("siteId", siteId);
        obligation.addProperty("method", method);
        obligation.addProperty("targetCell", outputCell);
        obligation.addProperty("transferKind", "HEAP_WRITE");
        obligation.addProperty("kind", "field_mutation");
        JsonArray edgeIds = new JsonArray();
        edgeIds.add(edgeId);
        obligation.add("causalEdgeIds", edgeIds);
        obligation.addProperty("authority",
                "STATIC_EXACT_REQUESTED_OUTPUT_TARGET_CELL");
        return obligation;
    }

    private static JsonObject transformerInputBinding(
            String inputPort, String dependencyCell, JsonArray sinkSites,
            JsonArray guardSites) {
        JsonObject binding = new JsonObject();
        binding.addProperty("inputPort", inputPort);
        binding.addProperty("dependencyCell", dependencyCell);
        binding.addProperty("bindingAuthority", "EXACT_CELL_IDENTITY");
        binding.add("dependencyMethods", new JsonArray());
        binding.add("requestedStateTransformerSinkSites",
                sinkSites.deepCopy());
        binding.add("requestedStateTransformerGuardSites",
                guardSites.deepCopy());
        binding.addProperty(
                "requestedStateTransformerSinkClosureComplete", true);
        binding.addProperty("requestedStateTransformerSinkExclusive", true);
        binding.add("requestedStateTransformerUnclassifiedEdgeIds",
                new JsonArray());
        binding.addProperty("requestedStateTransformerSinkAuthority",
                "STATIC_FORWARD_CAUSAL_CLOSURE_TO_EXACT_"
                        + "REQUESTED_STATE_TRANSFORMERS");
        return binding;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) {
            result.add(value);
        }
        return result;
    }

    private static JsonArray stringsAsObjects(JsonObject... values) {
        JsonArray result = new JsonArray();
        for (JsonObject value : values) {
            result.add(value);
        }
        return result;
    }

    private static MapFixture importContainerMutationFixture(
            Path root, int arrayLength, int[] selectors, String mutation)
            throws Exception {
        String method = "<example.Store: void update()>";
        String outputCell = "<example.Store: java.util.Map data>";
        String base = "REGION.P.in.1";
        String containerPort = "REGION.P.in.2";
        String containerCell =
                "<example.Envelope: example.Value[] values>";
        String field = "<example.Value: long id>";
        long arrayToken = 500L;
        String engineArrayId = "AL_1";

        JsonArray actions = new JsonArray();
        actions.add(fieldAccessAction(base, "id"));
        JsonObject containerAction = new JsonObject();
        containerAction.addProperty("symbol", containerPort);
        containerAction.addProperty("bindingMode", "FIELD_ACCESS");
        containerAction.addProperty("field", containerCell);
        containerAction.addProperty("cell", containerCell);
        containerAction.add("fieldPath",
                JsonParser.parseString("[\"values\"]"));
        actions.add(containerAction);

        JsonArray declarations = new JsonArray();
        JsonArray dynamicBindings = new JsonArray();
        JsonArray fieldObservations = new JsonArray();
        JsonObject[] putExpressions = new JsonObject[selectors.length];
        JsonObject[] loadExpressions = new JsonObject[selectors.length];
        String[] dynamicSymbols = new String[selectors.length];
        JsonArray causalEdges = new JsonArray();
        JsonArray obligations = new JsonArray();
        JsonArray sinkSites = new JsonArray();

        for (int ordinal = 0; ordinal < selectors.length; ordinal++) {
            int selectorIndex = selectors[ordinal];
            String bindingId = "CONTAINER.FIELD." + ordinal;
            String fieldSite = method + "#u" + (14 + ordinal * 6);
            String loadSite = method + "#u" + (13 + ordinal * 6);
            String writeSite = method + "#u" + (17 + ordinal * 6);
            String edgeId = "DF.PUT." + ordinal;
            String dynamic = dynamicFieldSymbol(base, fieldSite, 1);
            dynamicSymbols[ordinal] = dynamic;

            JsonObject declaration = new JsonObject();
            declaration.addProperty("schemaVersion", 1);
            declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
            declaration.addProperty("bindingId", bindingId);
            declaration.addProperty("baseInputSymbol", base);
            declaration.addProperty("containerInputPort", containerPort);
            declaration.addProperty("containerInputCell", containerCell);
            declaration.addProperty("selectorAuthority",
                    "EXACT_ARRAY_INDEX");
            declaration.addProperty("elementIndex", selectorIndex);
            declaration.addProperty("elementOccurrence", 1);
            declaration.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            declaration.addProperty("declaredFieldSignature", field);
            declaration.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            declaration.addProperty("declaredFieldType", "long");
            declaration.addProperty("declaredFieldName", "id");
            declaration.addProperty("method", method);
            declaration.addProperty("fieldMaterializationSiteId",
                    fieldSite);
            declaration.addProperty("arrayLoadSiteId", loadSite);
            declaration.add("proofCausalEdgeIds", strings(
                    "PROOF." + ordinal + ".0",
                    "PROOF." + ordinal + ".1",
                    "PROOF." + ordinal + ".2",
                    "PROOF." + ordinal + ".3", edgeId));
            declaration.addProperty("proofAuthority",
                    "STATIC_EXACT_CONTAINER_ARRAY_FIELD_TO_MAP_PUT_"
                            + "KEY_VALUE_V1");
            declaration.addProperty("requestedStateTransformerSiteId",
                    "SITE".equals(mutation) && ordinal == 0
                            ? method + "#u999" : writeSite);
            declaration.addProperty("complete", true);
            declarations.add(declaration);

            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "ARRAY_INDEX");
            selector.addProperty("bindingId", bindingId);
            selector.addProperty("containerInputPort", containerPort);
            selector.addProperty("containerInputCell", containerCell);
            selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
            selector.addProperty("resolvedFromSelectorAuthority",
                    "EXACT_ARRAY_INDEX");
            selector.addProperty("elementIndex", selectorIndex);
            selector.addProperty("elementOccurrence", 1);
            selector.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            selector.addProperty("declaredFieldType", "long");
            selector.addProperty("containerObjectToken", arrayToken);
            selector.addProperty("elementObjectToken", 601L + ordinal);
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.P");
            selector.addProperty("containerObservationLocation",
                    "FIELD_ACCESS");
            selector.addProperty("authority",
                    "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                            + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
            selector.addProperty("complete", true);

            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 2);
            binding.addProperty("kind",
                    "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", base);
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId", fieldSite);
            binding.addProperty("materializationOccurrence", 1);
            binding.addProperty("fieldSignature", field);
            binding.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            binding.addProperty("leafOwnerObjectToken", 601L + ordinal);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.P");
            binding.add("containerSelector", selector.deepCopy());
            addContainerSelectorFlatFields(binding, selector);
            addContainerSiteBridge(binding, fieldSite, 1, bindingId,
                    601L + ordinal);
            binding.addProperty("actualHookSiteId",
                    "<example.Value: long getId()>#u1");
            binding.addProperty("actualHookOccurrence", ordinal + 1);
            binding.addProperty("authority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                            + "AND_STABLE_FIELD_SITE_OCCURRENCE");
            binding.addProperty("complete", true);
            dynamicBindings.add(binding);

            JsonObject observation = new JsonObject();
            observation.addProperty("symbol", dynamic);
            observation.addProperty("phase", "AT_MATERIALIZATION");
            observation.add("path",
                    JsonParser.parseString("[\"id\"]"));
            observation.addProperty("available", true);
            observation.addProperty("leafOwnerObjectToken",
                    601L + ordinal);
            observation.addProperty("leafOwnerObjectTokenKnown", true);
            observation.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            observation.addProperty("objectTokenScope", "ACT.P");
            observation.addProperty("baseInputSymbol", base);
            observation.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            observation.addProperty("dynamicFieldSymbol", dynamic);
            observation.addProperty("materializationSiteId", fieldSite);
            observation.addProperty("materializationOccurrence", 1);
            addContainerSiteBridge(observation, fieldSite, 1, bindingId,
                    601L + ordinal);
            observation.addProperty("actualHookSiteId",
                    "<example.Value: long getId()>#u1");
            observation.addProperty("actualHookOccurrence", ordinal + 1);
            observation.addProperty("dynamicFieldBindingSchemaVersion", 2);
            observation.addProperty("dynamicFieldBindingKind",
                    "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
            observation.addProperty("fieldSignature", field);
            observation.add("fieldPath",
                    JsonParser.parseString("[\"id\"]"));
            observation.add("containerSelector", selector.deepCopy());
            addContainerSelectorFlatFields(observation, selector);
            observation.addProperty("dynamicFieldBindingAuthority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                            + "AND_STABLE_FIELD_SITE_OCCURRENCE");
            observation.addProperty("dynamicFieldBindingComplete", true);
            observation.addProperty("complete", true);
            fieldObservations.add(observation);

            JsonObject causal = causalEdge(edgeId, method, writeSite,
                    "HEAP_WRITE", "field_mutation");
            causal.addProperty("fromCell", method + "::value" + ordinal);
            causal.addProperty("toCell", outputCell);
            causalEdges.add(causal);
            obligations.add(exactTransformerObligation(edgeId, method,
                    writeSite, outputCell));
            sinkSites.add(writeSite);
        }
        if ("MIXED_RESIDUAL".equals(mutation)) {
            String edgeId = "DF.PUT.RESIDUAL";
            String writeSite = method + "#u90";
            JsonObject causal = causalEdge(edgeId, method, writeSite,
                    "HEAP_WRITE", "field_mutation");
            causal.addProperty("fromCell", method + "::literalValue");
            causal.addProperty("toCell", outputCell);
            causalEdges.add(causal);
            obligations.add(exactTransformerObligation(edgeId, method,
                    writeSite, outputCell));
            sinkSites.add(writeSite);
        }

        JsonObject map = mapInputExpression();
        for (int ordinal = 0; ordinal < selectors.length; ordinal++) {
            JsonElement value = symbol("EL_1-0-" + (ordinal + 1),
                    "Lexample/Value;");
            loadExpressions[ordinal] = arrayLoadExpression(engineArrayId,
                    selectors[ordinal], value, 100 + ordinal);
            putExpressions[ordinal] = methodExpression(
                    "java/util/HashMap put", 100 + ordinal,
                    map.deepCopy(), symbol(
                            "M_J_field_" + dynamicSymbols[ordinal]
                                    + "_example/Value", "J"),
                    value.deepCopy());
        }
        if ("VALUE".equals(mutation)) {
            loadExpressions[0].add("_value_exp",
                    symbol("EL_1-0-wrong", "Lexample/Value;"));
        }
        JsonArray path = new JsonArray();
        for (int ordinal = 0; ordinal < selectors.length; ordinal++) {
            if ("MISSING_EFFECT".equals(mutation)
                    && ordinal == selectors.length - 1) {
                continue;
            }
            path.add(loadExpressions[ordinal]);
            if ("DUPLICATE_LOAD".equals(mutation)) {
                path.add(loadExpressions[ordinal].deepCopy());
            }
            if (arrayLength > selectors.length) {
                path.add(arrayLoadExpression(engineArrayId, 0,
                        symbol("EL_noise_" + ordinal,
                                "Lexample/Value;"),
                        200 + ordinal));
            }
            path.add(putExpressions[ordinal]);
        }
        if ("MIXED_RESIDUAL".equals(mutation)) {
            path.add(methodExpression("java/util/HashMap put", 300,
                    map.deepCopy(), constant("Y_I_99", "I"),
                    symbol("EL_literal", "Lexample/Value;")));
        }

        JsonObject containerInput = transformerInputBinding(containerPort,
                containerCell, sinkSites, new JsonArray());
        JsonArray inputBindings = stringsAsObjects(containerInput);
        JsonObject sliceMetadata = exactTransformerSliceMetadata(outputCell,
                obligations, inputBindings);
        addHeapEffectCaptureDischarge(sliceMetadata, outputCell,
                "REGION.P.in.0");

        JsonElement[] arrayElements = new JsonElement[arrayLength];
        for (int index = 0; index < arrayLength; index++) {
            arrayElements[index] = symbol("M_L_array_element_" + index,
                    "Lexample/Value;");
        }
        for (int ordinal = 0; ordinal < selectors.length; ordinal++) {
            arrayElements[selectors[ordinal]] = putExpressions[ordinal]
                    .getAsJsonArray("_param_list").get(2).deepCopy();
        }
        if ("SNAPSHOT_VALUE".equals(mutation)) {
            arrayElements[selectors[0]] = symbol(
                    "M_L_array_element_wrong", "Lexample/Value;");
        }
        JsonObject arrayValue = arrayValueExpression(
                "[Lexample/Value;", "Lexample/Value;", true,
                arrayElements);
        arrayValue.addProperty("_engine_array_id", engineArrayId);
        arrayValue.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject engineArray = new JsonObject();
        engineArray.addProperty("schemaVersion", 1);
        engineArray.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        engineArray.addProperty("sourceActivationId", "ACT.P");
        engineArray.addProperty("inputPort", containerPort);
        engineArray.addProperty("inputCell", containerCell);
        engineArray.addProperty("inputJavaType", "example.Value[]");
        engineArray.addProperty("inputJavaTypeDescriptor",
                "[Lexample/Value;");
        engineArray.addProperty("symbolizationPrefix", containerPort);
        engineArray.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        engineArray.addProperty("engineArrayId", engineArrayId);
        engineArray.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        engineArray.addProperty("arrayObjectToken", arrayToken);
        engineArray.addProperty("symbolizationArrayObjectToken", arrayToken);
        engineArray.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        engineArray.addProperty("sameArrayObjectTokenVerified", true);
        engineArray.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        engineArray.addProperty("objectTokenScope", "ACT.P");
        engineArray.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        engineArray.add("arrayValueExpression", arrayValue);
        engineArray.addProperty("complete", true);

        return importMapFixture(root, path, true, new JsonArray(),
                singletonString(method), causalEdges, null, actions,
                new JsonArray(), fieldObservations, dynamicBindings,
                sliceMetadata, new JsonArray(), declarations,
                singletonObject(engineArray));
    }

    private static JsonObject arrayLoadExpression(
            String engineArrayId, int index, JsonElement value, int line) {
        JsonObject load = new JsonObject();
        load.addProperty("_code_position",
                "virtual void example.Store.update():" + line);
        load.addProperty("_type", "_array_expr");
        load.addProperty("_arr_str", engineArrayId);
        load.addProperty("_is_load", true);
        load.add("_index_exp", constant("Y_I_" + index, "I"));
        load.add("_value_exp", value.deepCopy());
        return load;
    }

    private static ExactTransformerFixture exactTransformerFixture(
            JsonArray inputBindings) {
        ExactTransformerFixture fixture = new ExactTransformerFixture();
        fixture.outputCell = "<example.Store: java.util.Map data>";
        fixture.update = "<example.Store: void update()>";
        fixture.prune = "<example.Store: void prune()>";
        fixture.wrapper = "<example.Store: void wrapper()>";
        fixture.updateSite = fixture.update + "#u1";
        fixture.pruneSite = fixture.prune + "#u15";
        fixture.outerGuardSite = fixture.prune + "#u6";
        fixture.innerGuardSite = fixture.prune + "#u14";

        JsonObject map = symbol(
                "M_L_field_REGION.P.in.0_example/Store", "L");
        fixture.path.add(methodExpression("java/util/HashMap put", 19,
                symbolCopy(map), symbol("putKey", "I"),
                symbol("putValue", "example/Value")));
        fixture.methods.add(fixture.update);
        fixture.methods.add(fixture.prune);
        fixture.methods.add(fixture.wrapper);

        JsonObject updateWrite = causalEdge("DF.WRITE.UPDATE",
                fixture.update, fixture.updateSite, "HEAP_WRITE",
                "field_mutation");
        updateWrite.addProperty("fromCell", fixture.update + "::key");
        updateWrite.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(updateWrite);
        JsonObject pruneWrite = causalEdge("DF.WRITE.PRUNE",
                fixture.prune, fixture.pruneSite, "HEAP_WRITE",
                "field_mutation");
        pruneWrite.addProperty("fromCell", fixture.prune + "::expiredKey");
        pruneWrite.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(pruneWrite);
        JsonObject otherFieldWrite = causalEdge("DF.WRITE.OTHER",
                fixture.wrapper, fixture.wrapper + "#u2", "HEAP_WRITE",
                "field_write");
        otherFieldWrite.addProperty("fromCell", fixture.wrapper
                + "::enabled");
        otherFieldWrite.addProperty("toCell",
                "<example.Store: boolean enabled>");
        fixture.causalEdges.add(otherFieldWrite);
        JsonObject outer = guardedMutationEdge("DF.GUARD.OUTER",
                fixture.prune, 6, 15, false);
        outer.addProperty("fromCell", fixture.prune + "::hasNext");
        outer.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(outer);
        JsonObject inner = guardedMutationEdge("DF.GUARD.INNER",
                fixture.prune, 14, 15, false);
        inner.addProperty("fromCell", fixture.prune + "::expiryPredicate");
        inner.addProperty("toCell", fixture.outputCell);
        fixture.causalEdges.add(inner);

        JsonArray obligations = new JsonArray();
        obligations.add(exactTransformerObligation("DF.WRITE.UPDATE",
                fixture.update, fixture.updateSite, fixture.outputCell));
        obligations.add(exactTransformerObligation("DF.WRITE.PRUNE",
                fixture.prune, fixture.pruneSite, fixture.outputCell));
        fixture.sliceMetadata = exactTransformerSliceMetadata(
                fixture.outputCell, obligations, inputBindings);
        fixture.branchMappings.add(branchMapping(fixture.prune, 6, 1,
                true, symbol("outerLoopGate", "Z")));
        return fixture;
    }

    private static final class ExactTransformerFixture {
        private String outputCell;
        private String update;
        private String prune;
        private String wrapper;
        private String updateSite;
        private String pruneSite;
        private String outerGuardSite;
        private String innerGuardSite;
        private final JsonArray path = new JsonArray();
        private final JsonArray methods = new JsonArray();
        private final JsonArray causalEdges = new JsonArray();
        private final JsonArray branchMappings = new JsonArray();
        private JsonObject sliceMetadata;
    }

    private static JsonObject guardedMutationEdge(
            String edgeId, String method, int guardUnitIndex,
            int mutationUnitIndex, boolean requiredOutcome) {
        JsonObject edge = causalEdge(edgeId, method,
                method + "#u" + guardUnitIndex, "GUARD",
                "heap_mutation_path_guard");
        edge.addProperty("guardSiteId", method + "#u" + guardUnitIndex);
        edge.addProperty("guardedMutationCount", 1);
        edge.addProperty("guardedMutationsAuthority",
                "STATIC_CONTROL_DEPENDENCE_PER_MUTATION_SITE");
        JsonObject mutation = new JsonObject();
        mutation.addProperty("guardSiteId",
                method + "#u" + guardUnitIndex);
        mutation.addProperty("guardedMutationSiteId",
                method + "#u" + mutationUnitIndex);
        mutation.addProperty("method", method);
        mutation.addProperty("unitIndex", mutationUnitIndex);
        mutation.addProperty("requiredOutcome", requiredOutcome);
        JsonArray mutations = new JsonArray();
        mutations.add(mutation);
        edge.add("guardedMutations", mutations);
        return edge;
    }

    private static JsonObject branchMapping(
            String method, int unitIndex, int occurrence,
            boolean observedOutcome, JsonElement condition) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", method + "#u" + unitIndex);
        mapping.addProperty("method", method);
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", observedOutcome);
        mapping.addProperty("observedOutcome", observedOutcome);
        mapping.addProperty("conditionIndex", -1);
        mapping.addProperty("rawConditionIndex", -1);
        mapping.add("condition", condition.deepCopy());
        return mapping;
    }

    private static JsonElement authorizeRawBranchMappingsForTest(
            JsonElement encoded, JsonArray path) {
        if (encoded == null || !encoded.isJsonArray()) {
            return encoded == null ? null : encoded.deepCopy();
        }
        JsonArray result = new JsonArray();
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                result.add(element.deepCopy());
                continue;
            }
            JsonObject mapping = element.getAsJsonObject().deepCopy();
            if (!mapping.has("witness")
                    && !mapping.has("concreteObservation")
                    && (!mapping.has("vmBranchEventValidated")
                    || mapping.get("vmBranchEventValidated")
                    .getAsBoolean())) {
                String site = mapping.get("siteId").getAsString();
                String method = mapping.get("method").getAsString();
                int unit = mapping.get("unitIndex").getAsInt();
                int occurrence = mapping.get("occurrence").getAsInt();
                boolean outcome = mapping.get("outcome").getAsBoolean();
                int index = mapping.has("rawConditionIndex")
                        ? mapping.get("rawConditionIndex").getAsInt()
                        : mapping.has("conditionIndex")
                        ? mapping.get("conditionIndex").getAsInt() : -1;
                if (index >= 0 && index < path.size()) {
                    JsonElement predicate = mapping.has("condition")
                            ? mapping.get("condition") : path.get(index);
                    JsonObject metadata = new JsonObject();
                    metadata.addProperty("predicateNormalization",
                            mapping.has("conditionNormalization")
                                    ? BranchWitness.CMP_NORMALIZATION
                                    : BranchWitness.IDENTITY_NORMALIZATION);
                    mapping.add("witness", BranchWitness.vmPc(site,
                            method, unit, occurrence, outcome, predicate,
                            index, metadata).toJson());
                } else {
                    mapping.add("concreteObservation",
                            ExactConcreteBranchObservation.attested(site,
                                    method, unit, occurrence, outcome)
                                    .toJson());
                }
            }
            result.add(mapping);
        }
        return result;
    }

    private static JsonArray branchPoliciesForTest(JsonElement mappings) {
        JsonArray result = new JsonArray();
        java.util.Set<String> seen = new java.util.LinkedHashSet<>();
        if (mappings == null || !mappings.isJsonArray()) return result;
        for (JsonElement element : mappings.getAsJsonArray()) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            String site = mapping.has("siteId")
                    ? mapping.get("siteId").getAsString() : "";
            if (site.isEmpty() && mapping.has("witness")) {
                site = BranchWitness.fromJson(mapping.getAsJsonObject(
                        "witness")).siteId();
            }
            if (site.isEmpty() && mapping.has("concreteObservation")) {
                site = ExactConcreteBranchObservation.fromJson(
                        mapping.getAsJsonObject("concreteObservation"))
                        .siteId();
            }
            if (site.isEmpty() || !seen.add(site)) continue;
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", site);
            branch.addProperty("policy", "EXPLORE");
            result.add(branch);
        }
        return result;
    }

    private static JsonObject fieldAccessAction(String symbol,
                                                String field) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", symbol);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("field", "<example.Value: long " + field + ">");
        action.addProperty("cell", "<example.Value: long " + field + ">");
        JsonArray path = new JsonArray();
        path.add(field);
        action.add("fieldPath", path);
        return action;
    }

    private static JsonObject fieldObservation(String symbol, String field,
                                               int leafOwnerIdentity) {
        JsonObject observation = new JsonObject();
        observation.addProperty("symbol", symbol);
        observation.addProperty("phase", "AT_MATERIALIZATION");
        JsonArray path = new JsonArray();
        path.add(field);
        observation.add("path", path);
        observation.addProperty("available", true);
        observation.addProperty("leafOwnerIdentity", leafOwnerIdentity);
        return observation;
    }

    private static JsonObject freshMapInitializer(String initializerId) {
        JsonObject initializer = new JsonObject();
        initializer.addProperty("initializerId", initializerId);
        initializer.addProperty("kind",
                "FRESH_DEFAULT_CONSTRUCTED_OBJECT");
        initializer.addProperty("allocatedType", "java.util.HashMap");
        initializer.addProperty("allocationEdgeId", "EDGE.ALLOC.0");
        initializer.addProperty("allocationMethod",
                "<example.Store: void update()>");
        initializer.addProperty("allocationSiteId", "SITE.ALLOC.0");
        initializer.addProperty("constructor",
                "<java.util.HashMap: void <init>()>");
        initializer.addProperty("constructorArgumentCount", 0);
        initializer.addProperty("outputPort", "REGION.P.out.0");
        JsonArray proof = new JsonArray();
        proof.add("EDGE.ALLOC.0");
        initializer.add("proofEdgeIds", proof);
        initializer.addProperty("proofComplete", true);
        initializer.addProperty("selectionAuthority",
                "STATIC_ALLOCATION_CONSTRUCTOR_AND_FORWARD_CAUSAL_PATH");
        initializer.addProperty("captureBoundaryRequirement",
                "REGION_ROOT_ENTRY_PRECEDES_ALLOCATION");
        return initializer;
    }

    private static JsonObject importExactOutputCaptureFixture(
            Path root, JsonElement expression, int captureCount)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String rootMethod = "<example.Root: void run()>";
        String caller = "<example.Client: void send()>";
        String callee = "<example.Protocol: void accept(java.lang.String)>";
        String outputCell = callee + ".param0:java.lang.String";

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId",
                "REGION.OUT.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.OUT.out.0");
        capture.addProperty("outputCell", outputCell);
        capture.addProperty("callerMethod", caller);
        capture.addProperty("unitIndex", 7);
        capture.addProperty("siteId", caller + "#u7");
        capture.addProperty("calleeMethod", callee);
        capture.addProperty("argumentIndex", 0);
        capture.addProperty("occurrence", 1);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.OUT");
        activation.addProperty("regionId", "REGION.OUT");
        activation.addProperty("regionInstanceId",
                "REGION.OUT@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", rootMethod);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.OUT.out.0");
        requested.addProperty("cell", outputCell);
        requested.addProperty("kind", "SINK_STATE");
        activation.add("requestedOutput", requested);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.OUT.out.0");
        slice.addProperty("complete", true);
        slice.add("inputPorts", singletonString("REGION.OUT.in.0"));
        slice.add("methods", singletonString(rootMethod));
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputCapture", singletonObject(capture));
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.OUT.in.0");
        input.addProperty("cell", rootMethod + ".param0:java.lang.String");
        input.addProperty("location", "ARGUMENT");
        activation.add("symbolize", singletonObject(input));
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.OUT.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.OUT");
        region.addProperty("rootMethod", rootMethod);
        region.add("methods", singletonString(rootMethod));
        write(regions, region + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.OUT");
        raw.addProperty("regionId", "REGION.OUT");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", singletonString("REGION.OUT.in.0"));
        raw.add("rootOutputExpression", constant("Y_L_NULL", "L"));
        JsonArray captures = new JsonArray();
        for (int index = 0; index < captureCount; index++) {
            JsonObject observed = capture.deepCopy();
            observed.addProperty("expressionCaptured", true);
            observed.add("expression", expression.deepCopy());
            captures.add(observed);
        }
        raw.add("outputCaptures", captures);
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.OUT");
        engine.addProperty("activationId", "ACT.OUT");
        engine.add("pathCondition", new JsonArray());
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics);
        return JsonParser.parseString(new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim()).getAsJsonObject();
    }

    private static JsonObject importJointOutputCaptureFixture(
            Path root, boolean omitSecondCapture, boolean wrongGoal)
            throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String regionId = "REGION.JOINT";
        String activationId = "ACT.JOINT";
        String rootMethod = "<example.Client: void send(int,int)>";
        String callee = "<example.Protocol: void accept(int,int)>";

        JsonObject first = jointCallMemberActivation(regionId,
                activationId, rootMethod, callee, 0);
        JsonObject second = jointCallMemberActivation(regionId,
                activationId, rootMethod, callee, 1);
        OutputClosureContract contract = OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(first),
                        OutputClosureCodec.decode(second)));

        JsonObject activation = first.deepCopy();
        JsonArray inputs = new JsonArray();
        for (int index = 0; index < 2; index++) {
            JsonObject input = new JsonObject();
            input.addProperty("symbol", regionId + ".in." + index);
            input.addProperty("cell",
                    rootMethod + ".param" + index + ":int");
            input.addProperty("location", "ARGUMENT");
            inputs.add(input);
        }
        activation.add("symbolize", inputs);
        activation.add("materializations", inputs.deepCopy());
        OutputClosureCodec.writeTo(activation, contract);
        if (wrongGoal) {
            activation.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
        }
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", regionId);
        region.addProperty("rootMethod", rootMethod);
        region.add("methods", singletonString(rootMethod));
        write(regions, region + "\n");

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", activationId);
        raw.addProperty("regionId", regionId);
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        JsonArray symbolized = new JsonArray();
        symbolized.add(regionId + ".in.0");
        symbolized.add(regionId + ".in.1");
        raw.add("symbolizedInputs", symbolized);
        raw.add("rootOutputExpression", constant("Y_I_0", "I"));
        JsonArray captures = new JsonArray();
        JsonArray requests = OutputClosureCodec.captures(contract);
        for (int index = 0; index < requests.size(); index++) {
            if (omitSecondCapture && index == 1) continue;
            JsonObject observed = requests.get(index)
                    .getAsJsonObject().deepCopy();
            observed.addProperty("expressionCaptured", true);
            observed.add("expression", symbol(
                    "M_I_field_" + regionId + ".in." + index + "_value",
                    "I"));
            captures.add(observed);
        }
        raw.add("outputCaptures", captures);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics);
        String row = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        return row.isEmpty() ? new JsonObject()
                : JsonParser.parseString(row).getAsJsonObject();
    }

    private static JsonObject jointCallMemberActivation(
            String regionId, String activationId, String rootMethod,
            String callee, int index) {
        String port = regionId + ".out." + index;
        String cell = callee + ".param" + index + ":int";
        String site = rootMethod + "#u7";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "CALL_ARGUMENT");
        capture.addProperty("captureBindingId", port + ".capture.0");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("callerMethod", rootMethod);
        capture.addProperty("calleeMethod", callee);
        capture.addProperty("unitIndex", 7);
        capture.addProperty("siteId", site);
        capture.addProperty("argumentIndex", index);
        capture.addProperty("argumentCell", rootMethod + "::i" + index);
        capture.addProperty("occurrence", 1);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.addProperty("complete", true);
        slice.add("inputPorts",
                singletonString(regionId + ".in." + index));
        slice.add("sites", singletonString(site));
        slice.add("staticSites", singletonString(site));
        slice.add("methods", singletonString(rootMethod));
        slice.add("causalEdgeIds",
                singletonString("DF.JOINT." + index));
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("captureBindings", singletonObject(capture));

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", activationId);
        activation.addProperty("regionId", regionId);
        activation.addProperty("regionInstanceId",
                regionId + "@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", rootMethod);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", port);
        requested.addProperty("cell", cell);
        requested.addProperty("kind", "SINK_STATE");
        requested.addProperty("javaTypeDescriptor", "I");
        requested.addProperty("selectionAuthority",
                "CONFIRMED_READ_FROM_EDGE");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputCapture",
                singletonObject(capture));
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);
        activation.add("requestedOutputMethods",
                singletonString(rootMethod));
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("cell", cell);
        action.addProperty("kind", "SINK_STATE");
        action.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        action.addProperty("javaTypeDescriptor", "I");
        activation.add("outputs", singletonObject(action));
        OutputClosureCodec.writeTo(activation,
                OutputClosureCodec.singleton(
                        regionId, regionId + "@fixture#call1", 1,
                        port, cell, "SINK_STATE",
                        "CONFIRMED_READ_FROM_EDGE", slice));
        return activation;
    }

    private static JsonObject importJointFieldOutputCaptureFixture(
            Path root, boolean invalidateSecondTransformer)
            throws Exception {
        Path firstRoot = root.resolve("first");
        Path secondRoot = root.resolve("second");
        importExactFieldAssignmentCaptureFixture(firstRoot, "NORMAL",
                true, true, "<example.State: int x>",
                symbol("M_I_field_REGION.FIELD.in.0_x", "I"));
        importExactFieldAssignmentCaptureFixture(secondRoot, "NORMAL",
                true, true, "<example.State: int y>",
                symbol("M_I_field_REGION.FIELD.in.0_y", "I"));

        JsonObject firstActivation = readObject(
                firstRoot.resolve("activation.jsonl"));
        JsonObject secondActivation = renamedOutputPort(readObject(
                secondRoot.resolve("activation.jsonl")), 1);
        makeCodecLegacyReady(firstActivation);
        makeCodecLegacyReady(secondActivation);
        if (invalidateSecondTransformer) {
            secondActivation.getAsJsonObject(OutputClosureContract.FIELD)
                    .getAsJsonArray("members").get(0).getAsJsonObject()
                    .getAsJsonObject("slice")
                    .addProperty(
                            "requestedStateTransformerContractComplete",
                            false);
        }
        OutputClosureContract contract = OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(firstActivation),
                        OutputClosureCodec.decode(secondActivation)));
        OutputClosureCodec.writeTo(firstActivation, contract);

        JsonObject raw = readObject(firstRoot.resolve("results.jsonl"));
        JsonObject secondRaw = renamedOutputPort(readObject(
                secondRoot.resolve("results.jsonl")), 1);
        JsonArray captures = raw.getAsJsonArray("outputCaptures");
        captures.add(secondRaw.getAsJsonArray("outputCaptures")
                .get(0).deepCopy());

        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        write(activations, firstActivation + "\n");
        write(regions, readObject(firstRoot.resolve("regions.jsonl"))
                + "\n");
        write(results, raw + "\n");
        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics);
        return readObject(output);
    }

    private static JsonObject importMixedJointOutputCaptureFixture(
            Path root) throws Exception {
        Path fieldRoot = root.resolve("field");
        importExactFieldAssignmentCaptureFixture(fieldRoot, "NORMAL",
                true, true, "<example.State: int y>",
                symbol("M_I_field_REGION.FIELD.in.0_y", "I"));
        JsonObject fieldActivation = renamedOutputPort(readObject(
                fieldRoot.resolve("activation.jsonl")), 1);
        makeCodecLegacyReady(fieldActivation);
        String rootMethod = fieldActivation.get("rootMethod").getAsString();
        JsonObject callActivation = jointCallMemberActivation(
                "REGION.FIELD", "ACT.FIELD", rootMethod,
                "<example.Protocol: void accept(int)>", 0);
        OutputClosureContract contract = OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(callActivation),
                        OutputClosureCodec.decode(fieldActivation)));
        OutputClosureCodec.writeTo(fieldActivation, contract);

        JsonObject raw = readObject(fieldRoot.resolve("results.jsonl"));
        raw.add("outputCaptures", renamedOutputPort(
                raw.deepCopy(), 1).getAsJsonArray(
                "outputCaptures").deepCopy());
        JsonObject callRequest = null;
        for (JsonElement element : OutputClosureCodec.captures(contract)) {
            JsonObject request = element.getAsJsonObject();
            if ("REGION.FIELD.out.0".equals(
                    request.get("outputPort").getAsString())) {
                callRequest = request.deepCopy();
            }
        }
        callRequest.addProperty("expressionCaptured", true);
        callRequest.add("expression", symbol(
                "M_I_field_REGION.FIELD.in.0_call", "I"));
        raw.getAsJsonArray("outputCaptures").add(callRequest);

        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        write(activations, fieldActivation + "\n");
        write(regions, readObject(fieldRoot.resolve("regions.jsonl"))
                + "\n");
        write(results, raw + "\n");
        ConcolicSummaryImporter.importSummaries(results, activations,
                regions, output, diagnostics);
        return readObject(output);
    }

    private static void makeCodecLegacyReady(JsonObject activation) {
        if (activation.has(OutputClosureContract.FIELD)) {
            return;
        }
        JsonObject requested = activation.getAsJsonObject(
                "requestedOutput");
        requested.addProperty("selectionAuthority",
                "CONFIRMED_READ_FROM_EDGE");
        requested.addProperty("javaTypeDescriptor", "I");
        JsonObject slice = activation.getAsJsonObject(
                "requestedOutputSlice");
        JsonObject capture = activation.getAsJsonArray(
                "requestedOutputCapture").get(0).getAsJsonObject();
        if (!slice.has("sites")) {
            slice.add("sites", singletonString(
                    capture.get("siteId").getAsString()));
        }
        if (!slice.has("staticSites")) {
            slice.add("staticSites", slice.getAsJsonArray(
                    "sites").deepCopy());
        }
        JsonObject action = activation.getAsJsonArray("outputs")
                .get(0).getAsJsonObject();
        action.addProperty("cell", requested.get("cell").getAsString());
        action.addProperty("kind", requested.get("kind").getAsString());
        action.addProperty("javaTypeDescriptor", "I");
        OutputClosureCodec.writeTo(activation,
                OutputClosureCodec.singleton(
                        activation.get("regionId").getAsString(),
                        activation.get("regionInstanceId").getAsString(),
                        activation.get("rootCallId").getAsLong(),
                        requested.get("portId").getAsString(),
                        requested.get("cell").getAsString(),
                        requested.get("kind").getAsString(),
                        requested.get("selectionAuthority").getAsString(),
                        slice));
    }

    private static JsonObject renamedOutputPort(
            JsonObject value, int index) {
        return JsonParser.parseString(value.toString().replace(
                "REGION.FIELD.out.0",
                "REGION.FIELD.out." + index)).getAsJsonObject();
    }

    private static JsonObject readObject(Path path) throws Exception {
        return JsonParser.parseString(new String(Files.readAllBytes(path),
                StandardCharsets.UTF_8).trim()).getAsJsonObject();
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, JsonElement expression)
            throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete,
                "<example.State: java.lang.String value>", expression);
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression) throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete, field, expression,
                false);
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression, boolean exactVmGuard) throws Exception {
        return importExactFieldAssignmentCaptureFixture(root, exitKind,
                identityVerified, rhsRelationComplete, field, expression,
                exactVmGuard ? "EXACT" : "NONE");
    }

    private static MapFixture importExactFieldAssignmentCaptureFixture(
            Path root, String exitKind, boolean identityVerified,
            boolean rhsRelationComplete, String field,
            JsonElement expression, String guardMode) throws Exception {
        boolean causalMapObservation =
                "CAUSAL_MAP_OBSERVATION".equals(guardMode);
        boolean nullGuardWithUnusedInput =
                "EXACT_NULL_WITH_UNUSED_INPUT".equals(guardMode);
        boolean exactVmGuard = !"NONE".equals(guardMode)
                && !causalMapObservation;
        boolean projectedDischarge = expression == null
                || expression.isJsonNull();
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = projectedDischarge
                ? "<example.Heartbeat: void install(example.Snapshot)>"
                : "<example.Heartbeat: void install(java.lang.String)>";
        String site = method + "#u3";
        String edgeId = "DF.FIELD.WRITE";

        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId",
                "REGION.FIELD.out.0.capture.0");
        capture.addProperty("outputPort", "REGION.FIELD.out.0");
        capture.addProperty("outputCell", field);
        capture.addProperty("method", method);
        capture.addProperty("unitIndex", 3);
        capture.addProperty("siteId", site);
        capture.addProperty("unit", "r0." + field + " = r1");
        capture.addProperty("fieldSignature", field);
        capture.addProperty("fieldOwnerExpression", "r0");
        capture.addProperty("fieldOwnerCell", method + "::r0");
        capture.addProperty("fieldOwnerDeclaredType", "example.State");
        capture.addProperty("fieldOwnerBindingKind",
                "INSTANCE_FIELD_LHS_BASE");
        capture.addProperty("fieldOwnerBindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_LHS");
        capture.addProperty("rhsExpression", "r1");
        capture.addProperty("rhsCell", method + "::r1");
        capture.addProperty("rhsCausalEdgeId", edgeId);
        capture.addProperty("rhsRelation", "value_flow");
        capture.addProperty("rhsRelationComplete", rhsRelationComplete);
        capture.addProperty("rhsRelationAuthority",
                "STATIC_EXACT_HEAP_WRITE_VALUE_FLOW");
        capture.addProperty("causalEdgeId", edgeId);
        capture.addProperty("transferKind", "HEAP_WRITE");
        capture.addProperty("bindingKind", "field_write");
        capture.addProperty("bindingAuthority",
                "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS");
        capture.addProperty("occurrence", 1);
        capture.addProperty("occurrenceAuthority",
                "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_"
                        + "SITE_LAST_WRITE_OCCURRENCE");
        capture.addProperty("runtimeFieldOwnerObjectId", 17);
        capture.addProperty("runtimeFieldOwnerBindingAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY");
        capture.addProperty("runtimeEventSeq", 5);

        JsonObject obligation = exactTransformerObligation(edgeId, method,
                site, field);
        obligation.addProperty("kind", "field_write");
        JsonObject causal = causalEdge(edgeId, method, site, "HEAP_WRITE",
                "field_write");
        causal.addProperty("fromCell", method + "::r1");
        causal.addProperty("toCell", field);
        JsonArray inputBindings = new JsonArray();
        JsonArray causalEdges = new JsonArray();
        if (projectedDischarge) {
            String baseCell = method + ".param0:example.Snapshot";
            String projectedCell = baseCell + "#field:value";
            JsonObject baseBinding = exactProjectedInputBinding(baseCell,
                    "EXACT_CELL_IDENTITY", site);
            JsonObject projectedBinding = exactProjectedInputBinding(
                    projectedCell,
                    "UNIQUE_EXACT_PROJECTED_VALUE_CARRIER", site);
            inputBindings.add(baseBinding);
            inputBindings.add(projectedBinding);
            JsonObject projection = causalEdge("DF.FIELD.PROJECTION",
                    method, method + "#synthetic:projected_local_def_use",
                    "VALUE_PASS", "projected_local_def_use");
            projection.addProperty("fromCell", projectedCell);
            projection.addProperty("toCell", method + "::r1");
            causalEdges.add(projection);
            if (causalMapObservation) {
                JsonObject guard = causalEdge("DF.FIELD.GUARD", method,
                        method + "#u2", "GUARD",
                        "path_guard_dependency");
                guard.addProperty("fromCell", projectedCell);
                guard.addProperty("toCell", method + "::guard");
                causalEdges.add(guard);
            }
        }
        causalEdges.add(causal);
        JsonObject slice = exactTransformerSliceMetadata(field,
                singletonObject(obligation), inputBindings);
        slice.addProperty("requestedStateTransformerContractOutputPort",
                "REGION.FIELD.out.0");
        slice.addProperty("outputPort", "REGION.FIELD.out.0");
        slice.addProperty("outputCell", field);
        JsonArray sliceInputs = singletonString("REGION.FIELD.in.0");
        if (nullGuardWithUnusedInput) {
            sliceInputs.add("REGION.FIELD.in.1");
        }
        slice.add("inputPorts", sliceInputs);
        slice.add("methods", singletonString(method));
        slice.add("causalEdges", causalEdges);
        JsonArray causalEdgeIds = singletonString(edgeId);
        if (projectedDischarge) {
            causalEdgeIds.add("DF.FIELD.PROJECTION");
            if (causalMapObservation) {
                causalEdgeIds.add("DF.FIELD.GUARD");
            }
        }
        slice.add("causalEdgeIds", causalEdgeIds);
        slice.addProperty("causalEdgeCount", causalEdges.size());
        slice.add("captureBindings", singletonObject(capture));
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("complete", true);
        slice.addProperty("structuralComplete", true);
        slice.addProperty("truncated", false);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.FIELD");
        activation.addProperty("regionId", "REGION.FIELD");
        activation.addProperty("regionInstanceId",
                "REGION.FIELD@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("requestedOutputCaptureRequired", true);
        activation.addProperty("requestedOutputCaptureComplete", true);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.FIELD.out.0");
        requested.addProperty("cell", field);
        requested.addProperty("kind", "HEAP_STATE");
        activation.add("requestedOutput", requested);
        activation.add("requestedOutputSlice", slice);
        activation.add("requestedOutputCapture", singletonObject(capture));
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.FIELD.in.0");
        input.addProperty("cell", method + ".param0:"
                + (projectedDischarge ? "example.Snapshot"
                : "java.lang.String"));
        input.addProperty("location", "ARGUMENT");
        JsonArray symbolize = singletonObject(input);
        if (nullGuardWithUnusedInput) {
            JsonObject unused = new JsonObject();
            unused.addProperty("symbol", "REGION.FIELD.in.1");
            unused.addProperty("cell", method + ".param1:int");
            unused.addProperty("location", "ARGUMENT");
            unused.addProperty("bindingMode", "LOCAL_DEFINITION");
            unused.addProperty("lazy", true);
            symbolize.add(unused);
        }
        activation.add("symbolize", symbolize);
        if (projectedDischarge) {
            JsonObject fallback = input.deepCopy();
            fallback.addProperty("bindingMode", "CONCRETE_PASSTHROUGH");
            fallback.addProperty("concreteFallback", true);
            activation.add("concreteFallbacks", singletonObject(fallback));
            activation.add("materializations", new JsonArray());
        }
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.FIELD.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        if (exactVmGuard) {
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", method + "#u2");
            branch.addProperty("policy", "EXPLORE");
            activation.add("branches", singletonObject(branch));
        }
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.FIELD");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        if (exactVmGuard) {
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", method + "#u2");
            branch.addProperty("policy", "EXPLORE");
            region.add("branchPolicies", singletonObject(branch));
        }
        write(regions, region + "\n");

        JsonObject observed = new JsonObject();
        observed.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        observed.addProperty("captureBindingId",
                "REGION.FIELD.out.0.capture.0");
        observed.addProperty("outputPort", "REGION.FIELD.out.0");
        observed.addProperty("outputCell", field);
        observed.addProperty("method", method);
        observed.addProperty("unitIndex", 3);
        observed.addProperty("siteId", site);
        observed.addProperty("fieldSignature", field);
        observed.addProperty("requestedOccurrence", 1);
        observed.addProperty("occurrence", 1);
        observed.addProperty("captureAuthority",
                "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT");
        observed.addProperty("declaredFieldOwnerVerified", true);
        observed.addProperty("declaredFieldTypeVerified", true);
        observed.addProperty("observedFieldValueAvailable", true);
        observed.addProperty("assignmentIdentityVerified", identityVerified);
        observed.addProperty("fieldOwnerObjectTokenKnown", true);
        observed.addProperty("fieldOwnerObjectToken", 1);
        observed.addProperty("assignedValueObjectTokenKnown", true);
        observed.addProperty("assignedValueObjectToken", 2);
        observed.addProperty("observedFieldValueObjectToken", 2);
        observed.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        observed.addProperty("objectTokenScope", "ACT.FIELD");
        observed.addProperty("assignedValueClass", "java.lang.String");
        observed.addProperty("observedFieldValueClass", "java.lang.String");
        observed.addProperty("assignedValueWasNull", false);
        observed.addProperty("observedFieldValueWasNull", false);
        observed.addProperty("assignmentIdentityMode",
                "REFERENCE_IDENTITY");
        observed.addProperty("assignmentIdentityAuthority",
                "EXACT_DECLARED_FIELD_REFLECTION_AND_REFERENCE_IDENTITY");
        observed.addProperty("expressionCaptured", !projectedDischarge);
        if (!projectedDischarge) {
            observed.add("expression", expression.deepCopy());
        }
        if (exactVmGuard) {
            observed.addProperty("expressionEnvelopeSchemaVersion", 1);
            observed.addProperty("expressionEnvelopeActive",
                    !"INACTIVE_ENVELOPE".equals(guardMode));
            observed.addProperty("assignedValueClass", "java.lang.Integer");
            observed.addProperty("observedFieldValueClass",
                    "java.lang.Integer");
            observed.addProperty("assignedValueWasNull", false);
            observed.addProperty("observedFieldValueWasNull", false);
            observed.addProperty("assignmentIdentityMode",
                    "BOXED_PRIMITIVE_VALUE_EQUALITY");
            observed.addProperty("concretePrimitiveValue", "10");
            observed.addProperty("expressionEnvelopeKind",
                    "CONCRETE_PRIMITIVE");
            observed.addProperty("expressionEnvelopeSymbolic", false);
            observed.addProperty("expressionEnvelopeAuthority",
                    "VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1");
            observed.addProperty("expressionEnvelopeJavaTypeDescriptor",
                    "I");
        }

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.FIELD");
        raw.addProperty("regionId", "REGION.FIELD");
        raw.addProperty("exitKind", exitKind);
        JsonArray unresolvedInputs = new JsonArray();
        if (projectedDischarge) {
            unresolvedInputs.add("REGION.FIELD.out.0.capture.0: "
                    + "field-assignment expression capture failed");
        }
        raw.add("unresolvedInputs", unresolvedInputs);
        raw.add("symbolizedInputs", projectedDischarge
                ? new JsonArray()
                : singletonString("REGION.FIELD.in.0"));
        raw.add("rootOutputExpression", constant("Y_L_NULL", "L"));
        raw.add("outputCaptures", singletonObject(observed));
        if (exactVmGuard || projectedDischarge) {
            JsonArray runtimeHeapObservations = new JsonArray();
            if (projectedDischarge) {
                runtimeHeapObservations.add(incompleteMapEntryObservation(
                        causalMapObservation ? method + "#u2"
                                : "<example.UnrelatedMap: void scan()>#u7"));
            }
            raw.add("runtimeHeapObservations", runtimeHeapObservations);
        }
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.FIELD");
        engine.addProperty("activationId", "ACT.FIELD");
        JsonArray pathCondition = new JsonArray();
        if (exactVmGuard) {
            String codePosition = "FILTERED".equals(guardMode)
                    ? "virtual void example.Unrelated.install(jobject):12"
                    : "virtual void example.Heartbeat.install(jobject):12";
            JsonElement rawLeft = "FORGED_SEMANTIC".equals(guardMode)
                    ? symbol("M_L_unrelated_guard", "L")
                    : symbol("M_L_field_REGION.FIELD.in.0_java/lang/String",
                    "L");
            JsonObject condition;
            if ("EXACT_STRING_PREDICATE".equals(guardMode)) {
                condition = stringPredicate(codePosition, "contains", false,
                        symbol("M_L'String'_REGION.FIELD.in.0_example/State",
                                "java/lang/String"),
                        stringConstant("ready"));
            } else {
                JsonObject right = nullGuardWithUnusedInput
                        ? symbol("N", "")
                        : constant("Y_L_NULL", "L");
                condition = binaryCondition(
                        codePosition, "!=", rawLeft,
                        right);
            }
            JsonObject semanticCondition = condition.deepCopy();
            if ("FORGED_SEMANTIC".equals(guardMode)) {
                semanticCondition.add("_left", symbol(
                        "M_L_field_REGION.FIELD.in.0_java/lang/String",
                        "L"));
            } else if ("FORGED_OPERATOR".equals(guardMode)) {
                semanticCondition.addProperty("_op", "==");
            }
            pathCondition.add(condition.deepCopy());
            JsonObject mapping = new JsonObject();
            mapping.addProperty("siteId", method + "#u2");
            mapping.addProperty("method", method);
            mapping.addProperty("unitIndex", 2);
            mapping.addProperty("occurrence", 1);
            mapping.addProperty("vmOccurrence", 1);
            mapping.addProperty("outcome", true);
            mapping.addProperty("observedOutcome", true);
            mapping.addProperty("conditionIndex", 0);
            mapping.addProperty("rawConditionIndex", 0);
            mapping.addProperty("rawPathConditionBaseline", 0);
            mapping.addProperty("enginePathConditionBaseline", 0);
            mapping.addProperty("rawPathConditionSize", 1);
            mapping.addProperty("enginePathConditionSize", 1);
            mapping.addProperty("mappingPolicy",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
            mapping.addProperty("conditionAuthority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
            mapping.addProperty("vmBranchEventExpected", true);
            mapping.addProperty("vmBranchEventValidated", true);
            mapping.addProperty("vmBranchEventId", 1);
            mapping.addProperty("vmBranchEventAuthority",
                    "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
            mapping.addProperty("vmThreadContextId", 2);
            mapping.addProperty("vmOwnerJavaThreadId", 3);
            mapping.addProperty("vmOwnerOsThreadId", 4);
            JsonArray vmConditionIndices = new JsonArray();
            vmConditionIndices.add(0);
            mapping.add("vmConditionIndices", vmConditionIndices);
            mapping.add("rawCondition", condition.deepCopy());
            mapping.add("condition", semanticCondition);
            raw.add("branchMappings", authorizeRawBranchMappingsForTest(
                    singletonObject(mapping), pathCondition));
        }
        engine.add("pathCondition", pathCondition);
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics);
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        String diagnosticRows = readOptional(diagnostics);
        return new MapFixture(summary, diagnosticRows);
    }

    private static MapFixture importEngineArrayBridgeFixture(
            Path root, JsonArray bindings, boolean store,
            boolean includeUnusedArray) throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = includeUnusedArray
                ? "<example.ArrayHandler: int run(java.lang.Object[],"
                + "java.lang.Object[])>"
                : "<example.ArrayHandler: int run(java.lang.Object[])>";

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.ARRAY");
        activation.addProperty("regionId", "REGION.ARRAY");
        activation.addProperty("regionInstanceId",
                "REGION.ARRAY@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", "REGION.ARRAY.out.0");
        JsonArray inputPorts = new JsonArray();
        inputPorts.add("REGION.ARRAY.in.0");
        if (includeUnusedArray) inputPorts.add("REGION.ARRAY.in.1");
        slice.add("inputPorts", inputPorts);
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.ARRAY.out.0");
        requested.addProperty("kind", "PRIMITIVE");
        activation.add("requestedOutput", requested);

        JsonArray materializations = new JsonArray();
        JsonArray regionInputs = new JsonArray();
        for (int index = 0; index < (includeUnusedArray ? 2 : 1);
                index++) {
            String port = "REGION.ARRAY.in." + index;
            String cell = method + ".param" + index
                    + ":java.lang.Object[]";
            JsonObject action = new JsonObject();
            action.addProperty("symbol", port);
            action.addProperty("cell", cell);
            action.addProperty("javaType", "java.lang.Object[]");
            action.addProperty("location", "ARGUMENT");
            materializations.add(action);
            JsonObject input = new JsonObject();
            input.addProperty("portId", port);
            input.addProperty("cell", cell);
            input.addProperty("javaType", "java.lang.Object[]");
            regionInputs.add(input);
        }
        activation.add("materializations", materializations);
        JsonObject outputAction = new JsonObject();
        outputAction.addProperty("symbol", "REGION.ARRAY.out.0");
        outputAction.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        activation.add("outputs", singletonObject(outputAction));
        write(activations, activation + "\n");

        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.ARRAY");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        region.add("symbolicInputs", regionInputs);
        write(regions, region + "\n");

        JsonObject load = new JsonObject();
        load.addProperty("_type", "_array_expr");
        load.addProperty("_is_load", !store);
        load.addProperty("_arr_str", "AL_1");
        load.add("_index_exp", constant("Y_I_0", "I"));
        load.add("_value_exp", symbol("M_L_ARRAY_VALUE",
                "Ljava/lang/Object;"));
        load.addProperty("_code_position", "virtual int "
                + "example.ArrayHandler.run(java.lang.Object"
                + (includeUnusedArray ? "[],java.lang.Object[]" : "[]")
                + "):12");
        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.ARRAY");
        engine.addProperty("activationId", "ACT.ARRAY");
        engine.add("pathCondition", singletonObject(load));

        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.ARRAY");
        raw.addProperty("regionId", "REGION.ARRAY");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", inputPorts.deepCopy());
        raw.add("rootOutputExpression", constant("Y_I_1", "I"));
        raw.add("engineSummary", engine);
        if (bindings != null) {
            raw.add("engineArrayInputBindings", bindings.deepCopy());
        }
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics);
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        return new MapFixture(summary, readOptional(diagnostics));
    }

    private static MapFixture importMapProjectionFixture(
            Path root, String operation, String fault) throws Exception {
        Files.createDirectories(root);
        Path activations = root.resolve("activation.jsonl");
        Path regions = root.resolve("regions.jsonl");
        Path results = root.resolve("results.jsonl");
        Path output = root.resolve("summaries.jsonl");
        Path diagnostics = root.resolve("diagnostics.jsonl");
        String method = "<example.ProjectionProducer: example.Value[] "
                + "export()>";
        String mapPort = "REGION.MAP.in.0";
        String outputPort = "REGION.MAP.out.0";
        String mapCell = "<example.ProjectionProducer: java.util.Map values>";
        String outputCell =
                "<example.Payload: example.Value[] values>";
        String fieldSignature = "<example.Value: long expiry>";
        String staticBindingId = "BIND.MAP.EXPIRY";
        String snapshotSite = method + "#u6";
        String materializationSite = snapshotSite + "#map-element:"
                + staticBindingId;

        JsonObject action = new JsonObject();
        action.addProperty("symbol", mapPort);
        action.addProperty("cell", mapCell);
        action.addProperty("field", mapCell);
        action.addProperty("javaType", "java.util.Map");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        JsonArray mapPath = new JsonArray();
        mapPath.add("values");
        action.add("fieldPath", mapPath);

        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind",
                "MAP_VALUE_TO_OUTPUT_ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", staticBindingId);
        declaration.addProperty("mapInputPort", mapPort);
        declaration.addProperty("mapInputCell", mapCell);
        declaration.addProperty("outputPort", outputPort);
        declaration.addProperty("outputCell", outputCell);
        declaration.add("outputFieldPath", singletonString("values"));
        declaration.addProperty("outputValidationMode",
                "ROOT_RETURN_PROJECTED_FIELD");
        declaration.addProperty("mapProjectionOperation", operation);
        declaration.addProperty("mapViewSiteId", method + "#u5");
        declaration.addProperty("snapshotSiteId", snapshotSite);
        declaration.addProperty("downstreamRegionInstance",
                "REGION.DOWNSTREAM@fixture#call2");
        declaration.addProperty("downstreamInputPort",
                "REGION.DOWNSTREAM.in.0");
        declaration.addProperty("downstreamBaseInputSymbol",
                "REGION.DOWNSTREAM.in.1");
        declaration.addProperty("downstreamContainerBindingId",
                "BIND.DOWNSTREAM.ARRAY.EXPIRY");
        declaration.addProperty("declaredFieldSignature", fieldSignature);
        declaration.addProperty("declaredFieldOwnerClass", "example.Value");
        declaration.addProperty("declaredFieldType", "long");
        declaration.addProperty("declaredFieldName", "expiry");
        declaration.add("fieldPath", singletonString("expiry"));
        declaration.addProperty("selectorAuthority",
                "CURRENT_EXECUTION_ENTRY_SNAPSHOT_THEN_EXACT_"
                        + "OUTPUT_INDEX_IDENTITY");
        declaration.add("projectionProofCausalEdgeIds",
                singletonString("EDGE.MAP.TO.ARRAY"));
        declaration.addProperty("recursiveElementProjectionComposable",
                true);
        declaration.addProperty("complete", true);

        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.MAP");
        activation.addProperty("regionId", "REGION.MAP");
        activation.addProperty("regionInstanceId",
                "REGION.MAP@fixture#call1");
        activation.addProperty("rootCallId", 1);
        activation.addProperty("rootMethod", method);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        slice.addProperty("outputPort", outputPort);
        slice.add("inputPorts", singletonString(mapPort));
        slice.add("methods", singletonString(method));
        activation.add("requestedOutputSlice", slice);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", outputPort);
        requested.addProperty("cell", outputCell);
        requested.addProperty("kind", "REFERENCE");
        activation.add("requestedOutput", requested);
        activation.add("materializations", singletonObject(action));
        activation.add("mapValueElementFieldProjections",
                singletonObject(declaration));
        write(activations, activation + "\n");

        JsonObject input = new JsonObject();
        input.addProperty("portId", mapPort);
        input.addProperty("cell", mapCell);
        input.addProperty("javaType", "java.util.Map");
        JsonObject outputSchema = new JsonObject();
        outputSchema.addProperty("portId", outputPort);
        outputSchema.addProperty("cell", outputCell);
        outputSchema.addProperty("javaType", "example.Value[]");
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.MAP");
        region.addProperty("rootMethod", method);
        region.add("methods", singletonString(method));
        region.add("symbolicInputs", singletonObject(input));
        region.add("outputs", singletonObject(outputSchema));
        write(regions, region + "\n");

        JsonArray snapshotTokens = new JsonArray();
        snapshotTokens.add(601L);
        snapshotTokens.add(602L);
        JsonArray snapshotKeys = new JsonArray();
        snapshotKeys.add(constant("Y_I_11", "java/lang/Integer"));
        snapshotKeys.add(constant("Y_I_22", "java/lang/Integer"));
        JsonObject entry = mapProjectionObservation("ENTRY_SNAPSHOT",
                operation, mapPort, outputPort, outputCell, 501L);
        entry.addProperty("snapshotElementCount", 2);
        entry.add("snapshotElementObjectTokens", snapshotTokens.deepCopy());
        entry.add("snapshotEntryKeyExpressions", snapshotKeys.deepCopy());
        entry.addProperty("entryKeyExpressionAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        entry.addProperty("entrySnapshotComplete", true);
        JsonObject outputObservation = mapProjectionObservation(
                "OUTPUT_IDENTITY_VALIDATION", operation, mapPort,
                outputPort, outputCell, 501L);
        outputObservation.addProperty("outputIdentityVerified", true);
        outputObservation.addProperty("outputArrayObjectToken", 701L);
        outputObservation.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        outputObservation.addProperty("outputDeclaredFieldOwnerVerified",
                true);
        outputObservation.addProperty("outputDeclaredFieldTypeVerified",
                true);
        outputObservation.addProperty("projectedFieldBindingCount", 2);
        outputObservation.addProperty("outputFieldValueVerifiedCount", 2);
        outputObservation.addProperty("outputFieldValueFlowVerified", true);
        outputObservation.addProperty("fieldValueFlowAuthority",
                "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                        + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_"
                        + "RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK");

        JsonArray bindings = new JsonArray();
        JsonArray fieldObservations = new JsonArray();
        JsonArray symbolized = singletonString(mapPort);
        for (int index = 0; index < 2; index++) {
            String dynamic = mapPort + ".field."
                    + testSha256(materializationSite).substring(0, 12)
                    + ".occ." + (index + 1);
            JsonObject selector = mapProjectionSelector(staticBindingId,
                    operation, mapPort, mapCell, outputPort, outputCell,
                    fieldSignature, index, 501L, 601L + index, 701L, true);
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 3);
            binding.addProperty("kind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", mapPort);
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId", materializationSite);
            binding.addProperty("materializationOccurrence", index + 1);
            binding.addProperty("fieldSignature", fieldSignature);
            binding.add("fieldPath", singletonString("expiry"));
            binding.addProperty("leafOwnerObjectToken", 601L + index);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.MAP");
            binding.add("mapProjectionSelector", selector);
            binding.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            binding.addProperty("complete", true);
            bindings.add(binding);
            symbolized.add(dynamic);

            JsonObject observedSelector = selector.deepCopy();
            observedSelector.addProperty("outputArrayObjectToken", 0L);
            observedSelector.addProperty("outputIdentityVerified", false);
            observedSelector.addProperty("outputVerificationAuthority", "");
            observedSelector.addProperty(
                    "noInterveningFieldWriteVerified", false);
            observedSelector.addProperty("outputFieldValueVerified", false);
            observedSelector.addProperty("fieldValueFlowAuthority", "");
            observedSelector.addProperty("complete", false);
            JsonObject field = new JsonObject();
            field.addProperty("symbol", dynamic);
            field.addProperty("phase", "AT_MAP_PROJECTION_ENTRY");
            field.add("path", singletonString("expiry"));
            field.addProperty("exactFieldSignature", fieldSignature);
            field.addProperty("exactFieldSignatureAuthority",
                    "BYTECODE_GETFIELD_DECLARING_OWNER_NAME_AND_TYPE");
            field.addProperty("accessOwnerClass", "example.Value");
            field.addProperty("accessOwnerObjectToken", 601L + index);
            field.addProperty("accessOwnerObjectTokenKnown", true);
            field.addProperty("leafOwnerClass", "example.Value");
            field.addProperty("leafOwnerObjectToken", 601L + index);
            field.addProperty("leafOwnerObjectTokenKnown", true);
            field.addProperty("available", true);
            field.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            field.addProperty("objectTokenScope", "ACT.MAP");
            field.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            field.addProperty("dynamicFieldBindingKind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            field.add("mapProjectionSelector", observedSelector);
            fieldObservations.add(field);
        }

        if ("SCOPE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "objectTokenScope", "ACT.OTHER");
        } else if ("TOKEN".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "elementObjectToken", 0L);
        } else if ("ORDER".equals(fault)) {
            JsonElement first = bindings.remove(0);
            bindings.add(first);
        } else if ("LENGTH".equals(fault)) {
            entry.addProperty("snapshotElementCount", 3);
        } else if ("IDENTITY".equals(fault)) {
            outputObservation.addProperty("outputIdentityVerified", false);
        } else if ("TYPE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "declaredFieldType", "int");
        } else if ("DUPLICATE_KEY".equals(fault)) {
            entry.getAsJsonArray("snapshotEntryKeyExpressions").set(1,
                    entry.getAsJsonArray("snapshotEntryKeyExpressions")
                            .get(0).deepCopy());
        } else if ("FLOAT_ZERO_KEY".equals(fault)) {
            JsonObject negativeZero = constant("Y_F_-0.0",
                    "java/lang/Float");
            entry.getAsJsonArray("snapshotEntryKeyExpressions").set(0,
                    negativeZero.deepCopy());
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").add("expectedMapKey",
                    negativeZero.deepCopy());
            fieldObservations.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").add("expectedMapKey",
                    negativeZero.deepCopy());
        } else if ("IDENTITY_MAP".equals(fault)) {
            entry.addProperty("mapImplementationClass",
                    "java.util.IdentityHashMap");
            outputObservation.addProperty("mapImplementationClass",
                    "java.util.IdentityHashMap");
            for (JsonElement element : bindings) {
                element.getAsJsonObject().getAsJsonObject(
                        "mapProjectionSelector").addProperty(
                        "mapImplementationClass",
                        "java.util.IdentityHashMap");
            }
            for (JsonElement element : fieldObservations) {
                element.getAsJsonObject().getAsJsonObject(
                        "mapProjectionSelector").addProperty(
                        "mapImplementationClass",
                        "java.util.IdentityHashMap");
            }
        } else if ("FIELD_WRITE".equals(fault)) {
            bindings.get(0).getAsJsonObject().getAsJsonObject(
                    "mapProjectionSelector").addProperty(
                    "noInterveningFieldWriteVerified", false);
        } else if ("FIELD_VALUE".equals(fault)) {
            outputObservation.addProperty("outputFieldValueFlowVerified",
                    false);
        } else if ("IMPLEMENTATION_DRIFT".equals(fault)) {
            outputObservation.addProperty("mapImplementationClass",
                    "java.util.HashMap");
        } else if ("FIELD_SIGNATURE_DRIFT".equals(fault)) {
            fieldObservations.get(0).getAsJsonObject().addProperty(
                    "exactFieldSignature", "<example.Value: int expiry>");
        }

        JsonObject engine = new JsonObject();
        engine.addProperty("active", true);
        engine.addProperty("regionId", "REGION.MAP");
        engine.addProperty("activationId", "ACT.MAP");
        engine.add("pathCondition", new JsonArray());
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("activationId", "ACT.MAP");
        raw.addProperty("regionId", "REGION.MAP");
        raw.addProperty("exitKind", "NORMAL");
        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", symbolized);
        raw.add("dynamicFieldBindings", bindings);
        raw.add("fieldObservations", fieldObservations);
        JsonArray projectionRows = new JsonArray();
        projectionRows.add(entry);
        projectionRows.add(outputObservation);
        raw.add("mapValueElementProjectionObservations", projectionRows);
        raw.add("rootOutputExpression", arrayValueExpression(
                "[Lexample/Value;", "Lexample/Value;", true,
                symbol("M_L_map_output_0", "Lexample/Value;"),
                symbol("M_L_map_output_1", "Lexample/Value;")));
        raw.add("engineSummary", engine);
        write(results, raw + "\n");

        ConcolicSummaryImporter.importSummaries(results, activations, regions,
                output, diagnostics);
        String rows = new String(Files.readAllBytes(output),
                StandardCharsets.UTF_8).trim();
        JsonObject summary = rows.isEmpty() ? new JsonObject()
                : JsonParser.parseString(rows).getAsJsonObject();
        return new MapFixture(summary, readOptional(diagnostics));
    }

    private static JsonObject mapProjectionObservation(
            String phase, String operation, String mapPort,
            String outputPort, String outputCell, long mapToken) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "MAP_VALUE_OUTPUT_ARRAY_PROJECTION");
        row.addProperty("phase", phase);
        row.addProperty("groupId", mapPort + "\n" + outputPort + "\n"
                + outputCell + "\n" + operation);
        row.addProperty("mapInputPort", mapPort);
        row.addProperty("outputPort", outputPort);
        row.addProperty("outputCell", outputCell);
        row.addProperty("mapProjectionOperation", operation);
        row.addProperty("mapObjectToken", mapToken);
        row.addProperty("mapImplementationClass",
                "java.util.LinkedHashMap");
        row.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        row.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        row.addProperty("objectTokenScope", "ACT.MAP");
        row.addProperty("crossExecutionOrdinalAuthority", "NONE");
        row.addProperty("identityPolicy",
                "ENTRYSET_KEY_AND_MAP_VIEW_ELEMENT_SAME_EXECUTION_"
                        + "POSITIONAL_REFERENCE_EQUALITY");
        row.addProperty("entrySetViewOrderVerified", true);
        row.addProperty("entrySetViewOrderAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        row.addProperty("complete", true);
        return row;
    }

    private static JsonObject mapProjectionSelector(
            String bindingId, String operation, String mapPort,
            String mapCell, String outputPort, String outputCell,
            String signature, int index, long mapToken, long elementToken,
            long outputToken, boolean complete) {
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", bindingId);
        selector.addProperty("mapInputPort", mapPort);
        selector.addProperty("mapInputCell", mapCell);
        selector.addProperty("outputPort", outputPort);
        selector.addProperty("outputCell", outputCell);
        selector.addProperty("mapProjectionOperation", operation);
        selector.addProperty("outputIndex", index);
        selector.addProperty("elementOccurrence", index + 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature", signature);
        selector.addProperty("mapObjectToken", mapToken);
        selector.addProperty("elementObjectToken", elementToken);
        selector.addProperty("outputArrayObjectToken", outputToken);
        selector.addProperty("outputIdentityVerified", complete);
        selector.addProperty("outputVerificationAuthority", complete
                ? "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD" : "");
        selector.addProperty("mapImplementationClass",
                "java.util.LinkedHashMap");
        selector.addProperty("mapImplementationAuthority",
                "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_LINKEDHASHMAP_"
                        + "JAVA_EQUALS_HASHCODE_EXTENSIONAL_V1");
        selector.addProperty("entryConcreteFieldValueCaptured", true);
        selector.addProperty("noInterveningFieldWriteVerified", complete);
        selector.addProperty("outputFieldValueVerified", complete);
        selector.addProperty("fieldValueFlowAuthority", complete
                ? "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_INTERVENING_"
                + "RUNTIME_FIELD_WRITE_AND_EXACT_OUTPUT_RECHECK" : "");
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.MAP");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        selector.add("expectedMapKey", constant("Y_I_"
                + (index == 0 ? "11" : "22"), "java/lang/Integer"));
        selector.addProperty("expectedMapKeyAuthority",
                "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
        selector.addProperty("sourceOutputIndexAuthority",
                "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                        + "REFERENCE_EQUALITY");
        selector.addProperty("replaySelectionAuthority",
                "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("authority",
                "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_EXACT_"
                        + "OUTPUT_IDENTITY");
        selector.addProperty("complete", complete);
        return selector;
    }


    private static String testSha256(String value) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256").digest(
                value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte current : digest) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }

    private static JsonObject engineArrayInputBinding(
            String port, String cell, String engineArrayId,
            long objectToken) {
        JsonObject expression = arrayValueExpression(
                "[Ljava/lang/Object;", "Ljava/lang/Object;", true);
        expression.addProperty("_engine_array_id", engineArrayId);
        expression.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        result.addProperty("sourceActivationId", "ACT.ARRAY");
        result.addProperty("inputPort", port);
        result.addProperty("inputCell", cell);
        result.addProperty("inputJavaType", "java.lang.Object[]");
        result.addProperty("inputJavaTypeDescriptor",
                "[Ljava/lang/Object;");
        result.addProperty("symbolizationPrefix", port);
        result.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        result.addProperty("engineArrayId", engineArrayId);
        result.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        result.addProperty("arrayObjectToken", objectToken);
        result.addProperty("symbolizationArrayObjectToken", objectToken);
        result.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        result.addProperty("sameArrayObjectTokenVerified", true);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", "ACT.ARRAY");
        result.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        result.add("arrayValueExpression", expression);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject arrayValueExpression(
            String javaType, String componentType, boolean complete,
            JsonElement... expressions) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ArrayValueExpression");
        result.addProperty("_schema_version", 1);
        result.addProperty("_java_type", javaType);
        result.addProperty("_component_java_type", componentType);
        result.addProperty("_concrete_length", expressions.length);
        result.add("_length_exp", constant("Y_I_" + expressions.length,
                "I"));
        result.addProperty("_elements_complete", complete);
        result.addProperty("_authority",
                "VM_EXACT_FINITE_ARRAY_VALUE_V1");
        JsonArray elements = new JsonArray();
        for (int index = 0; index < expressions.length; index++) {
            JsonObject element = new JsonObject();
            element.addProperty("index", index);
            element.addProperty("provenance", "SYMBOLIC_ELEMENT");
            element.add("expression", expressions[index].deepCopy());
            elements.add(element);
        }
        result.add("_elements", elements);
        return result;
    }

    private static JsonObject methodExpression(String name, int line,
                                               JsonElement... parameters) {
        return methodExpressionAt(name, "example.Store.update()", line,
                parameters);
    }

    private static JsonObject methodExpressionAt(
            String name, String method, int line, JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "MethodExpression");
        result.addProperty("_name", name);
        result.addProperty("_code_position", "virtual void " + method
                + ":" + line);
        JsonArray params = new JsonArray();
        for (JsonElement parameter : parameters) {
            params.add(parameter);
        }
        result.add("_param_list", params);
        result.add("_res_exp", JsonNull.INSTANCE);
        return result;
    }

    private static JsonObject symbol(String expression, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject constant(String expression, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject stringConstant(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "java/lang/String");
        result.addProperty("_exp", "Y_L'String'_" + value);
        return result;
    }

    private static JsonObject stringPredicate(String codePosition,
                                              String operation,
                                              boolean negated,
                                              JsonElement... parameters) {
        JsonObject result = new JsonObject();
        result.addProperty("_code_position", codePosition);
        result.addProperty("_type", "OpStrExpression");
        result.addProperty("_name", operation);
        result.addProperty("_is_not", negated);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : parameters) {
            arguments.add(parameter);
        }
        result.add("_param_list", arguments);
        return result;
    }

    private static JsonObject symbolCopy(JsonObject value) {
        return value.deepCopy();
    }

    private static String effect(JsonArray effects, int index, String field) {
        return effects.get(index).getAsJsonObject().get(field).getAsString();
    }

    private static final class MapFixture {
        private final JsonObject summary;
        private final String diagnostics;

        private MapFixture(JsonObject summary, String diagnostics) {
            this.summary = summary;
            this.diagnostics = diagnostics;
        }
    }

    private static final class PlaceholderFixture {
        private final JsonObject summary;
        private final String diagnostics;

        private PlaceholderFixture(JsonObject summary, String diagnostics) {
            this.summary = summary;
            this.diagnostics = diagnostics;
        }
    }

    private static String readOptional(Path path) throws Exception {
        return Files.exists(path)
                ? new String(Files.readAllBytes(path), StandardCharsets.UTF_8)
                : "";
    }

    private static void write(Path path, String value) throws Exception {
        String[] lines = value.split("\\n", -1);
        StringBuilder canonical = new StringBuilder();
        for (int index = 0; index < lines.length; index++) {
            String line = lines[index];
            if (!line.trim().isEmpty()) {
                JsonElement parsed = JsonParser.parseString(line);
                if (parsed.isJsonObject()
                        && "CONCOLIC_REGION_RESULT".equals(
                        parsed.getAsJsonObject().has("event")
                                ? parsed.getAsJsonObject().get("event")
                                .getAsString() : "")) {
                    line = canonicalRuntimeResultForTest(
                            parsed.getAsJsonObject()).toString();
                } else if (parsed.isJsonObject()
                        && parsed.getAsJsonObject().has("activationId")) {
                    JsonObject activation = parsed.getAsJsonObject();
                    if (!activation.has("materializations")) {
                        JsonElement declarations = activation.get(
                                "symbolize");
                        activation.add("materializations",
                                declarations != null
                                        && declarations.isJsonArray()
                                        ? declarations.deepCopy()
                                        : new JsonArray());
                    }
                    canonicalizeOutputClosureForTest(activation);
                    line = activation.toString();
                }
            }
            canonical.append(line);
            if (index + 1 < lines.length) canonical.append('\n');
        }
        writeVerbatim(path, canonical.toString());
    }

    private static void canonicalizeOutputClosureForTest(
            JsonObject activation) {
        if (activation.has(OutputClosureContract.FIELD)
                || !RegionCaptureGoal.from(activation).isOutputClosure()) {
            return;
        }
        JsonObject requested = activation.has("requestedOutput")
                ? activation.getAsJsonObject("requestedOutput").deepCopy()
                : new JsonObject();
        JsonObject outputAction = new JsonObject();
        for (JsonElement element : activation.has("outputs")
                ? activation.getAsJsonArray("outputs") : new JsonArray()) {
            if (element.isJsonObject()) {
                outputAction = element.getAsJsonObject();
                break;
            }
        }
        String port = firstNonBlankForTest(
                textForTest(requested, "portId"),
                textForTest(outputAction, "symbol"));
        String kind = firstNonBlankForTest(
                textForTest(requested, "kind"),
                textForTest(outputAction, "kind"));
        if ("PRIMITIVE".equals(kind)) kind = "RETURN";
        if (kind.isEmpty()) {
            kind = "THROW_OR_BRANCH".equals(textForTest(
                    outputAction, "location"))
                    ? "FAILURE_PREDICATE" : "RETURN";
        }
        String rootMethod = textForTest(activation, "rootMethod");
        String cell = firstNonBlankForTest(
                textForTest(requested, "cell"),
                textForTest(outputAction, "cell"),
                "FAILURE_PREDICATE".equals(kind)
                        ? rootMethod + ".failure"
                        : rootMethod + ".return");

        JsonObject slice = activation.has("requestedOutputSlice")
                ? activation.getAsJsonObject("requestedOutputSlice")
                .deepCopy() : new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        if (!slice.has("complete")) slice.addProperty("complete", true);
        ensureStringArray(slice, "inputPorts", new JsonArray());
        ensureStringArray(slice, "sites", new JsonArray());
        ensureStringArray(slice, "staticSites", new JsonArray());
        JsonArray methods = activation.has("requestedOutputMethods")
                ? activation.getAsJsonArray("requestedOutputMethods")
                .deepCopy() : new JsonArray();
        if (methods.size() == 0 && !rootMethod.isEmpty()) {
            methods.add(rootMethod);
        }
        ensureStringArray(slice, "methods", methods);
        JsonArray causalEdgeIds = new JsonArray();
        for (JsonElement element : slice.has("causalEdges")
                ? slice.getAsJsonArray("causalEdges") : new JsonArray()) {
            if (element.isJsonObject()
                    && !textForTest(element.getAsJsonObject(),
                    "edgeId").isEmpty()) {
                causalEdgeIds.add(textForTest(
                        element.getAsJsonObject(), "edgeId"));
            }
        }
        ensureStringArray(slice, "causalEdgeIds", causalEdgeIds);
        JsonArray captures = activation.has("requestedOutputCapture")
                ? activation.getAsJsonArray("requestedOutputCapture")
                .deepCopy() : new JsonArray();
        slice.add("captureBindings", captures);
        slice.addProperty("captureBindingsRequired",
                captures.size() > 0);
        slice.addProperty("captureBindingsComplete",
                !activation.has("requestedOutputCaptureComplete")
                        || activation.get(
                        "requestedOutputCaptureComplete").getAsBoolean());

        String regionId = textForTest(activation, "regionId");
        if (!activation.has("rootCallId")) {
            activation.addProperty("rootCallId", 0);
        }
        long rootCallId = activation.get("rootCallId").getAsLong();
        if (!activation.has("regionInstanceId")) {
            activation.addProperty("regionInstanceId",
                    regionId + "@test#call" + rootCallId);
        }
        OutputClosureCodec.writeTo(activation,
                OutputClosureCodec.singleton(
                        regionId,
                        textForTest(activation, "regionInstanceId"),
                        rootCallId, port, cell, kind,
                        "TEST_FIXTURE_DECLARATION", slice));
    }

    private static void ensureStringArray(
            JsonObject target, String field, JsonArray fallback) {
        if (!target.has(field)) target.add(field, fallback);
    }

    private static String textForTest(JsonObject value, String field) {
        JsonElement element = value == null ? null : value.get(field);
        return element != null && element.isJsonPrimitive()
                ? element.getAsString() : "";
    }

    private static String firstNonBlankForTest(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return "";
    }

    private static JsonObject canonicalRuntimeResultForTest(JsonObject raw) {
        JsonObject result = raw.deepCopy();
        if (!result.has("schemaVersion")) {
            result.addProperty("schemaVersion", 1);
        }
        if (!result.has("executionMode")) {
            result.addProperty("executionMode", "SYMBOLIC_CONCOLIC");
        }
        if (!result.has("pathConditionIsolationPolicy")) {
            result.addProperty("pathConditionIsolationPolicy",
                    ConcolicSummaryImporter.PATH_CONDITION_ISOLATION_POLICY);
        }
        for (String field : new String[]{"runtimeHeapObservations",
                "dynamicFieldBindings"}) {
            if (!result.has(field)) result.add(field, new JsonArray());
        }

        JsonObject engine = result.has("engineSummary")
                && result.get("engineSummary").isJsonObject()
                ? result.getAsJsonObject("engineSummary")
                : new JsonObject();
        if (!engine.has("schemaVersion")) {
            engine.addProperty("schemaVersion", 1);
        }
        if (!engine.has("engine")) {
            engine.addProperty("engine", "openjdk8-zero-concolic");
        }
        if (!engine.has("active")) engine.addProperty("active", true);
        if (!engine.has("regionId")) {
            engine.addProperty("regionId", result.get("regionId")
                    .getAsString());
        }
        if (!engine.has("activationId")) {
            engine.addProperty("activationId", result.get("activationId")
                    .getAsString());
        }
        if (!engine.has("threadContextId")) {
            engine.addProperty("threadContextId", 1L);
        }
        if (!engine.has("pathConditionRecordingPaused")) {
            engine.addProperty("pathConditionRecordingPaused", true);
        }
        if (!engine.has("pathConditionPauseDepth")) {
            engine.addProperty("pathConditionPauseDepth", 1);
        }
        if (!engine.has("pathCondition")) {
            engine.add("pathCondition", new JsonArray());
        }
        result.add("engineSummary", engine);
        return result;
    }

    private static void writeVerbatim(Path path, String value)
            throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }
}
