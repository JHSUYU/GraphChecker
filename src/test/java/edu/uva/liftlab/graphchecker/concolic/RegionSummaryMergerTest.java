package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RegionSummaryMergerTest {
    @Rule
    public final TemporaryFolder temporaryFolder = new TemporaryFolder();

    @Test
    public void mergesOutputPathsUnderTheirOwnGuards() {
        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">"), summary("B", "<=")),
                closedManifest());

        assertEquals(1, result.summaries.size());
        JsonObject relation = result.summaries.get(0)
                .getAsJsonObject("regionRelation");
        assertEquals("GUARDED_PATH_MERGE",
                relation.get("kind").getAsString());
        assertEquals(2, relation.get("caseCount").getAsInt());
        for (com.google.gson.JsonElement element : relation.getAsJsonArray(
                "cases")) {
            JsonObject pathCase = element.getAsJsonObject();
            assertTrue(pathCase.get("symbolScope").getAsString().startsWith(
                    "region:REGION.4/case:CASE."));
        }
        assertTrue(relation.get("complete").getAsBoolean());
        assertTrue(result.summaries.get(0).get(
                "relationallyComplete").getAsBoolean());
        assertFalse(result.summaries.get(0).has("protocolModel"));
        assertEquals(2, result.summaries.get(0).getAsJsonArray(
                "sourceRegionInstanceIds").size());
    }

    @Test
    public void openPathWorklistCannotBecomeAnAutomaticCompleteRelation() {
        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">")),
                pathManifest(RegionPathWorklist.State.PENDING));

        assertFalse(result.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertFalse(result.summaries.get(0).get(
                "relationallyComplete").getAsBoolean());
    }

    @Test
    public void closedStateWithoutAnObservedPathFailsClosed() {
        JsonObject manifest = closedManifest();
        manifest.addProperty("observedPathCount", 0);

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">")), manifest);

        assertFalse(result.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("diagnostics").toString()
                .contains("PATH_WORKLIST_HAS_NO_OBSERVED_PATH"));
    }

    @Test
    public void closureForAnotherRegionCannotCertifyThisRelation() {
        JsonObject manifest = closedManifest();
        manifest.addProperty("regionId", "REGION.OTHER");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">")), manifest);

        assertFalse(result.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertTrue(result.manifest.getAsJsonArray("diagnostics").toString()
                .contains("PATH_WORKLIST_REGION_MISMATCH"));
    }

    @Test
    public void commandDoesNotPersistAMergeManifestUnlessRequested()
            throws Exception {
        Path directory = temporaryFolder.newFolder("merge-cli").toPath();
        Path summaries = directory.resolve("summaries.jsonl");
        Path pathManifest = directory.resolve("path-manifest.json");
        Path output = directory.resolve("merged.jsonl");
        Path oldDefault = directory.resolve(
                "region_relation_merge_manifest.json");
        Files.write(summaries, (summary("CLI", ">").toString() + "\n")
                .getBytes(StandardCharsets.UTF_8));
        Files.write(pathManifest, closedManifest().toString()
                .getBytes(StandardCharsets.UTF_8));

        RegionSummaryMerger.main(new String[]{
                "--summaries", summaries.toString(),
                "--path-manifest", pathManifest.toString(),
                "--output", output.toString()
        });

        assertTrue(Files.isRegularFile(output));
        assertFalse(Files.exists(oldDefault));
        JsonObject merged = JsonParser.parseString(
                new String(Files.readAllBytes(output),
                        StandardCharsets.UTF_8).trim()).getAsJsonObject();
        assertTrue(merged.get("relationallyComplete").getAsBoolean());
        assertTrue(merged.getAsJsonObject("regionRelation")
                .get("complete").getAsBoolean());
    }

    @Test
    public void noValidOutputClosureCannotReportACompleteMerge() {
        JsonObject invalid = summary("INVALID", ">");
        invalid.addProperty("valid", false);

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(invalid), closedManifest());

        assertTrue(result.summaries.isEmpty());
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals("REGION_RELATIONS_WITH_EXPLICIT_GAPS",
                result.manifest.get("status").getAsString());
        assertEquals(1, result.manifest.get("diagnosticCount").getAsInt());
        assertEquals("NO_VALID_OUTPUT_CLOSURE_RELATIONS",
                result.manifest.getAsJsonArray("diagnostics").get(0)
                        .getAsJsonObject().get("reason").getAsString());
    }

    @Test
    public void alphaEquivalentJvmLocalNamesMergeAsOnePathCase() {
        JsonObject first = summary("A", ">");
        JsonObject second = summary("B", ">");
        setLocalSymbol(first, "M_I_1");
        setLocalSymbol(second, "M_I_41");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), closedManifest());

        JsonObject relation = result.summaries.get(0).getAsJsonObject(
                "regionRelation");
        assertEquals(1, relation.get("caseCount").getAsInt());
    }

    @Test
    public void preservesNormalizedHeapObservationsInsideEachCase() {
        JsonObject summary = summary("OBS", ">");
        JsonObject observation = new JsonObject();
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("observationId", "OBS.1");
        JsonArray observations = new JsonArray();
        observations.add(observation);
        summary.add("heapObservations", observations);
        JsonObject dynamicBinding = new JsonObject();
        dynamicBinding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:REGION.4.in.0.field.a.occ.1");
        JsonArray dynamicBindings = new JsonArray();
        dynamicBindings.add(dynamicBinding);
        summary.add("dynamicFieldBindings", dynamicBindings);

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary), closedManifest());

        JsonObject pathCase = result.summaries.get(0).getAsJsonObject(
                "regionRelation").getAsJsonArray("cases").get(0)
                .getAsJsonObject();
        assertEquals(observations, pathCase.getAsJsonArray(
                "heapObservations"));
        assertEquals(dynamicBindings, pathCase.getAsJsonArray(
                "dynamicFieldBindings"));
        assertEquals(0, result.summaries.get(0).getAsJsonArray(
                "heapObservations").size());
        assertEquals(0, result.summaries.get(0).getAsJsonArray(
                "dynamicFieldBindings").size());
    }

    @Test
    public void preservesEngineArrayBridgeInsideItsSourceCase() {
        JsonObject first = summary("ARRAY.A", ">");
        JsonObject second = summary("ARRAY.B", "<=");
        first.add("engineArrayInputBindings",
                engineArrayBinding("VM_ARRAY_1", 11));
        second.add("engineArrayInputBindings",
                engineArrayBinding("VM_ARRAY_99", 99));

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), closedManifest());

        JsonArray cases = result.summaries.get(0).getAsJsonObject(
                "regionRelation").getAsJsonArray("cases");
        assertEquals(2, cases.size());
        JsonArray observed = new JsonArray();
        for (com.google.gson.JsonElement element : cases) {
            JsonObject pathCase = element.getAsJsonObject();
            assertEquals("ACT." + pathCase.get("sourceSummaryId")
                            .getAsString(),
                    pathCase.get("sourceActivationId").getAsString());
            observed.add(pathCase.getAsJsonArray(
                    "engineArrayInputBindings").get(0).getAsJsonObject()
                    .get("engineArrayId").getAsString());
        }
        assertTrue(observed.toString().contains("VM_ARRAY_1"));
        assertTrue(observed.toString().contains("VM_ARRAY_99"));
        assertEquals(0, result.summaries.get(0).getAsJsonArray(
                "engineArrayInputBindings").size());
    }

    @Test
    public void preservesFiniteMapAndVmCertificatesInsideSourceCase() {
        JsonObject summary = summary("CERT", ">");
        JsonObject snapshot = new JsonObject();
        snapshot.addProperty("snapshotId", "FINITE.1");
        JsonArray snapshots = new JsonArray();
        snapshots.add(snapshot);
        summary.add("finiteMapSnapshots", snapshots);

        JsonObject binding = new JsonObject();
        binding.addProperty("placeholderIdentity", "currentTimeMills#3");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("vmIntrinsicPlaceholderBindings", bindings);
        JsonObject bindingAdmission = new JsonObject();
        bindingAdmission.addProperty("complete", true);
        bindingAdmission.add("bindings", bindings.deepCopy());
        summary.add("vmIntrinsicPlaceholderBindingAdmission",
                bindingAdmission);
        JsonObject inputAdmission = new JsonObject();
        inputAdmission.addProperty("complete", true);
        summary.add("inputMaterializationAdmission", inputAdmission);
        JsonObject requirement = new JsonObject();
        requirement.addProperty("inputPort", "REGION.4.in.0");
        JsonArray requirements = new JsonArray();
        requirements.add(requirement);
        summary.add("unforcedEnvironmentValidationRequirements",
                requirements);

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary), closedManifest());

        JsonObject merged = result.summaries.get(0);
        JsonObject pathCase = merged.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        assertEquals(snapshots, pathCase.getAsJsonArray(
                "finiteMapSnapshots"));
        assertEquals(bindings, pathCase.getAsJsonArray(
                "vmIntrinsicPlaceholderBindings"));
        assertEquals(bindingAdmission, pathCase.getAsJsonObject(
                "vmIntrinsicPlaceholderBindingAdmission"));
        assertEquals(inputAdmission, pathCase.getAsJsonObject(
                "inputMaterializationAdmission"));
        assertEquals(requirements, pathCase.getAsJsonArray(
                "unforcedEnvironmentValidationRequirements"));
        assertEquals(0, merged.getAsJsonArray("finiteMapSnapshots").size());
        assertEquals(0, merged.getAsJsonArray(
                "vmIntrinsicPlaceholderBindings").size());
    }

    private static void setLocalSymbol(JsonObject summary, String raw) {
        summary.getAsJsonArray("pathCondition").get(0).getAsJsonObject()
                .getAsJsonObject("_left").addProperty("_exp", raw);
        summary.getAsJsonObject("outputExpressions")
                .getAsJsonObject("REGION.4.out.0")
                .addProperty("_exp", raw);
    }

    private static JsonObject summary(String id, String operator) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", id);
        summary.addProperty("activationId", "ACT." + id);
        summary.addProperty("regionId", "REGION.4");
        summary.addProperty("regionInstanceId",
                "REGION.4@fixture#call" + id);
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.4.out.0");
        summary.add("requestedOutput", output);
        JsonArray path = new JsonArray();
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.addProperty("_op", operator);
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "REGION.4.in.0");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        condition.add("_left", left);
        condition.add("_right", right);
        path.add(condition);
        summary.add("pathCondition", path);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.4.out.0", left.deepCopy());
        summary.add("outputExpressions", outputs);
        summary.add("heapStateInitializers", new JsonArray());
        summary.add("heapEffects", new JsonArray());
        JsonObject heapModel = new JsonObject();
        heapModel.addProperty("complete", true);
        heapModel.addProperty("effectCount", 0);
        heapModel.addProperty("initializerCount", 0);
        heapModel.addProperty("initializedInputCount", 0);
        heapModel.addProperty("mapStateFamilyCount", 0);
        summary.add("heapEffectModel", heapModel);
        return summary;
    }

    private static JsonArray engineArrayBinding(String id, long token) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        binding.addProperty("inputPort", "REGION.4.in.1");
        binding.addProperty("engineArrayId", id);
        binding.addProperty("arrayObjectToken", token);
        JsonArray result = new JsonArray();
        result.add(binding);
        return result;
    }

    private static JsonObject closedManifest() {
        return pathManifest(RegionPathWorklist.State.CLOSED);
    }

    private static JsonObject pathManifest(RegionPathWorklist.State state) {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "REGION_PATH_WORKLIST");
        manifest.addProperty("regionId", "REGION.4");
        manifest.addProperty("state", state.name());
        JsonObject bounds = new JsonObject();
        bounds.addProperty("maxPathsPerRegion", 64);
        bounds.addProperty("maxFlipsPerPath", 32);
        bounds.addProperty("maxTasks", 256);
        bounds.addProperty("maxWallClockMillis", 30_000L);
        manifest.add("bounds", bounds);
        manifest.addProperty("observedPathCount", 1);
        manifest.addProperty("pendingTaskCount",
                state == RegionPathWorklist.State.PENDING ? 1 : 0);
        manifest.add("gaps", new JsonArray());
        return manifest;
    }
}
