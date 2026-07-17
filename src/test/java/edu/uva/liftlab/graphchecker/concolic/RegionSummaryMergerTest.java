package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RegionSummaryMergerTest {
    @Test
    public void mergesOutputPathsUnderTheirOwnGuards() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("complete", true);
        manifest.addProperty("status", "COMPLETE_BOUNDED_PATH_CLOSURE");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">"), summary("B", "<=")),
                manifest);

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
        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertFalse(result.summaries.get(0).has("protocolModel"));
        assertEquals(2, result.summaries.get(0).getAsJsonArray(
                "sourceRegionInstanceIds").size());
    }

    @Test
    public void openPathWorklistCannotBecomeAnAutomaticCompleteRelation() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("complete", false);
        manifest.addProperty("status", "PATH_CLOSURE_HAS_PENDING_WORK");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary("A", ">")), manifest);

        assertFalse(result.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertEquals("REGION_RELATIONS_WITH_EXPLICIT_GAPS",
                result.manifest.get("status").getAsString());
    }

    @Test
    public void alphaEquivalentJvmLocalNamesMergeAsOnePathCase() {
        JsonObject first = summary("A", ">");
        JsonObject second = summary("B", ">");
        setLocalSymbol(first, "M_I_1");
        setLocalSymbol(second, "M_I_41");
        JsonObject manifest = new JsonObject();
        manifest.addProperty("complete", true);
        manifest.addProperty("status", "COMPLETE_BOUNDED_PATH_CLOSURE");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), manifest);

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
        JsonObject manifest = new JsonObject();
        manifest.addProperty("complete", true);
        manifest.addProperty("status", "COMPLETE_BOUNDED_PATH_CLOSURE");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary), manifest);

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
        JsonObject manifest = new JsonObject();
        manifest.addProperty("complete", true);
        manifest.addProperty("status", "COMPLETE_BOUNDED_PATH_CLOSURE");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), manifest);

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
}
