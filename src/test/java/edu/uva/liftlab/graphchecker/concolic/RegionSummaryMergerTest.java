package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
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
        JsonObject first = summary("A", ">");
        JsonObject second = summary("B", "<=");
        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), manifestFor(first));

        assertEquals(1, result.summaries.size());
        JsonObject relation = result.summaries.get(0)
                .getAsJsonObject("regionRelation");
        assertEquals("GUARDED_PATH_MERGE",
                relation.get("kind").getAsString());
        assertEquals(2, relation.getAsJsonArray("cases").size());
        assertFalse(relation.has("caseCount"));
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
        assertEquals(1, result.summaries.get(0).getAsJsonArray(
                "sourceRegionInstanceIds").size());
    }

    @Test
    public void mergesCanonicalJointAndPreservesSingletonHeapSemantics() {
        JsonObject first = jointSummary("JOINT.A", ">");
        JsonObject second = jointSummary("JOINT.B", "<=");

        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(first, second), manifestFor(first));

        assertEquals(1, result.summaries.size());
        JsonObject merged = result.summaries.get(0);
        assertTrue(merged.has(OutputClosureContract.FIELD));
        assertFalse(merged.has("requestedOutput"));
        assertFalse(merged.has("requestedOutputSlice"));
        OutputClosureContract contract = OutputClosureCodec.decode(merged);
        assertEquals(2, contract.members().size());
        JsonArray cases = merged.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        assertEquals(2, cases.size());
        for (com.google.gson.JsonElement element : cases) {
            assertEquals(Arrays.asList("REGION.4.out.0",
                            "REGION.4.out.1"),
                    new java.util.ArrayList<>(element.getAsJsonObject()
                            .getAsJsonObject("outputExpressions").keySet()));
        }
        assertTrue(merged.get("relationallyComplete").getAsBoolean());

        JsonObject heap = heapSingletonSummary("HEAP", ">");
        RegionSummaryMerger.Result heapResult = RegionSummaryMerger.merge(
                Arrays.asList(heap), manifestFor(heap));
        JsonObject mergedHeap = heapResult.summaries.get(0);
        assertTrue(mergedHeap.has(OutputClosureContract.FIELD));
        assertEquals(0, mergedHeap.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject()
                .getAsJsonObject("outputExpressions").size());
        assertTrue(mergedHeap.get(
                "relationallyComplete").getAsBoolean());
    }

    @Test
    public void canonicalJointContractViolationsFailClosed() {
        JsonObject missing = jointSummary("MISSING.Y", ">");
        missing.getAsJsonObject("outputExpressions").remove(
                "REGION.4.out.1");

        RegionSummaryMerger.Result missingResult =
                RegionSummaryMerger.merge(
                        Arrays.asList(missing), manifestFor(missing));

        JsonObject missingRelation = missingResult.summaries.get(0)
                .getAsJsonObject("regionRelation");
        assertEquals(0, missingRelation.getAsJsonArray("cases").size());
        assertFalse(missingRelation.get("complete").getAsBoolean());
        assertTrue(missingResult.manifest.getAsJsonArray(
                "diagnostics").toString()
                .contains("JOINT_OUTPUT_EXPRESSION_SET_MISMATCH"));

        JsonObject wrongManifest = jointSummary("MANIFEST", ">");
        JsonObject manifest = manifestFor(wrongManifest);
        manifest.addProperty("outputClosureFingerprint", "wrong");

        RegionSummaryMerger.Result manifestResult =
                RegionSummaryMerger.merge(
                        Arrays.asList(wrongManifest), manifest);

        assertFalse(manifestResult.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertTrue(manifestResult.manifest.getAsJsonArray(
                "diagnostics").toString()
                .contains("PATH_WORKLIST_OUTPUT_CLOSURE_"
                        + "FINGERPRINT_MISMATCH"));

        JsonObject first = jointSummary("DUP.A", ">");
        JsonObject second = jointSummary("DUP.B", ">");
        JsonObject observation = new JsonObject();
        observation.addProperty("observationId", "different");
        JsonArray observations = new JsonArray();
        observations.add(observation);
        second.add("heapObservations", observations);

        RegionSummaryMerger.Result duplicateResult =
                RegionSummaryMerger.merge(
                Arrays.asList(first, second), manifestFor(first));

        JsonObject duplicateRelation = duplicateResult.summaries.get(0)
                .getAsJsonObject("regionRelation");
        assertEquals(1, duplicateRelation.getAsJsonArray("cases").size());
        assertFalse(duplicateRelation.get("complete").getAsBoolean());
        assertTrue(duplicateResult.manifest.getAsJsonArray(
                "diagnostics").toString()
                .contains("CONFLICTING_DUPLICATE_PATH_PAYLOAD"));
    }

    @Test
    public void openPathWorklistCannotBecomeAnAutomaticCompleteRelation() {
        JsonObject summary = summary("A", ">");
        JsonObject manifest = manifestFor(summary);
        manifest.addProperty("state", RegionPathWorklist.State.PENDING.name());
        RegionSummaryMerger.Result result = RegionSummaryMerger.merge(
                Arrays.asList(summary), manifest);

        assertFalse(result.summaries.get(0).getAsJsonObject(
                "regionRelation").get("complete").getAsBoolean());
        assertFalse(result.summaries.get(0).get(
                "relationallyComplete").getAsBoolean());
    }

    private static JsonObject jointSummary(String id, String operator) {
        JsonObject summary = explicitSummary(id, operator,
                outputClosure(false, 2));
        JsonObject expression = summary.getAsJsonObject(
                "outputExpressions").getAsJsonObject(
                "REGION.4.out.0").deepCopy();
        summary.getAsJsonObject("outputExpressions").add(
                "REGION.4.out.1", expression);
        return summary;
    }

    private static JsonObject heapSingletonSummary(
            String id, String operator) {
        JsonObject summary = explicitSummary(id, operator,
                outputClosure(true, 1));
        summary.add("outputExpressions", new JsonObject());
        return summary;
    }

    private static JsonObject explicitSummary(
            String id, String operator, JsonObject closure) {
        JsonObject summary = summary(id, operator);
        summary.addProperty("regionInstanceId",
                "REGION.4@fixture#call7");
        summary.addProperty("rootCallId", 7);
        summary.remove("requestedOutput");
        summary.add(OutputClosureContract.FIELD, closure);
        return summary;
    }

    private static JsonObject outputClosure(
            boolean heapSingleton, int memberCount) {
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 1);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", "REGION.4");
        producer.addProperty("regionInstanceId",
                "REGION.4@fixture#call7");
        producer.addProperty("rootCallId", 7);
        closure.add("producer", producer);
        JsonArray members = new JsonArray();
        for (int index = 0; index < memberCount; index++) {
            members.add(outputMember(index, heapSingleton));
        }
        closure.add("members", members);
        return closure;
    }

    private static JsonObject outputMember(
            int index, boolean heapSingleton) {
        String port = "REGION.4.out." + index;
        String cell = heapSingleton
                ? "<example.State: java.util.Map values>"
                : "<example.State: int "
                + (index == 0 ? "x" : "y") + ">";
        JsonObject member = new JsonObject();
        JsonObject output = new JsonObject();
        output.addProperty("portId", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor",
                heapSingleton ? "Ljava/util/Map;" : "I");
        output.addProperty("selectionAuthority",
                "CONFIRMED_READ_FROM_EDGE");
        member.add("output", output);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        String method = "<example.Producer: void run()>";
        methods.add(method);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        if (!heapSingleton) {
            JsonObject capture = new JsonObject();
            capture.addProperty("captureKind",
                    "FIELD_ASSIGNMENT_RHS");
            capture.addProperty("captureBindingId",
                    port + ".capture");
            capture.addProperty("outputPort", port);
            capture.addProperty("outputCell", cell);
            capture.addProperty("method", method);
            capture.addProperty("unitIndex", index);
            capture.addProperty("siteId", method + "#u" + index);
            capture.addProperty("fieldSignature", cell);
            captures.add(capture);
        }
        slice.addProperty("captureBindingsRequired", !heapSingleton);
        slice.addProperty("captureBindingsComplete", true);
        slice.add("captureBindings", captures);
        member.add("slice", slice);
        return member;
    }

    private static JsonObject manifestFor(JsonObject summary) {
        OutputClosureContract contract = OutputClosureCodec.decode(summary);
        JsonObject manifest = closedManifest();
        manifest.addProperty("outputDemandKey", contract.demandKey());
        manifest.addProperty("outputClosureFingerprint",
                contract.closureFingerprint());
        return manifest;
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
                "REGION.4@fixture#call7");
        summary.addProperty("rootCallId", 7);
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        summary.add(OutputClosureContract.FIELD, outputClosure(false, 1));
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
