package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {
    @Test
    public void targetCaptureDoesNotEnumerateEveryRegionPath() {
        JsonObject summary = summary("ACT.TARGET",
                RegionCaptureGoal.targetBranch());
        JsonObject activation = activation("ACT.TARGET",
                RegionCaptureGoal.targetBranch());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertTrue(result.manifest.get("complete").getAsBoolean());
        assertEquals("ONE_DIRECTED_TARGET_BRANCH_OUTSIDE_THIS_WORKLIST",
                result.manifest.get("targetRegionPolicy").getAsString());
    }

    @Test
    public void outputCaptureFlipsLatestBranchAndDropsOldSuffix() {
        JsonObject summary = summary("ACT.NEW",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.NEW",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(2, result.tasks.size());
        JsonObject latest = result.tasks.get(0);
        assertEquals("SITE.1", latest.get("flipSite").getAsString());
        assertEquals(1, latest.getAsJsonArray("prefix").size());
        assertEquals(2, latest.getAsJsonArray("constraints").size());
        assertEquals(">=", latest.getAsJsonObject("negatedCondition")
                .get("_op").getAsString());
        assertEquals("DROP_OLD_SUFFIX",
                latest.get("suffixPolicy").getAsString());
        assertFalse(result.manifest.get("complete").getAsBoolean());
    }

    @Test
    public void legacySummaryWithoutPolicyStillEnumeratesEveryMapping() {
        JsonObject summary = summary("ACT.LEGACY",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.LEGACY",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(2, result.tasks.size());
        assertEquals("SITE.1", result.tasks.get(0).get("flipSite")
                .getAsString());
        assertEquals("SITE.0", result.tasks.get(1).get("flipSite")
                .getAsString());
    }

    @Test
    public void policyAwareSummaryEnumeratesOnlyExploreMappings() {
        JsonObject summary = summary("ACT.POLICY",
                RegionCaptureGoal.outputClosure());
        JsonArray mappings = summary.getAsJsonArray("branchMappings");
        mappings.get(0).getAsJsonObject().addProperty("policy",
                "PATH_ASSUMPTION");
        mappings.get(1).getAsJsonObject().addProperty("policy", "EXPLORE");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.POLICY",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(1, result.tasks.size());
        assertEquals("SITE.1", result.tasks.get(0).get("flipSite")
                .getAsString());
    }

    @Test
    public void policyAwareSummaryFailsClosedForMissingAndUnknownPolicies() {
        JsonObject summary = summary("ACT.FAIL.CLOSED",
                RegionCaptureGoal.outputClosure());
        summary.getAsJsonArray("branchMappings").get(1).getAsJsonObject()
                .addProperty("policy", "UNKNOWN");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.FAIL.CLOSED",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(0, result.manifest.get("candidateFlipCount").getAsInt());
    }

    @Test
    public void stableFlipIdentityExcludesActivationIdsAndUnsatClosesIt() {
        JsonObject first = summary("ACT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.2",
                RegionCaptureGoal.outputClosure());
        JsonObject activation1 = activation("ACT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject activation2 = activation("ACT.2",
                RegionCaptureGoal.outputClosure());

        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                Arrays.asList(first, second), Arrays.asList(activation1,
                        activation2), Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, initial.tasks.size());

        List<JsonObject> records = new ArrayList<>();
        for (JsonObject task : initial.tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey", task.get("queryKey").getAsString());
            record.addProperty("status", "UNSAT");
            records.add(record);
        }
        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Arrays.asList(first, second), Arrays.asList(activation1,
                        activation2), records,
                RegionPathWorklist.Bounds.defaults());

        assertTrue(closed.tasks.isEmpty());
        assertTrue(closed.manifest.get("complete").getAsBoolean());
        assertEquals(2, closed.manifest.get("terminalFlipCount").getAsInt());
    }

    @Test
    public void materializationGapIsTerminalAndSurfacesExplorationGap() {
        JsonObject summary = summary("ACT.GAP",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.GAP",
                RegionCaptureGoal.outputClosure());
        RegionPathWorklist.Result initial = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        List<JsonObject> records = new ArrayList<>();
        for (JsonObject task : initial.tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey",
                    task.get("queryKey").getAsString());
            record.addProperty("status", "MATERIALIZATION_GAP");
            record.addProperty("reason",
                    "OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT");
            records.add(record);
        }

        RegionPathWorklist.Result replanned = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation), records,
                RegionPathWorklist.Bounds.defaults());

        assertTrue(replanned.tasks.isEmpty());
        assertEquals(initial.tasks.size(), replanned.manifest.get(
                "terminalFlipCount").getAsInt());
        assertFalse(replanned.manifest.get("complete").getAsBoolean());
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("EXPLORATION_GAP"));
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT"));
    }

    @Test
    public void incompleteRegionSummaryIsAGapAndIsNeverFlipped() {
        JsonObject summary = summary("ACT.INCOMPLETE",
                RegionCaptureGoal.outputClosure());
        summary.addProperty("relationallyComplete", false);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.INCOMPLETE",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals("INCOMPLETE_REGION_SUMMARY", result.manifest
                .getAsJsonArray("gaps").get(0).getAsJsonObject()
                .get("kind").getAsString());
    }

    @Test
    public void quarantinedDiscoverySeedMayFlipOnlyItsReachabilityGuard() {
        JsonObject summary = summary("ACT.DISCOVERY",
                RegionCaptureGoal.transitionDiscovery());
        summary.addProperty("relationallyComplete", false);
        summary.addProperty("normalExit", true);
        summary.addProperty("requestedOutputSliceComplete", true);
        JsonObject slice = new JsonObject();
        slice.addProperty("complete", true);
        JsonArray sites = new JsonArray();
        sites.add("SITE.1");
        slice.add("sites", sites);
        slice.add("inputPorts", new JsonArray());
        summary.add("requestedOutputSlice", slice);
        JsonObject discovery = new JsonObject();
        discovery.addProperty("candidateEdgeId", "EDGE.P.C");
        discovery.addProperty("guardSiteId", "SITE.1");
        discovery.addProperty("guardOccurrence", 1);
        discovery.addProperty("desiredOutcome", false);
        discovery.addProperty("seedExecutionId", "EXEC.1");
        summary.add("transitionDiscovery", discovery);
        JsonObject activation = activation("ACT.DISCOVERY",
                RegionCaptureGoal.transitionDiscovery());

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject task = result.tasks.get(0);
        assertEquals("SITE.1", task.get("flipSite").getAsString());
        assertTrue(task.get("discoveryOnly").getAsBoolean());
        assertTrue(RegionCaptureGoal.from(task).isTransitionDiscovery());
        assertEquals("QUARANTINED", task.get(
                "summaryCacheAdmission").getAsString());
        assertEquals(1, result.manifest.get(
                "transitionDiscoveryTaskCount").getAsInt());

        JsonObject anotherExecution = summary.deepCopy();
        anotherExecution.getAsJsonObject("transitionDiscovery").addProperty(
                "seedExecutionId", "EXEC.99");
        RegionPathWorklist.Result replanned = RegionPathWorklist.plan(
                Collections.singletonList(anotherExecution),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(task.get("queryKey").getAsString(), replanned.tasks
                .get(0).get("queryKey").getAsString());
    }

    @Test
    public void stablePathIdentityAlphaNormalizesOnlyExecutionLocals() {
        JsonObject first = summary("ACT.ALPHA.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.ALPHA.2",
                RegionCaptureGoal.outputClosure());
        replaceConditionSymbol(first, "M_I_1");
        replaceConditionSymbol(second, "M_I_97");
        first.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", localSymbol("M_I_1"));
        second.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", localSymbol("M_I_97"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentAlias = second.deepCopy();
        differentAlias.getAsJsonArray("pathCondition").get(1)
                .getAsJsonObject().getAsJsonObject("_left")
                .addProperty("_exp", "M_I_98");
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentAlias));
    }

    @Test
    public void stablePathIdentityPreservesCanonicalActivationPorts() {
        JsonObject first = summary("ACT.PORT.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.PORT.2",
                RegionCaptureGoal.outputClosure());
        first.add("symbolicInputs", strings("REGION.3.in.0"));
        second.add("symbolicInputs", strings("REGION.3.in.1"));
        replaceConditionSymbol(first,
                "M_I_field_REGION.3.in.0_java/lang/Integer");
        replaceConditionSymbol(second,
                "M_I_field_REGION.3.in.1_java/lang/Integer");

        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));
    }

    @Test
    public void dynamicSelectorIsStableAcrossObjectTokensButKeepsOccurrence()
            throws Exception {
        JsonObject first = summary("ACT.DYNAMIC.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.DYNAMIC.2",
                RegionCaptureGoal.outputClosure());
        first.add("dynamicFieldBindings", dynamicBindings("OBJECT.1", 2,
                "key-two"));
        second.add("dynamicFieldBindings", dynamicBindings("OBJECT.99", 2,
                "key-two"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentOccurrence = second.deepCopy();
        differentOccurrence.getAsJsonArray("dynamicFieldBindings").get(0)
                .getAsJsonObject().addProperty("materializationOccurrence",
                1);
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentOccurrence));

        RegionPathWorklist.Result planned = RegionPathWorklist.plan(
                Collections.singletonList(first),
                Collections.singletonList(activation("ACT.DYNAMIC.1",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, planned.tasks.get(0).getAsJsonArray(
                "dynamicFieldBindings").get(0).getAsJsonObject().get(
                "materializationOccurrence").getAsInt());
    }

    @Test
    public void mapProjectionStableKeyErasesTokensButKeepsIndexAndOperation() {
        JsonObject first = summary("ACT.MAP.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.MAP.2",
                RegionCaptureGoal.outputClosure());
        first.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.1", 10L, 20L, 30L, 0,
                "MAP_VALUES_VIEW"));
        second.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.2", 100L, 200L, 300L, 0,
                "MAP_VALUES_VIEW"));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentIndex = second.deepCopy();
        differentIndex.add("dynamicFieldBindings", mapProjectionBindings(
                "ACT.MAP.2", 100L, 200L, 300L, 1,
                "MAP_VALUES_VIEW"));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentIndex));

        JsonObject differentOperation = second.deepCopy();
        differentOperation.add("dynamicFieldBindings",
                mapProjectionBindings("ACT.MAP.2", 100L, 200L, 300L, 0,
                        "MAP_KEY_SET_VIEW"));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentOperation));
    }

    @Test
    public void engineArrayBridgeAlphaNormalizesIdsButPreservesPortJoin() {
        JsonObject first = summary("ACT.ARRAY.1",
                RegionCaptureGoal.outputClosure());
        JsonObject second = summary("ACT.ARRAY.2",
                RegionCaptureGoal.outputClosure());
        first.getAsJsonArray("pathCondition").set(0,
                arrayLoad("VM_ARRAY_1"));
        second.getAsJsonArray("pathCondition").set(0,
                arrayLoad("VM_ARRAY_99"));
        first.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.0", "VM_ARRAY_1", 7));
        second.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.0", "VM_ARRAY_99", 700));

        assertEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(second));

        JsonObject differentPort = second.deepCopy();
        differentPort.add("engineArrayInputBindings", engineArrayBindings(
                "REGION.3.in.1", "VM_ARRAY_99", 700));
        assertNotEquals(RegionPathWorklist.stablePathKey(first),
                RegionPathWorklist.stablePathKey(differentPort));
    }

    @Test
    public void pathFlipTaskCarriesExactEngineArrayBridgeCatalog() {
        JsonObject summary = summary("ACT.ARRAY.TASK",
                RegionCaptureGoal.outputClosure());
        JsonArray bindings = engineArrayBindings("REGION.3.in.0",
                "VM_ARRAY_TASK", 17);
        summary.add("engineArrayInputBindings", bindings);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation("ACT.ARRAY.TASK",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertFalse(result.tasks.isEmpty());
        assertEquals(bindings, result.tasks.get(0).getAsJsonArray(
                "engineArrayInputBindings"));
    }

    private static void replaceConditionSymbol(JsonObject summary,
                                               String symbol) {
        for (com.google.gson.JsonElement element : summary.getAsJsonArray(
                "pathCondition")) {
            element.getAsJsonObject().getAsJsonObject("_left")
                    .addProperty("_exp", symbol);
        }
    }

    private static JsonObject localSymbol(String raw) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", raw);
        return symbol;
    }

    private static JsonArray strings(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray dynamicBindings(String objectToken,
                                             int occurrence, String key) {
        JsonArray result = new JsonArray();
        JsonObject binding = new JsonObject();
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("baseInputSymbol", "REGION.3.in.0");
        binding.addProperty("dynamicFieldSymbol",
                "REGION.3.in.0.field.stable.occ." + occurrence);
        binding.addProperty("materializationSiteId", "SITE.FIELD");
        binding.addProperty("materializationOccurrence", occurrence);
        binding.addProperty("leafOwnerObjectToken", objectToken);
        JsonObject selector = new JsonObject();
        selector.addProperty("_type", "ConstExpr");
        selector.addProperty("_exp", key);
        binding.add("keyExpression", selector);
        binding.addProperty("keyExpressionAuthority", "RUNTIME_KEY");
        binding.addProperty("complete", true);
        result.add(binding);
        return result;
    }

    private static JsonArray mapProjectionBindings(
            String scope, long mapToken, long elementToken,
            long outputToken, int index, String operation) {
        JsonObject binding = new JsonObject();
        binding.addProperty("kind",
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
        binding.addProperty("baseInputSymbol", "REGION.3.in.0");
        binding.addProperty("dynamicFieldSymbol",
                "REGION.3.in.0.field.mapstable.occ." + (index + 1));
        binding.addProperty("materializationSiteId", "SITE.MAP");
        binding.addProperty("materializationOccurrence", index + 1);
        binding.addProperty("fieldSignature", "<example.Value: long expiry>");
        binding.add("fieldPath", strings("expiry"));
        binding.addProperty("leafOwnerObjectToken", elementToken);
        binding.addProperty("objectTokenScope", scope);
        binding.addProperty("entrySnapshotElementCount", 2);
        binding.addProperty("outputElementCount", 2);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.MAP");
        selector.addProperty("mapInputPort", "REGION.3.in.0");
        selector.addProperty("mapInputCell", "<Producer: Map values>");
        selector.addProperty("outputPort", "REGION.3.out.1");
        selector.addProperty("outputCell", "<Payload: Value[] values>");
        selector.addProperty("mapProjectionOperation", operation);
        selector.addProperty("outputIndex", index);
        selector.addProperty("elementOccurrence", index + 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Value");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                "<example.Value: long expiry>");
        selector.addProperty("mapObjectToken", mapToken);
        selector.addProperty("elementObjectToken", elementToken);
        selector.addProperty("outputArrayObjectToken", outputToken);
        selector.addProperty("objectTokenScope", scope);
        selector.addProperty("complete", true);
        binding.add("mapProjectionSelector", selector);
        binding.addProperty("complete", true);
        JsonArray result = new JsonArray();
        result.add(binding);
        return result;
    }

    private static JsonObject arrayLoad(String arrayId) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "_array_expr");
        result.addProperty("_is_load", true);
        result.addProperty("_arr_str", arrayId);
        result.add("_index_exp", localSymbol("M_I_INDEX"));
        result.add("_value_exp", localSymbol("M_I_VALUE"));
        return result;
    }

    private static JsonArray engineArrayBindings(String port, String id,
                                                 long token) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        binding.addProperty("inputPort", port);
        binding.addProperty("inputCell",
                "<example.Handler: void run(java.lang.Object[])>"
                        + ".param0:java.lang.Object[]");
        binding.addProperty("inputJavaType", "java.lang.Object[]");
        binding.addProperty("inputJavaTypeDescriptor",
                "[Ljava/lang/Object;");
        binding.addProperty("symbolizationPrefix", port);
        binding.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        binding.addProperty("engineArrayId", id);
        binding.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        binding.addProperty("arrayObjectToken", token);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        binding.addProperty("sameArrayObjectTokenVerified", true);
        binding.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        binding.addProperty("complete", true);
        JsonArray result = new JsonArray();
        result.add(binding);
        return result;
    }

    private static JsonObject activation(String id, RegionCaptureGoal goal) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", id);
        activation.addProperty("regionId", "REGION.3");
        activation.add("captureGoal", goal.toJson());
        return activation;
    }

    private static JsonObject summary(String activationId,
                                      RegionCaptureGoal goal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + activationId);
        summary.addProperty("activationId", activationId);
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", goal.toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.3.out.0");
        summary.add("requestedOutput", output);

        JsonArray conditions = new JsonArray();
        conditions.add(binary(">", 0));
        conditions.add(binary("<", 5));
        summary.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("SITE.0", 0));
        mappings.add(mapping("SITE.1", 1));
        summary.add("branchMappings", mappings);
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapEffects", new JsonArray());
        return summary;
    }

    private static JsonObject mapping(String site, int condition) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("conditionIndex", condition);
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("outcome", true);
        return mapping;
    }

    private static JsonObject binary(String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp",
                "M_I_field_REGION.3.in.0_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }
}
