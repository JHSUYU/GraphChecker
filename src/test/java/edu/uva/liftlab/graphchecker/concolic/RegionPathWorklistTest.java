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
        BranchReplayContract replay = replayContract(latest);
        assertEquals("SITE.1", replay.source().siteId());
        assertEquals(1, replay.orderedPrefix().size());
        assertEquals(2, replay.requiredPathPredicates().size());
        assertEquals(">=", replay.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
        assertEquals(BranchReplayContract.DROP_SOURCE_SUFFIX,
                latest.getAsJsonObject("replayContract")
                        .get("suffixPolicy").getAsString());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void completeEmptyOutputSliceDoesNotBecomeWildcard() {
        JsonObject summary = summary("ACT.EMPTY.SLICE",
                RegionCaptureGoal.outputClosure());
        JsonObject slice = new JsonObject();
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        summary.add("requestedOutputSlice", slice);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation(
                        "ACT.EMPTY.SLICE",
                        RegionCaptureGoal.outputClosure())),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void explicitClosureScopesBranchTasksAndManifest() {
        JsonObject summary = summary("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(activation, closure);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject task = result.tasks.get(0);
        assertEquals("SITE.1", sourceSite(task));
        assertTrue(task.has("outputClosure"));
        assertFalse(task.has("requestedOutput"));
        assertEquals("REGION.3@test#call7",
                task.get("regionInstanceId").getAsString());
        assertEquals(7, task.get("rootCallId").getAsLong());
        assertEquals(task.get("outputDemandKey"),
                result.manifest.get("outputDemandKey"));
        assertEquals(task.get("outputClosureFingerprint"),
                result.manifest.get("outputClosureFingerprint"));

        JsonObject legacySummary = summary("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        boolean rejected = false;
        try {
            RegionPathWorklist.plan(
                    Collections.singletonList(legacySummary),
                    Collections.singletonList(activation),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults());
        } catch (IllegalArgumentException expected) {
            rejected = expected.getMessage().contains(
                    "canonical outputClosure summary");
        }
        assertTrue("legacy summary must not inherit joint activation scope",
                rejected);
    }

    @Test
    public void closureDemandAndProofCannotReuseTerminalFlipRecord() {
        JsonObject firstSummary = summary("ACT.CLOSURE.A",
                RegionCaptureGoal.outputClosure());
        JsonObject firstActivation = activation("ACT.CLOSURE.A",
                RegionCaptureGoal.outputClosure());
        JsonObject firstClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(firstSummary, firstClosure);
        attachClosure(firstActivation, firstClosure);
        RegionPathWorklist.Result first = RegionPathWorklist.plan(
                Collections.singletonList(firstSummary),
                Collections.singletonList(firstActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        JsonObject secondSummary = summary("ACT.CLOSURE.B",
                RegionCaptureGoal.outputClosure());
        JsonObject secondActivation = activation("ACT.CLOSURE.B",
                RegionCaptureGoal.outputClosure());
        JsonObject secondClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.B", "SITE.1");
        attachClosure(secondSummary, secondClosure);
        attachClosure(secondActivation, secondClosure);
        RegionPathWorklist.Result second = RegionPathWorklist.plan(
                Collections.singletonList(secondSummary),
                Collections.singletonList(secondActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(first.tasks.get(0).get("outputDemandKey"),
                second.tasks.get(0).get("outputDemandKey"));
        assertNotEquals(first.tasks.get(0).get("queryKey"),
                second.tasks.get(0).get("queryKey"));
        JsonObject record = new JsonObject();
        record.addProperty("queryKey", first.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status", "UNSAT");
        RegionPathWorklist.Result replay = RegionPathWorklist.plan(
                Collections.singletonList(secondSummary),
                Collections.singletonList(secondActivation),
                Collections.singletonList(record),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(1, replay.tasks.size());

        JsonObject otherDemandSummary = summary("ACT.CLOSURE.C",
                RegionCaptureGoal.outputClosure());
        JsonObject otherDemandActivation = activation("ACT.CLOSURE.C",
                RegionCaptureGoal.outputClosure());
        JsonObject otherDemand = outputClosure("REGION.3.out.1",
                "<P: int y>", "PROOF.A", "SITE.1");
        attachClosure(otherDemandSummary, otherDemand);
        attachClosure(otherDemandActivation, otherDemand);
        RegionPathWorklist.Result third = RegionPathWorklist.plan(
                Collections.singletonList(otherDemandSummary),
                Collections.singletonList(otherDemandActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertNotEquals(first.tasks.get(0).get("outputDemandKey"),
                third.tasks.get(0).get("outputDemandKey"));
        assertNotEquals(first.tasks.get(0).get("queryKey"),
                third.tasks.get(0).get("queryKey"));
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
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                replanned.manifest.get("state").getAsString());
        assertEquals(0, replanned.manifest.get(
                "pendingTaskCount").getAsInt());
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("EXPLORATION_GAP"));
        assertTrue(replanned.manifest.getAsJsonArray("gaps").toString()
                .contains("OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT"));
    }

    private static JsonObject exactBranchTemplateSummary(
            String activationId, boolean concreteUpperGuard) {
        JsonObject result = summary(activationId,
                RegionCaptureGoal.outputClosure());
        result.add("symbolicInputs", strings("REGION.3.in.0"));
        JsonArray conditions = new JsonArray();
        conditions.add(binary("<", 0));
        if (!concreteUpperGuard) conditions.add(binary("<=", 4));
        result.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        JsonObject lower = mapping("SITE.CLAMP.LOWER", 0);
        lower.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(lower);
        JsonObject upper = exactVmIfMapping("SITE.CLAMP.UPPER",
                concreteUpperGuard ? -1 : 1, true,
                concreteUpperGuard ? 0 : 1);
        upper.addProperty("policy", concreteUpperGuard
                ? "EXPLORE" : "PATH_ASSUMPTION");
        upper.addProperty("pathConditionBaseline", 1);
        if (!concreteUpperGuard) {
            upper.add("condition", conditions.get(1).deepCopy());
        }
        mappings.add(upper);
        result.add("branchMappings", mappings);
        authorizeVmPcMappings(result);
        return result;
    }

    private static JsonObject exactVmIfMapping(String site,
                                               int conditionIndex,
                                               boolean outcome,
                                               int conditionCount) {
        JsonObject mapping = mapping(site, conditionIndex);
        mapping.addProperty("branchKind", "IF");
        mapping.addProperty("method", "<example.Producer: int compute(int)>");
        mapping.addProperty("unitIndex", 6);
        mapping.addProperty("expression", "i3 <= 4");
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("observedOutcome", outcome);
        mapping.addProperty("mappingPolicy",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_ID_AND_PC_INDEX");
        mapping.addProperty("vmBranchEventExpected", true);
        mapping.addProperty("vmBranchEventId", 17);
        mapping.addProperty("vmOccurrence", 1);
        mapping.addProperty("vmBranchEventValidated", true);
        mapping.addProperty("vmBranchEventAuthority",
                "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
        mapping.addProperty("vmThreadContextId", 7L);
        mapping.addProperty("vmOwnerJavaThreadId", 11L);
        mapping.addProperty("vmOwnerOsThreadId", 13L);
        JsonArray indices = new JsonArray();
        if (conditionCount == 1) indices.add(1);
        mapping.add("vmConditionIndices", indices);
        mapping.addProperty("conditionAuthority", conditionCount == 0
                ? "VM_THREAD_CONTEXT_EXACT_CONCRETE_BRANCH_EVENT"
                : "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_PC_INDEX");
        return mapping;
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

    private static JsonObject outputClosure(
            String port, String cell, String proofTag, String... sites) {
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", "REGION.3");
        producer.addProperty("regionInstanceId",
                "REGION.3@test#call7");
        producer.addProperty("rootCallId", 7);

        JsonObject output = new JsonObject();
        output.addProperty("portId", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("javaTypeDescriptor", "I");
        output.addProperty("selectionAuthority", "TEST_EXACT_DEMAND");

        JsonArray siteArray = new JsonArray();
        for (String site : sites) siteArray.add(site);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", siteArray.deepCopy());
        slice.add("staticSites", siteArray.deepCopy());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.addProperty("captureBindingsRequired", false);
        slice.addProperty("captureBindingsComplete", true);
        slice.addProperty("proofTag", proofTag);

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 1);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static void attachClosure(JsonObject artifact,
                                      JsonObject closure) {
        artifact.remove("requestedOutput");
        artifact.addProperty("regionInstanceId",
                "REGION.3@test#call7");
        artifact.addProperty("rootCallId", 7);
        artifact.add("outputClosure", closure.deepCopy());
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
        authorizeVmPcMappings(summary);
        return summary;
    }

    private static JsonObject oneBranchSummary(String activationId,
                                               String operator,
                                               boolean outcome,
                                               int outputValue) {
        JsonObject result = summary(activationId,
                RegionCaptureGoal.outputClosure());
        JsonArray conditions = new JsonArray();
        conditions.add(binary(operator, 0));
        result.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        JsonObject mapping = mapping("SITE.0", 0);
        mapping.addProperty("outcome", outcome);
        mappings.add(mapping);
        result.add("branchMappings", mappings);
        authorizeVmPcMappings(result);
        JsonObject outputs = new JsonObject();
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", "Y_I_" + outputValue);
        outputs.add("REGION.3.out.0", value);
        result.add("outputExpressions", outputs);
        return result;
    }

    private static void authorizeVmPcMappings(JsonObject summary) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        JsonArray canonical = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            JsonObject mapping = element.getAsJsonObject();
            int conditionIndex = mapping.get("conditionIndex").getAsInt();
            SummaryBranchMapping.Policy policy =
                    SummaryBranchMapping.Policy.fromWire(
                            mapping.has("policy")
                                    ? mapping.get("policy").getAsString()
                                    : "EXPLORE");
            if (conditionIndex < 0 || conditionIndex >= conditions.size()) {
                canonical.add(SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                mapping.get("siteId").getAsString(),
                                "<test.Region: void run()>", 0,
                                mapping.get("occurrence").getAsInt(),
                                mapping.get("outcome").getAsBoolean()),
                        policy).toJson());
                continue;
            }
            JsonObject event = new JsonObject();
            event.addProperty("eventId", conditionIndex + 1L);
            event.addProperty("contextId", 7L);
            event.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPc(
                    mapping.get("siteId").getAsString(),
                    "<test.Region: void run()>", conditionIndex,
                    mapping.get("occurrence").getAsInt(),
                    mapping.get("outcome").getAsBoolean(),
                    conditions.get(conditionIndex), conditionIndex, event);
            canonical.add(SummaryBranchMapping.witnessed(witness,
                    conditionIndex, policy).toJson());
        }
        summary.add("branchMappings", canonical);
    }

    private static void replaceWitnessOutcomes(
            JsonObject summary, boolean outcome) {
        JsonArray replacements = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            SummaryBranchMapping mapping = SummaryBranchMapping.fromJson(
                    element.getAsJsonObject());
            BranchWitness source = mapping.witness();
            JsonObject metadata = new JsonObject();
            metadata.addProperty("predicateNormalization",
                    source.predicateNormalization());
            BranchWitness replacement = BranchWitness.vmPc(
                    source.siteId(), source.method(), source.unitIndex(),
                    source.occurrence(), outcome,
                    summary.getAsJsonArray("pathCondition")
                            .get(mapping.summaryPcIndex()),
                    source.vmPcIndex(), metadata);
            replacements.add(SummaryBranchMapping.witnessed(replacement,
                    mapping.summaryPcIndex(), mapping.policy()).toJson());
        }
        summary.add("branchMappings", replacements);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
    }

    private static String sourceSite(JsonObject task) {
        return replayContract(task).source().siteId();
    }

    private static JsonObject mapping(String site, int condition) {
        return mapping(site, condition, 1);
    }

    private static JsonObject mapping(String site, int condition,
                                      int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("conditionIndex", condition);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        return mapping;
    }

    private static JsonObject typedBinary(String operator, String javaType,
                                          int constant) {
        JsonObject expression = binary(operator, constant);
        expression.getAsJsonObject("_left").addProperty("_java_type",
                javaType);
        expression.getAsJsonObject("_left").addProperty("_exp",
                "M_" + javaType + "_field_REGION.3.in.0");
        expression.getAsJsonObject("_right").addProperty("_java_type",
                javaType);
        expression.getAsJsonObject("_right").addProperty("_exp",
                "Y_" + javaType + "_" + constant);
        return expression;
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
