package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicReplayValidatorTest {
    @Test
    public void admitsNormalExactOutputClosureReplay() {
        JsonObject task = outputTask();
        JsonObject raw = result(true);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                outputSummary(task));

        assertTrue(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertTrue(validation.get("normalExitValidated").getAsBoolean());
        assertTrue(validation.get("requestedOutputExpressionValidated")
                .getAsBoolean());
        assertFalse(validation.get("outputClosureAdmissionGap")
                .getAsBoolean());
    }

    @Test
    public void jointOutputClosureRequiresEveryDeclaredExpression() {
        JsonObject task = jointOutputTask();
        JsonObject raw = result(true);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");

        JsonObject complete = ConcolicReplayValidator.validate(task, raw,
                outputSummary(task));
        assertTrue(complete.toString(), complete.get("valid").getAsBoolean());

        JsonObject missingSummary = outputSummary(task);
        missingSummary.getAsJsonObject("outputExpressions")
                .remove("REGION.3.out.1");
        JsonObject missing = ConcolicReplayValidator.validate(task, raw,
                missingSummary);
        assertFalse(missing.toString(), missing.get("valid").getAsBoolean());
        assertTrue(missing.get("requestedOutputIdentityValidated")
                .getAsBoolean());
        assertFalse(missing.get("requestedOutputExpressionValidated")
                .getAsBoolean());
        assertTrue(missing.getAsJsonArray("failures").toString().contains(
                "REQUESTED_OUTPUT_EXPRESSION_MISSING"));

        JsonObject stale = outputSummary(task);
        stale.addProperty("activationId", "ACT.OLDER.PATH");
        JsonObject staleValidation = ConcolicReplayValidator.validate(
                task, raw, stale);
        assertFalse(staleValidation.toString(),
                staleValidation.get("valid").getAsBoolean());
        assertTrue(staleValidation.getAsJsonArray("failures").toString()
                .contains(
                "IMPORTED_OUTPUT_SUMMARY_ACTIVATION_ID_MISMATCH"));
    }

    @Test
    public void rejectsSamePortsWhenImportedClosureProofDiffers() {
        JsonObject task = jointOutputTask();
        JsonObject raw = result(true);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        JsonObject summary = outputSummary(task);
        summary.getAsJsonObject(OutputClosureContract.FIELD)
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonArray("causalEdgeIds").set(0,
                        new com.google.gson.JsonPrimitive("DF.changed"));

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                summary);

        assertFalse(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertFalse(validation.get("requestedOutputIdentityValidated")
                .getAsBoolean());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("REQUESTED_OUTPUT_MISMATCH"));
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("queryKey", "Q");
        task.addProperty("regionId", "REGION.3");
        task.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        BranchWitness prefix = branchWitness("SITE.0", true,
                branchPredicate("REGION.3.in.0", ">"), 0);
        BranchWitness source = branchWitness("SITE.1", true,
                branchPredicate("REGION.3.in.1", ">"), 1);
        task.add("replayContract", BranchReplayContract.flip(
                java.util.Collections.singletonList(prefix), source)
                .toJson());
        return task;
    }

    private static JsonObject outputTask() {
        JsonObject task = legacyOutputTask();
        OutputClosureContract closure = OutputClosureCodec.decode(task);
        OutputClosureCodec.writeTo(task, closure);
        return task;
    }

    private static JsonObject jointOutputTask() {
        JsonObject first = legacyOutputTask(
                "REGION.3.out.0", "<example.Region: int x>", 2);
        JsonObject second = legacyOutputTask(
                "REGION.3.out.1", "<example.Region: int y>", 3);
        OutputClosureContract closure = OutputClosureCodec.merge(
                Arrays.asList(OutputClosureCodec.decode(first),
                        OutputClosureCodec.decode(second)));
        OutputClosureCodec.writeTo(first, closure);
        return first;
    }

    private static JsonObject legacyOutputTask() {
        return legacyOutputTask("REGION.3.out.0",
                "<example.Region: java.util.Map out>", 2);
    }

    private static JsonObject legacyOutputTask(
            String port, String cell, int unitIndex) {
        JsonObject task = task();
        task.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        task.addProperty("regionInstanceId", "REGION.3@test#call7");
        task.addProperty("rootCallId", 7);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", port);
        requested.addProperty("cell", cell);
        requested.addProperty("kind", "HEAP_STATE");
        requested.addProperty("selectionAuthority",
                "CONFIRMED_READ_FROM_EDGE");
        task.add("requestedOutput", requested);

        JsonObject output = new JsonObject();
        output.addProperty("symbol", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("location", "RETURN_OR_HEAP_EFFECT");
        JsonArray outputs = new JsonArray();
        outputs.add(output);
        task.add("outputs", outputs);

        String method = "<example.Region: void run()>";
        String site = method + "#u" + unitIndex;
        JsonObject capture = new JsonObject();
        capture.addProperty("captureKind", "FIELD_ASSIGNMENT_RHS");
        capture.addProperty("captureBindingId", port + ".capture.0");
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("method", method);
        capture.addProperty("siteId", site);
        capture.addProperty("unitIndex", unitIndex);
        capture.addProperty("fieldSignature", cell);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        task.add("requestedOutputCapture", captures);
        task.addProperty("requestedOutputCaptureRequired", true);
        task.addProperty("requestedOutputCaptureComplete", true);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings("REGION.3.in.0"));
        slice.add("sites", strings(site));
        slice.add("staticSites", strings(site));
        slice.add("methods", strings(method));
        slice.add("causalEdgeIds", strings("DF." + unitIndex));
        slice.add("captureBindings", captures.deepCopy());
        slice.addProperty("captureBindingsRequired", true);
        slice.addProperty("captureBindingsComplete", true);
        task.add("requestedOutputSlice", slice);
        task.add("requestedOutputMethods", strings(method));
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                "REGION.3", "REGION.3@test#call7", 7,
                port, cell, "HEAP_STATE", "CONFIRMED_READ_FROM_EDGE",
                slice));
        return task;
    }

    private static JsonObject outputSummary(JsonObject task) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.REPLAY");
        summary.addProperty("activationId", "ACT.REPLAY");
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("regionInstanceId",
                task.get("regionInstanceId").getAsString());
        summary.addProperty("rootCallId",
                task.get("rootCallId").getAsLong());
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("normalExit", true);
        summary.addProperty("exceptionType", "");
        summary.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        if (task.has(OutputClosureContract.FIELD)) {
            summary.add(OutputClosureContract.FIELD,
                    task.getAsJsonObject(
                            OutputClosureContract.FIELD).deepCopy());
        } else {
            for (String field : new String[]{"requestedOutput",
                    "requestedOutputSlice", "requestedOutputCapture",
                    "requestedOutputCaptureRequired",
                    "requestedOutputCaptureComplete",
                    "requestedOutputMethods", "outputs"}) {
                if (task.has(field)) {
                    summary.add(field, task.get(field).deepCopy());
                }
            }
        }
        JsonObject outputs = new JsonObject();
        for (String port : OutputClosureCodec.decode(task).outputPorts()) {
            outputs.add(port, outputExpression());
        }
        summary.add("outputExpressions", outputs);
        return summary;
    }

    private static JsonObject outputExpression() {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "REGION.3.in.0");
        return expression;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static JsonObject result(boolean flippedOutcome) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("regionId", "REGION.3");
        raw.addProperty("activationId", "ACT.REPLAY");
        raw.addProperty("allModelAssignmentsApplied", true);
        raw.addProperty("modelAssignmentAppliedCount", 0);
        raw.add("modelAssignmentsApplied", new JsonArray());
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(branchWitness("SITE.0", true,
                branchPredicate("REGION.3.in.0", ">"), 0)));
        boolean targetOutcome = flippedOutcome ? false : true;
        mappings.add(mapping(branchWitness("SITE.1", targetOutcome,
                branchPredicate("REGION.3.in.1",
                        targetOutcome ? ">" : "<="), 1)));
        raw.add("branchMappings", mappings);
        return raw;
    }

    private static JsonObject mapping(BranchWitness witness) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", witness.siteId());
        mapping.addProperty("occurrence", witness.occurrence());
        mapping.addProperty("observedOutcome",
                witness.sourceTakenOutcome());
        mapping.add("witness", witness.toJson());
        return mapping;
    }

    private static BranchWitness branchWitness(String site, boolean outcome,
                                               JsonObject predicate,
                                               int pcIndex) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", pcIndex + 1L);
        event.addProperty("contextId", 1L);
        return BranchWitness.vmPc(site, "<test.Replay: void run()>",
                pcIndex, 1, outcome, predicate, pcIndex, event);
    }

    private static JsonObject branchPredicate(String input,
                                              String operator) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", input);
        JsonObject zero = new JsonObject();
        zero.addProperty("_type", "ConstExpr");
        zero.addProperty("_java_type", "I");
        zero.addProperty("_exp", "Y_I_0");
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", zero);
        return expression;
    }

    private static JsonArray dynamicAssignments() {
        JsonArray result = new JsonArray();
        result.add(dynamicAssignment(
                "REGION.3.in.0.field.first.occ.1", 1, "key-one"));
        result.add(dynamicAssignment(
                "REGION.3.in.0.field.second.occ.2", 2, "key-two"));
        return result;
    }

    private static JsonObject freshRebindingPlan() {
        String dynamic = "REGION.3.in.0.field.fresh.occ.1";
        JsonObject assignment = dynamicAssignment(dynamic, 1, "seed-key");
        assignment.remove("expectedEntryKey");
        assignment.remove("expectedEntryKeyAuthority");
        assignment.addProperty("dynamicReplayRebindingAuthority",
                "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                        + "FRESH_ENTRY_REBIND_V1");
        assignment.addProperty("sourceEntrySelectorRetained", false);
        JsonArray path = new JsonArray();
        path.add("expiry");
        assignment.add("materializationPath", path);
        return assignment;
    }

    private static JsonObject freshRebindingApplied(JsonObject planned,
                                                    int freshKey) {
        JsonObject applied = planned.deepCopy();
        applied.remove("solverSymbol");
        applied.addProperty("entryReadObservationId",
                "MAP_ENTRY_READ:SITE.NEXT#1");
        applied.add("keyExpression", integerKey(freshKey));
        applied.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        applied.addProperty("freshEntrySelectorCaptured", true);
        applied.addProperty("sameSeedEntryClaimed", false);
        return applied;
    }

    private static JsonObject freshRawBinding(JsonObject applied) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        for (String member : new String[]{"baseInputSymbol",
                "dynamicBindingId", "dynamicFieldSymbol",
                "materializationSiteId", "materializationOccurrence",
                "entryReadObservationId", "keyExpression",
                "keyExpressionAuthority"}) {
            if (applied.has(member)) {
                binding.add(member, applied.get(member).deepCopy());
            }
        }
        binding.add("fieldPath", applied.getAsJsonArray(
                "materializationPath").deepCopy());
        binding.addProperty("complete", true);
        return binding;
    }

    private static void addImportedFreshBindings(
            JsonObject summary, JsonArray bindings, String observationId) {
        JsonObject observation = new JsonObject();
        observation.addProperty("kind", "MAP_ENTRY_READ");
        observation.addProperty("observationId", observationId);
        observation.addProperty("complete", true);
        observation.add("entryFieldBindings", bindings);
        JsonArray observations = new JsonArray();
        observations.add(observation);
        summary.add("heapObservations", observations);
    }

    private static JsonObject integerKey(int value) {
        JsonObject key = new JsonObject();
        key.addProperty("_type", "ConstExpr");
        key.addProperty("_java_type", "java/lang/Integer");
        key.addProperty("_exp", "Y_I_" + value);
        return key;
    }

    private static JsonObject dynamicAssignment(String dynamic,
                                                int occurrence,
                                                String key) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("baseInputSymbol", "REGION.3.in.0");
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("solverSymbol", "solver_" + occurrence);
        assignment.addProperty("inputSymbol", "REGION.3.in.0");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", String.valueOf(40 + occurrence));
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.addProperty("materializationSiteId", "SITE.FIELD");
        assignment.addProperty("materializationOccurrence", occurrence);
        JsonObject expectedKey = new JsonObject();
        expectedKey.addProperty("_type", "ConstExpr");
        expectedKey.addProperty("_java_type", "Ljava/lang/String;");
        expectedKey.addProperty("_exp", key);
        assignment.add("expectedEntryKey", expectedKey);
        assignment.addProperty("expectedEntryKeyAuthority",
                "RUNTIME_MAP_ENTRY_READ_KEY_EXPRESSION");
        return assignment;
    }

    private static JsonObject containerAssignment(int index,
                                                  int occurrence) {
        String dynamic = "REGION.3.in.0.field.array.occ." + occurrence;
        JsonObject assignment = new JsonObject();
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("baseInputSymbol", "REGION.3.in.0");
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("solverSymbol", "solver_array_" + occurrence);
        assignment.addProperty("inputSymbol", "REGION.3.in.0");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", String.valueOf(100 + occurrence));
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.addProperty("materializationSiteId", "SITE.FIELD");
        assignment.addProperty("materializationOccurrence", occurrence);
        assignment.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        JsonArray materializationPath = new JsonArray();
        materializationPath.add("id");
        assignment.add("materializationPath", materializationPath);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.3");
        selector.addProperty("containerInputPort", "REGION.3.in.array");
        selector.addProperty("containerInputCell",
                "<example.Keys: example.Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", index);
        selector.addProperty("elementOccurrence", occurrence);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        assignment.add("containerSelector", selector);
        assignment.addProperty("containerReplayRebindingAuthority",
                "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                        + "IDENTITY_REBIND_V1");
        assignment.addProperty("sourceContainerObjectTokensRetained",
                false);
        return assignment;
    }

    private static JsonObject appliedContainerAssignment(JsonObject planned,
                                                         String activation) {
        JsonObject applied = planned.deepCopy();
        applied.remove("solverSymbol");
        JsonObject selector = applied.getAsJsonObject("containerSelector");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", activation);
        selector.addProperty("containerObservationLocation",
                "EXACT_CONSUMED_LEAF_OBSERVATION");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        applied.addProperty("sameSourceContainerIdentityClaimed", false);
        applied.addProperty("currentContainerSelectorCaptured", true);
        return applied;
    }

    private static JsonObject rawContainerBinding(JsonObject applied) {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 2);
        binding.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        binding.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        for (String member : new String[]{"baseInputSymbol",
                "dynamicBindingId", "dynamicFieldSymbol",
                "materializationSiteId", "materializationOccurrence"}) {
            binding.add(member, applied.get(member).deepCopy());
        }
        binding.add("fieldPath", applied.getAsJsonArray(
                "materializationPath").deepCopy());
        JsonObject selector = applied.getAsJsonObject(
                "containerSelector").deepCopy();
        binding.add("containerSelector", selector);
        binding.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        binding.addProperty("objectTokenScope",
                selector.get("objectTokenScope").getAsString());
        binding.addProperty("materializationSiteBridgeAuthority",
                "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_"
                        + "ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1");
        binding.addProperty("materializationSiteBridgeBindingId",
                selector.get("bindingId").getAsString());
        binding.addProperty("materializationSiteBridgeElementObjectToken",
                selector.get("elementObjectToken").getAsLong());
        binding.addProperty("materializationSiteBridgeObjectTokenScope",
                selector.get("objectTokenScope").getAsString());
        binding.addProperty("complete", true);
        return binding;
    }

    private static JsonObject mapProjectionAssignment() {
        String dynamic = "REGION.3.in.0.field.map.occ.1";
        JsonObject assignment = new JsonObject();
        assignment.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamic);
        assignment.addProperty("baseInputSymbol", "REGION.3.in.0");
        assignment.addProperty("dynamicFieldSymbol", dynamic);
        assignment.addProperty("engineSymbol", dynamic);
        assignment.addProperty("solverSymbol", "solver_map_1");
        assignment.addProperty("inputSymbol", "REGION.3.in.0");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "1234");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.addProperty("materializationSiteId", "SITE.MAP");
        assignment.addProperty("materializationOccurrence", 1);
        assignment.addProperty("dynamicFieldBindingKind",
                "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.MAP.EXPIRY");
        selector.addProperty("mapInputPort", "REGION.3.in.0");
        selector.addProperty("mapInputCell", "<Manager: Map allKeys>");
        selector.addProperty("outputPort", "REGION.3.out.0");
        selector.addProperty("outputCell", "<Payload: Key[] keys>");
        selector.addProperty("mapProjectionOperation", "MAP_VALUES_VIEW");
        selector.addProperty("outputIndex", 0);
        selector.addProperty("elementOccurrence", 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "long");
        selector.addProperty("declaredFieldSignature",
                "<example.Key: long expiry>");
        selector.addProperty("mapObjectToken", 501L);
        selector.addProperty("elementObjectToken", 601L);
        selector.addProperty("outputArrayObjectToken", 701L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.REPLAY");
        selector.addProperty("sourceObjectTokenScope", "ACT.SOURCE");
        selector.addProperty("replayScopeRebindingAuthority",
                "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_ACTIVATION_"
                        + "SCOPE_REBOUND_TOKENS_NOT_COMPARED_ACROSS_"
                        + "EXECUTIONS");
        selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
        JsonObject key = new JsonObject();
        key.addProperty("_type", "ConstExpr");
        key.addProperty("_java_type", "java/lang/Integer");
        key.addProperty("_exp", "Y_I_11");
        selector.add("expectedMapKey", key);
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
        selector.addProperty("outputIdentityVerified", true);
        selector.addProperty("outputVerificationAuthority",
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
        selector.addProperty("complete", true);
        assignment.add("mapProjectionSelector", selector);
        return assignment;
    }

    private static JsonObject directAssignment(String input, String value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", input);
        assignment.addProperty("solverSymbol", "solver_"
                + input.replace('.', '_'));
        assignment.addProperty("inputSymbol", input);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", value);
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        return assignment;
    }
}
