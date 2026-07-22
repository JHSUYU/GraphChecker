package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicReplayValidatorTest {
    @Test
    public void admitsOnlyInputDrivenUnforcedBranchFlip() {
        JsonObject validation = ConcolicReplayValidator.validate(task(),
                result(false, true));

        assertTrue(validation.get("valid").getAsBoolean());
        assertTrue(validation.get("inputModelOnly").getAsBoolean());
    }

    @Test
    public void rejectsSootBranchOverrideEvenWhenOutcomeMatches() {
        JsonObject validation = ConcolicReplayValidator.validate(task(),
                result(true, true));

        assertFalse(validation.get("valid").getAsBoolean());
        assertFalse(validation.get("inputModelOnly").getAsBoolean());
    }

    @Test
    public void rejectsAReplayThatDoesNotTakeTheSolvedFlip() {
        JsonObject validation = ConcolicReplayValidator.validate(task(),
                result(false, false));

        assertFalse(validation.get("valid").getAsBoolean());
        assertFalse(validation.get("flippedBranchValidated").getAsBoolean());
    }

    @Test
    public void admitsNormalExactOutputClosureReplay() {
        JsonObject task = outputTask();
        JsonObject raw = result(false, true);
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
    public void rejectsExceptionalOutputClosureAfterObservedFlip() {
        JsonObject task = outputTask();
        JsonObject raw = result(false, true);
        raw.addProperty("exitKind", "EXCEPTION");
        raw.addProperty("exceptionType",
                "java.util.NoSuchElementException");
        JsonObject summary = outputSummary(task);
        summary.addProperty("normalExit", false);
        summary.addProperty("exceptionType",
                "java.util.NoSuchElementException");

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                summary);

        assertFalse(validation.get("valid").getAsBoolean());
        assertTrue(validation.get("flippedBranchValidated").getAsBoolean());
        assertTrue(validation.get("outputClosureAdmissionGap")
                .getAsBoolean());
        assertEquals("OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT",
                validation.get("outputClosureGapReason").getAsString());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("IMPORTED_OUTPUT_SUMMARY_NOT_NORMAL_EXIT"));
    }

    @Test
    public void rejectsOutputClosureWithoutExactRequestedExpression() {
        JsonObject task = outputTask();
        JsonObject raw = result(false, true);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        JsonObject summary = outputSummary(task);
        summary.add("outputExpressions", new JsonObject());

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                summary);

        assertFalse(validation.get("valid").getAsBoolean());
        assertTrue(validation.get("outputClosureAdmissionGap")
                .getAsBoolean());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("REQUESTED_OUTPUT_EXPRESSION_MISSING"));
    }

    @Test
    public void validatesExactTwoEntryDynamicAssignmentSet() {
        JsonObject task = task();
        JsonArray planned = dynamicAssignments();
        task.add("modelAssignments", planned.deepCopy());
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", planned.size());
        raw.add("modelAssignmentsApplied", planned.deepCopy());

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertTrue(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertTrue(validation.get("dynamicAssignmentIdentityValidated")
                .getAsBoolean());
        assertEquals(2, validation.get(
                "appliedDynamicModelAssignmentCount").getAsInt());
    }

    @Test
    public void validatesFreshKeyRebindingByExactStaticOccurrence() {
        JsonObject task = outputTask();
        JsonObject plannedRow = freshRebindingPlan();
        JsonArray planned = new JsonArray();
        planned.add(plannedRow);
        task.add("modelAssignments", planned);

        JsonObject appliedRow = freshRebindingApplied(plannedRow, 99);
        JsonArray applied = new JsonArray();
        applied.add(appliedRow);
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", 1);
        raw.add("modelAssignmentsApplied", applied);
        JsonArray freshBindings = new JsonArray();
        freshBindings.add(freshRawBinding(appliedRow));
        raw.add("dynamicFieldBindings", freshBindings);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        JsonObject summary = outputSummary(task);
        JsonObject importedBinding = freshRawBinding(appliedRow);
        importedBinding.addProperty("authority",
                "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                        + "ENTRY_VALUE_TOKEN_JOIN");
        importedBinding.remove("complete");
        JsonArray importedBindings = new JsonArray();
        importedBindings.add(importedBinding);
        addImportedFreshBindings(summary, importedBindings,
                appliedRow.get("entryReadObservationId").getAsString());

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                summary);

        assertTrue(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertEquals(1, validation.get("freshMapEntryRebindingCount")
                .getAsInt());
        assertTrue(validation.get("freshMapEntryRebindingValidated")
                .getAsBoolean());
        assertFalse("planned replay must not retain a seed key",
                plannedRow.has("expectedEntryKey"));
        assertEquals("Y_I_99", appliedRow.getAsJsonObject("keyExpression")
                .get("_exp").getAsString());
    }

    @Test
    public void rejectsFreshRebindingWhenRuntimeSelectorDoesNotMatch() {
        JsonObject plannedRow = freshRebindingPlan();
        for (String fault : new String[]{"KEY", "OCCURRENCE", "SITE"}) {
            JsonObject task = task();
            JsonArray planned = new JsonArray();
            planned.add(plannedRow.deepCopy());
            task.add("modelAssignments", planned);
            JsonObject appliedRow = freshRebindingApplied(plannedRow, 99);
            JsonArray applied = new JsonArray();
            applied.add(appliedRow);
            JsonObject rawBinding = freshRawBinding(appliedRow);
            if ("KEY".equals(fault)) {
                rawBinding.add("keyExpression", integerKey(100));
            } else if ("OCCURRENCE".equals(fault)) {
                rawBinding.addProperty("materializationOccurrence", 2);
            } else {
                rawBinding.addProperty("materializationSiteId",
                        "SITE.OTHER.GETTER");
            }
            JsonObject raw = result(false, true);
            raw.addProperty("modelAssignmentAppliedCount", 1);
            raw.add("modelAssignmentsApplied", applied);
            JsonArray bindings = new JsonArray();
            bindings.add(rawBinding);
            raw.add("dynamicFieldBindings", bindings);

            JsonObject validation = ConcolicReplayValidator.validate(task,
                    raw);

            assertFalse(fault + ":" + validation,
                    validation.get("valid").getAsBoolean());
            assertTrue(validation.getAsJsonArray("failures").toString()
                    .contains("NO_EXACT_FRESH_RAW_BINDING"));
        }
    }

    @Test
    public void rejectsFreshRebindingWhenImportedSelectorDoesNotMatch() {
        JsonObject task = outputTask();
        JsonObject plannedRow = freshRebindingPlan();
        JsonArray planned = new JsonArray();
        planned.add(plannedRow);
        task.add("modelAssignments", planned);

        JsonObject appliedRow = freshRebindingApplied(plannedRow, 99);
        JsonArray applied = new JsonArray();
        applied.add(appliedRow);
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", 1);
        raw.add("modelAssignmentsApplied", applied);
        JsonArray rawBindings = new JsonArray();
        rawBindings.add(freshRawBinding(appliedRow));
        raw.add("dynamicFieldBindings", rawBindings);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");

        JsonObject summary = outputSummary(task);
        JsonObject importedBinding = freshRawBinding(appliedRow);
        importedBinding.addProperty("authority",
                "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                        + "ENTRY_VALUE_TOKEN_JOIN");
        importedBinding.remove("complete");
        importedBinding.add("keyExpression", integerKey(100));
        JsonArray importedBindings = new JsonArray();
        importedBindings.add(importedBinding);
        addImportedFreshBindings(summary, importedBindings,
                appliedRow.get("entryReadObservationId").getAsString());

        JsonObject validation = ConcolicReplayValidator.validate(task, raw,
                summary);

        assertFalse(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("NO_EXACT_FRESH_IMPORTED_BINDING"));
    }

    @Test
    public void validatesExactArrayElementAssignmentWithoutMapKey() {
        JsonObject task = task();
        JsonArray planned = new JsonArray();
        planned.add(containerAssignment(2, 3));
        task.add("modelAssignments", planned.deepCopy());
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", 1);
        JsonObject applied = appliedContainerAssignment(
                planned.get(0).getAsJsonObject(), "ACT.REPLAY");
        // Runtime reconstructs the selector but does not need to echo the
        // producer-only binding-kind discriminator.
        applied.remove("dynamicFieldBindingKind");
        JsonArray appliedRows = new JsonArray();
        appliedRows.add(applied);
        raw.add("modelAssignmentsApplied", appliedRows);
        JsonArray rawBindings = new JsonArray();
        rawBindings.add(rawContainerBinding(applied));
        raw.add("dynamicFieldBindings", rawBindings);

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertTrue(validation.toString(), validation.get("valid")
                .getAsBoolean());
        assertTrue(validation.get("dynamicAssignmentIdentityValidated")
                .getAsBoolean());
    }

    @Test
    public void rejectsSeedTokensWrongReplayScopeAndUnjoinedContainerToken() {
        for (String fault : new String[]{"SEED_TOKEN", "WRONG_SCOPE",
                "RAW_TOKEN"}) {
            JsonObject plannedRow = containerAssignment(2, 3);
            if ("SEED_TOKEN".equals(fault)) {
                plannedRow.getAsJsonObject("containerSelector")
                        .addProperty("containerObjectToken", 77L);
            }
            JsonObject task = task();
            JsonArray planned = new JsonArray();
            planned.add(plannedRow);
            task.add("modelAssignments", planned);
            String scope = "WRONG_SCOPE".equals(fault)
                    ? "ACT.SOURCE" : "ACT.REPLAY";
            JsonObject applied = appliedContainerAssignment(plannedRow,
                    scope);
            JsonObject binding = rawContainerBinding(applied);
            if ("RAW_TOKEN".equals(fault)) {
                binding.addProperty(
                        "materializationSiteBridgeElementObjectToken",
                        999L);
            }
            JsonObject raw = result(false, true);
            raw.addProperty("modelAssignmentAppliedCount", 1);
            JsonArray appliedRows = new JsonArray();
            appliedRows.add(applied);
            raw.add("modelAssignmentsApplied", appliedRows);
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            raw.add("dynamicFieldBindings", bindings);

            JsonObject validation = ConcolicReplayValidator.validate(task,
                    raw);

            assertFalse(fault + ":" + validation,
                    validation.get("valid").getAsBoolean());
            String failures = validation.getAsJsonArray("failures")
                    .toString();
            if ("SEED_TOKEN".equals(fault)) {
                assertTrue(failures.contains(
                        "PLANNED_CONTAINER_HAS_RUNTIME_MEMBER"));
            } else if ("WRONG_SCOPE".equals(fault)) {
                assertTrue(failures.contains(
                        "INVALID_CONTAINER_OBJECT_TOKEN_SCOPE"));
            } else {
                assertTrue(failures.contains(
                        "NO_EXACT_FRESH_RAW_CONTAINER_BINDING"));
            }
        }
    }

    @Test
    public void rejectsMissingDiscoveryOrWrongArraySelector() {
        JsonObject exact = containerAssignment(2, 3);
        JsonObject missing = exact.deepCopy();
        missing.remove("containerSelector");
        JsonObject discovery = exact.deepCopy();
        discovery.getAsJsonObject("containerSelector").addProperty(
                "selectorAuthority", "DISCOVER_UNIQUE_IDENTITY_INDEX");
        for (JsonObject invalid : new JsonObject[]{missing, discovery}) {
            JsonObject task = task();
            JsonArray planned = new JsonArray();
            planned.add(invalid);
            task.add("modelAssignments", planned.deepCopy());
            JsonObject raw = result(false, true);
            raw.add("modelAssignmentsApplied", planned.deepCopy());
            JsonObject validation = ConcolicReplayValidator.validate(
                    task, raw);
            assertFalse(validation.get("valid").getAsBoolean());
            assertTrue(validation.getAsJsonArray("failures").toString()
                    .contains("INVALID_PLANNED_DYNAMIC_ASSIGNMENT"));
        }

        JsonObject task = task();
        JsonArray planned = new JsonArray();
        planned.add(exact);
        task.add("modelAssignments", planned.deepCopy());
        JsonArray applied = new JsonArray();
        applied.add(appliedContainerAssignment(exact, "ACT.REPLAY"));
        applied.get(0).getAsJsonObject().getAsJsonObject(
                "containerSelector").addProperty("elementIndex", 1);
        JsonObject raw = result(false, true);
        raw.add("modelAssignmentsApplied", applied);
        JsonArray rawBindings = new JsonArray();
        rawBindings.add(rawContainerBinding(
                applied.get(0).getAsJsonObject()));
        raw.add("dynamicFieldBindings", rawBindings);
        JsonObject mismatch = ConcolicReplayValidator.validate(task, raw);
        assertFalse(mismatch.get("valid").getAsBoolean());
        assertTrue(mismatch.getAsJsonArray("failures").toString().contains(
                "DYNAMIC_MODEL_ASSIGNMENT_SET_MISMATCH"));
    }

    @Test
    public void validatesRealVmFieldWrapperWithOwnerSuffix() {
        JsonObject task = task();
        JsonArray planned = dynamicAssignments();
        for (int index = 0; index < planned.size(); index++) {
            JsonObject assignment = planned.get(index).getAsJsonObject();
            assignment.addProperty("engineSymbol", "M_J_field_"
                    + assignment.get("dynamicFieldSymbol").getAsString()
                    + "_org/apache/hadoop/hdfs/security/token/block/BlockKey");
        }
        task.add("modelAssignments", planned.deepCopy());
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", planned.size());
        raw.add("modelAssignmentsApplied", planned.deepCopy());

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertTrue(validation.toString(), validation.get("valid")
                .getAsBoolean());
    }

    @Test
    public void rejectsMalformedVmSuffixAndCrossBindingEngine() {
        JsonObject task = task();
        JsonArray malformed = dynamicAssignments();
        JsonObject first = malformed.get(0).getAsJsonObject();
        first.addProperty("engineSymbol", "M_J_field_"
                + first.get("dynamicFieldSymbol").getAsString()
                + "_java.lang.Long");
        task.add("modelAssignments", malformed.deepCopy());
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", malformed.size());
        raw.add("modelAssignmentsApplied", malformed.deepCopy());

        JsonObject invalid = ConcolicReplayValidator.validate(task, raw);
        assertFalse(invalid.get("valid").getAsBoolean());
        assertTrue(invalid.getAsJsonArray("failures").toString().contains(
                "ENGINE_DYNAMIC_SYMBOL_MISMATCH"));

        JsonArray crossed = dynamicAssignments();
        String otherDynamic = crossed.get(0).getAsJsonObject().get(
                "dynamicFieldSymbol").getAsString();
        crossed.get(1).getAsJsonObject().addProperty("engineSymbol",
                "M_J_field_" + otherDynamic + "_java/lang/Long");
        JsonObject crossedTask = task();
        crossedTask.add("modelAssignments", crossed.deepCopy());
        JsonObject crossedRaw = result(false, true);
        crossedRaw.addProperty("modelAssignmentAppliedCount",
                crossed.size());
        crossedRaw.add("modelAssignmentsApplied", crossed.deepCopy());

        JsonObject crossValidation = ConcolicReplayValidator.validate(
                crossedTask, crossedRaw);
        assertFalse(crossValidation.get("valid").getAsBoolean());
        assertTrue(crossValidation.getAsJsonArray("failures").toString()
                .contains("ENGINE_DYNAMIC_SYMBOL_MISMATCH"));
    }

    @Test
    public void rejectsWrongOccurrenceTwoKeySelector() {
        JsonObject task = task();
        JsonArray planned = dynamicAssignments();
        task.add("modelAssignments", planned.deepCopy());
        JsonArray applied = planned.deepCopy();
        applied.get(1).getAsJsonObject().getAsJsonObject(
                "expectedEntryKey").addProperty("_exp", "wrong-key");
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", applied.size());
        raw.add("modelAssignmentsApplied", applied);

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertFalse(validation.get("valid").getAsBoolean());
        assertFalse(validation.get("dynamicAssignmentIdentityValidated")
                .getAsBoolean());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("DYNAMIC_MODEL_ASSIGNMENT_SET_MISMATCH"));
    }

    @Test
    public void rejectsWrongDynamicOwnerEvenWithSameBindingId() {
        JsonObject task = task();
        JsonArray planned = dynamicAssignments();
        task.add("modelAssignments", planned.deepCopy());
        JsonArray applied = planned.deepCopy();
        applied.get(1).getAsJsonObject().addProperty("inputSymbol",
                "REGION.3.in.99");
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", applied.size());
        raw.add("modelAssignmentsApplied", applied);

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertFalse(validation.get("valid").getAsBoolean());
        assertTrue(validation.getAsJsonArray("failures").toString()
                .contains("WRONG_INPUT_OWNER"));
    }

    @Test
    public void rejectsMissingOrExtraDynamicAssignment() {
        JsonObject task = task();
        JsonArray planned = dynamicAssignments();
        task.add("modelAssignments", planned.deepCopy());
        JsonArray applied = new JsonArray();
        applied.add(planned.get(0).deepCopy());
        applied.add(dynamicAssignment("REGION.3.in.0.field.extra.occ.3",
                3, "key-three"));
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", applied.size());
        raw.add("modelAssignmentsApplied", applied);

        JsonObject validation = ConcolicReplayValidator.validate(task, raw);

        assertFalse(validation.get("valid").getAsBoolean());
        assertTrue(validation.getAsJsonArray(
                "missingDynamicModelAssignments").size() > 0);
        assertTrue(validation.getAsJsonArray(
                "extraDynamicModelAssignments").size() > 0);
    }

    @Test
    public void keyedMapProjectionReplayRequiresExactScopeKeyAndTokens() {
        JsonObject exact = mapProjectionAssignment();
        JsonObject task = task();
        task.addProperty("activationId", "ACT.REPLAY");
        JsonArray assignments = new JsonArray();
        assignments.add(exact);
        task.add("modelAssignments", assignments.deepCopy());
        JsonObject raw = result(false, true);
        raw.addProperty("activationId", "ACT.REPLAY");
        raw.addProperty("modelAssignmentAppliedCount", 1);
        raw.add("modelAssignmentsApplied", assignments.deepCopy());

        JsonObject valid = ConcolicReplayValidator.validate(task, raw);
        assertTrue(valid.toString(), valid.get("valid").getAsBoolean());

        for (String fault : new String[]{"TOKEN", "SCOPE", "SOURCE",
                "FLOAT"}) {
            JsonObject invalidAssignment = exact.deepCopy();
            JsonObject selector = invalidAssignment.getAsJsonObject(
                    "mapProjectionSelector");
            if ("TOKEN".equals(fault)) {
                selector.addProperty("elementObjectToken",
                        selector.get("mapObjectToken").getAsLong());
            } else if ("SCOPE".equals(fault)) {
                selector.addProperty("objectTokenScope", "ACT.OTHER");
            } else if ("SOURCE".equals(fault)) {
                selector.remove("sourceObjectTokenScope");
            } else {
                JsonObject floatKey = new JsonObject();
                floatKey.addProperty("_type", "ConstExpr");
                floatKey.addProperty("_java_type", "java/lang/Float");
                floatKey.addProperty("_exp", "Y_F_-0.0");
                selector.add("expectedMapKey", floatKey);
            }
            JsonObject invalidTask = task();
            invalidTask.addProperty("activationId", "ACT.REPLAY");
            JsonArray invalidRows = new JsonArray();
            invalidRows.add(invalidAssignment);
            invalidTask.add("modelAssignments", invalidRows.deepCopy());
            JsonObject invalidRaw = result(false, true);
            invalidRaw.addProperty("activationId", "ACT.REPLAY");
            invalidRaw.add("modelAssignmentsApplied",
                    invalidRows.deepCopy());
            JsonObject rejected = ConcolicReplayValidator.validate(
                    invalidTask, invalidRaw);
            assertFalse(fault + ":" + rejected,
                    rejected.get("valid").getAsBoolean());
            assertTrue(rejected.getAsJsonArray("failures").toString()
                    .contains("INVALID_PLANNED_DYNAMIC_ASSIGNMENT"));
        }

        JsonObject duplicateKeyAtOtherIndex = exact.deepCopy();
        String secondDynamic = "REGION.3.in.0.field.map.occ.2";
        duplicateKeyAtOtherIndex.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + secondDynamic);
        duplicateKeyAtOtherIndex.addProperty("dynamicFieldSymbol",
                secondDynamic);
        duplicateKeyAtOtherIndex.addProperty("engineSymbol", secondDynamic);
        duplicateKeyAtOtherIndex.addProperty(
                "materializationOccurrence", 2);
        JsonObject duplicateSelector = duplicateKeyAtOtherIndex
                .getAsJsonObject("mapProjectionSelector");
        duplicateSelector.addProperty("outputIndex", 1);
        duplicateSelector.addProperty("elementOccurrence", 2);
        duplicateSelector.addProperty("elementObjectToken", 602L);
        JsonArray duplicatePlan = new JsonArray();
        duplicatePlan.add(exact.deepCopy());
        duplicatePlan.add(duplicateKeyAtOtherIndex);
        JsonObject duplicateTask = task();
        duplicateTask.addProperty("activationId", "ACT.REPLAY");
        duplicateTask.add("modelAssignments", duplicatePlan.deepCopy());
        JsonObject duplicateRaw = result(false, true);
        duplicateRaw.addProperty("activationId", "ACT.REPLAY");
        duplicateRaw.add("modelAssignmentsApplied", duplicatePlan.deepCopy());
        JsonObject duplicateRejected = ConcolicReplayValidator.validate(
                duplicateTask, duplicateRaw);
        assertFalse(duplicateRejected.get("valid").getAsBoolean());
        assertTrue(duplicateRejected.getAsJsonArray("failures").toString()
                .contains("MAP_PROJECTION_KEY_INDEX_NOT_BIJECTIVE"));
    }

    @Test
    public void rejectsAppliedValueTypeOrAuthorityTampering() {
        for (String member : new String[]{"value", "valueType",
                "authority"}) {
            JsonObject task = task();
            JsonArray planned = dynamicAssignments();
            task.add("modelAssignments", planned.deepCopy());
            JsonArray applied = planned.deepCopy();
            JsonObject first = applied.get(0).getAsJsonObject();
            if ("value".equals(member)) {
                first.addProperty(member, "9223372036854775807");
            } else if ("valueType".equals(member)) {
                first.addProperty(member, "BOOL");
            } else {
                first.addProperty(member, "UNTRUSTED_MODEL");
            }
            JsonObject raw = result(false, true);
            raw.addProperty("modelAssignmentAppliedCount", applied.size());
            raw.add("modelAssignmentsApplied", applied);

            JsonObject rejected = ConcolicReplayValidator.validate(task, raw);
            assertFalse(member + ":" + rejected,
                    rejected.get("valid").getAsBoolean());
            assertTrue(rejected.getAsJsonArray("failures").toString(),
                    rejected.getAsJsonArray("failures").toString().contains(
                            "MODEL_ASSIGNMENT_SET_MISMATCH")
                            || rejected.getAsJsonArray("failures").toString()
                            .contains("INVALID_APPLIED_MODEL_ASSIGNMENT"));
        }
    }

    @Test
    public void rejectsExtraAppliedDirectAssignment() {
        JsonObject task = task();
        JsonArray planned = new JsonArray();
        planned.add(directAssignment("REGION.3.in.0", "7"));
        task.add("modelAssignments", planned.deepCopy());
        JsonArray applied = planned.deepCopy();
        applied.add(directAssignment("REGION.3.in.1", "8"));
        JsonObject raw = result(false, true);
        raw.addProperty("modelAssignmentAppliedCount", applied.size());
        raw.add("modelAssignmentsApplied", applied);

        JsonObject rejected = ConcolicReplayValidator.validate(task, raw);

        assertFalse(rejected.get("valid").getAsBoolean());
        assertTrue(rejected.getAsJsonArray("failures").toString().contains(
                "MODEL_ASSIGNMENT_SET_MISMATCH"));
        assertEquals(1, rejected.getAsJsonArray(
                "extraModelAssignments").size());
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
        JsonObject task = task();
        task.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.3.out.0");
        requested.addProperty("cell", "<example.Region: java.util.Map out>");
        requested.addProperty("kind", "HEAP_STATE");
        task.add("requestedOutput", requested);
        return task;
    }

    private static JsonObject outputSummary(JsonObject task) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.REPLAY");
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("normalExit", true);
        summary.addProperty("exceptionType", "");
        summary.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        summary.add("requestedOutput", task.getAsJsonObject(
                "requestedOutput").deepCopy());
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "Ljava/util/Map;");
        expression.addProperty("_exp", "REGION.3.in.0");
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.3.out.0", expression);
        summary.add("outputExpressions", outputs);
        JsonObject admission = new JsonObject();
        admission.addProperty("complete", true);
        summary.add("outputExpressionAdmission", admission);
        return summary;
    }

    private static JsonObject result(boolean override,
                                     boolean flippedOutcome) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("regionId", "REGION.3");
        raw.addProperty("activationId", "ACT.REPLAY");
        raw.addProperty("allModelAssignmentsApplied", true);
        raw.addProperty("modelAssignmentAppliedCount", 0);
        raw.add("modelAssignmentsApplied", new JsonArray());
        raw.addProperty("branchOverrideUsed", override);
        raw.add("replayMaterializationsApplied", new JsonArray());
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(branchWitness("SITE.0", true,
                branchPredicate("REGION.3.in.0", ">"), 0), false));
        boolean targetOutcome = flippedOutcome ? false : true;
        mappings.add(mapping(branchWitness("SITE.1", targetOutcome,
                branchPredicate("REGION.3.in.1",
                        targetOutcome ? ">" : "<="), 1), override));
        raw.add("branchMappings", mappings);
        return raw;
    }

    private static JsonObject mapping(BranchWitness witness,
                                      boolean override) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", witness.siteId());
        mapping.addProperty("occurrence", witness.occurrence());
        mapping.addProperty("observedOutcome",
                witness.sourceTakenOutcome());
        mapping.addProperty("overrideApplied", override);
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
