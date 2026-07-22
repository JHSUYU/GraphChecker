package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.List;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

/**
 * Admits a solver-generated execution only after ordinary Java branches,
 * without forced outcomes, reproduce the retained prefix and take the
 * requested flipped edge.
 */
public final class ConcolicReplayValidator {
    private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
            "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                    + "FRESH_ENTRY_REBIND_V1";
    private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
            "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                    + "IDENTITY_REBIND_V1";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private ConcolicReplayValidator() {
    }

    public static JsonObject validate(JsonObject task, JsonObject rawResult) {
        return validate(task, rawResult, null);
    }

    /**
     * Validates an unforced branch replay and, for an output-closure task,
     * also validates that the replay actually materialized the exact output
     * requested by the path work item.
     *
     * <p>The imported summary is intentionally part of this admission
     * boundary.  A branch observation alone cannot prove an output
     * transformer: execution may take the desired edge and then throw before
     * the requested output exists (for example, {@code hasNext()==true}
     * followed by {@code Iterator.next()} throwing).  Such an execution is
     * useful gap evidence, but is not a mergeable path summary.</p>
     */
    public static JsonObject validate(JsonObject task, JsonObject rawResult,
                                      JsonObject importedSummary) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_REPLAY_VALIDATION");
        result.addProperty("queryKey", string(task, "queryKey"));
        result.addProperty("regionId", string(task, "regionId"));
        JsonArray failures = new JsonArray();
        BranchReplayContract replayContract = null;
        JsonElement encodedReplayContract = task == null ? null
                : task.get("replayContract");
        if (encodedReplayContract != null) {
            try {
                replayContract = BranchReplayContract.fromJson(
                        encodedReplayContract.getAsJsonObject());
            } catch (RuntimeException malformed) {
                failures.add("INVALID_BRANCH_REPLAY_CONTRACT");
            }
        }
        boolean outputClosure = RegionCaptureGoal.from(task)
                .isOutputClosure();

        require(failures, "MISSING_REGION_RESULT",
                "CONCOLIC_REGION_RESULT".equals(string(rawResult, "event")));
        require(failures, "REGION_ID_MISMATCH", string(task, "regionId")
                .equals(string(rawResult, "regionId")));
        if (replayContract == null) {
            require(failures, "BRANCH_OVERRIDE_USED",
                    !bool(rawResult, "branchOverrideUsed", false)
                            && !hasOverride(array(rawResult,
                            "branchMappings")));
        }
        require(failures, "NON_INPUT_REPLAY_MATERIALIZATION_USED",
                array(rawResult, "replayMaterializationsApplied").size()
                        == 0);
        String plannedActivationId = string(task, "activationId");
        // Runtime-local identity evidence must name the replay activation
        // itself; a task/source activation is never a valid fallback.
        String appliedActivationId = string(rawResult, "activationId");
        JsonArray plannedRows = array(task, "modelAssignments");
        JsonArray appliedRows = array(rawResult,
                "modelAssignmentsApplied");
        DynamicAssignmentSet planned = DynamicAssignmentSet.from(
                plannedRows, "PLANNED",
                plannedActivationId);
        DynamicAssignmentSet applied = DynamicAssignmentSet.from(
                appliedRows, "APPLIED", appliedActivationId);
        boolean dynamicPlan = planned.dynamicCount > 0;
        for (String problem : planned.problems) {
            failures.add("INVALID_PLANNED_MODEL_ASSIGNMENT:" + problem);
            if (problem.contains("DYNAMIC_")
                    || problem.contains("SELECTOR")
                    || problem.contains("BINDING_")
                    || problem.contains("MAP_PROJECTION")) {
                failures.add("INVALID_PLANNED_DYNAMIC_ASSIGNMENT:"
                        + problem);
            }
        }
        for (String problem : applied.problems) {
            failures.add("INVALID_APPLIED_MODEL_ASSIGNMENT:" + problem);
            if (problem.contains("DYNAMIC_")
                    || problem.contains("SELECTOR")
                    || problem.contains("BINDING_")
                    || problem.contains("MAP_PROJECTION")) {
                failures.add("INVALID_APPLIED_DYNAMIC_ASSIGNMENT:"
                        + problem);
            }
        }
        Set<String> missing = new LinkedHashSet<>(planned.identities);
        missing.removeAll(applied.identities);
        Set<String> extra = new LinkedHashSet<>(applied.identities);
        extra.removeAll(planned.identities);
        boolean exactAssignmentSet = planned.problems.isEmpty()
                && applied.problems.isEmpty()
                && missing.isEmpty() && extra.isEmpty()
                && planned.assignmentCount == applied.assignmentCount;
        require(failures, "MODEL_ASSIGNMENT_SET_MISMATCH",
                exactAssignmentSet);
        if (dynamicPlan || applied.dynamicCount > 0) {
            require(failures, "DYNAMIC_MODEL_ASSIGNMENT_SET_MISMATCH",
                    exactAssignmentSet
                            && planned.dynamicCount == applied.dynamicCount);
        }
        require(failures, "MODEL_ASSIGNMENT_NOT_APPLIED",
                bool(rawResult, "allModelAssignmentsApplied", false)
                        && integer(rawResult,
                        "modelAssignmentAppliedCount", -1)
                        == appliedRows.size()
                        && appliedRows.size() == plannedRows.size());
        result.add("missingModelAssignments", GSON.toJsonTree(missing));
        result.add("extraModelAssignments", GSON.toJsonTree(extra));
        result.add("missingDynamicModelAssignments",
                GSON.toJsonTree(dynamicOnly(missing)));
        result.add("extraDynamicModelAssignments",
                GSON.toJsonTree(dynamicOnly(extra)));
        result.addProperty("plannedModelAssignmentCount",
                planned.assignmentCount);
        result.addProperty("appliedModelAssignmentCount",
                applied.assignmentCount);
        result.addProperty("plannedDynamicModelAssignmentCount",
                planned.dynamicCount);
        result.addProperty("appliedDynamicModelAssignmentCount",
                applied.dynamicCount);

        List<String> freshRebindingProblems =
                validateFreshMapEntryRebindings(plannedRows, appliedRows,
                        array(rawResult, "dynamicFieldBindings"),
                        importedSummary == null ? new JsonArray()
                                : importedFreshEntryFieldBindings(
                                importedSummary),
                        importedSummary != null);
        for (String problem : freshRebindingProblems) {
            failures.add("FRESH_MAP_ENTRY_REBINDING_INVALID:" + problem);
        }
        result.addProperty("freshMapEntryRebindingCount",
                freshMapEntryRebindingCount(plannedRows));
        result.addProperty("freshMapEntryRebindingValidated",
                freshRebindingProblems.isEmpty());

        List<String> containerRebindingProblems =
                validateContainerRebindings(plannedRows, appliedRows,
                        array(rawResult, "dynamicFieldBindings"),
                        importedSummary == null ? new JsonArray()
                                : array(importedSummary,
                                "dynamicFieldBindings"),
                        importedSummary != null, appliedActivationId);
        for (String problem : containerRebindingProblems) {
            failures.add("CONTAINER_REPLAY_REBINDING_INVALID:" + problem);
        }
        result.addProperty("containerReplayRebindingCount",
                containerReplayRebindingCount(plannedRows));
        result.addProperty("containerReplayRebindingValidated",
                containerRebindingProblems.isEmpty());

        BranchReplayObservationValidator.Result branchObservation = null;
        if (replayContract != null) {
            List<BranchWitness> witnesses = new ArrayList<>();
            int ordinal = 0;
            for (JsonElement element : array(rawResult,
                    "branchMappings")) {
                if (!element.isJsonObject()) {
                    ordinal++;
                    continue;
                }
                JsonElement encoded = element.getAsJsonObject().get(
                        "witness");
                if (encoded == null) {
                    ordinal++;
                    continue;
                }
                try {
                    witnesses.add(BranchWitness.fromJson(
                            encoded.getAsJsonObject()));
                } catch (RuntimeException malformed) {
                    failures.add("MALFORMED_BRANCH_WITNESS_AT_" + ordinal);
                }
                ordinal++;
            }
            branchObservation = BranchReplayObservationValidator.validate(
                    replayContract, witnesses);
            require(failures, "BRANCH_REPLAY_CONTRACT_NOT_SATISFIED",
                    branchObservation.valid());
            result.add("branchReplayObservation",
                    branchObservation.toJson());
        } else {
            JsonArray observed = array(rawResult, "branchMappings");
            for (JsonElement element : array(task,
                    "expectedBranchPrefix")) {
                if (!element.isJsonObject()) continue;
                JsonObject expected = element.getAsJsonObject();
                require(failures, "PREFIX_MISMATCH:" + identity(expected),
                        observed(observed, expected, bool(expected, "outcome",
                                false)));
            }
            JsonObject flip = new JsonObject();
            flip.addProperty("siteId", string(task, "flipSite"));
            flip.addProperty("occurrence", integer(task,
                    "flipOccurrence", 1));
            boolean desired = bool(task, "desiredOutcome", false);
            require(failures,
                    "FLIPPED_BRANCH_NOT_OBSERVED:" + identity(flip),
                    observed(observed, flip, desired));
        }

        boolean rawNormalExit = !outputClosure || "NORMAL".equals(
                string(rawResult, "exitKind"))
                && string(rawResult, "exceptionType").isEmpty();
        boolean importedSummaryPresent = importedSummary != null;
        boolean importedSummaryValid = !outputClosure
                || importedSummaryPresent
                && bool(importedSummary, "valid", false);
        boolean importedSummaryNormalExit = !outputClosure
                || importedSummaryPresent
                && bool(importedSummary, "normalExit", false)
                && string(importedSummary, "exceptionType").isEmpty();
        boolean importedSummaryRelationallyComplete = !outputClosure
                || importedSummaryPresent
                && bool(importedSummary, "relationallyComplete", false);
        boolean importedSummaryGoalMatches = !outputClosure
                || importedSummaryPresent
                && RegionCaptureGoal.from(importedSummary)
                .isOutputClosure();
        boolean importedSummaryRegionMatches = !outputClosure
                || importedSummaryPresent
                && string(task, "regionId").equals(string(importedSummary,
                "regionId"));
        boolean requestedOutputMatches = !outputClosure
                || importedSummaryPresent
                && exactRequestedOutput(task, importedSummary);
        boolean requestedOutputExpressionPresent = !outputClosure
                || importedSummaryPresent
                && exactRequestedOutputExpression(task, importedSummary);
        boolean outputExpressionAdmissionComplete = !outputClosure
                || importedSummaryPresent
                && outputExpressionAdmissionComplete(importedSummary);

        if (outputClosure) {
            require(failures, "OUTPUT_CLOSURE_REPLAY_EXCEPTIONAL_EXIT",
                    rawNormalExit);
            require(failures, "MISSING_IMPORTED_OUTPUT_SUMMARY",
                    importedSummaryPresent);
            if (importedSummaryPresent) {
                require(failures, "IMPORTED_OUTPUT_SUMMARY_INVALID",
                        importedSummaryValid);
                require(failures,
                        "IMPORTED_OUTPUT_SUMMARY_NOT_RELATIONALLY_COMPLETE",
                        importedSummaryRelationallyComplete);
                require(failures,
                        "IMPORTED_OUTPUT_SUMMARY_NOT_NORMAL_EXIT",
                        importedSummaryNormalExit);
                require(failures,
                        "IMPORTED_OUTPUT_SUMMARY_WRONG_CAPTURE_GOAL",
                        importedSummaryGoalMatches);
                require(failures,
                        "IMPORTED_OUTPUT_SUMMARY_REGION_ID_MISMATCH",
                        importedSummaryRegionMatches);
                require(failures, "REQUESTED_OUTPUT_MISMATCH",
                        requestedOutputMatches);
                require(failures,
                        "REQUESTED_OUTPUT_EXPRESSION_MISSING",
                        requestedOutputExpressionPresent);
                require(failures,
                        "OUTPUT_EXPRESSION_ADMISSION_INCOMPLETE",
                        outputExpressionAdmissionComplete);
            }
        }

        result.add("failures", failures);
        result.addProperty("failureCount", failures.size());
        result.addProperty("prefixValidated", branchObservation != null
                ? branchObservation.valid()
                : !containsPrefixFailure(failures));
        result.addProperty("flippedBranchValidated",
                branchObservation != null ? branchObservation.valid()
                        : !contains(failures,
                        "FLIPPED_BRANCH_NOT_OBSERVED"));
        result.addProperty("inputModelOnly", !contains(failures,
                "BRANCH_OVERRIDE_USED") && !contains(failures,
                "NON_INPUT_REPLAY_MATERIALIZATION_USED"));
        result.addProperty("dynamicAssignmentIdentityValidated",
                !dynamicPlan || !contains(failures,
                        "DYNAMIC_MODEL_ASSIGNMENT_SET_MISMATCH")
                        && !contains(failures,
                        "INVALID_PLANNED_DYNAMIC_ASSIGNMENT")
                        && !contains(failures,
                        "INVALID_APPLIED_DYNAMIC_ASSIGNMENT")
                        && !contains(failures,
                        "FRESH_MAP_ENTRY_REBINDING_INVALID")
                        && !contains(failures,
                        "CONTAINER_REPLAY_REBINDING_INVALID"));
        result.addProperty("modelAssignmentIdentityValidated",
                !contains(failures, "MODEL_ASSIGNMENT_SET_MISMATCH")
                        && !contains(failures,
                        "INVALID_PLANNED_MODEL_ASSIGNMENT")
                        && !contains(failures,
                        "INVALID_APPLIED_MODEL_ASSIGNMENT")
                        && !contains(failures,
                        "CONTAINER_REPLAY_REBINDING_INVALID"));
        boolean outputClosureGap = outputClosure
                && containsOutputClosureFailure(failures);
        int outputClosureFailureCount = countOutputClosureFailures(failures);
        int nonOutputClosureFailureCount = failures.size()
                - outputClosureFailureCount;
        result.addProperty("captureGoal",
                RegionCaptureGoal.from(task).kind());
        result.addProperty("outputClosureAdmissionRequired",
                outputClosure);
        result.addProperty("normalExitValidated", rawNormalExit
                && importedSummaryNormalExit);
        result.addProperty("importedOutputSummaryValidated",
                importedSummaryValid && importedSummaryRelationallyComplete
                        && importedSummaryGoalMatches
                        && importedSummaryRegionMatches);
        result.addProperty("requestedOutputIdentityValidated",
                requestedOutputMatches);
        result.addProperty("requestedOutputExpressionValidated",
                requestedOutputExpressionPresent
                        && outputExpressionAdmissionComplete);
        result.addProperty("outputClosureAdmissionGap", outputClosureGap);
        result.addProperty("outputClosureFailureCount",
                outputClosureFailureCount);
        result.addProperty("nonOutputClosureFailureCount",
                nonOutputClosureFailureCount);
        result.addProperty("branchAndInputReplayValidated",
                nonOutputClosureFailureCount == 0);
        result.addProperty("outputClosureGapReason", outputClosureGap
                ? firstOutputClosureFailure(failures) : "");
        result.addProperty("valid", failures.size() == 0);
        result.addProperty("status", failures.size() == 0
                ? "VALIDATED_UNFORCED_REPLAY" : "REPLAY_REJECTED");
        result.addProperty("admissionAuthority", failures.size() == 0
                ? replayContract == null
                ? "SOLVER_MODEL_PLUS_CONCRETE_BRANCH_OBSERVATION"
                : "SOLVER_MODEL_PLUS_IMMUTABLE_BRANCH_REPLAY_CONTRACT_V1"
                : "NONE");
        return result;
    }

    private static final class DynamicAssignmentSet {
        private final Set<String> identities = new LinkedHashSet<>();
        private final List<String> problems = new ArrayList<>();
        private int assignmentCount;
        private int dynamicCount;

        private static DynamicAssignmentSet empty() {
            return new DynamicAssignmentSet();
        }

        private static DynamicAssignmentSet from(JsonArray assignments,
                                                 String source,
                                                 String activationId) {
            DynamicAssignmentSet result = new DynamicAssignmentSet();
            java.util.Map<String, Integer> mapKeyIndices =
                    new java.util.LinkedHashMap<>();
            java.util.Map<String, String> mapIndexKeys =
                    new java.util.LinkedHashMap<>();
            for (int index = 0; index < assignments.size(); index++) {
                JsonElement element = assignments.get(index);
                result.assignmentCount++;
                if (!element.isJsonObject()) {
                    result.problems.add(source + "_" + index
                            + ":NON_OBJECT_MODEL_ASSIGNMENT");
                    continue;
                }
                JsonObject assignment = element.getAsJsonObject();
                List<String> validation = validateModelAssignment(
                        assignment, source);
                boolean dynamic = !string(assignment,
                        "dynamicBindingId").isEmpty();
                if (dynamic) {
                    result.dynamicCount++;
                    validation.addAll(validateDynamicAssignment(
                            assignment, activationId, source));
                }
                for (String problem : validation) {
                    result.problems.add(source + "_" + index + ":"
                            + problem);
                }
                if (!validation.isEmpty()) continue;
                JsonObject mapSelector = object(assignment,
                        "mapProjectionSelector");
                if (dynamic && mapSelector.size() > 0) {
                    String group = string(mapSelector, "mapInputPort")
                            + "\u0000" + string(mapSelector, "outputPort")
                            + "\u0000" + string(mapSelector, "outputCell")
                            + "\u0000" + string(mapSelector,
                            "mapProjectionOperation");
                    String stableKey = stableImmutableMapKeySelector(
                            mapSelector.get("expectedMapKey"));
                    int outputIndex = integer(mapSelector,
                            "outputIndex", -1);
                    Integer previousIndex = mapKeyIndices.put(group
                            + "\u0000" + stableKey, outputIndex);
                    String previousKey = mapIndexKeys.put(group + "\u0000"
                            + outputIndex, stableKey);
                    if (previousIndex != null
                            && previousIndex.intValue() != outputIndex
                            || previousKey != null
                            && !previousKey.equals(stableKey)) {
                        result.problems.add(source + "_" + index
                                + ":MAP_PROJECTION_KEY_INDEX_NOT_BIJECTIVE");
                        continue;
                    }
                }
                String identity = assignmentIdentity(assignment);
                if (!result.identities.add(identity)) {
                    result.problems.add(source + "_" + index
                            + ":DUPLICATE_MODEL_ASSIGNMENT");
                }
            }
            return result;
        }
    }

    private static List<String> validateModelAssignment(
            JsonObject assignment, String source) {
        List<String> result = new ArrayList<>();
        if (string(assignment, "engineSymbol").isEmpty()) {
            result.add("MISSING_ENGINE_SYMBOL");
        }
        if (string(assignment, "inputSymbol").isEmpty()) {
            result.add("MISSING_INPUT_SYMBOL");
        }
        if (string(assignment, "valueType").isEmpty()) {
            result.add("MISSING_MODEL_VALUE_TYPE");
        }
        if (!assignment.has("value") || assignment.get("value").isJsonNull()) {
            result.add("MISSING_MODEL_VALUE");
        }
        String authority = string(assignment, "authority");
        if (!("Z3_PATH_FLIP_MODEL".equals(authority)
                || "Z3_BOUNDED_COMPOSED_MODEL_PROJECTION".equals(
                authority))) {
            result.add("INVALID_TOP_LEVEL_MODEL_AUTHORITY");
        }
        if (!bool(assignment, "materializeAtRealDefinition", false)) {
            result.add("MODEL_NOT_MATERIALIZED_AT_REAL_DEFINITION");
        }
        // A planned assignment must retain the exact solver term which
        // supplied its value. Runtime-applied rows intentionally do not echo
        // solverSymbol; their engine/input/selector identity below is the
        // canonical execution-side provenance.
        if ("PLANNED".equals(source)
                && string(assignment, "solverSymbol").isEmpty()) {
            result.add("MISSING_SOLVER_SYMBOL_PROVENANCE");
        }
        return result;
    }

    private static void validateMapEntrySelector(JsonObject assignment,
                                                 String source,
                                                 List<String> result) {
        boolean freshRebinding = freshMapEntryRebinding(assignment);
        if (!freshRebinding) {
            JsonElement key = selectorKey(assignment);
            String authority = selectorAuthority(assignment);
            if (key == null || key.isJsonNull()) {
                result.add("MISSING_EXPECTED_ENTRY_KEY");
            }
            if (authority.isEmpty()) {
                result.add("MISSING_EXPECTED_ENTRY_KEY_AUTHORITY");
            }
            return;
        }

        if (bool(assignment, "sourceEntrySelectorRetained", true)) {
            result.add("FRESH_REBIND_RETAINS_SOURCE_ENTRY_SELECTOR");
        }
        if (assignment.has("expectedEntryKey")
                || assignment.has("expectedEntryKeyAuthority")) {
            result.add("FRESH_REBIND_HAS_SEED_EXPECTED_KEY");
        }
        if ("PLANNED".equals(source)) {
            if (assignment.has("entryReadObservationId")
                    || assignment.has("keyExpression")
                    || assignment.has("keyExpressionAuthority")) {
                result.add("PLANNED_FRESH_REBIND_HAS_SEED_SELECTOR");
            }
            return;
        }

        JsonElement key = assignment.get("keyExpression");
        if (key == null || !key.isJsonObject()
                || string(assignment, "keyExpressionAuthority").isEmpty()
                || string(assignment, "entryReadObservationId").isEmpty()) {
            result.add("APPLIED_FRESH_ENTRY_SELECTOR_INCOMPLETE");
        }
        if (!bool(assignment, "freshEntrySelectorCaptured", false)) {
            result.add("APPLIED_FRESH_ENTRY_SELECTOR_NOT_CAPTURED");
        }
        if (bool(assignment, "sameSeedEntryClaimed", true)) {
            result.add("APPLIED_FRESH_REBIND_CLAIMS_SEED_ENTRY_IDENTITY");
        }
    }

    private static boolean freshMapEntryRebinding(JsonObject assignment) {
        return FRESH_MAP_ENTRY_REBINDING_AUTHORITY.equals(string(assignment,
                "dynamicReplayRebindingAuthority"));
    }

    private static int freshMapEntryRebindingCount(JsonArray assignments) {
        int result = 0;
        for (JsonElement element : assignments) {
            if (element.isJsonObject() && freshMapEntryRebinding(
                    element.getAsJsonObject())) result++;
        }
        return result;
    }

    /**
     * Joins a static replay selector to the entry selector captured in the
     * replay JVM.  No seed key or object token participates in this join.
     */
    private static List<String> validateFreshMapEntryRebindings(
            JsonArray planned, JsonArray applied, JsonArray rawBindings,
            JsonArray importedBindings, boolean importedSummaryPresent) {
        List<String> problems = new ArrayList<>();
        int plannedCount = freshMapEntryRebindingCount(planned);
        int appliedCount = freshMapEntryRebindingCount(applied);
        if (plannedCount != appliedCount) {
            problems.add("PLANNED_APPLIED_REBIND_COUNT_MISMATCH");
        }
        for (int index = 0; index < planned.size(); index++) {
            JsonElement element = planned.get(index);
            if (!element.isJsonObject()
                    || !freshMapEntryRebinding(element.getAsJsonObject())) {
                continue;
            }
            JsonObject plan = element.getAsJsonObject();
            if (containsMember(plan, "expectedEntryKey")
                    || containsMember(plan, "expectedEntryKeyAuthority")
                    || containsMember(plan, "entryReadObservationId")
                    || containsMember(plan, "keyExpression")
                    || containsMember(plan, "keyExpressionAuthority")) {
                problems.add("PLAN_" + index
                        + "_CONTAINS_SEED_ENTRY_SELECTOR");
                continue;
            }
            List<JsonObject> appliedMatches = matchingStaticRebindings(
                    applied, plan);
            if (appliedMatches.size() != 1) {
                problems.add("PLAN_" + index
                        + (appliedMatches.isEmpty()
                        ? "_NO_EXACT_APPLIED_REBIND"
                        : "_AMBIGUOUS_APPLIED_REBIND"));
                continue;
            }
            JsonObject appliedRow = appliedMatches.get(0);
            List<JsonObject> rawMatches = matchingFreshBindings(rawBindings,
                    appliedRow, true);
            if (rawMatches.size() != 1) {
                problems.add("PLAN_" + index + (rawMatches.isEmpty()
                        ? "_NO_EXACT_FRESH_RAW_BINDING"
                        : "_AMBIGUOUS_FRESH_RAW_BINDING"));
                continue;
            }
            if (importedSummaryPresent) {
                List<JsonObject> importedMatches = matchingFreshBindings(
                        importedBindings, appliedRow, false);
                if (importedMatches.size() != 1) {
                    problems.add("PLAN_" + index
                            + (importedMatches.isEmpty()
                            ? "_NO_EXACT_FRESH_IMPORTED_BINDING"
                            : "_AMBIGUOUS_FRESH_IMPORTED_BINDING"));
                }
            }
        }
        return problems;
    }

    private static List<JsonObject> matchingStaticRebindings(
            JsonArray assignments, JsonObject expected) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (freshMapEntryRebinding(candidate)
                    && same(candidate, expected, "engineSymbol")
                    && same(candidate, expected, "inputSymbol")
                    && same(candidate, expected, "baseInputSymbol")
                    && same(candidate, expected, "dynamicBindingId")
                    && same(candidate, expected, "dynamicFieldSymbol")
                    && same(candidate, expected, "materializationSiteId")
                    && integer(candidate, "materializationOccurrence", -1)
                    == integer(expected, "materializationOccurrence", -2)
                    && canonical(array(candidate, "materializationPath"))
                    .equals(canonical(array(expected,
                            "materializationPath")))) {
                result.add(candidate);
            }
        }
        return result;
    }

    private static List<JsonObject> matchingFreshBindings(
            JsonArray bindings, JsonObject applied, boolean raw) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String expectedKind = "DYNAMIC_MAP_ENTRY_FIELD_BINDING";
            String expectedAuthority = raw
                    ? "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                    + "FIELD_SITE_OCCURRENCE"
                    : "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                    + "ENTRY_VALUE_TOKEN_JOIN";
            if (!expectedKind.equals(string(binding, "kind"))
                    || !expectedAuthority.equals(string(binding,
                    "authority"))
                    || raw && !bool(binding, "complete", false)
                    || !same(binding, applied, "baseInputSymbol")
                    || !same(binding, applied, "dynamicBindingId")
                    || !same(binding, applied, "dynamicFieldSymbol")
                    || !same(binding, applied, "materializationSiteId")
                    || integer(binding, "materializationOccurrence", -1)
                    != integer(applied, "materializationOccurrence", -2)
                    || !canonical(array(binding, "fieldPath")).equals(
                    canonical(array(applied, "materializationPath")))
                    || !same(binding, applied, "entryReadObservationId")
                    || !same(binding, applied, "keyExpressionAuthority")
                    || binding.get("keyExpression") == null
                    || applied.get("keyExpression") == null
                    || !binding.get("keyExpression").equals(
                    applied.get("keyExpression"))) {
                continue;
            }
            result.add(binding);
        }
        return result;
    }

    /**
     * The summary-level dynamicFieldBindings array preserves the raw runtime
     * declaration.  The importer-certified semantic join lives under the
     * exact complete MAP_ENTRY_READ observation; only those nested rows are
     * eligible to validate a fresh cross-execution entry rebinding.
     */
    private static JsonArray importedFreshEntryFieldBindings(
            JsonObject summary) {
        JsonArray result = new JsonArray();
        for (JsonElement element : array(summary, "heapObservations")) {
            if (!element.isJsonObject()) continue;
            JsonObject observation = element.getAsJsonObject();
            String observationId = string(observation, "observationId");
            if (!"MAP_ENTRY_READ".equals(string(observation, "kind"))
                    || observationId.isEmpty()
                    || !bool(observation, "complete", false)) {
                continue;
            }
            for (JsonElement bindingElement : array(observation,
                    "entryFieldBindings")) {
                if (!bindingElement.isJsonObject()) continue;
                JsonObject binding = bindingElement.getAsJsonObject();
                if (observationId.equals(string(binding,
                        "entryReadObservationId"))) {
                    result.add(binding);
                }
            }
        }
        return result;
    }

    private static boolean containerReplayRebinding(
            JsonObject assignment) {
        return CONTAINER_REPLAY_REBINDING_AUTHORITY.equals(string(
                assignment, "containerReplayRebindingAuthority"));
    }

    private static int containerReplayRebindingCount(
            JsonArray assignments) {
        int result = 0;
        for (JsonElement element : assignments) {
            if (element.isJsonObject() && containerReplayRebinding(
                    element.getAsJsonObject())) {
                result++;
            }
        }
        return result;
    }

    /**
     * Joins a stable array selector in the solver plan to the fresh
     * activation-local object identities observed by the replay JVM.  Object
     * token numbers are never compared to the source execution; only the
     * static selector tuple crosses that boundary.
     */
    private static List<String> validateContainerRebindings(
            JsonArray planned, JsonArray applied, JsonArray rawBindings,
            JsonArray importedBindings, boolean importedSummaryPresent,
            String replayActivationId) {
        List<String> problems = new ArrayList<>();
        int plannedCount = containerReplayRebindingCount(planned);
        int appliedCount = containerReplayRebindingCount(applied);
        if (plannedCount != appliedCount) {
            problems.add("PLANNED_APPLIED_REBIND_COUNT_MISMATCH");
        }
        for (int index = 0; index < planned.size(); index++) {
            JsonElement element = planned.get(index);
            if (!element.isJsonObject()
                    || !containerReplayRebinding(
                    element.getAsJsonObject())) {
                continue;
            }
            JsonObject plan = element.getAsJsonObject();
            List<JsonObject> appliedMatches =
                    matchingStableContainerAssignments(applied, plan);
            if (appliedMatches.size() != 1) {
                problems.add("PLAN_" + index
                        + (appliedMatches.isEmpty()
                        ? "_NO_EXACT_APPLIED_REBIND"
                        : "_AMBIGUOUS_APPLIED_REBIND"));
                continue;
            }
            JsonObject appliedRow = appliedMatches.get(0);
            List<JsonObject> rawMatches = matchingRuntimeContainerBindings(
                    rawBindings, appliedRow, replayActivationId);
            if (rawMatches.size() != 1) {
                problems.add("PLAN_" + index
                        + (rawMatches.isEmpty()
                        ? "_NO_EXACT_FRESH_RAW_CONTAINER_BINDING"
                        : "_AMBIGUOUS_FRESH_RAW_CONTAINER_BINDING"));
                continue;
            }
            if (importedSummaryPresent) {
                List<JsonObject> importedMatches =
                        matchingRuntimeContainerBindings(importedBindings,
                                appliedRow, replayActivationId);
                if (importedMatches.size() != 1) {
                    problems.add("PLAN_" + index
                            + (importedMatches.isEmpty()
                            ? "_NO_EXACT_FRESH_IMPORTED_CONTAINER_BINDING"
                            : "_AMBIGUOUS_FRESH_IMPORTED_CONTAINER_BINDING"));
                }
            }
        }
        return problems;
    }

    private static List<JsonObject> matchingStableContainerAssignments(
            JsonArray assignments, JsonObject expected) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (containerReplayRebinding(candidate)
                    && same(candidate, expected, "engineSymbol")
                    && same(candidate, expected, "inputSymbol")
                    && same(candidate, expected, "baseInputSymbol")
                    && same(candidate, expected, "valueType")
                    && same(candidate, expected, "value")
                    && same(candidate, expected, "authority")
                    && same(candidate, expected, "dynamicBindingId")
                    && same(candidate, expected, "dynamicFieldSymbol")
                    && same(candidate, expected,
                    "materializationSiteId")
                    && integer(candidate, "materializationOccurrence", -1)
                    == integer(expected, "materializationOccurrence", -2)
                    && canonical(array(candidate, "materializationPath"))
                    .equals(canonical(array(expected,
                            "materializationPath")))
                    && sameStableContainerSelector(object(candidate,
                    "containerSelector"), object(expected,
                    "containerSelector"))) {
                result.add(candidate);
            }
        }
        return result;
    }

    private static boolean sameStableContainerSelector(JsonObject left,
                                                       JsonObject right) {
        for (String member : new String[]{"kind", "bindingId",
                "containerInputPort", "containerInputCell",
                "selectorAuthority", "declaredFieldOwnerClass",
                "declaredFieldType"}) {
            if (!same(left, right, member)) return false;
        }
        return integer(left, "elementIndex", -1)
                == integer(right, "elementIndex", -2)
                && integer(left, "elementOccurrence", -1)
                == integer(right, "elementOccurrence", -2);
    }

    private static JsonObject stableContainerSelector(
            JsonObject selector) {
        JsonObject result = new JsonObject();
        for (String member : new String[]{"kind", "bindingId",
                "containerInputPort", "containerInputCell",
                "selectorAuthority", "elementIndex",
                "elementOccurrence", "declaredFieldOwnerClass",
                "declaredFieldType"}) {
            JsonElement value = selector.get(member);
            if (value != null) result.add(member, value.deepCopy());
        }
        return result;
    }

    private static List<JsonObject> matchingRuntimeContainerBindings(
            JsonArray bindings, JsonObject applied,
            String replayActivationId) {
        List<JsonObject> result = new ArrayList<>();
        JsonObject expectedSelector = object(applied,
                "containerSelector");
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            JsonObject selector = object(binding, "containerSelector");
            long elementToken = longInteger(selector,
                    "elementObjectToken", 0L);
            String scope = string(selector, "objectTokenScope");
            if (!"DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                    string(binding, "kind"))
                    || !"ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                    .concat("IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE")
                    .equals(string(binding, "authority"))
                    || !bool(binding, "complete", false)
                    || !same(binding, applied, "baseInputSymbol")
                    || !same(binding, applied, "dynamicBindingId")
                    || !same(binding, applied, "dynamicFieldSymbol")
                    || !same(binding, applied, "materializationSiteId")
                    || integer(binding, "materializationOccurrence", -1)
                    != integer(applied, "materializationOccurrence", -2)
                    || !canonical(array(binding, "fieldPath")).equals(
                    canonical(array(applied, "materializationPath")))
                    || !selector.equals(expectedSelector)
                    || replayActivationId.isEmpty()
                    || !replayActivationId.equals(scope)
                    || !scope.equals(string(binding, "objectTokenScope"))
                    || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(binding, "objectTokenAuthority"))
                    || !"STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_"
                    .concat("EXACT_ELEMENT_IDENTITY_TO_DECLARED_FIELD_"
                            + "HOOK_V1").equals(string(binding,
                    "materializationSiteBridgeAuthority"))
                    || !string(selector, "bindingId").equals(string(
                    binding, "materializationSiteBridgeBindingId"))
                    || elementToken <= 0L
                    || elementToken != longInteger(binding,
                    "materializationSiteBridgeElementObjectToken", 0L)
                    || !scope.equals(string(binding,
                    "materializationSiteBridgeObjectTokenScope"))) {
                continue;
            }
            result.add(binding);
        }
        return result;
    }

    private static boolean same(JsonObject left, JsonObject right,
                                String member) {
        return string(left, member).equals(string(right, member));
    }

    private static boolean containsMember(JsonElement value, String member) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return false;
        }
        if (value.isJsonArray()) {
            for (JsonElement element : value.getAsJsonArray()) {
                if (containsMember(element, member)) return true;
            }
            return false;
        }
        JsonObject object = value.getAsJsonObject();
        if (object.has(member)) return true;
        for (java.util.Map.Entry<String, JsonElement> entry
                : object.entrySet()) {
            if (containsMember(entry.getValue(), member)) return true;
        }
        return false;
    }

    private static List<String> validateDynamicAssignment(
            JsonObject assignment, String activationId, String source) {
        List<String> result = new ArrayList<>();
        String bindingId = string(assignment, "dynamicBindingId");
        String base = string(assignment, "baseInputSymbol");
        String dynamic = string(assignment, "dynamicFieldSymbol");
        String engine = string(assignment, "engineSymbol");
        String input = string(assignment, "inputSymbol");
        String site = string(assignment, "materializationSiteId");
        int occurrence = integer(assignment, "materializationOccurrence",
                -1);
        JsonObject containerSelector = object(assignment,
                "containerSelector");
        JsonObject mapProjectionSelector = object(assignment,
                "mapProjectionSelector");
        boolean mapProjection = mapProjectionSelector.size() > 0
                || "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                .equals(string(assignment, "dynamicFieldBindingKind"));
        boolean container = containerSelector.size() > 0
                || "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                string(assignment, "dynamicFieldBindingKind"))
                || containerReplayRebinding(assignment);
        if (base.isEmpty()) result.add("MISSING_BASE_INPUT_SYMBOL");
        if (dynamic.isEmpty()) result.add("MISSING_DYNAMIC_FIELD_SYMBOL");
        if (engine.isEmpty()) result.add("MISSING_ENGINE_SYMBOL");
        if (site.isEmpty()) result.add("MISSING_MATERIALIZATION_SITE");
        if (occurrence < 1) {
            result.add("INVALID_MATERIALIZATION_OCCURRENCE");
        }
        if (mapProjection) {
            validateMapProjectionSelector(mapProjectionSelector,
                    occurrence, activationId, result);
            if (assignment.has("expectedEntryKey")
                    || assignment.has("containerSelector")) {
                result.add("MAP_PROJECTION_HAS_FOREIGN_SELECTOR");
            }
        } else if (container) {
            validateContainerSelector(assignment, containerSelector,
                    occurrence, activationId, source, result);
        } else {
            validateMapEntrySelector(assignment, source, result);
        }
        if (!dynamic.isEmpty()
                && !bindingId.equals("DYNAMIC_FIELD:" + dynamic)) {
            result.add("BINDING_ID_DYNAMIC_SYMBOL_MISMATCH");
        }
        if (!base.isEmpty() && !base.equals(input)) {
            result.add("WRONG_INPUT_OWNER");
        }
        if (!dynamic.isEmpty() && !exactEngineSymbol(engine, dynamic)) {
            result.add("ENGINE_DYNAMIC_SYMBOL_MISMATCH");
        }
        return result;
    }

    private static void validateContainerSelector(JsonObject assignment,
                                                  JsonObject selector,
                                                  int occurrence,
                                                  String activationId,
                                                  String source,
                                                  List<String> result) {
        if (selector.size() == 0) {
            result.add("MISSING_CONTAINER_SELECTOR");
            return;
        }
        if (!"ARRAY_INDEX".equals(string(selector, "kind"))) {
            result.add("WRONG_CONTAINER_SELECTOR_KIND");
        }
        if (string(selector, "bindingId").isEmpty()) {
            result.add("MISSING_CONTAINER_BINDING_ID");
        }
        if (string(selector, "containerInputPort").isEmpty()
                || string(selector, "containerInputCell").isEmpty()) {
            result.add("MISSING_CONTAINER_ENDPOINT");
        }
        if (!"EXACT_ARRAY_INDEX".equals(string(selector,
                "selectorAuthority"))) {
            result.add("NON_EXACT_CONTAINER_SELECTOR");
        }
        if (integer(selector, "elementIndex", -1) < 0) {
            result.add("INVALID_CONTAINER_ELEMENT_INDEX");
        }
        int elementOccurrence = integer(selector, "elementOccurrence", -1);
        if (elementOccurrence < 1 || elementOccurrence != occurrence) {
            result.add("CONTAINER_OCCURRENCE_MISMATCH");
        }
        if (string(selector, "declaredFieldOwnerClass").isEmpty()) {
            result.add("MISSING_DECLARED_FIELD_OWNER");
        }
        if (string(selector, "declaredFieldType").isEmpty()) {
            result.add("MISSING_DECLARED_FIELD_TYPE");
        }
        if (!CONTAINER_REPLAY_REBINDING_AUTHORITY.equals(string(
                assignment, "containerReplayRebindingAuthority"))) {
            result.add("INVALID_CONTAINER_REPLAY_REBINDING_AUTHORITY");
        }
        if (bool(assignment, "sourceContainerObjectTokensRetained", true)) {
            result.add("SOURCE_CONTAINER_OBJECT_TOKENS_RETAINED");
        }
        if ("PLANNED".equals(source)) {
            for (String runtimeMember : new String[]{
                    "resolvedFromSelectorAuthority",
                    "containerObjectToken", "elementObjectToken",
                    "objectTokenAuthority", "objectTokenScope",
                    "containerObservationLocation"}) {
                if (containsMember(assignment, runtimeMember)) {
                    result.add("PLANNED_CONTAINER_HAS_RUNTIME_MEMBER:"
                            + runtimeMember);
                }
            }
            for (String runtimeClaim : new String[]{"authority",
                    "complete"}) {
                if (selector.has(runtimeClaim)) {
                    result.add("PLANNED_CONTAINER_HAS_RUNTIME_MEMBER:"
                            + runtimeClaim);
                }
            }
            if (assignment.has("sameSourceContainerIdentityClaimed")
                    || assignment.has("currentContainerSelectorCaptured")) {
                result.add("PLANNED_CONTAINER_HAS_APPLIED_REBIND_WITNESS");
            }
            return;
        }
        if (longInteger(selector, "containerObjectToken", 0L) <= 0L
                || longInteger(selector, "elementObjectToken", 0L) <= 0L) {
            result.add("INVALID_CONTAINER_OBJECT_TOKEN");
        }
        String tokenScope = string(selector, "objectTokenScope");
        if (!"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))
                || activationId.isEmpty()
                || !activationId.equals(tokenScope)) {
            result.add("INVALID_CONTAINER_OBJECT_TOKEN_SCOPE");
        }
        if (!("EXACT_ARRAY_INDEX".equals(string(selector,
                "resolvedFromSelectorAuthority"))
                || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(string(selector,
                "resolvedFromSelectorAuthority")))) {
            result.add("INVALID_CONTAINER_RESOLUTION_AUTHORITY");
        }
        if (!"EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_LOCAL_"
                .concat("ELEMENT_IDENTITY").equals(string(selector,
                        "authority"))
                || !bool(selector, "complete", false)) {
            result.add("INCOMPLETE_CONTAINER_SELECTOR_AUTHORITY");
        }
        if (bool(assignment, "sameSourceContainerIdentityClaimed", true)) {
            result.add("APPLIED_CONTAINER_CLAIMS_SOURCE_IDENTITY");
        }
        if (!bool(assignment, "currentContainerSelectorCaptured", false)) {
            result.add("APPLIED_CURRENT_CONTAINER_SELECTOR_NOT_CAPTURED");
        }
    }

    private static void validateMapProjectionSelector(
            JsonObject selector, int occurrence, String activationId,
            List<String> result) {
        if (selector.size() == 0) {
            result.add("MISSING_MAP_PROJECTION_SELECTOR");
            return;
        }
        if (!"MAP_OUTPUT_ARRAY_INDEX".equals(string(selector, "kind"))) {
            result.add("WRONG_MAP_PROJECTION_SELECTOR_KIND");
        }
        if (string(selector, "bindingId").isEmpty()) {
            result.add("MISSING_MAP_PROJECTION_BINDING_ID");
        }
        if (string(selector, "mapInputPort").isEmpty()
                || string(selector, "mapInputCell").isEmpty()
                || string(selector, "outputPort").isEmpty()
                || string(selector, "outputCell").isEmpty()) {
            result.add("MISSING_MAP_PROJECTION_ENDPOINT");
        }
        String operation = string(selector, "mapProjectionOperation");
        if (!("MAP_VALUES_VIEW".equals(operation)
                || "MAP_KEY_SET_VIEW".equals(operation))) {
            result.add("UNSUPPORTED_MAP_PROJECTION_OPERATION");
        }
        int index = integer(selector, "outputIndex", -1);
        int elementOccurrence = integer(selector,
                "elementOccurrence", -1);
        if (index < 0 || elementOccurrence != index + 1
                || elementOccurrence != occurrence) {
            result.add("MAP_PROJECTION_INDEX_OCCURRENCE_MISMATCH");
        }
        if (string(selector, "declaredFieldOwnerClass").isEmpty()
                || string(selector, "declaredFieldType").isEmpty()
                || string(selector, "declaredFieldSignature").isEmpty()) {
            result.add("MISSING_MAP_PROJECTION_DECLARED_FIELD");
        }
        long mapToken = longInteger(selector, "mapObjectToken", 0L);
        long elementToken = longInteger(selector,
                "elementObjectToken", 0L);
        long outputToken = longInteger(selector,
                "outputArrayObjectToken", 0L);
        if (mapToken <= 0L || elementToken <= 0L || outputToken <= 0L) {
            result.add("INVALID_MAP_PROJECTION_OBJECT_TOKEN");
        }
        if (mapToken == elementToken || mapToken == outputToken
                || elementToken == outputToken) {
            result.add("NON_DISTINCT_MAP_PROJECTION_OBJECT_TOKEN");
        }
        String scope = string(selector, "objectTokenScope");
        if (!"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))
                || activationId.isEmpty() || !activationId.equals(scope)) {
            result.add("INVALID_MAP_PROJECTION_OBJECT_TOKEN_SCOPE");
        }
        if (!"NONE".equals(string(selector,
                "crossExecutionOrdinalAuthority"))) {
            result.add("INVALID_MAP_PROJECTION_CROSS_EXECUTION_AUTHORITY");
        }
        if (!"IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_EXACT_"
                .concat("OUTPUT_IDENTITY").equals(string(selector,
                        "authority"))) {
            result.add("INVALID_MAP_PROJECTION_SELECTOR_AUTHORITY");
        }
        if (!exactImmutableMapKey(selector.get("expectedMapKey"))
                || !"CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT"
                .equals(string(selector, "expectedMapKeyAuthority"))) {
            result.add("INVALID_MAP_PROJECTION_EXPECTED_KEY");
        }
        if (!"ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_POSITIONAL_"
                .concat("REFERENCE_EQUALITY").equals(string(selector,
                        "sourceOutputIndexAuthority"))
                || !"IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                .concat("EXACT_OUTPUT_IDENTITY").equals(string(selector,
                        "replaySelectionAuthority"))) {
            result.add("INVALID_MAP_PROJECTION_KEYED_REPLAY_AUTHORITY");
        }
        String outputAuthority = string(selector,
                "outputVerificationAuthority");
        boolean exactOutputAuthority =
                "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD".equals(
                        outputAuthority)
                || "ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                        outputAuthority)
                || "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                .equals(outputAuthority);
        if (!bool(selector, "outputIdentityVerified", false)
                || !exactOutputAuthority
                || !bool(selector, "complete", false)) {
            result.add("INCOMPLETE_MAP_PROJECTION_OUTPUT_IDENTITY");
        }
        boolean sourceScopePresent = selector.has("sourceObjectTokenScope")
                && !string(selector, "sourceObjectTokenScope").isEmpty();
        boolean rebindingPresent = selector.has(
                "replayScopeRebindingAuthority")
                && !string(selector,
                "replayScopeRebindingAuthority").isEmpty();
        if (!sourceScopePresent || !rebindingPresent
                || !"SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_"
                .concat("ACTIVATION_SCOPE_REBOUND_TOKENS_NOT_COMPARED_"
                        + "ACROSS_EXECUTIONS").equals(string(selector,
                        "replayScopeRebindingAuthority"))) {
            result.add("INVALID_MAP_PROJECTION_REPLAY_SCOPE_REBINDING");
        }
    }

    /** Shared admission boundary used by natural-propagation validation. */
    static List<String> validateDynamicAssignmentsForReplay(
            JsonArray plannedAssignments, JsonArray appliedAssignments,
            String activationId) {
        List<String> result = new ArrayList<>();
        DynamicAssignmentSet planned = DynamicAssignmentSet.from(
                plannedAssignments, "PLANNED", activationId);
        DynamicAssignmentSet applied = DynamicAssignmentSet.from(
                appliedAssignments, "APPLIED", activationId);
        result.addAll(planned.problems);
        result.addAll(applied.problems);
        Set<String> missing = new LinkedHashSet<>(planned.identities);
        missing.removeAll(applied.identities);
        Set<String> extra = new LinkedHashSet<>(applied.identities);
        extra.removeAll(planned.identities);
        if (!missing.isEmpty() || !extra.isEmpty()
                || planned.dynamicCount != applied.dynamicCount) {
            result.add("DYNAMIC_MODEL_ASSIGNMENT_SET_MISMATCH:missing="
                    + missing + ":extra=" + extra);
        }
        return result;
    }

    /**
     * Compares a projection-manifest model definition with one activation's
     * replay plan. Candidate replay rewrites activation-local map token scope;
     * normalize that authorized rebind back to sourceObjectTokenScope while
     * retaining solver symbol, value, type, authority, and every selector.
     */
    static List<String> validateProjectedAssignmentDefinitions(
            JsonArray manifestAssignments, JsonArray plannedAssignments) {
        List<String> result = new ArrayList<>();
        Set<String> manifest = assignmentDefinitionSet(
                manifestAssignments, "MANIFEST", result);
        Set<String> planned = assignmentDefinitionSet(
                plannedAssignments, "PLAN", result);
        Set<String> missing = new LinkedHashSet<>(manifest);
        missing.removeAll(planned);
        Set<String> extra = new LinkedHashSet<>(planned);
        extra.removeAll(manifest);
        if (manifestAssignments.size() != plannedAssignments.size()
                || !missing.isEmpty() || !extra.isEmpty()) {
            result.add("PROJECTED_MODEL_ASSIGNMENT_DEFINITION_MISMATCH:"
                    + "missing=" + missing + ":extra=" + extra);
        }
        return result;
    }

    private static Set<String> assignmentDefinitionSet(
            JsonArray assignments, String source, List<String> problems) {
        Set<String> result = new LinkedHashSet<>();
        for (int index = 0; index < assignments.size(); index++) {
            JsonElement element = assignments.get(index);
            if (!element.isJsonObject()) {
                problems.add(source + "_" + index
                        + ":NON_OBJECT_MODEL_ASSIGNMENT");
                continue;
            }
            JsonObject assignment = element.getAsJsonObject();
            for (String problem : validateModelAssignment(assignment,
                    "PLANNED")) {
                problems.add(source + "_" + index + ":" + problem);
            }
            String identity = modelDefinitionIdentity(assignment);
            if (!result.add(identity)) {
                problems.add(source + "_" + index
                        + ":DUPLICATE_MODEL_ASSIGNMENT_DEFINITION");
            }
        }
        return result;
    }

    private static String modelDefinitionIdentity(JsonObject assignment) {
        JsonObject normalized = assignment.deepCopy();
        JsonObject selector = object(normalized,
                "mapProjectionSelector");
        if (selector.size() > 0) {
            String sourceScope = string(selector,
                    "sourceObjectTokenScope");
            if (!sourceScope.isEmpty()) {
                selector.addProperty("objectTokenScope", sourceScope);
            }
            selector.remove("sourceObjectTokenScope");
            selector.remove("replayScopeRebindingAuthority");
        }
        StringBuilder result = new StringBuilder();
        identityComponent(result, string(normalized, "solverSymbol"));
        identityComponent(result, assignmentIdentity(normalized));
        return result.toString();
    }

    private static boolean exactImmutableMapKey(JsonElement element) {
        if (element == null || !element.isJsonObject()) return false;
        JsonObject expression = element.getAsJsonObject();
        if (!"ConstExpr".equals(string(expression, "_type"))) return false;
        String encoded = string(expression, "_exp");
        if (!encoded.startsWith("Y_") || encoded.length() < 4
                || encoded.charAt(3) != '_') return false;
        char kind = encoded.charAt(2);
        if (kind != immutableKeyKind(string(expression, "_java_type"))) {
            return false;
        }
        String payload = encoded.substring(4);
        try {
            java.math.BigInteger integer;
            switch (kind) {
                case 'Z':
                    return "0".equals(payload) || "1".equals(payload);
                case 'B':
                    integer = new java.math.BigInteger(payload);
                    return integer.toString().equals(payload)
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Byte.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Byte.MAX_VALUE)) <= 0;
                case 'C':
                    integer = new java.math.BigInteger(payload);
                    return integer.toString().equals(payload)
                            && integer.signum() >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Character.MAX_VALUE)) <= 0;
                case 'S':
                    integer = new java.math.BigInteger(payload);
                    return integer.toString().equals(payload)
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Short.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Short.MAX_VALUE)) <= 0;
                case 'I':
                    integer = new java.math.BigInteger(payload);
                    return integer.toString().equals(payload)
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Integer.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Integer.MAX_VALUE)) <= 0;
                case 'J':
                    integer = new java.math.BigInteger(payload);
                    return integer.toString().equals(payload)
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Long.MIN_VALUE)) >= 0
                            && integer.compareTo(java.math.BigInteger.valueOf(
                            Long.MAX_VALUE)) <= 0;
                case 'L':
                    return true;
                default:
                    return false;
            }
        } catch (RuntimeException malformed) {
            return false;
        }
    }

    private static char immutableKeyKind(String javaType) {
        String value = javaType == null ? ""
                : javaType.replace('.', '/');
        if ("java/lang/Boolean".equals(value)) return 'Z';
        if ("java/lang/Byte".equals(value)) return 'B';
        if ("java/lang/Character".equals(value)) return 'C';
        if ("java/lang/Short".equals(value)) return 'S';
        if ("java/lang/Integer".equals(value)) return 'I';
        if ("java/lang/Long".equals(value)) return 'J';
        if ("java/lang/String".equals(value)) return 'L';
        return 0;
    }

    private static String stableImmutableMapKeySelector(
            JsonElement element) {
        if (!exactImmutableMapKey(element)) return "";
        String raw = string(element.getAsJsonObject(), "_exp");
        String value = raw.substring(4);
        return raw.charAt(2) + ":" + value.length() + ":" + value;
    }

    private static String assignmentIdentity(JsonObject assignment) {
        StringBuilder value = new StringBuilder();
        boolean dynamic = !string(assignment,
                "dynamicBindingId").isEmpty();
        identityComponent(value, dynamic ? "DYNAMIC" : "DIRECT");
        identityComponent(value, string(assignment, "engineSymbol"));
        identityComponent(value, string(assignment, "inputSymbol"));
        identityComponent(value, string(assignment, "baseInputSymbol"));
        identityComponent(value, string(assignment, "valueType"));
        identityComponent(value, string(assignment, "value"));
        identityComponent(value, string(assignment, "authority"));
        identityComponent(value, string(assignment, "modelOperation"));
        identityComponent(value, canonical(array(assignment,
                "materializationPath")));
        identityComponent(value, string(assignment, "dynamicBindingId"));
        identityComponent(value, string(assignment, "dynamicFieldSymbol"));
        identityComponent(value, string(assignment,
                "materializationSiteId"));
        identityComponent(value, String.valueOf(integer(assignment,
                "materializationOccurrence", -1)));
        JsonObject container = object(assignment, "containerSelector");
        JsonObject mapProjection = object(assignment,
                "mapProjectionSelector");
        if (mapProjection.size() > 0) {
            identityComponent(value, "MAP_OUTPUT_ARRAY_INDEX");
            identityComponent(value, canonical(mapProjection));
        } else if (container.size() > 0) {
            identityComponent(value, "ARRAY_INDEX");
            // Runtime object tokens and their scope are replay-local.  The
            // stable selector is the cross-execution identity; a separate
            // join validates the applied selector against the fresh raw
            // binding before admission.
            identityComponent(value, canonical(stableContainerSelector(
                    container)));
            identityComponent(value, string(assignment,
                    "containerReplayRebindingAuthority"));
        } else {
            if (freshMapEntryRebinding(assignment)) {
                // Planned and applied rows intentionally differ in their key:
                // only the applied row may contain the selector captured in
                // the replay JVM.  Static base/site/occurrence identity above
                // plus this explicit authority is the comparison key; a
                // separate raw-binding join validates the fresh selector.
                identityComponent(value, "MAP_ENTRY_FRESH_REBIND");
                identityComponent(value,
                        FRESH_MAP_ENTRY_REBINDING_AUTHORITY);
            } else {
                identityComponent(value, "MAP_ENTRY_KEY");
                identityComponent(value, canonical(selectorKey(assignment)));
                identityComponent(value, selectorAuthority(assignment));
            }
        }
        return value.toString();
    }

    private static Set<String> dynamicOnly(Set<String> identities) {
        Set<String> result = new LinkedHashSet<>();
        for (String identity : identities) {
            // assignmentIdentity's first length-prefixed component is either
            // DYNAMIC or DIRECT.
            if (identity.startsWith("7:DYNAMIC|")) result.add(identity);
        }
        return result;
    }

    private static JsonElement selectorKey(JsonObject assignment) {
        JsonElement expected = assignment.get("expectedEntryKey");
        return expected != null ? expected : assignment.get("keyExpression");
    }

    private static String selectorAuthority(JsonObject assignment) {
        return firstNonBlank(string(assignment,
                "expectedEntryKeyAuthority"), string(assignment,
                "keyExpressionAuthority"));
    }

    private static boolean exactEngineSymbol(String engine,
                                             String dynamic) {
        if (engine == null || dynamic == null || dynamic.isEmpty()) {
            return false;
        }
        if (engine.equals(dynamic)) return true;
        if (engine.length() <= 10 || engine.charAt(0) != 'M'
                || engine.charAt(1) != '_'
                || "ZCBSIFJDL".indexOf(engine.charAt(2)) < 0
                || !engine.startsWith("_field_", 3)) {
            return false;
        }
        String payload = engine.substring(10);
        if (payload.equals(dynamic)) return true;
        String boundary = dynamic + "_";
        return payload.startsWith(boundary)
                && legalVmOwnerSuffix(payload.substring(boundary.length()));
    }

    private static boolean legalVmOwnerSuffix(String suffix) {
        return suffix != null && suffix.matches(
                "[A-Za-z_$][A-Za-z0-9_$]*"
                        + "(?:/[A-Za-z_$][A-Za-z0-9_$]*)*");
    }

    private static void identityComponent(StringBuilder result,
                                          String value) {
        String safe = value == null ? "" : value;
        result.append(safe.length()).append(':').append(safe).append('|');
    }

    private static String canonical(JsonElement value) {
        if (value == null || value.isJsonNull()) return "null";
        if (value.isJsonPrimitive()) {
            JsonPrimitive primitive = value.getAsJsonPrimitive();
            return GSON.toJson(primitive);
        }
        if (value.isJsonArray()) {
            StringBuilder result = new StringBuilder("[");
            boolean first = true;
            for (JsonElement element : value.getAsJsonArray()) {
                if (!first) result.append(',');
                first = false;
                result.append(canonical(element));
            }
            return result.append(']').toString();
        }
        JsonObject object = value.getAsJsonObject();
        StringBuilder result = new StringBuilder("{");
        boolean first = true;
        for (String key : new TreeSet<>(object.keySet())) {
            if (!first) result.append(',');
            first = false;
            result.append(GSON.toJson(key)).append(':')
                    .append(canonical(object.get(key)));
        }
        return result.append('}').toString();
    }

    private static boolean observed(JsonArray mappings, JsonObject expected,
                                    boolean outcome) {
        String site = string(expected, "siteId");
        int occurrence = integer(expected, "occurrence", 1);
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (site.equals(string(mapping, "siteId"))
                    && occurrence == integer(mapping, "occurrence", 1)
                    && outcome == bool(mapping, "observedOutcome",
                    bool(mapping, "outcome", false))
                    && !bool(mapping, "overrideApplied", false)) return true;
        }
        return false;
    }

    private static boolean hasOverride(JsonArray mappings) {
        for (JsonElement element : mappings) {
            if (element.isJsonObject() && bool(element.getAsJsonObject(),
                    "overrideApplied", false)) return true;
        }
        return false;
    }

    private static void require(JsonArray failures, String code,
                                boolean condition) {
        if (!condition) failures.add(code);
    }

    private static String identity(JsonObject branch) {
        return string(branch, "siteId") + "#"
                + integer(branch, "occurrence", 1);
    }

    private static boolean containsPrefixFailure(JsonArray failures) {
        return contains(failures, "PREFIX_MISMATCH");
    }

    private static boolean contains(JsonArray failures, String prefix) {
        for (JsonElement failure : failures) {
            if (failure.isJsonPrimitive()
                    && failure.getAsString().startsWith(prefix)) return true;
        }
        return false;
    }

    private static boolean containsOutputClosureFailure(JsonArray failures) {
        for (JsonElement failure : failures) {
            if (!failure.isJsonPrimitive()) continue;
            String code = failure.getAsString();
            if (isOutputClosureFailure(code)) return true;
        }
        return false;
    }

    private static int countOutputClosureFailures(JsonArray failures) {
        int result = 0;
        for (JsonElement failure : failures) {
            if (failure.isJsonPrimitive()
                    && isOutputClosureFailure(failure.getAsString())) {
                result++;
            }
        }
        return result;
    }

    private static String firstOutputClosureFailure(JsonArray failures) {
        for (JsonElement failure : failures) {
            if (!failure.isJsonPrimitive()) continue;
            String code = failure.getAsString();
            if (isOutputClosureFailure(code)) return code;
        }
        return "OUTPUT_CLOSURE_REPLAY_NOT_IMPORTABLE";
    }

    private static boolean isOutputClosureFailure(String code) {
        return code != null && (code.startsWith("OUTPUT_CLOSURE_")
                || code.startsWith("MISSING_IMPORTED_OUTPUT_SUMMARY")
                || code.startsWith("IMPORTED_OUTPUT_SUMMARY_")
                || code.startsWith("REQUESTED_OUTPUT_")
                || code.startsWith("OUTPUT_EXPRESSION_ADMISSION_"));
    }

    private static boolean exactRequestedOutput(JsonObject task,
                                                JsonObject summary) {
        JsonObject expected = object(task, "requestedOutput");
        JsonObject imported = object(summary, "requestedOutput");
        if (expected.size() == 0 || imported.size() == 0) return false;
        return canonical(expected).equals(canonical(imported));
    }

    private static boolean exactRequestedOutputExpression(
            JsonObject task, JsonObject summary) {
        JsonObject requested = object(task, "requestedOutput");
        JsonObject expressions = object(summary, "outputExpressions");
        Set<String> identities = new LinkedHashSet<>();
        addNonBlank(identities, string(requested, "portId"));
        addNonBlank(identities, string(requested, "symbol"));
        addNonBlank(identities, string(requested, "cell"));
        for (String identity : identities) {
            JsonElement expression = expressions.get(identity);
            if (usableExpression(expression)) return true;
        }
        return false;
    }

    private static boolean outputExpressionAdmissionComplete(
            JsonObject summary) {
        JsonElement admission = summary == null ? null
                : summary.get("outputExpressionAdmission");
        // Older importer artifacts predate this diagnostic object.  Exact
        // requested-output identity, a usable expression, and the summary's
        // relationallyComplete bit are their admission evidence.
        return admission == null || admission.isJsonNull()
                || admission.isJsonObject()
                && bool(admission.getAsJsonObject(), "complete", false);
    }

    private static boolean usableExpression(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonObject()) {
            return expression.getAsJsonObject().size() > 0;
        }
        if (expression.isJsonArray()) {
            return expression.getAsJsonArray().size() > 0;
        }
        return true;
    }

    private static void addNonBlank(Set<String> values, String value) {
        if (value != null && !value.trim().isEmpty()) {
            values.add(value.trim());
        }
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject owner, String field,
                                boolean fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject owner, String field,
                               int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject owner, String field,
                                    long fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }
}
