package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Proves the two joins whose identities are created by the replay JVM.
 *
 * <p>The importer owns generic model-assignment, branch, output-closure and
 * dynamic-binding schema admission. This class only joins a planned static
 * selector to one applied selector and then to one activation-local runtime
 * binding.</p>
 */
public final class ConcolicReplayValidator {
    private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
            "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                    + "FRESH_ENTRY_REBIND_V1";
    private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
            "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                    + "IDENTITY_REBIND_V1";

    private ConcolicReplayValidator() {
    }

    static List<String> validateDynamicRebindings(
            JsonObject task, JsonObject rawResult,
            JsonObject importedSummary) {
        JsonArray planned = array(task, "modelAssignments");
        JsonArray applied = array(rawResult, "modelAssignmentsApplied");
        JsonArray rawBindings = array(rawResult, "dynamicFieldBindings");
        String activationId = string(rawResult, "activationId");
        boolean imported = importedSummary != null;
        List<String> failures = new ArrayList<>();

        if (dynamicCount(planned) != dynamicCount(applied)) {
            failures.add("DYNAMIC_MODEL_ASSIGNMENT_COUNT_MISMATCH");
        }
        addFailures(failures, "FRESH_MAP_ENTRY_REBINDING_INVALID:",
                validateFreshMapEntryRebindings(planned, applied,
                        rawBindings, imported
                                ? importedFreshEntryBindings(importedSummary)
                                : new JsonArray(), imported));
        addFailures(failures, "CONTAINER_REPLAY_REBINDING_INVALID:",
                validateContainerRebindings(planned, applied, rawBindings,
                        imported ? array(importedSummary,
                                "dynamicFieldBindings") : new JsonArray(),
                        imported, activationId));
        return failures;
    }

    private static void addFailures(List<String> target, String prefix,
                                    List<String> failures) {
        for (String failure : failures) target.add(prefix + failure);
    }

    private static int dynamicCount(JsonArray assignments) {
        int count = 0;
        for (JsonElement element : assignments) {
            if (element.isJsonObject() && !string(
                    element.getAsJsonObject(), "dynamicBindingId").isEmpty()) {
                count++;
            }
        }
        return count;
    }

    private static boolean freshMapEntry(JsonObject assignment) {
        return FRESH_MAP_ENTRY_REBINDING_AUTHORITY.equals(string(assignment,
                "dynamicReplayRebindingAuthority"));
    }

    private static boolean container(JsonObject assignment) {
        return CONTAINER_REPLAY_REBINDING_AUTHORITY.equals(string(assignment,
                "containerReplayRebindingAuthority"));
    }

    private static int count(JsonArray assignments, boolean fresh) {
        int count = 0;
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if (fresh ? freshMapEntry(assignment) : container(assignment)) {
                count++;
            }
        }
        return count;
    }

    /**
     * A fresh Map.Entry has no cross-execution key identity. The plan carries
     * only its static field site; the applied row supplies the key captured by
     * this replay activation.
     */
    private static List<String> validateFreshMapEntryRebindings(
            JsonArray planned, JsonArray applied, JsonArray rawBindings,
            JsonArray importedBindings, boolean imported) {
        List<String> failures = new ArrayList<>();
        if (count(planned, true) != count(applied, true)) {
            failures.add("PLANNED_APPLIED_REBIND_COUNT_MISMATCH");
        }
        for (int index = 0; index < planned.size(); index++) {
            JsonElement element = planned.get(index);
            if (!element.isJsonObject()
                    || !freshMapEntry(element.getAsJsonObject())) {
                continue;
            }
            JsonObject plan = element.getAsJsonObject();
            if (bool(plan, "sourceEntrySelectorRetained", true)
                    || plan.has("expectedEntryKey")
                    || plan.has("expectedEntryKeyAuthority")
                    || plan.has("entryReadObservationId")
                    || plan.has("keyExpression")
                    || plan.has("keyExpressionAuthority")) {
                failures.add("PLAN_" + index
                        + "_CONTAINS_SEED_ENTRY_SELECTOR");
                continue;
            }
            List<JsonObject> appliedMatches =
                    freshAssignments(applied, plan);
            if (appliedMatches.size() != 1) {
                failures.add(matchFailure(index, appliedMatches,
                        "APPLIED_REBIND"));
                continue;
            }
            JsonObject appliedRow = appliedMatches.get(0);
            String witnessProblem = freshAppliedProblem(appliedRow);
            if (!witnessProblem.isEmpty()) {
                failures.add("PLAN_" + index + "_" + witnessProblem);
                continue;
            }
            List<JsonObject> rawMatches = freshBindings(rawBindings,
                    appliedRow, true);
            if (rawMatches.size() != 1) {
                failures.add(matchFailure(index, rawMatches,
                        "FRESH_RAW_BINDING"));
                continue;
            }
            if (imported) {
                List<JsonObject> importedMatches = freshBindings(
                        importedBindings, appliedRow, false);
                if (importedMatches.size() != 1) {
                    failures.add(matchFailure(index, importedMatches,
                            "FRESH_IMPORTED_BINDING"));
                }
            }
        }
        return failures;
    }

    private static String freshAppliedProblem(JsonObject assignment) {
        if (bool(assignment, "sourceEntrySelectorRetained", true)
                || assignment.has("expectedEntryKey")
                || assignment.has("expectedEntryKeyAuthority")
                || bool(assignment, "sameSeedEntryClaimed", true)) {
            return "APPLIED_FRESH_REBIND_CARRIES_SEED_IDENTITY";
        }
        JsonElement key = assignment.get("keyExpression");
        if (key == null || !key.isJsonObject()
                || string(assignment, "entryReadObservationId").isEmpty()
                || string(assignment, "keyExpressionAuthority").isEmpty()
                || !bool(assignment, "freshEntrySelectorCaptured", false)) {
            return "APPLIED_FRESH_ENTRY_SELECTOR_INCOMPLETE";
        }
        return "";
    }

    private static List<JsonObject> freshAssignments(
            JsonArray assignments, JsonObject plan) {
        List<JsonObject> matches = new ArrayList<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (freshMapEntry(candidate)
                    && sameAssignmentSite(candidate, plan)) {
                matches.add(candidate);
            }
        }
        return matches;
    }

    private static List<JsonObject> freshBindings(
            JsonArray bindings, JsonObject applied, boolean raw) {
        List<JsonObject> matches = new ArrayList<>();
        String authority = raw
                ? "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                + "FIELD_SITE_OCCURRENCE"
                : "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                + "ENTRY_VALUE_TOKEN_JOIN";
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            JsonElement expectedKey = applied.get("keyExpression");
            if ("DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(string(binding,
                    "kind"))
                    && authority.equals(string(binding, "authority"))
                    && (!raw || bool(binding, "complete", false))
                    && sameBindingSite(binding, applied)
                    && same(binding, applied, "entryReadObservationId")
                    && same(binding, applied, "keyExpressionAuthority")
                    && expectedKey != null
                    && expectedKey.equals(binding.get("keyExpression"))) {
                matches.add(binding);
            }
        }
        return matches;
    }

    /**
     * Imported fresh-entry bindings are eligible only under the complete
     * MAP_ENTRY_READ observation that certified their replay-local key join.
     */
    private static JsonArray importedFreshEntryBindings(JsonObject summary) {
        JsonArray bindings = new JsonArray();
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
                if (bindingElement.isJsonObject()
                        && observationId.equals(string(
                        bindingElement.getAsJsonObject(),
                        "entryReadObservationId"))) {
                    bindings.add(bindingElement);
                }
            }
        }
        return bindings;
    }

    /**
     * A container plan crosses executions by stable array selector only.
     * Object tokens must be newly supplied by the replay activation.
     */
    private static List<String> validateContainerRebindings(
            JsonArray planned, JsonArray applied, JsonArray rawBindings,
            JsonArray importedBindings, boolean imported,
            String activationId) {
        List<String> failures = new ArrayList<>();
        if (count(planned, false) != count(applied, false)) {
            failures.add("PLANNED_APPLIED_REBIND_COUNT_MISMATCH");
        }
        for (int index = 0; index < planned.size(); index++) {
            JsonElement element = planned.get(index);
            if (!element.isJsonObject()
                    || !container(element.getAsJsonObject())) {
                continue;
            }
            JsonObject plan = element.getAsJsonObject();
            if (containerPlanCarriesRuntimeIdentity(plan)) {
                failures.add("PLAN_" + index
                        + "_CONTAINS_RUNTIME_CONTAINER_IDENTITY");
                continue;
            }
            List<JsonObject> appliedMatches =
                    containerAssignments(applied, plan);
            if (appliedMatches.size() != 1) {
                failures.add(matchFailure(index, appliedMatches,
                        "APPLIED_REBIND"));
                continue;
            }
            JsonObject appliedRow = appliedMatches.get(0);
            String witnessProblem = containerAppliedProblem(appliedRow,
                    activationId);
            if (!witnessProblem.isEmpty()) {
                failures.add("PLAN_" + index + "_" + witnessProblem);
                continue;
            }
            List<JsonObject> rawMatches = containerBindings(rawBindings,
                    appliedRow, activationId);
            if (rawMatches.size() != 1) {
                failures.add(matchFailure(index, rawMatches,
                        "FRESH_RAW_CONTAINER_BINDING"));
                continue;
            }
            if (imported) {
                List<JsonObject> importedMatches = containerBindings(
                        importedBindings, appliedRow, activationId);
                if (importedMatches.size() != 1) {
                    failures.add(matchFailure(index, importedMatches,
                            "FRESH_IMPORTED_CONTAINER_BINDING"));
                }
            }
        }
        return failures;
    }

    private static boolean containerPlanCarriesRuntimeIdentity(
            JsonObject plan) {
        if (bool(plan, "sourceContainerObjectTokensRetained", true)
                || plan.has("sameSourceContainerIdentityClaimed")
                || plan.has("currentContainerSelectorCaptured")) {
            return true;
        }
        JsonObject selector = object(plan, "containerSelector");
        for (String member : new String[]{"resolvedFromSelectorAuthority",
                "containerObjectToken", "elementObjectToken",
                "objectTokenAuthority", "objectTokenScope",
                "containerObservationLocation", "authority", "complete"}) {
            if (selector.has(member)) return true;
        }
        return false;
    }

    private static String containerAppliedProblem(
            JsonObject assignment, String activationId) {
        JsonObject selector = object(assignment, "containerSelector");
        if (longInteger(selector, "containerObjectToken", 0L) <= 0L
                || longInteger(selector, "elementObjectToken", 0L) <= 0L) {
            return "INVALID_CONTAINER_OBJECT_TOKEN";
        }
        if (activationId.isEmpty()
                || !activationId.equals(string(selector,
                "objectTokenScope"))
                || !"ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                string(selector, "objectTokenAuthority"))) {
            return "INVALID_CONTAINER_OBJECT_TOKEN_SCOPE";
        }
        String resolution = string(selector,
                "resolvedFromSelectorAuthority");
        if (!("EXACT_ARRAY_INDEX".equals(resolution)
                || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(resolution))) {
            return "INVALID_CONTAINER_RESOLUTION_AUTHORITY";
        }
        if (!"EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_LOCAL_"
                .concat("ELEMENT_IDENTITY").equals(string(selector,
                        "authority"))
                || !bool(selector, "complete", false)
                || bool(assignment,
                "sameSourceContainerIdentityClaimed", true)
                || !bool(assignment,
                "currentContainerSelectorCaptured", false)) {
            return "INCOMPLETE_CONTAINER_SELECTOR_AUTHORITY";
        }
        return "";
    }

    private static List<JsonObject> containerAssignments(
            JsonArray assignments, JsonObject plan) {
        List<JsonObject> matches = new ArrayList<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (container(candidate)
                    && sameAssignmentSite(candidate, plan)
                    && same(candidate, plan, "valueType")
                    && same(candidate, plan, "value")
                    && same(candidate, plan, "authority")
                    && sameStableContainerSelector(object(candidate,
                    "containerSelector"), object(plan,
                    "containerSelector"))) {
                matches.add(candidate);
            }
        }
        return matches;
    }

    private static boolean sameStableContainerSelector(
            JsonObject left, JsonObject right) {
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

    private static List<JsonObject> containerBindings(
            JsonArray bindings, JsonObject applied,
            String activationId) {
        List<JsonObject> matches = new ArrayList<>();
        JsonObject expectedSelector = object(applied,
                "containerSelector");
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            JsonObject selector = object(binding, "containerSelector");
            String scope = string(selector, "objectTokenScope");
            if (integer(binding, "schemaVersion", -1) == 3
                    && "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                    string(binding, "kind"))
                    && "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                    .concat("IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE")
                    .equals(string(binding, "authority"))
                    && bool(binding, "complete", false)
                    && sameBindingSite(binding, applied)
                    && selector.equals(expectedSelector)
                    && !activationId.isEmpty()
                    && activationId.equals(scope)
                    && scope.equals(string(binding, "objectTokenScope"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN"
                    .equals(string(binding, "objectTokenAuthority"))
                    && longInteger(selector,
                    "elementObjectToken", 0L) > 0L) {
                matches.add(binding);
            }
        }
        return matches;
    }

    private static boolean sameAssignmentSite(
            JsonObject left, JsonObject right) {
        return same(left, right, "engineSymbol")
                && same(left, right, "inputSymbol")
                && sameBindingSite(left, right);
    }

    private static boolean sameBindingSite(
            JsonObject left, JsonObject right) {
        return same(left, right, "baseInputSymbol")
                && same(left, right, "dynamicBindingId")
                && same(left, right, "dynamicFieldSymbol")
                && same(left, right, "materializationSiteId")
                && integer(left, "materializationOccurrence", -1)
                == integer(right, "materializationOccurrence", -2)
                && array(left, pathField(left)).equals(array(right,
                pathField(right)));
    }

    private static String pathField(JsonObject value) {
        return value.has("fieldPath") ? "fieldPath"
                : "materializationPath";
    }

    private static boolean same(JsonObject left, JsonObject right,
                                String member) {
        return string(left, member).equals(string(right, member));
    }

    private static String matchFailure(
            int index, List<JsonObject> matches, String subject) {
        return "PLAN_" + index + (matches.isEmpty()
                ? "_NO_EXACT_" : "_AMBIGUOUS_") + subject;
    }
}
