package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Admits replay-local selectors after generic model-assignment admission has
 * already joined the plan to the applied rows.
 *
 * <p>A dynamic binding id is the only row identity across this boundary.
 * Fresh Map.Entry keys and container object tokens are execution-local and
 * therefore remain explicit evidence, never cross-execution identities.</p>
 */
public final class ConcolicReplayValidator {
    private static final String FRESH_MAP_ENTRY_REBINDING_AUTHORITY =
            "EXACT_BASE_PORT_GETTER_SITE_OCCURRENCE_THEN_"
                    + "FRESH_ENTRY_REBIND_V1";
    private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
            "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                    + "IDENTITY_REBIND_V1";
    private static final String TOKEN_AUTHORITY =
            "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN";

    private ConcolicReplayValidator() {
    }

    static List<String> validateDynamicRebindings(
            JsonObject rawResult, JsonObject importedSummary) {
        JsonArray applied = array(rawResult, "modelAssignmentsApplied");
        JsonArray rawBindings = array(rawResult, "dynamicFieldBindings");
        String activationId = string(rawResult, "activationId");
        Set<String> admitted = new LinkedHashSet<>();
        List<String> failures = new ArrayList<>();

        for (int index = 0; index < applied.size(); index++) {
            if (!applied.get(index).isJsonObject()) continue;
            JsonObject assignment = applied.get(index).getAsJsonObject();
            boolean freshEntry = freshMapEntry(assignment);
            boolean container = container(assignment);
            if (!freshEntry && !container) continue;

            String bindingId = string(assignment, "dynamicBindingId");
            String prefix = (freshEntry ? "FRESH_MAP_ENTRY_" : "CONTAINER_")
                    + "REBINDING_INVALID:APPLIED_" + index + "_";
            if (bindingId.isEmpty() || !admitted.add(bindingId)) {
                failures.add(prefix + "DYNAMIC_BINDING_ID_NOT_UNIQUE");
                continue;
            }
            String assignmentIssue = freshEntry
                    ? freshAssignmentIssue(assignment)
                    : containerAssignmentIssue(assignment, activationId);
            if (!assignmentIssue.isEmpty()) {
                failures.add(prefix + assignmentIssue);
                continue;
            }

            JsonObject rawBinding = uniqueBinding(rawBindings, bindingId);
            String rawIssue = bindingIssue(rawBinding, assignment,
                    activationId, freshEntry, true);
            if (!rawIssue.isEmpty()) {
                failures.add(prefix + "RAW_" + rawIssue);
                continue;
            }

            JsonArray importedBindings = freshEntry
                    ? importedFreshEntryBindings(importedSummary)
                    : array(importedSummary, "dynamicFieldBindings");
            JsonObject importedBinding = uniqueBinding(importedBindings,
                    bindingId);
            String importedIssue = bindingIssue(importedBinding, assignment,
                    activationId, freshEntry, false);
            if (!importedIssue.isEmpty()) {
                failures.add(prefix + "IMPORTED_" + importedIssue);
            }
        }
        return failures;
    }

    private static boolean freshMapEntry(JsonObject assignment) {
        return FRESH_MAP_ENTRY_REBINDING_AUTHORITY.equals(string(assignment,
                "dynamicReplayRebindingAuthority"));
    }

    private static boolean container(JsonObject assignment) {
        return CONTAINER_REPLAY_REBINDING_AUTHORITY.equals(string(assignment,
                "containerReplayRebindingAuthority"));
    }

    private static String freshAssignmentIssue(JsonObject assignment) {
        JsonElement key = assignment.get("keyExpression");
        if (bool(assignment, "sourceEntrySelectorRetained", true)
                || bool(assignment, "sameSeedEntryClaimed", true)
                || assignment.has("expectedEntryKey")
                || assignment.has("expectedEntryKeyAuthority")) {
            return "CARRIES_SEED_ENTRY_IDENTITY";
        }
        return key == null || !key.isJsonObject()
                || string(assignment, "entryReadObservationId").isEmpty()
                || string(assignment, "keyExpressionAuthority").isEmpty()
                || !bool(assignment, "freshEntrySelectorCaptured", false)
                ? "FRESH_ENTRY_SELECTOR_INCOMPLETE" : "";
    }

    private static String containerAssignmentIssue(
            JsonObject assignment, String activationId) {
        JsonObject selector = object(assignment, "containerSelector");
        if (longInteger(selector, "containerObjectToken", 0L) <= 0L
                || longInteger(selector, "elementObjectToken", 0L) <= 0L) {
            return "INVALID_CONTAINER_OBJECT_TOKEN";
        }
        if (activationId.isEmpty()
                || !activationId.equals(string(selector, "objectTokenScope"))
                || !TOKEN_AUTHORITY.equals(string(selector,
                "objectTokenAuthority"))) {
            return "INVALID_CONTAINER_OBJECT_TOKEN_SCOPE";
        }
        String resolution = string(selector,
                "resolvedFromSelectorAuthority");
        if (!"EXACT_ARRAY_INDEX".equals(resolution)
                && !"DISCOVER_UNIQUE_IDENTITY_INDEX".equals(resolution)) {
            return "INVALID_CONTAINER_RESOLUTION_AUTHORITY";
        }
        return !"EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_ACTIVATION_LOCAL_"
                .concat("ELEMENT_IDENTITY").equals(string(selector,
                        "authority"))
                || !bool(selector, "complete", false)
                || bool(assignment, "sameSourceContainerIdentityClaimed",
                true)
                || !bool(assignment, "currentContainerSelectorCaptured",
                false)
                ? "INCOMPLETE_CONTAINER_SELECTOR_AUTHORITY" : "";
    }

    private static String bindingIssue(
            JsonObject binding, JsonObject assignment, String activationId,
            boolean freshEntry, boolean raw) {
        if (binding == null) return "BINDING_NOT_UNIQUE";
        if (freshEntry) {
            String authority = raw
                    ? "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                    + "FIELD_SITE_OCCURRENCE"
                    : "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                    + "ENTRY_VALUE_TOKEN_JOIN";
            JsonElement key = assignment.get("keyExpression");
            return !"DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(
                    string(binding, "kind"))
                    || !authority.equals(string(binding, "authority"))
                    || raw && !bool(binding, "complete", false)
                    || !same(binding, assignment, "entryReadObservationId")
                    || !same(binding, assignment, "keyExpressionAuthority")
                    || key == null
                    || !key.equals(binding.get("keyExpression"))
                    ? "FRESH_ENTRY_EVIDENCE_MISMATCH" : "";
        }

        JsonObject expected = object(assignment, "containerSelector");
        JsonObject selector = object(binding, "containerSelector");
        String scope = string(selector, "objectTokenScope");
        return integer(binding, "schemaVersion", -1) != 3
                || !"DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                string(binding, "kind"))
                || !"ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_"
                .concat("AND_STABLE_FIELD_SITE_OCCURRENCE").equals(
                        string(binding, "authority"))
                || !bool(binding, "complete", false)
                || !selector.equals(expected)
                || activationId.isEmpty() || !activationId.equals(scope)
                || !scope.equals(string(binding, "objectTokenScope"))
                || !TOKEN_AUTHORITY.equals(string(binding,
                "objectTokenAuthority"))
                ? "CONTAINER_SELECTOR_EVIDENCE_MISMATCH" : "";
    }

    private static JsonObject uniqueBinding(JsonArray bindings,
                                            String bindingId) {
        JsonObject match = null;
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (!bindingId.equals(string(candidate, "dynamicBindingId"))) {
                continue;
            }
            if (match != null) return null;
            match = candidate;
        }
        return match;
    }

    private static JsonArray importedFreshEntryBindings(JsonObject summary) {
        JsonArray bindings = new JsonArray();
        for (JsonElement element : array(summary, "heapObservations")) {
            if (!element.isJsonObject()) continue;
            JsonObject observation = element.getAsJsonObject();
            String id = string(observation, "observationId");
            if (!"MAP_ENTRY_READ".equals(string(observation, "kind"))
                    || id.isEmpty() || !bool(observation, "complete", false)) {
                continue;
            }
            for (JsonElement candidate : array(observation,
                    "entryFieldBindings")) {
                if (candidate.isJsonObject() && id.equals(string(
                        candidate.getAsJsonObject(),
                        "entryReadObservationId"))) {
                    bindings.add(candidate);
                }
            }
        }
        return bindings;
    }

    private static boolean same(JsonObject left, JsonObject right,
                                String field) {
        return string(left, field).equals(string(right, field));
    }
}
