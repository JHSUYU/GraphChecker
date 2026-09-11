package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Builds one executable task for a solver-selected path replay. */
final class PathReplayTaskFactory {
    private PathReplayTaskFactory() {
    }

    private static JsonObject create(JsonObject task, JsonObject source,
                                     JsonArray assignments,
                                     JsonArray guardedReads,
                                     BranchReplayContract contract) {
        ClosureGoalKind goalKind = ClosureGoalKind.fromTask(task);
        String queryKey = string(task, "queryKey");
        if (queryKey.isEmpty()) {
            throw new IllegalArgumentException("path queryKey is required");
        }

        JsonObject result = source.deepCopy();
        result.remove("solverPathContext");
        if (!string(task, "goalId").equals(string(source, "goalId"))) {
            throw new IllegalArgumentException(
                    "path task and source task goals differ");
        }
        // This solver result covers the new primary prefix and frontier.
        // Assignments from an older primary path may belong to a suffix that
        // the new flip no longer executes, so they are not replay obligations.
        JsonArray currentAssignments = overlayAssignments(null, assignments);
        String taskId = "TASK.REPLAY." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(currentAssignments) + "\n"
                + CanonicalJson.render(guardedReads));
        result.addProperty("taskId", taskId);
        goalKind.writeToTask(result);
        result.add("modelAssignments", currentAssignments);
        result.add(ExecutionTask.GUARDED_READ_ASSIGNMENTS,
                guardedReads.deepCopy());
        result.add("replayContract", contract.toImmutableJsonView());
        result.addProperty("pathQueryKey", queryKey);
        applyTargetBranchOverride(result, task);
        return result;
    }

    /**
     * Builds one fresh-JVM replay plan for the primary flip and every causal
     * companion in its target closure.
     */
    static java.util.List<JsonObject> createLinked(
            JsonObject query, Map<String, JsonObject> taskById,
            JsonArray assignments, JsonArray guardedReads,
            BranchReplayContract contract) {
        JsonObject bundle = LinkedReplayBundle.decode(query);
        java.util.List<JsonObject> sources =
                LinkedReplayBundle.sourceTasks(bundle, taskById);
        String primarySourceTaskId =
                LinkedReplayBundle.primarySourceTaskId(bundle);
        Map<String, JsonArray> assignmentsByTask =
                distributeAssignments(assignments, sources,
                        primarySourceTaskId);
        Map<String, JsonArray> readsByTask = distributeGuardedReads(
                guardedReads, sources);
        String queryKey = string(query, "queryKey");
        String groupId = "REPLAY.GROUP." + ArtifactIO.sha256(queryKey + "\n"
                + CanonicalJson.render(assignments) + "\n"
                + CanonicalJson.render(guardedReads));

        java.util.List<JsonObject> result = new ArrayList<>();
        for (JsonObject source : sources) {
            String sourceId = string(source, "taskId");
            String role = LinkedReplayBundle.memberRole(bundle, sourceId);
            JsonArray owned = assignmentsByTask.getOrDefault(sourceId,
                    new JsonArray());
            JsonArray ownedReads = readsByTask.getOrDefault(sourceId,
                    new JsonArray());
            JsonObject replay;
            if (LinkedReplayBundle.PRIMARY.equals(role)) {
                replay = create(query, source, owned, ownedReads, contract);
            } else {
                replay = source.deepCopy();
                // A task that was primary in an earlier bundle can become a
                // downstream companion here. Its old primary query belongs
                // to that earlier frontier. Keeping it would freeze a
                // stale path instead of letting propagated values, thread
                // order and VM read-from choices recompute in this JVM.
                replay.remove("replayContract");
                replay.remove("solverPathContext");
                replay.remove("pathQueryKey");
                replay.remove(ExecutionTask.GUARDED_READ_ASSIGNMENTS);
                replay.add("modelAssignments", overlayAssignments(
                        modelAssignments(source), owned));
                replay.add(ExecutionTask.GUARDED_READ_ASSIGNMENTS,
                        ownedReads.deepCopy());
                replay.addProperty("taskId", "TASK.REPLAY."
                        + ArtifactIO.sha256(queryKey + "\n" + sourceId
                        + "\n" + CanonicalJson.render(
                        replay.getAsJsonArray("modelAssignments")) + "\n"
                        + CanonicalJson.render(ownedReads)));
            }
            replay.addProperty(LinkedReplayBundle.GROUP_FIELD, groupId);
            replay.addProperty(LinkedReplayBundle.ROLE_FIELD, role);
            replay.addProperty(LinkedReplayBundle.FAMILY_DIGEST_FIELD,
                    string(bundle, LinkedReplayBundle.FAMILY_DIGEST_FIELD));
            replay.addProperty(LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD,
                    string(bundle, LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD));
            result.add(replay);
        }
        result.sort(Comparator.comparing((JsonObject task) ->
                LinkedReplayBundle.PRIMARY.equals(string(task,
                        LinkedReplayBundle.ROLE_FIELD)) ? "0" : "1")
                .thenComparing(task -> string(task, "taskId")));
        for (int index = 0; index < result.size(); index++) {
            result.set(index, SharedExpressionTable.compact(
                    result.get(index)));
        }
        return result;
    }

    /** A read override belongs only to the activation that issued the read. */
    private static Map<String, JsonArray> distributeGuardedReads(
            JsonArray assignments, java.util.List<JsonObject> sources) {
        Map<String, JsonArray> result = new LinkedHashMap<>();
        Map<String, String> occurrenceByTask = new LinkedHashMap<>();
        for (JsonObject source : sources) {
            String taskId = string(source, "taskId");
            result.put(taskId, new JsonArray());
            occurrenceByTask.put(taskId, PathObservation
                    .plannedOccurrenceOf(string(source, "occurrenceId")));
        }
        if (assignments == null) return result;
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "guarded read assignment must be an object");
            }
            JsonObject assignment = element.getAsJsonObject();
            String owner = string(assignment, "readerTaskId");
            String readerOccurrence = PathObservation.plannedOccurrenceOf(
                    string(assignment, "readerOccurrenceId"));
            JsonArray owned = result.get(owner);
            if (owned == null && !readerOccurrence.isEmpty()) {
                String occurrenceOwner = null;
                for (Map.Entry<String, String> entry
                        : occurrenceByTask.entrySet()) {
                    if (!readerOccurrence.equals(entry.getValue())) continue;
                    if (occurrenceOwner != null) {
                        throw new IllegalArgumentException(
                                "guarded read assignment has multiple linked "
                                        + "readers at occurrence: "
                                        + readerOccurrence);
                    }
                    occurrenceOwner = entry.getKey();
                }
                if (occurrenceOwner != null) {
                    owner = occurrenceOwner;
                    owned = result.get(owner);
                }
            }
            if (owned == null) {
                throw new IllegalArgumentException(
                        "guarded read assignment has no linked reader: "
                                + string(assignment, "readerTaskId"));
            }
            if (readerOccurrence.isEmpty()
                    || !readerOccurrence.equals(occurrenceByTask.get(owner))) {
                throw new IllegalArgumentException(
                        "guarded read assignment occurrence differs from "
                                + "its linked reader: " + owner);
            }
            owned.add(assignment.deepCopy());
        }
        return result;
    }

    /** One materialized input has exactly one task owner in a linked plan. */
    private static Map<String, JsonArray> distributeAssignments(
            JsonArray assignments, java.util.List<JsonObject> sources,
            String primarySourceTaskId) {
        Map<String, JsonArray> result = new LinkedHashMap<>();
        for (JsonObject source : sources) {
            result.put(string(source, "taskId"), new JsonArray());
        }
        for (JsonElement element : assignments) {
            JsonObject assignment = element.getAsJsonObject();
            String input = string(assignment, "inputSymbol");
            String phase = string(assignment,
                    "configuredSourcePhaseId");
            java.util.List<String> owners = phase.isEmpty()
                    ? actionOwners(input, sources)
                    : configuredPhaseOwners(phase, sources);
            // A propagated input action can appear in several occurrences'
            // frozen catalogs.  The current exact flip owns that control at
            // its primary activation; companions re-evaluate it through the
            // live propagation chain.  Keep all other ambiguity fail-closed.
            if (phase.isEmpty() && owners.size() > 1
                    && owners.contains(primarySourceTaskId)) {
                owners = java.util.Collections.singletonList(
                        primarySourceTaskId);
            }
            if (owners.size() != 1) {
                throw new IllegalArgumentException(
                        "linked model assignment has " + owners.size()
                                + " owners: " + input);
            }
            result.get(owners.get(0)).add(assignment.deepCopy());
        }
        return result;
    }

    private static java.util.List<String> actionOwners(
            String input, java.util.List<JsonObject> sources) {
        java.util.List<String> owners = new ArrayList<>();
        for (JsonObject source : sources) {
            ExecutionTask task = ExecutionTask.decode(source);
            for (JsonElement action : task.inputActions().all()) {
                if (action.isJsonObject() && input.equals(string(
                        action.getAsJsonObject(), "symbol"))) {
                    owners.add(task.taskId());
                    break;
                }
            }
        }
        return owners;
    }

    /** A configured phase names its source occurrence. Prefer that exact
     * task address when several closure members carry the shared catalog. */
    private static java.util.List<String> configuredPhaseOwners(
            String phaseId, java.util.List<JsonObject> sources) {
        java.util.List<String> declared = new ArrayList<>();
        java.util.List<String> exact = new ArrayList<>();
        for (JsonObject source : sources) {
            ExecutionTask task = ExecutionTask.decode(source);
            for (ConfiguredSourcePhaseContract.Occurrence occurrence
                    : task.configuredSourcePhases()) {
                if (!phaseId.equals(occurrence.phaseId())) continue;
                declared.add(task.taskId());
                if (task.occurrenceId().equals(
                        occurrence.sourceOccurrenceId())) {
                    exact.add(task.taskId());
                }
                break;
            }
        }
        return exact.isEmpty() ? declared : exact;
    }

    /**
     * Advances a nested target from the flipped frontier to the next exact
     * failure guard.
     */
    private static void applyTargetBranchOverride(JsonObject result,
                                                  JsonObject query) {
        if (!query.has("targetBranch")
                || !query.get("targetBranch").isJsonObject()) {
            return;
        }
        JsonObject requested = query.getAsJsonObject("targetBranch");
        String siteId = string(requested, "siteId");
        int occurrence = JsonFields.integer(requested,
                "occurrence", -1);
        if (siteId.isEmpty() || occurrence < 1) {
            throw new IllegalArgumentException(
                    "target frontier override is incomplete");
        }

        int matches = 0;
        JsonArray rewritten = new JsonArray();
        for (JsonElement element : result.getAsJsonArray("branches")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "target branch catalog entries must be objects");
            }
            JsonObject branch = element.getAsJsonObject().deepCopy();
            if (siteId.equals(string(branch, "siteId"))) {
                JsonElement required = branch.get("requiredOutcome");
                if (!JsonFields.bool(branch, "failureTarget", false)
                        || required == null || !required.isJsonPrimitive()
                        || !required.getAsJsonPrimitive().isBoolean()) {
                    throw new IllegalArgumentException(
                            "target frontier override is not an exact "
                                    + "failure guard: " + siteId);
                }
                branch.addProperty("policy", "EXPLORE");
                branch.addProperty("policyReason",
                        "TARGET_REPLAY_NEXT_FAILURE_GUARD");
                branch.addProperty("selectedOccurrence", occurrence);
                matches++;
            } else if ("EXPLORE".equals(string(branch, "policy"))) {
                branch.addProperty("policy", "PATH_ASSUMPTION");
                branch.addProperty("policyReason",
                        "TARGET_REPLAY_FRONTIER_PREFIX");
            }
            rewritten.add(branch);
        }
        if (matches != 1) {
            throw new IllegalArgumentException(
                    "target frontier override must match one branch: "
                            + siteId + " (found " + matches + ')');
        }
        result.add("branches", rewritten);
        result.add("targetBranch", requested.deepCopy());
    }

    /**
     * Overlays newly solved values on the explicit assignments retained by a
     * linked companion.
     */
    private static JsonArray overlayAssignments(JsonArray source,
                                                JsonArray current) {
        Map<String, JsonObject> byKey = new TreeMap<>();
        addAssignments(byKey, source, "source");
        addAssignments(byKey, current, "current");
        JsonArray merged = new JsonArray();
        for (JsonObject assignment : byKey.values()) {
            merged.add(assignment.deepCopy());
        }
        return merged;
    }

    private static JsonArray modelAssignments(JsonObject source) {
        JsonElement encoded = source.get("modelAssignments");
        if (encoded == null) return null;
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    "source modelAssignments must be an array");
        }
        return encoded.getAsJsonArray();
    }

    private static void addAssignments(Map<String, JsonObject> target,
                                       JsonArray assignments,
                                       String origin) {
        if (assignments == null) return;
        Set<String> keys = new TreeSet<>();
        for (JsonElement element : assignments) {
            if (element == null || !element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "model assignment must be an object");
            }
            JsonObject assignment = element.getAsJsonObject();
            String explicitKey = string(assignment,
                    "modelAssignmentKey").trim();
            String engineSymbol = string(assignment, "engineSymbol").trim();
            String key = firstNonBlank(explicitKey, engineSymbol);
            if (key.isEmpty()) {
                throw new IllegalArgumentException(
                        "model assignment has no stable key");
            }
            if (!keys.add(key)) {
                throw new IllegalArgumentException("duplicate " + origin
                        + " model assignment key: " + key);
            }
            JsonObject normalized = assignment.deepCopy();
            if (normalized.has("modelAssignmentKey")) {
                if (explicitKey.isEmpty()) {
                    normalized.remove("modelAssignmentKey");
                } else {
                    normalized.addProperty("modelAssignmentKey", explicitKey);
                }
            }
            if (normalized.has("engineSymbol")) {
                if (engineSymbol.isEmpty()) {
                    normalized.remove("engineSymbol");
                } else {
                    normalized.addProperty("engineSymbol", engineSymbol);
                }
            }
            // The two arrays are two precedence layers.  Uniqueness is local
            // to each layer; a current solver result deliberately replaces the
            // source-prefix assignment with the same normalized key.
            target.put(key, normalized);
        }
    }
}
