package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * One path flip and the target dependency closure replayed with it.
 *
 * <p>The scheduler's target-first plan is already one dependency closure.
 * This contract keeps exactly one task for each planned occurrence in the
 * same workload JVM.  The primary member owns the flipped branch; companion
 * members keep the causal prefix alive so VM expression handles can travel
 * through the real RPC/shared-state execution.</p>
 */
final class LinkedReplayBundle {
    static final String FIELD = "linkedReplayBundle";
    static final String GROUP_FIELD = "linkedReplayGroupId";
    static final String ROLE_FIELD = "linkedReplayRole";
    static final String FAMILY_DIGEST_FIELD = "familySnapshotDigest";
    static final String TOPOLOGY_EPOCH_FIELD = "topologyEpoch";
    static final String SOURCE_REPLAY_GROUP_FIELD = "sourceReplayGroupId";
    static final String CASE_DEPENDENCIES_FIELD =
            "consumerAnchorCaseDependencies";
    static final String PRIMARY = "PRIMARY";
    static final String COMPANION = "COMPANION";

    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "LINKED_CAUSAL_REPLAY_BUNDLE";

    private LinkedReplayBundle() {
    }

    static String familySnapshotDigest(JsonArray caseDependencies) {
        List<JsonObject> ordered = new ArrayList<>();
        if (caseDependencies != null) {
            for (JsonElement element : caseDependencies) {
                if (element != null && element.isJsonObject()) {
                    ordered.add(element.getAsJsonObject());
                }
            }
        }
        ordered.sort(Comparator.comparing(row -> string(row,
                VmExpressionIr.FAMILY_KEY)));
        JsonArray rows = new JsonArray();
        for (JsonObject row : ordered) rows.add(row);
        JsonObject snapshot = new JsonObject();
        snapshot.add(CASE_DEPENDENCIES_FIELD, rows);
        return SharedExpressionTable.semanticDigest(snapshot);
    }

    static JsonObject create(String primarySourceTaskId,
                             Collection<JsonObject> executionTasks,
                             Collection<JsonObject> closureSummaries,
                             String primarySummaryId,
                             String familySnapshotDigest,
                             String topologyEpoch) {
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        for (JsonObject task : executionTasks) {
            String id = string(task, "taskId");
            if (!id.isEmpty() && byId.put(id, task) != null) {
                throw new IllegalArgumentException(
                        "duplicate linked replay source task: " + id);
            }
        }
        JsonObject primary = byId.get(primarySourceTaskId);
        if (primary == null) {
            throw new IllegalArgumentException(
                    "linked replay primary source is absent: "
                            + primarySourceTaskId);
        }

        Map<String, List<JsonObject>> summariesByTask =
                new LinkedHashMap<>();
        List<String> summaryIds = new ArrayList<>();
        JsonObject primarySummary = null;
        if (closureSummaries != null) {
            for (JsonObject summary : closureSummaries) {
                String summaryId = string(summary, "summaryId");
                if (!summaryId.isEmpty()) summaryIds.add(summaryId);
                if (primarySummaryId != null
                        && primarySummaryId.equals(summaryId)) {
                    primarySummary = summary;
                }
                String taskId = string(summary, "taskId");
                if (!taskId.isEmpty()) {
                    summariesByTask.computeIfAbsent(taskId,
                            ignored -> new ArrayList<>()).add(summary);
                }
            }
        }
        if (primarySummary == null) {
            throw new IllegalArgumentException(
                    "linked replay primary summary is absent");
        }
        String priorGroup = string(primary, GROUP_FIELD);
        String sourceReplayGroup = string(primarySummary, "replayGroupId");
        if (sourceReplayGroup.isEmpty()) {
            throw new IllegalArgumentException(
                    "linked replay primary summary has no replay group");
        }
        if (!priorGroup.isEmpty()
                && !priorGroup.equals(sourceReplayGroup)) {
            throw new IllegalArgumentException(
                    "linked replay task and summary groups differ");
        }
        String epoch = topologyEpoch == null ? "" : topologyEpoch.trim();
        if (epoch.isEmpty() || !epoch.equals(string(primarySummary,
                VmExpressionIr.TOPOLOGY_EPOCH))) {
            throw new IllegalArgumentException(
                    "linked replay primary summary is outside topology epoch "
                            + epoch);
        }
        Map<String, JsonObject> selected = new LinkedHashMap<>();
        for (JsonObject task : byId.values()) {
            boolean candidate = priorGroup.isEmpty()
                    ? string(task, GROUP_FIELD).isEmpty()
                    && string(task, "pathQueryKey").isEmpty()
                    : priorGroup.equals(string(task, GROUP_FIELD));
            if (!candidate && !primarySourceTaskId.equals(
                    string(task, "taskId"))) {
                continue;
            }
            String key = memberKey(task);
            JsonObject previous = selected.putIfAbsent(key, task);
            if (previous != null && !string(previous, "taskId").equals(
                    string(task, "taskId"))) {
                throw new IllegalArgumentException(
                        "linked replay group has two tasks for " + key);
            }
        }
        List<JsonObject> members = new ArrayList<>(selected.values());
        members.sort(Comparator.comparing(LinkedReplayBundle::memberKey));
        JsonArray encodedMembers = new JsonArray();
        for (JsonObject task : members) {
            String taskId = string(task, "taskId");
            JsonObject member = new JsonObject();
            member.addProperty("sourceTaskId", taskId);
            member.addProperty("regionId", string(task, "regionId"));
            member.addProperty("sourceKey", string(task, "sourceKey"));
            member.addProperty("occurrenceId", string(task, "occurrenceId"));
            member.addProperty("goalId", string(task, "goalId"));
            JsonElement loopBound = task.get(LoopBoundPolicy.FIELD);
            if (loopBound == null || !loopBound.isJsonObject()) {
                throw new IllegalArgumentException(
                        "linked replay member has no loop bound: " + taskId);
            }
            member.add(LoopBoundPolicy.FIELD, loopBound.deepCopy());
            JsonArray activations = new JsonArray();
            List<JsonObject> sourceSummaries = summariesByTask.getOrDefault(
                    taskId, Collections.emptyList());
            sourceSummaries.sort(Comparator
                    .comparingInt((JsonObject summary) -> integer(summary,
                            PathObservation.ACTIVATION_ORDINAL, -1))
                    .thenComparing(summary -> string(summary, "summaryId")));
            for (JsonObject summary : sourceSummaries) {
                int activationOrdinal = integer(summary,
                        PathObservation.ACTIVATION_ORDINAL, -1);
                String activationOccurrence = string(summary,
                        "occurrenceId");
                if (activationOrdinal < 1 || activationOccurrence.isEmpty()) {
                    throw new IllegalArgumentException(
                            "linked replay summary has no activation tuple: "
                                    + string(summary, "summaryId"));
                }
                JsonObject activation = new JsonObject();
                activation.addProperty("summaryId",
                        string(summary, "summaryId"));
                activation.addProperty("occurrenceId",
                        activationOccurrence);
                activation.addProperty(PathObservation.ACTIVATION_ORDINAL,
                        activationOrdinal);
                if (summary.has(LoopBoundPolicy.PATH_LOOP_COUNTS)) {
                    activation.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                            summary.get(LoopBoundPolicy.PATH_LOOP_COUNTS)
                                    .deepCopy());
                }
                activations.add(activation);
            }
            member.add("sourceActivations", activations);
            boolean isPrimary = primarySourceTaskId.equals(taskId);
            member.addProperty("role", isPrimary ? PRIMARY : COMPANION);
            encodedMembers.add(member);
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("primarySourceTaskId", primarySourceTaskId);
        result.addProperty(FAMILY_DIGEST_FIELD,
                requireDigest(familySnapshotDigest));
        result.addProperty(TOPOLOGY_EPOCH_FIELD,
                epoch);
        result.addProperty(SOURCE_REPLAY_GROUP_FIELD, sourceReplayGroup);
        result.addProperty("primarySummaryId", primarySummaryId);
        JsonArray encodedSummaryIds = new JsonArray();
        Collections.sort(summaryIds);
        String previous = "";
        for (String summaryId : summaryIds) {
            if (summaryId.equals(previous)) continue;
            encodedSummaryIds.add(summaryId);
            previous = summaryId;
        }
        result.add("closureSummaryIds", encodedSummaryIds);
        result.add("members", encodedMembers);
        result.addProperty("bundleDigest", CanonicalJson.sha256(result));
        return result;
    }

    static JsonObject decode(JsonObject workItem) {
        JsonElement encoded = workItem == null ? null : workItem.get(FIELD);
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "path flip has no linked replay bundle");
        }
        JsonObject bundle = encoded.getAsJsonObject();
        if (integer(bundle, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(bundle, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported linked replay bundle schema");
        }
        requireDigest(string(bundle, FAMILY_DIGEST_FIELD));
        JsonArray members = array(bundle, "members");
        JsonArray summaries = array(bundle, "closureSummaryIds");
        if (members.size() == 0 || summaries.size() == 0
                || string(bundle, "primarySummaryId").isEmpty()
                || string(bundle, SOURCE_REPLAY_GROUP_FIELD).isEmpty()
                || string(bundle, TOPOLOGY_EPOCH_FIELD).isEmpty()) {
            throw new IllegalArgumentException(
                    "linked replay bundle has no members or summary refs");
        }
        Set<String> ids = new LinkedHashSet<>();
        Set<String> addresses = new LinkedHashSet<>();
        int primaries = 0;
        for (JsonElement element : members) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "linked replay member must be an object");
            }
            JsonObject member = element.getAsJsonObject();
            String id = string(member, "sourceTaskId");
            String role = string(member, "role");
            if (id.isEmpty() || !ids.add(id)
                    || !addresses.add(memberKey(member))
                    || !member.has(LoopBoundPolicy.FIELD)
                    || !member.get(LoopBoundPolicy.FIELD).isJsonObject()
                    || !member.has("sourceActivations")
                    || !member.get("sourceActivations").isJsonArray()) {
                throw new IllegalArgumentException(
                        "linked replay members are missing or duplicate");
            }
            if (PRIMARY.equals(role)) primaries++;
            else if (!COMPANION.equals(role)) {
                throw new IllegalArgumentException(
                        "unknown linked replay member role: " + role);
            }
        }
        if (primaries != 1 || !ids.contains(string(bundle,
                "primarySourceTaskId"))) {
            throw new IllegalArgumentException(
                    "linked replay primary and members disagree");
        }
        JsonObject digestBase = bundle.deepCopy();
        String statedDigest = string(digestBase, "bundleDigest");
        digestBase.remove("bundleDigest");
        if (statedDigest.isEmpty()
                || !statedDigest.equals(CanonicalJson.sha256(digestBase))) {
            throw new IllegalArgumentException(
                    "linked replay bundle digest differs");
        }
        return bundle;
    }

    static List<JsonObject> sourceTasks(JsonObject bundle,
                                        Map<String, JsonObject> taskById) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(bundle, "members")) {
            String id = string(element.getAsJsonObject(), "sourceTaskId");
            JsonObject task = taskById.get(id);
            if (task == null) {
                throw new IllegalArgumentException(
                        "linked replay source task is absent: " + id);
            }
            result.add(task.deepCopy());
        }
        return result;
    }

    static String primarySourceTaskId(JsonObject bundle) {
        return string(bundle, "primarySourceTaskId");
    }

    static String memberRole(JsonObject bundle, String sourceTaskId) {
        for (JsonElement element : array(bundle, "members")) {
            JsonObject member = element.getAsJsonObject();
            if (sourceTaskId.equals(string(member, "sourceTaskId"))) {
                return string(member, "role");
            }
        }
        return "";
    }

    private static String memberKey(JsonObject task) {
        return string(task, "regionId") + '\u0000'
                + string(task, "sourceKey") + '\u0000'
                + string(task, "occurrenceId") + '\u0000'
                + string(task, "goalId");
    }

    private static String requireDigest(String value) {
        String digest = value == null ? "" : value.trim();
        if (!digest.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException(
                    "family snapshot digest must be lowercase SHA-256");
        }
        return digest;
    }
}
