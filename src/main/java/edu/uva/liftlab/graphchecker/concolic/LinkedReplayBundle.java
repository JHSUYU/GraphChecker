package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
    static final String TOPOLOGY_EPOCH_FIELD = "topologyEpoch";
    static final String PRIMARY = "PRIMARY";
    static final String COMPANION = "COMPANION";

    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "LINKED_CAUSAL_REPLAY_BUNDLE";

    private LinkedReplayBundle() {
    }

    static JsonObject create(String primarySourceTaskId,
                             Collection<JsonObject> executionTasks,
                             Collection<JsonObject> closureSummaries,
                             String primarySummaryId,
                             String topologyEpoch) {
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        for (JsonObject task : executionTasks) {
            String id = optionalString(task, "taskId");
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

        JsonObject primarySummary = null;
        if (closureSummaries != null) {
            for (JsonObject summary : closureSummaries) {
                String summaryId = optionalString(summary, "summaryId");
                if (primarySummaryId != null
                        && primarySummaryId.equals(summaryId)) {
                    primarySummary = summary;
                }
            }
        }
        if (primarySummary == null) {
            throw new IllegalArgumentException(
                    "linked replay primary summary is absent");
        }
        String priorGroup = optionalString(primary, GROUP_FIELD);
        String sourceReplayGroup = optionalString(primarySummary, "replayGroupId");
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
        if (epoch.isEmpty() || !epoch.equals(optionalString(primarySummary,
                VmExpressionIr.TOPOLOGY_EPOCH))) {
            throw new IllegalArgumentException(
                    "linked replay primary summary is outside topology epoch "
                            + epoch);
        }
        Map<String, JsonObject> selected = new LinkedHashMap<>();
        for (JsonObject task : byId.values()) {
            boolean candidate = priorGroup.isEmpty()
                    ? optionalString(task, GROUP_FIELD).isEmpty()
                    && optionalString(task, "pathQueryKey").isEmpty()
                    : priorGroup.equals(optionalString(task, GROUP_FIELD));
            if (!candidate && !primarySourceTaskId.equals(
                    optionalString(task, "taskId"))) {
                continue;
            }
            String key = memberKey(task);
            JsonObject previous = selected.putIfAbsent(key, task);
            if (previous != null && !optionalString(previous, "taskId").equals(
                    optionalString(task, "taskId"))) {
                throw new IllegalArgumentException(
                        "linked replay group has two tasks for " + key);
            }
        }
        List<JsonObject> members = new ArrayList<>(selected.values());
        members.sort(Comparator.comparing(LinkedReplayBundle::memberKey));
        JsonArray encodedMembers = new JsonArray();
        for (JsonObject task : members) {
            String taskId = optionalString(task, "taskId");
            JsonObject member = new JsonObject();
            member.addProperty("sourceTaskId", taskId);
            member.addProperty("regionId", optionalString(task, "regionId"));
            member.addProperty("sourceKey", optionalString(task, "sourceKey"));
            member.addProperty("occurrenceId", optionalString(task, "occurrenceId"));
            member.addProperty("goalId", optionalString(task, "goalId"));
            JsonElement loopBound = task.get(LoopBoundPolicy.FIELD);
            if (loopBound == null || !loopBound.isJsonObject()) {
                throw new IllegalArgumentException(
                        "linked replay member has no loop bound: " + taskId);
            }
            boolean isPrimary = primarySourceTaskId.equals(taskId);
            member.addProperty("role", isPrimary ? PRIMARY : COMPANION);
            encodedMembers.add(member);
        }

        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("primarySourceTaskId", primarySourceTaskId);
        result.addProperty(TOPOLOGY_EPOCH_FIELD,
                epoch);
        result.add("members", encodedMembers);
        return result;
    }

    static JsonObject decode(JsonObject workItem) {
        JsonElement encoded = workItem == null ? null : workItem.get(FIELD);
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "path flip has no linked replay bundle");
        }
        JsonObject bundle = encoded.getAsJsonObject();
        if (optionalInteger(bundle, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(optionalString(bundle, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported linked replay bundle schema");
        }
        JsonArray members = array(bundle, "members");
        if (members.size() == 0
                || optionalString(bundle, TOPOLOGY_EPOCH_FIELD).isEmpty()) {
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
            String id = optionalString(member, "sourceTaskId");
            String role = optionalString(member, "role");
            if (id.isEmpty() || !ids.add(id)
                    || !addresses.add(memberKey(member))) {
                throw new IllegalArgumentException(
                        "linked replay members are missing or duplicate");
            }
            if (PRIMARY.equals(role)) primaries++;
            else if (!COMPANION.equals(role)) {
                throw new IllegalArgumentException(
                        "unknown linked replay member role: " + role);
            }
        }
        if (primaries != 1 || !ids.contains(optionalString(bundle,
                "primarySourceTaskId"))) {
            throw new IllegalArgumentException(
                    "linked replay primary and members disagree");
        }
        return bundle;
    }

    static List<JsonObject> sourceTasks(JsonObject bundle,
                                        Map<String, JsonObject> taskById) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(bundle, "members")) {
            String id = optionalString(element.getAsJsonObject(), "sourceTaskId");
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
        return optionalString(bundle, "primarySourceTaskId");
    }

    static String memberRole(JsonObject bundle, String sourceTaskId) {
        for (JsonElement element : array(bundle, "members")) {
            JsonObject member = element.getAsJsonObject();
            if (sourceTaskId.equals(optionalString(member, "sourceTaskId"))) {
                return optionalString(member, "role");
            }
        }
        return "";
    }

    private static String memberKey(JsonObject task) {
        return optionalString(task, "regionId") + '\u0000'
                + optionalString(task, "sourceKey") + '\u0000'
                + optionalString(task, "occurrenceId") + '\u0000'
                + optionalString(task, "goalId");
    }

}
