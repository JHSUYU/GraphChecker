package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Core contracts for the linked region-path worklist. */
public class RegionPathWorklistTest {

    @Test
    public void observedOppositeOutcomesCloseTheSemanticFlip() {
        JsonObject task = task("B", "REGION.B",
                "REGION.B/occurrence-1");
        JsonObject taken = summary(task, 1, true);
        JsonObject notTaken = summary(task, 1, false);
        taken.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                finalLoopProfile("LOOP.B", 2));
        notTaken.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                finalLoopProfile("LOOP.B", 1));
        refreshLocalCaseId(taken);
        refreshLocalCaseId(notTaken);
        notTaken.addProperty("summaryId", "SUMMARY.B.not-taken");
        notTaken.addProperty("replayGroupId", "REPLAY.GROUP.SECOND");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(taken, notTaken),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                CanonicalJson.sha256("same-family-snapshot"));

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void oneFlipCarriesTheWholeDependencyClosure() {
        JsonObject c = task("C", "REGION.C", "REGION.C/occurrence-1");
        JsonObject b = task("B", "REGION.B", "REGION.B/occurrence-1");
        JsonObject a = task("A", "REGION.A", "REGION.A/occurrence-1");
        List<JsonObject> summaries = Arrays.asList(
                summary(c, 1), summary(b, 1), summary(b, 2), summary(a, 1));
        String familyDigest = CanonicalJson.sha256("family-snapshot");
        JsonObject bundle = LinkedReplayBundle.create(
                "TASK.B", Arrays.asList(c, b, a), summaries,
                "SUMMARY.B.2", familyDigest, "ITERATION.7");
        JsonObject carrier = new JsonObject();
        carrier.add(LinkedReplayBundle.FIELD, bundle);
        JsonObject decoded = LinkedReplayBundle.decode(carrier);

        assertEquals(3, decoded.getAsJsonArray("members").size());
        assertEquals("ITERATION.7", decoded.get(
                LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD).getAsString());
        int primaries = 0;
        for (JsonElement element : decoded.getAsJsonArray("members")) {
            JsonObject member = element.getAsJsonObject();
            if (LinkedReplayBundle.PRIMARY.equals(
                    member.get("role").getAsString())) {
                primaries++;
            }
        }
        assertEquals(1, primaries);

        BranchReplayContract oldContract = BranchReplayContract.fromSummary(
                summaries.get(0), "SITE.C", 1);
        for (JsonObject oldPrimary : Arrays.asList(c, b, a)) {
            oldPrimary.add("replayContract", oldContract.toJson());
            oldPrimary.addProperty("pathQueryKey", "old-frontier");
        }
        JsonObject currentAction = new JsonObject();
        currentAction.addProperty("mode", "SYMBOLIC");
        currentAction.addProperty("symbol", "M_I_CURRENT");
        currentAction.addProperty("location", "CALL_RETURN");
        currentAction.addProperty("javaType", "int");
        b.getAsJsonArray("inputActions").add(currentAction);
        JsonArray stalePrimaryAssignments = new JsonArray();
        stalePrimaryAssignments.add(modelAssignment("M_I_STALE_SUFFIX", 7));
        b.add("modelAssignments", stalePrimaryAssignments);
        JsonArray companionAssignments = new JsonArray();
        companionAssignments.add(modelAssignment("M_I_COMPANION", 8));
        a.add("modelAssignments", companionAssignments);
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("B-flip"));
        query.addProperty("goalId", "GOAL.LINKED");
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(query);
        query.add(LinkedReplayBundle.FIELD, bundle.deepCopy());
        Map<String, JsonObject> tasks = new LinkedHashMap<>();
        for (JsonObject task : Arrays.asList(c, b, a)) {
            tasks.put(task.get("taskId").getAsString(), task);
        }
        JsonArray currentAssignments = new JsonArray();
        currentAssignments.add(modelAssignment("M_I_CURRENT", 9));
        JsonArray guardedReads = new JsonArray();
        JsonObject guardedRead = new JsonObject();
        // The linked bundle may replace the task row with a replay clone;
        // the planned activation occurrence remains its stable identity.
        guardedRead.addProperty("readerTaskId", "TASK.PRIOR.A");
        guardedRead.addProperty("readerOccurrenceId",
                "REGION.A/occurrence-1");
        guardedRead.addProperty("readIdentity", "RFC.fixture");
        guardedReads.add(guardedRead);
        List<JsonObject> replay = PathReplayTaskFactory.createLinked(query,
                tasks, currentAssignments, guardedReads,
                BranchReplayContract.fromSummary(
                        summaries.get(2), "SITE.B", 1));
        for (JsonObject replayTask : replay) {
            boolean primary = LinkedReplayBundle.PRIMARY.equals(replayTask
                    .get(LinkedReplayBundle.ROLE_FIELD).getAsString());
            assertEquals(primary, replayTask.has("replayContract"));
            assertEquals(primary, replayTask.has("pathQueryKey"));
            JsonObject expanded = SharedExpressionTable.expand(replayTask);
            ExecutionTask decodedTask = ExecutionTask.decode(replayTask);
            assertEquals(string(expanded, "taskId"),
                    decodedTask.taskId());
            if (primary) {
                assertTrue(replayTask.has(SharedExpressionTable.FIELD));
                assertEquals(string(query, "queryKey"),
                        string(replayTask, "pathQueryKey"));
                assertEquals(expanded.get("replayContract"),
                        decodedTask.replayContract());
                assertEquals("SITE.B", decodedTask.replaySchedule()
                        .sourceSiteId());
                assertEquals(1, expanded.getAsJsonArray(
                        "modelAssignments").size());
                assertEquals("M_I_CURRENT", expanded.getAsJsonArray(
                        "modelAssignments").get(0).getAsJsonObject()
                        .get("engineSymbol").getAsString());
            } else if ("REGION.A".equals(string(expanded, "regionId"))) {
                assertEquals("M_I_COMPANION", expanded.getAsJsonArray(
                        "modelAssignments").get(0).getAsJsonObject()
                        .get("engineSymbol").getAsString());
                assertEquals(1, decodedTask.guardedReadAssignments().size());
            } else {
                assertEquals(0, decodedTask.guardedReadAssignments().size());
            }
        }
    }

    @Test
    public void sharedInputActionIsAssignedOnlyToTheExactPrimary() {
        JsonObject first = task("FIRST", "REGION.FIRST",
                "REGION.FIRST/occurrence-1");
        JsonObject second = task("SECOND", "REGION.SECOND",
                "REGION.SECOND/occurrence-1");
        JsonObject third = task("THIRD", "REGION.THIRD",
                "REGION.THIRD/occurrence-1");
        String shared = "XCH.fixture.req.value";
        for (JsonObject owner : Arrays.asList(first, second)) {
            JsonObject action = new JsonObject();
            action.addProperty("mode", "SYMBOLIC");
            action.addProperty("symbol", shared);
            action.addProperty("location", "CALL_RETURN");
            action.addProperty("javaType", "int");
            owner.getAsJsonArray("inputActions").add(action);
        }
        List<JsonObject> tasks = Arrays.asList(first, second, third);
        List<JsonObject> summaries = Arrays.asList(
                summary(first, 1), summary(second, 1), summary(third, 1));
        Map<String, JsonObject> taskById = new LinkedHashMap<>();
        for (JsonObject task : tasks) {
            taskById.put(string(task, "taskId"), task);
        }
        JsonArray assignments = new JsonArray();
        assignments.add(modelAssignment(shared, 9));

        for (int primaryIndex = 0; primaryIndex < 2; primaryIndex++) {
            JsonObject primary = tasks.get(primaryIndex);
            JsonObject primarySummary = summaries.get(primaryIndex);
            JsonObject query = linkedQuery(primary, tasks, summaries,
                    primarySummary);
            List<JsonObject> replay = PathReplayTaskFactory.createLinked(
                    query, taskById, assignments, new JsonArray(),
                    BranchReplayContract.fromSummary(primarySummary,
                            "SITE." + (primaryIndex == 0
                                    ? "FIRST" : "SECOND"), 1));
            for (JsonObject replayTask : replay) {
                JsonObject expanded = SharedExpressionTable.expand(
                        replayTask);
                assertEquals(string(expanded, "regionId").equals(
                                string(primary, "regionId")) ? 1 : 0,
                        expanded.getAsJsonArray("modelAssignments").size());
            }
        }

        JsonObject query = linkedQuery(third, tasks, summaries,
                summaries.get(2));
        try {
            PathReplayTaskFactory.createLinked(query, taskById, assignments,
                    new JsonArray(), BranchReplayContract.fromSummary(
                            summaries.get(2), "SITE.THIRD", 1));
            throw new AssertionError("multiple companion owners accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("has 2 owners"));
        }
    }

    private static JsonObject task(String id, String region,
                                   String occurrence) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK." + id);
        task.addProperty("goalId", "GOAL.LINKED");
        task.addProperty("regionId", region);
        task.addProperty("sourceKey", "SOURCE." + id);
        task.addProperty("occurrenceId", occurrence);
        task.addProperty("relationKey", "RELATION." + id);
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(task);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", "SITE." + id);
        branch.addProperty("policy", "EXPLORE");
        branch.addProperty("selectedOccurrence", 1);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        task.add("branches", branches);
        task.add("inputActions", new JsonArray());
        return task;
    }

    private static JsonObject modelAssignment(String symbol, int value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", symbol);
        assignment.addProperty("inputSymbol", symbol);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", Integer.toString(value));
        return assignment;
    }

    private static JsonObject linkedQuery(JsonObject primary,
                                          List<JsonObject> tasks,
                                          List<JsonObject> summaries,
                                          JsonObject primarySummary) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256(
                "shared-owner-" + string(primary, "taskId")));
        query.addProperty("goalId", "GOAL.LINKED");
        query.addProperty("sourceTaskId", string(primary, "taskId"));
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(query);
        query.add(LinkedReplayBundle.FIELD, LinkedReplayBundle.create(
                string(primary, "taskId"), tasks, summaries,
                string(primarySummary, "summaryId"),
                CanonicalJson.sha256("shared-owner-family"),
                "ITERATION.7"));
        return query;
    }

    private static JsonObject summary(JsonObject task, int activation) {
        return summary(task, activation, true);
    }

    private static JsonObject summary(JsonObject task, int activation,
                                      boolean outcome) {
        String taskId = task.get("taskId").getAsString();
        String planned = task.get("occurrenceId").getAsString();
        String suffix = taskId.substring("TASK.".length());
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + suffix + "."
                + activation);
        summary.addProperty("taskId", taskId);
        summary.addProperty("goalId", task.get("goalId").getAsString());
        summary.addProperty("regionId", task.get("regionId").getAsString());
        summary.addProperty("sourceKey", task.get("sourceKey").getAsString());
        summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);
        summary.addProperty(PathObservation.ACTIVATION_ORDINAL, activation);
        summary.addProperty("occurrenceId", planned + "#a" + activation);
        summary.addProperty("replayGroupId", "REPLAY.GROUP.SEED");
        summary.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, "ITERATION.7");
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);

        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_field_" + suffix + "_in");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", left);
        condition.addProperty("_op", outcome ? ">" : "<=");
        condition.add("_right", right);
        JsonArray conditions = new JsonArray();
        conditions.add(condition);
        summary.add("pathCondition", conditions);

        JsonObject vmEvent = new JsonObject();
        vmEvent.addProperty("eventId", 1L);
        vmEvent.addProperty("contextId", 1L);
        vmEvent.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPcImmutable("SITE." + suffix,
                "<fixture.Linked: void run()>", 0, 1, outcome,
                condition, 0, vmEvent);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(witness, 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);
        refreshLocalCaseId(summary);
        return summary;
    }

    private static void refreshLocalCaseId(JsonObject summary) {
        summary.remove(LocalCaseIdentity.FIELD);
        summary.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(summary));
    }

    private static JsonArray finalLoopProfile(String siteId, int bodyCount) {
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, siteId);
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                "runtime-" + siteId);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                "CFG_BACKEDGE");
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, 8);
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        loop.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, true);
        JsonArray rows = new JsonArray();
        rows.add(loop);
        return rows;
    }
}
