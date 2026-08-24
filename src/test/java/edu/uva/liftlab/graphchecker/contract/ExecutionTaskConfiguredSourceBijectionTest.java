package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import org.junit.Test;

import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Fail-closed checks for the task-local selected-phase bijection. */
public class ExecutionTaskConfiguredSourceBijectionTest {
    private static final Gson GSON = new Gson();
    private static final String OCCURRENCE =
            "test/source#epoch0/region/REGION.TEST#1";
    private static final String SOURCE = "TEST.CONFIGURED.SOURCE";
    private static final String FIELD = "<test.Key: int value>";
    private static final String METHOD = "<test.Hook: void run()>";

    @Test
    public void selectedPublishRequiresOneTaskRow() {
        JsonObject missing = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        selectOnlyPhase(missing);
        assertRejected(missing, "PUBLISH/CONSUME task bindings");

        JsonObject extra = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        addPublishBinding(extra);
        assertRejected(extra, "PUBLISH/CONSUME task bindings");
    }

    @Test
    public void selectedConsumeRequiresOneTaskRow() {
        JsonObject missing = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.CONSUME);
        selectOnlyPhase(missing);
        assertRejected(missing, "PUBLISH/CONSUME task bindings");

        JsonObject extra = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.CONSUME);
        addConsumeBinding(extra);
        assertRejected(extra, "PUBLISH/CONSUME task bindings");
    }

    @Test
    public void taskBindingFieldsMustBeArrays() {
        JsonObject catalog = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        catalog.add(ConfiguredSourcePhaseContract.PLAN_FIELD,
                new JsonObject());
        assertRejected(catalog, "must be a collection");

        JsonObject selected = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        selected.addProperty(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD,
                phaseId(selected));
        assertRejected(selected, "must be an array");

        JsonObject publish = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        selectOnlyPhase(publish);
        publish.add(SymbolicSourceEvidence.TASK_FIELD, new JsonObject());
        assertRejected(publish, "must be an array");

        JsonObject consume = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.CONSUME);
        selectOnlyPhase(consume);
        consume.add(ConfiguredSourceSelectorContract.TASK_FIELD,
                new JsonObject());
        assertRejected(consume, "must be an array");
    }

    @Test
    public void repeatedTaskRowsAreRejected() {
        JsonObject publish = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        selectOnlyPhase(publish);
        JsonObject source = publishBinding(publish);
        JsonArray sources = new JsonArray();
        sources.add(source);
        sources.add(source.deepCopy());
        publish.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        assertRejected(publish, "repeats or omits sourcePhaseId");

        JsonObject consume = taskWithPhase(
                ConfiguredSourcePhaseContract.Phase.CONSUME);
        selectOnlyPhase(consume);
        JsonObject selector = consumeBinding(consume);
        JsonArray selectors = new JsonArray();
        selectors.add(selector);
        selectors.add(selector.deepCopy());
        consume.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        assertRejected(consume, "consume phase twice");
    }

    private static JsonObject taskWithPhase(
            ConfiguredSourcePhaseContract.Phase phase) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.TEST");
        task.addProperty("goalId", "GOAL.TEST");
        task.addProperty("regionId", "REGION.TEST");
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "test/source/REGION.TEST");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add(InputActionCatalog.FIELD, new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);

        String field = phase == ConfiguredSourcePhaseContract.Phase.PUBLISH
                ? FIELD : "";
        Map<String, Object> declaration =
                ConfiguredSourcePhaseContract.declaration(
                        phase, SOURCE, field, METHOD, 3);
        ConfiguredSourcePhaseContract.Declaration decoded =
                ConfiguredSourcePhaseContract.declarationsOf(
                        Collections.singletonList(declaration)).get(0);
        Map<String, Object> occurrence =
                ConfiguredSourcePhaseContract.occurrence(
                        decoded, OCCURRENCE, 1, 1L, 1L, 1L,
                        METHOD, Collections.singletonList(1L));
        JsonArray phases = new JsonArray();
        phases.add(GSON.toJsonTree(occurrence));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        return task;
    }

    private static void selectOnlyPhase(JsonObject task) {
        JsonArray selected = new JsonArray();
        selected.add(phaseId(task));
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD, selected);
    }

    private static void addPublishBinding(JsonObject task) {
        JsonArray rows = new JsonArray();
        rows.add(publishBinding(task));
        task.add(SymbolicSourceEvidence.TASK_FIELD, rows);
    }

    private static JsonObject publishBinding(JsonObject task) {
        JsonObject row = new JsonObject();
        row.addProperty("sourcePhaseId", phaseId(task));
        return row;
    }

    private static void addConsumeBinding(JsonObject task) {
        JsonArray rows = new JsonArray();
        rows.add(consumeBinding(task));
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, rows);
    }

    private static JsonObject consumeBinding(JsonObject task) {
        return ConfiguredSourceSelectorContract.exactInt(
                phaseId(task), "SOURCE_PHASE.producer",
                "test/producer#epoch0/region/REGION.PRODUCER#1",
                SOURCE, FIELD);
    }

    private static String phaseId(JsonObject task) {
        return task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(0).getAsJsonObject().get("phaseId").getAsString();
    }

    private static void assertRejected(JsonObject task, String message) {
        try {
            ExecutionTask.decode(task);
            fail("malformed configured-source task must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(),
                    expected.getMessage().contains(message));
        }
    }
}
