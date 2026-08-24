package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Exact target failure outcomes outrank the canonical seed outcome. */
public class ConcolicRegionRuntimeTargetReachTest {
    private static final String TASK = "TASK.target-companion";
    private static final String SOURCE = "test/namenode#epoch0";
    private static final String REGION = "REGION.target";
    private static final String ROOT =
            "<example.NameNode: void compare()>";
    private static final String TARGET_SITE = ROOT + "#u14";

    @After
    public void resetRuntime() {
        ConcolicRegionRuntime.resetForTests();
    }

    @Test
    public void exactRequiredTargetOutcomeIsNotRejectedAsSeedMismatch()
            throws Exception {
        Object runtimeTask = runtimeTask(task());
        Object active = activeRegion(runtimeTask);

        JsonObject reached = reach(false, 1);
        field(active, "targetReach").set(active, reached);
        @SuppressWarnings("unchecked")
        Map<String, Set<Boolean>> witnessed =
                (Map<String, Set<Boolean>>) field(active,
                        "witnessedOutcomes").get(active);
        Set<Boolean> outcomes = new LinkedHashSet<>();
        outcomes.add(Boolean.FALSE);
        witnessed.put(TARGET_SITE, outcomes);

        Method exact = runtimeTask.getClass().getDeclaredMethod(
                "reachedRequiredTargetOutcome", JsonObject.class);
        exact.setAccessible(true);
        assertTrue((Boolean) exact.invoke(runtimeTask, reached));
        assertFalse((Boolean) exact.invoke(runtimeTask, reach(true, 1)));
        assertFalse((Boolean) exact.invoke(runtimeTask, reach(false, 2)));

        Method judge = ConcolicRegionRuntime.class.getDeclaredMethod(
                "judgeFinishedOccurrence", active.getClass());
        judge.setAccessible(true);
        judge.invoke(null, active);

        Field abandoned = field(active, "abandoned");
        assertFalse("the selected failure outcome is a target witness",
                abandoned.getBoolean(active));
    }

    private static Object runtimeTask(JsonObject task) throws Exception {
        Class<?> type = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$RuntimeTask");
        Constructor<?> constructor = type.getDeclaredConstructor(
                ExecutionTask.class);
        constructor.setAccessible(true);
        return constructor.newInstance(ExecutionTask.decode(task));
    }

    private static Object activeRegion(Object runtimeTask) throws Exception {
        Class<?> type = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = type.getDeclaredConstructor(long.class,
                runtimeTask.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(91L, runtimeTask,
                new Object(), Thread.currentThread());
        @SuppressWarnings("unchecked")
        Set<String> observed = (Set<String>) field(active,
                "observedSourceKeys").get(active);
        observed.add(SOURCE);
        return active;
    }

    private static Field field(Object owner, String name) throws Exception {
        Field field = owner.getClass().getDeclaredField(name);
        field.setAccessible(true);
        return field;
    }

    private static JsonObject reach(boolean outcome, int occurrence) {
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", "TARGET_REACH_EVENT");
        reach.addProperty("siteId", TARGET_SITE);
        reach.addProperty("occurrence", occurrence);
        reach.addProperty("outcome", outcome);
        return reach;
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL.TARGET");
        task.addProperty("sourceKey", SOURCE);
        task.addProperty("occurrenceId",
                SOURCE + "/region/" + REGION + "#1");
        task.addProperty("relationKey", "RELATION.TARGET");
        task.addProperty("regionId", REGION);
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");

        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", SOURCE);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("edgeBindings", new JsonArray());

        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", TARGET_SITE);
        targetBranch.addProperty("occurrence", 1);
        task.add("targetBranch", targetBranch);

        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", TARGET_SITE);
        branch.addProperty("policy", "EXPLORE");
        branch.addProperty("selectedOccurrence", 1);
        branch.addProperty("observedOutcome", true);
        branch.addProperty("requiredOutcome", false);
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrence", 1);
        occurrence.addProperty("outcome", true);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence);
        branch.add("occurrences", occurrences);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        task.add("branches", branches);

        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }
}
