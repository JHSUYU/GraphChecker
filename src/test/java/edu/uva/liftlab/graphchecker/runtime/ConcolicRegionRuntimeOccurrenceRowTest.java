package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * README {@code OCC-1} result rows: every activation of one address is its
 * own occurrence, and its row says which one it is.
 *
 * <p>The contract the importer reads is in {@code
 * experiments/shrink/wave2-backlog.md} under "OCC-1 result rows".  Run 24 is
 * the motivating case: four of six tasks reported {@code
 * REGION_OCCURRENCE_ADDRESS_AMBIGUOUS}, i.e. the campaign observed those
 * occurrences and threw them away, and the one SASL activation it kept had
 * read {@code allKeys} before any writer ran.</p>
 */
public class ConcolicRegionRuntimeOccurrenceRowTest {
    private static final String TASK = "TASK.occurrence-rows";
    private static final String SOURCE_KEY = "test/occurrence-rows#epoch0";
    private static final String OCCURRENCE =
            SOURCE_KEY + "/region/SERVICE#3";
    private static final String ROOT = "<example.Service: void run()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    /**
     * Two activations of one address publish two rows, numbered and named
     * apart, and neither is suppressed for missing the boundary.
     */
    @Test
    public void eachActivationOfOneAddressIsItsOwnNumberedOccurrence()
            throws Exception {
        load("OUTPUT_RELATION_CLOSURE");

        Object firstActive = activation(11L);
        JsonObject first = identity(firstActive);
        assertEquals(TASK, first.get("taskId").getAsString());
        assertEquals(OCCURRENCE,
                first.get("plannedOccurrenceId").getAsString());
        assertEquals(OCCURRENCE + "#a1",
                first.get("occurrenceId").getAsString());
        assertEquals(1, first.get("activationOrdinal").getAsInt());

        JsonObject second = identity(activation(12L));
        assertEquals(OCCURRENCE + "#a2",
                second.get("occurrenceId").getAsString());
        assertEquals(2, second.get("activationOrdinal").getAsInt());
        // The planned address is kept verbatim on every row: it is what the
        // worklist merges the activations of one task on.
        assertEquals(OCCURRENCE,
                second.get("plannedOccurrenceId").getAsString());

        // This activation captured nothing, so it publishes as incomplete
        // rather than disappearing.
        assertFalse(second.get("relationallyComplete").getAsBoolean());
        // targetReached is a target-reach member only.
        assertFalse(second.has("targetReached"));

        Field activation = firstActive.getClass().getDeclaredField(
                "activation");
        activation.setAccessible(true);
        Object task = activation.get(firstActive);
        Method reserve = task.getClass().getDeclaredMethod(
                "reserveCompletedEvidence", boolean.class, boolean.class);
        reserve.setAccessible(true);
        Method blocksAdmission = task.getClass().getDeclaredMethod(
                "blocksAdmissionAfterCompletedTarget");
        blocksAdmission.setAccessible(true);
        Method suppressesDuplicate = task.getClass().getDeclaredMethod(
                "suppressesDuplicateRelationResult");
        suppressesDuplicate.setAccessible(true);
        reserve.invoke(task, false, false);
        assertFalse((Boolean) blocksAdmission.invoke(task));
        assertFalse((Boolean) suppressesDuplicate.invoke(task));
        reserve.invoke(task, false, true);
        assertFalse("a completed producer must remain live for propagation",
                (Boolean) blocksAdmission.invoke(task));
        assertTrue("only its duplicate durable row is suppressed",
                (Boolean) suppressesDuplicate.invoke(task));

        Object duplicate = activation(13L);
        ConcolicRegionRuntime.beginLiveSelectedRegion();
        Method suppress = ConcolicRegionRuntime.class.getDeclaredMethod(
                "suppressDuplicateRelationResult", duplicate.getClass());
        suppress.setAccessible(true);
        suppress.invoke(null, duplicate);
        Field abandoned = duplicate.getClass().getDeclaredField("abandoned");
        abandoned.setAccessible(true);
        assertTrue(abandoned.getBoolean(duplicate));
        assertEquals("a suppressed row does not spend an occurrence ordinal",
                OCCURRENCE + "#a3",
                identity(activation(14L)).get("occurrenceId").getAsString());
    }

    /** A target-reach address carries the member the importer selects on. */
    @Test
    public void aTargetReachRowStatesWhetherItTookTheTarget()
            throws Exception {
        load("TARGET_REACH_CLOSURE");

        JsonObject row = identity(activation(21L));
        assertTrue(row.has("targetReached"));
        // No declared branch event was taken and the exit is NORMAL.
        assertFalse(row.get("targetReached").getAsBoolean());
        // A task with no demanded output relation is complete by construction.
        assertTrue(row.get("relationallyComplete").getAsBoolean());
        assertEquals(OCCURRENCE + "#a1",
                row.get("occurrenceId").getAsString());
    }

    private static JsonObject identity(Object active) throws Exception {
        Class<?> activeType = active.getClass();
        Method add = ConcolicRegionRuntime.class.getDeclaredMethod(
                "addResultIdentity", JsonObject.class, activeType,
                String.class, String.class);
        add.setAccessible(true);
        JsonObject result = new JsonObject();
        add.invoke(null, result, active, "NORMAL", "");
        return result;
    }

    /** One admitted activation of the loaded task, ordinal taken as usual. */
    private static Object activation(long token) throws Exception {
        Field configurationField = ConcolicRegionRuntime.class
                .getDeclaredField("configuration");
        configurationField.setAccessible(true);
        Object configuration = configurationField.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, TASK);

        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, new Object(),
                Thread.currentThread());

        Method next = task.getClass().getDeclaredMethod(
                "nextActivationOrdinal");
        next.setAccessible(true);
        Field ordinal = activeType.getDeclaredField("activationOrdinal");
        ordinal.setAccessible(true);
        ordinal.setInt(active, ((Integer) next.invoke(task)).intValue());
        return active;
    }

    private void load(String goalKind) throws Exception {
        Path plan = folder.newFile(goalKind + "-plan.jsonl").toPath();
        Files.write(plan, (task(goalKind) + "\n")
                .getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(goalKind + ".jsonl")
                        .toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static JsonObject task(String goalKind) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", SOURCE_KEY);
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.SERVICE");
        task.addProperty("regionId", "SERVICE");
        task.addProperty("goalKind", goalKind);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", SOURCE_KEY);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        if ("OUTPUT_RELATION_CLOSURE".equals(goalKind)) {
            task.add("outputClosure", closure());
        }
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    /** One demanded field-write boundary, so an empty activation is
     *  relationally incomplete rather than vacuously complete. */
    private static JsonObject closure() {
        String cell = "<example.Service: long generation>";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.generation");
        capture.addProperty("outputPort", "SERVICE.out.generation");
        capture.addProperty("captureKind", "FIELD_WRITE_STATE");
        capture.addProperty("outputCell", cell);
        capture.addProperty("javaType", "long");
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");
        capture.addProperty("outputSiteId", "FIELD_WRITE_STATE:site");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("fieldSignature", cell);
        capture.addProperty("definitionMethod", ROOT);
        capture.addProperty("definitionUnitIndex", 4);
        JsonArray captures = new JsonArray();
        captures.add(capture);

        JsonObject slice = new JsonObject();
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.addProperty("outputPort", "SERVICE.out.generation");
        slice.addProperty("outputCell", cell);
        slice.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        slice.addProperty("activationLocalOccurrence", 1);

        JsonObject output = new JsonObject();
        output.addProperty("portId", "SERVICE.out.generation");
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("outputSiteId", "FIELD_WRITE_STATE:site");
        output.addProperty("outputOccurrence", 1);
        output.addProperty("cell", cell);
        output.addProperty("javaTypeDescriptor", "J");

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);

        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.SERVICE");
        producer.addProperty("regionId", "SERVICE");

        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
