package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
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
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * README {@code TERM-1}: a coarse occurrence ends at its real terminal.
 *
 * <p>A captured output version used to close the occurrence as soon as every
 * demanded port held one row.  Because one admitted row completes a port, the
 * <em>first</em> {@code put}/write of a map ended the occurrence: every later
 * version of the same relation, every later RPC/state effect and any throw the
 * occurrence would really have reached became unobservable, and the synthetic
 * {@code NORMAL} was published as the case terminal.</p>
 */
public class ConcolicRegionRuntimeTerminalBoundaryTest {
    private static final String TASK = "TASK.terminal-boundary";
    private static final String OCCURRENCE =
            "test/node#epoch0/region/PRODUCER#1";
    private static final String ROOT = "<example.Producer: void run()>";
    private static final String FIELD =
            "<example.Producer: int generation>";
    private static final String OUTPUT_PORT = "PRODUCER.out.generation";
    private static final String BINDING = "CAPTURE.GENERATION";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;
    private Path results;

    @Before
    public void rememberProperties() throws Exception {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
        installFakeEngine();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    /**
     * The demanded output boundary is complete after the first captured
     * version - the exact condition that used to publish a terminal - and the
     * occurrence stays open, so the second version of the same relation is
     * still recorded and reaches the result.
     */
    @Test
    public void laterVersionOfOneRelationOutlivesTheFirstCapturedVersion()
            throws Exception {
        load("later-version");
        Producer receiver = new Producer();
        Object active = activate(receiver, 91L);

        ConcolicRegionRuntime.recordFieldWriteStateOutput(
                BINDING, receiver, Integer.valueOf(1));
        assertTrue("the first version already completes the demanded output "
                        + "boundary, which is what used to finish here",
                demandedOutputRelationComplete(active));
        assertTrue("TERM-1: a captured version is not a terminal",
                live(91L));
        assertFalse(finished(active));

        ConcolicRegionRuntime.recordFieldWriteStateOutput(
                BINDING, receiver, Integer.valueOf(2));
        assertEquals(2, outputCaptures(active).size());

        ConcolicRegionRuntime.exitRegion(91L, null, "");
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        JsonObject result = onlyResult();
        assertEquals(TASK, result.get("taskId").getAsString());
        assertEquals("NORMAL", result.get("exitKind").getAsString());
        JsonArray captures = result.getAsJsonArray("outputCaptures");
        assertEquals(2, captures.size());
        assertEquals(1, captures.get(0).getAsJsonObject()
                .get("outputOccurrence").getAsInt());
        assertEquals(2, captures.get(1).getAsJsonObject()
                .get("outputOccurrence").getAsInt());
    }

    /**
     * A throw after a captured output is still the case terminal.  The
     * output-only completion published {@code NORMAL} for an occurrence that
     * really threw later, which is exactly the case TERM-1 forbids.
     */
    @Test
    public void throwAfterACapturedOutputIsStillTheCaseTerminal()
            throws Exception {
        load("throw-terminal");
        Producer receiver = new Producer();
        Object active = activate(receiver, 92L);

        ConcolicRegionRuntime.recordFieldWriteStateOutput(
                BINDING, receiver, Integer.valueOf(1));
        assertTrue(demandedOutputRelationComplete(active));
        assertTrue(live(92L));

        ConcolicRegionRuntime.throwRegion(92L,
                new IllegalStateException("later failure"));
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        JsonObject result = onlyResult();
        assertEquals("THROW", result.get("exitKind").getAsString());
        assertEquals(IllegalStateException.class.getName(),
                result.get("exceptionType").getAsString());
    }

    private JsonObject onlyResult() throws Exception {
        List<String> lines = Files.readAllLines(results,
                StandardCharsets.UTF_8);
        assertEquals(lines.toString(), 1, lines.size());
        return new JsonParser().parse(lines.get(0)).getAsJsonObject();
    }

    private void load(String name) throws Exception {
        Path plan = folder.newFile(name + "-plan.jsonl").toPath();
        Files.write(plan, (task() + "\n").getBytes(StandardCharsets.UTF_8));
        results = folder.getRoot().toPath().resolve(name + "-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(java.util.Collections.singletonList(TASK),
                ConcolicRegionRuntime.campaignTaskIdsForTests());
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", "test/node#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.PRODUCER");
        task.addProperty("regionId", "PRODUCER");
        task.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Producer.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "test/node#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        task.add("outputClosure", outputClosure());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    /**
     * One field-write relation whose recorded value is a closed constant, so
     * the capture needs no VM expression and the test states only what the
     * terminal rule does.
     */
    private static JsonObject outputClosure() {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", BINDING);
        capture.addProperty("captureKind", "FIELD_WRITE_STATE");
        capture.addProperty("outputPort", OUTPUT_PORT);
        capture.addProperty("outputCell", FIELD);
        capture.addProperty("fieldSignature", FIELD);
        capture.addProperty("javaType", "int");
        capture.addProperty("recordedPrimitiveValue", "7");
        capture.addProperty("definitionMethod", ROOT);
        capture.addProperty("definitionUnitIndex", 2);
        capture.addProperty("definitionCompletionSeq", 2L);
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");
        capture.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        capture.addProperty("outputSiteId", "FIELD_WRITE:" + ROOT + "#u2");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);

        JsonObject output = new JsonObject();
        output.addProperty("portId", OUTPUT_PORT);
        output.addProperty("cell", FIELD);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", OUTPUT_PORT);
        slice.addProperty("outputCell", FIELD);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(ROOT);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);

        JsonObject owner = new JsonObject();
        owner.addProperty("relationKey", "RELATION.PRODUCER");
        owner.addProperty("regionId", "PRODUCER");
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", owner);
        JsonArray members = new JsonArray();
        members.add(member);
        closure.add("members", members);
        return closure;
    }

    private static Object activate(Producer receiver, long token)
            throws Exception {
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
        Object active = constructor.newInstance(token, task, receiver,
                Thread.currentThread());
        // What admission would have confirmed: this activation ran on the
        // source its address anchors.  Without it every terminal below is
        // released as an unaddressed candidate before it can be judged.
        Field observedSourceKeys = activeType.getDeclaredField(
                "observedSourceKeys");
        observedSourceKeys.setAccessible(true);
        @SuppressWarnings("unchecked")
        java.util.Set<String> observed =
                (java.util.Set<String>) observedSourceKeys.get(active);
        observed.add("test/node#epoch0");
        activeRegions().put(Long.valueOf(token), active);
        currentToken().set(Long.valueOf(token));
        ConcolicRegionRuntime.beginLiveSelectedRegion();
        return active;
    }

    @SuppressWarnings("unchecked")
    private static Map<Long, Object> activeRegions() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField("ACTIVE");
        field.setAccessible(true);
        return (Map<Long, Object>) field.get(null);
    }

    private static boolean live(long token) throws Exception {
        return activeRegions().containsKey(Long.valueOf(token));
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> outputCaptures(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("outputCaptures");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static boolean demandedOutputRelationComplete(Object active)
            throws Exception {
        Method method = active.getClass().getDeclaredMethod(
                "demandedOutputRelationComplete");
        method.setAccessible(true);
        return (Boolean) method.invoke(active);
    }

    private static boolean finished(Object active) throws Exception {
        Field field = active.getClass().getDeclaredField("finished");
        field.setAccessible(true);
        return ((java.util.concurrent.atomic.AtomicBoolean)
                field.get(active)).get();
    }

    private static void installFakeEngine() throws Exception {
        Object engine = newEngine();
        bind(engine, "finishRegion", FakeVm.class.getDeclaredMethod("finish"));
        bind(engine, "pausePathCondition",
                FakeVm.class.getDeclaredMethod("pause"));
        bind(engine, "resumePathCondition",
                FakeVm.class.getDeclaredMethod("resume"));
        install(engine);
    }

    /** A stock EngineApi with every VM method absent, for selective binding. */
    private static Object newEngine() throws Exception {
        Constructor<?> constructor = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$EngineApi")
                .getDeclaredConstructor();
        constructor.setAccessible(true);
        return constructor.newInstance();
    }

    private static void bind(Object engine, String name, Method target)
            throws Exception {
        Field field = engine.getClass().getDeclaredField(name);
        field.setAccessible(true);
        field.set(engine, target);
    }

    private static void install(Object engine) throws Exception {
        Field engineApi = ConcolicRegionRuntime.class.getDeclaredField(
                "engineApi");
        engineApi.setAccessible(true);
        engineApi.set(null, engine);
    }

    private static void restore(String property, String value) {
        if (value == null) System.clearProperty(property);
        else System.setProperty(property, value);
    }

    /** Only the calls a constant field-write relation actually makes. */
    public static final class FakeVm {
        public static void pause() { }

        public static void resume() { }

        public static String finish() {
            return "{\"schemaVersion\":1,"
                    + "\"kind\":\"CONCOLIC_REGION_SUMMARY\"}";
        }
    }

    private static final class Producer {
        @SuppressWarnings("unused")
        private int generation;
    }
}
