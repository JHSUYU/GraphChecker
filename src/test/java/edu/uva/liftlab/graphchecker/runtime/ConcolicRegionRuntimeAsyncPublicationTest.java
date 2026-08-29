package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
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
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Response completion owns VM read-out, but not JSON result publication. */
public class ConcolicRegionRuntimeAsyncPublicationTest {
    private static final String TASK = "TASK.response-publication";
    private static final String ROOT =
            "<example.Server: example.Response serve()>";
    private static final String SOURCE = "test/server#epoch0";
    private static final String OCCURRENCE =
            SOURCE + "/region/SERVER#1";

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
        FakeVm.outputObservationBuilt = false;
        FakeVm.rawReadOutBuilt = false;
        FakeVm.finishCalled = false;
        FakeVm.workloadSessionClosed = false;
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.awaitSelectedResultPublications();
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    @Test
    public void responseReturnsBeforeDecodeAndBarrierWaitsForResult()
            throws Exception {
        Path resultFile = loadCampaign();
        activateResponseCandidate(71L);
        installFakeEngine();

        CountDownLatch decodeStarted = new CountDownLatch(1);
        CountDownLatch releaseDecode = new CountDownLatch(1);
        ConcolicRegionRuntime.setBeforePublicationDecodeForTests(
                () -> {
                    decodeStarted.countDown();
                    await(releaseDecode);
                });

        // The publication thread blocks before Gson sees the raw ledger.  If
        // response completion performed decode itself, this call could not
        // return and the assertions below would be unreachable.
        assertTrue(ConcolicRegionRuntime.completeResponseHandoff());
        assertTrue(decodeStarted.await(2, TimeUnit.SECONDS));
        assertFalse(Files.exists(resultFile));
        assertFalse("the closed VM occurrence must not block the next root "
                + "while JSON publication is pending", candidateLive());
        assertFalse("publication is not durable yet", occurrenceClaimed());

        CountDownLatch barrierReturned = new CountDownLatch(1);
        Thread barrier = new Thread(() -> {
            ConcolicRegionRuntime.awaitSelectedResultPublications();
            barrierReturned.countDown();
        });
        barrier.start();
        assertFalse(barrierReturned.await(150, TimeUnit.MILLISECONDS));

        releaseDecode.countDown();
        assertTrue(barrierReturned.await(5, TimeUnit.SECONDS));
        assertTrue(Files.exists(resultFile));
        String row = new String(Files.readAllBytes(resultFile),
                StandardCharsets.UTF_8);
        assertTrue(row.contains("\"sessionEventLedger\""));
        assertTrue(row.contains("\"engineSummary\""));
        assertTrue(row.contains("CAPTURE.state"));
        assertTrue(row.contains("OUTPUT_BEFORE_RAW"));
        assertFalse(candidateLive());
        assertTrue(occurrenceClaimed());
    }

    @Test
    public void workloadCloseIsThePublicationBarrier() throws Exception {
        Path resultFile = loadCampaign();
        activateResponseCandidate(73L);
        installFakeEngine();

        CountDownLatch decodeStarted = new CountDownLatch(1);
        CountDownLatch releaseDecode = new CountDownLatch(1);
        ConcolicRegionRuntime.setBeforePublicationDecodeForTests(() -> {
            decodeStarted.countDown();
            await(releaseDecode);
        });

        assertTrue(ConcolicRegionRuntime.completeResponseHandoff());
        assertTrue(decodeStarted.await(2, TimeUnit.SECONDS));

        CountDownLatch closeReturned = new CountDownLatch(1);
        Thread close = new Thread(() -> {
            assertTrue(ConcolicRegionRuntime.closeWorkloadSession().isEmpty());
            closeReturned.countDown();
        });
        close.start();
        assertFalse(closeReturned.await(150, TimeUnit.MILLISECONDS));
        assertFalse(FakeVm.workloadSessionClosed);

        releaseDecode.countDown();
        assertTrue(closeReturned.await(5, TimeUnit.SECONDS));
        // Direct/ordinary-JDK mode has no native workload session.  Its close
        // is still the publication durability boundary, without inventing a
        // native close call.
        assertFalse(FakeVm.workloadSessionClosed);
        assertTrue(Files.exists(resultFile));
    }

    @Test
    public void sharedWriterVersionKeepsItsMaterializedActivation()
            throws Exception {
        loadCampaign();
        activateResponseCandidate(79L);
        Object active = active(79L);
        Field ordinal = active.getClass().getDeclaredField(
                "activationOrdinal");
        ordinal.setAccessible(true);
        ordinal.setInt(active, 2);

        JsonObject envelope = new JsonObject();
        JsonArray versions = new JsonArray();
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", 101L);
        version.addProperty("writerContextId", 9L);
        version.addProperty("taskId", TASK);
        version.addProperty("regionId", "SERVER");
        versions.add(version);
        envelope.add("versions", versions);
        JsonArray reads = new JsonArray();
        JsonObject read = new JsonObject();
        read.addProperty("readEventId", 102L);
        read.addProperty("readerContextId", 9L);
        read.addProperty("regionId", "SERVER");
        reads.add(read);
        envelope.add("reads", reads);

        Method remember = ConcolicRegionRuntime.class.getDeclaredMethod(
                "rememberContextActivation", long.class,
                active.getClass());
        remember.setAccessible(true);
        remember.invoke(null, 9L, active);
        Method annotate = ConcolicRegionRuntime.class.getDeclaredMethod(
                "addActivationIdentity", JsonObject.class,
                active.getClass());
        annotate.setAccessible(true);
        JsonObject writeOnly = envelope.deepCopy();
        writeOnly.getAsJsonArray("reads").remove(0);
        annotate.invoke(null, writeOnly, null);
        assertEquals(OCCURRENCE + "#a2", writeOnly
                .getAsJsonArray("versions").get(0).getAsJsonObject()
                .get("writerOccurrenceId").getAsString());

        annotate.invoke(null, envelope, active);
        assertEquals(OCCURRENCE + "#a2", version.get(
                "writerOccurrenceId").getAsString());
        assertEquals(OCCURRENCE + "#a2", read.get(
                "readerOccurrenceId").getAsString());

        JsonObject later = envelope.deepCopy();
        later.getAsJsonArray("reads").remove(0);
        annotate.invoke(null, later, null);
        assertEquals(OCCURRENCE + "#a2", later.getAsJsonArray("versions")
                .get(0).getAsJsonObject().get("writerOccurrenceId")
                .getAsString());
    }

    @Test
    public void incompleteReplayReopensCandidateBeforeDecode() throws Exception {
        Path resultFile = loadCampaign(incompleteReplayTask());
        activateResponseCandidate(74L);
        installFakeEngine();

        CountDownLatch decodeStarted = new CountDownLatch(1);
        ConcolicRegionRuntime.setBeforePublicationDecodeForTests(
                decodeStarted::countDown);

        assertTrue(ConcolicRegionRuntime.completeResponseHandoff());
        assertFalse(decodeStarted.await(150, TimeUnit.MILLISECONDS));
        assertFalse(candidateLive());
        assertFalse(occurrenceClaimed());
        assertFalse(FakeVm.outputObservationBuilt);
        assertFalse(FakeVm.rawReadOutBuilt);
        assertTrue(FakeVm.finishCalled);
        assertTrue(Files.exists(resultFile));
        String row = new String(Files.readAllBytes(resultFile),
                StandardCharsets.UTF_8);
        assertTrue(row.contains("\"skipKind\":\""
                + ConcolicRegionRuntime.SKIP_REPLAY_PREFIX_UNMATCHED + "\""));
        assertFalse(row.contains("\"sessionEventLedger\""));
    }

    @Test
    public void terminalRejectsUnappliedModelAssignmentByKey()
            throws Exception {
        Path resultFile = loadCampaign(unappliedModelAssignmentTask());
        activateResponseCandidate(75L);
        completeReplayProgress(75L, ROOT + "#u8", 1, false);
        installFakeEngine();

        assertTrue(ConcolicRegionRuntime.completeResponseHandoff());
        assertTrue(Files.exists(resultFile));
        String row = new String(Files.readAllBytes(resultFile),
                StandardCharsets.UTF_8);
        assertTrue(row, row.contains("\"skipKind\":\""
                + ConcolicRegionRuntime.SKIP_UNAPPLIED_MODEL_ASSIGNMENT
                + "\""));
        assertTrue(row, row.contains("MODEL.unused"));
        assertFalse(occurrenceClaimed());
        assertFalse(FakeVm.outputObservationBuilt);
    }

    @Test
    public void abnormalPublicationReleasesCandidate() throws Exception {
        Path resultFile = loadCampaign();
        activateResponseCandidate(72L);
        installFakeEngine();
        ConcolicRegionRuntime.setBeforePublicationDecodeForTests(
                () -> { throw new IllegalStateException("decode refused"); });

        assertTrue(ConcolicRegionRuntime.completeResponseHandoff());
        ConcolicRegionRuntime.awaitSelectedResultPublications();

        assertFalse(candidateLive());
        assertFalse(occurrenceClaimed());
        assertFalse(Files.exists(resultFile));
    }

    private Path loadCampaign() throws Exception {
        return loadCampaign(task());
    }

    private Path loadCampaign(JsonObject task) throws Exception {
        Path plan = folder.newFile("execution_task_plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        Path results = folder.getRoot().toPath().resolve("results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertTrue(ConcolicRegionRuntime.campaignTaskIdsForTests()
                .contains(TASK));
        return results;
    }

    private static JsonObject incompleteReplayTask() {
        JsonObject task = task();
        addUnusedModelAssignment(task);
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "ConstExpr");
        predicate.addProperty("_java_type", "Z");
        predicate.addProperty("_exp", "Y_Z_1");
        BranchWitness source = BranchWitness.vmPc(
                ROOT + "#u7", ROOT, 7, 1, true, predicate, 0,
                new JsonObject());
        task.add("replayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), source).toJson());
        return task;
    }

    private static JsonObject unappliedModelAssignmentTask() {
        JsonObject task = task();
        addUnusedModelAssignment(task);

        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "ConstExpr");
        predicate.addProperty("_java_type", "Z");
        predicate.addProperty("_exp", "Y_Z_1");
        BranchWitness source = BranchWitness.vmPc(
                ROOT + "#u8", ROOT, 8, 1, true, predicate, 0,
                new JsonObject());
        task.add("replayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), source).toJson());
        return task;
    }

    private static void addUnusedModelAssignment(JsonObject task) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.unused");
        assignment.addProperty("engineSymbol", "M_I_unused");
        assignment.addProperty("inputSymbol", "INPUT.unused");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "41");
        JsonArray assignments = new JsonArray();
        assignments.add(assignment);
        task.add("modelAssignments", assignments);
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL.SERVER");
        task.addProperty("sourceKey", SOURCE);
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.SERVER");
        task.addProperty("regionId", "SERVER");
        task.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
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
        task.add("branches", new JsonArray());
        task.add("edgeBindings", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);

        JsonObject handoff = new JsonObject();
        handoff.addProperty("schemaVersion", 2);
        handoff.addProperty("kind", CommunicationHandoffSpec.KIND);
        handoff.addProperty("role", CommunicationHandoffSpec.ROLE_EXPORT);
        handoff.addProperty("portId", "XCH.response.resp.keyId");
        handoff.addProperty("handoffLeafPath", "resp/keyId");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("javaType", "int");
        handoff.addProperty("exchangeSiteKey", "XCH.response");
        handoff.addProperty("componentOfPortId", "XCH.response.resp");
        handoff.addProperty("encodingAuthority", "TEST_RESPONSE_PATH_V1");
        handoff.addProperty("definitionMethod", ROOT);
        JsonArray path = new JsonArray();
        JsonObject field = new JsonObject();
        field.addProperty("kind", "FIELD");
        field.addProperty("declaration", "<example.Response: int keyId>");
        path.add(field);
        handoff.add("handoffPath", path);
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add(CommunicationHandoffSpec.FIELD, handoffs);
        task.add("outputClosure", outputClosure());
        return task;
    }

    private static JsonObject outputClosure() {
        String fieldSignature = "<" + Carrier.class.getName()
                + ": int state>";
        String outputPort = "SERVER.out.state";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.state");
        capture.addProperty("captureKind", "REGION_EXIT_FIELD");
        capture.addProperty("outputPort", outputPort);
        capture.addProperty("outputCell", fieldSignature);
        capture.addProperty("fieldSignature", fieldSignature);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("state");
        capture.add("fieldPath", fieldPath);
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", "OWNER");

        JsonObject output = new JsonObject();
        output.addProperty("portId", outputPort);
        output.addProperty("cell", fieldSignature);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", outputPort);
        slice.addProperty("outputCell", fieldSignature);
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

        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.SERVER");
        producer.addProperty("regionId", "SERVER");
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        JsonArray members = new JsonArray();
        members.add(member);
        closure.add("members", members);
        return closure;
    }

    private static void activateResponseCandidate(long token)
            throws Exception {
        Object configuration = configuration();
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, TASK);

        Field candidateLive = configuration.getClass().getDeclaredField(
                "candidateLive");
        candidateLive.setAccessible(true);
        ((boolean[]) candidateLive.get(configuration))[0] = true;

        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, new Object(),
                Thread.currentThread());

        Field sources = activeType.getDeclaredField("observedSourceKeys");
        sources.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> observed = (Set<String>) sources.get(active);
        observed.add(SOURCE);

        Field owners = activeType.getDeclaredField("fieldAccessOwners");
        owners.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<String, Object> fieldOwners =
                (Map<String, Object>) owners.get(active);
        fieldOwners.put("OWNER", new Carrier());

        Class<?> terminalType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$DeferredTerminal");
        Constructor<?> terminal = terminalType.getDeclaredConstructor(
                String.class, String.class, Object.class);
        terminal.setAccessible(true);
        Field responseTerminal = activeType.getDeclaredField(
                "responseTerminal");
        responseTerminal.setAccessible(true);
        responseTerminal.set(active,
                terminal.newInstance("NORMAL", "", new Object()));

        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions =
                (Map<Long, Object>) activeRegions.get(null);
        regions.put(token, active);
        currentToken().set(token);
        ConcolicRegionRuntime.beginLiveSelectedRegion();
    }

    private static void completeReplayProgress(
            long token, String siteId, int occurrence, boolean outcome)
            throws Exception {
        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions =
                (Map<Long, Object>) activeRegions.get(null);
        Object active = regions.get(token);
        Field replayProgress = active.getClass().getDeclaredField(
                "replayProgress");
        replayProgress.setAccessible(true);
        Object progress = replayProgress.get(active);
        Method observe = progress.getClass().getDeclaredMethod(
                "observe", String.class, int.class, boolean.class);
        observe.setAccessible(true);
        assertTrue((Boolean) observe.invoke(
                progress, siteId, occurrence, outcome));
    }

    private static void installFakeEngine() throws Exception {
        Object engine = newEngine();
        bind(engine, "closeWorkloadSession", fake("closeWorkloadSession"));
        bind(engine, "getExpression", fake("expression", Object.class));
        bind(engine, "getFieldExpression", fake("fieldExpression",
                Object.class, String.class, String.class, String.class,
                Object.class));
        bind(engine, "finishRegion", fake("finish"));
        bind(engine, "pausePathCondition", fake("pause"));
        bind(engine, "resumePathCondition", fake("resume"));
        bind(engine, "cleanupEnd", fake("cleanup"));
        bind(engine, "selectField", fake("selectField", Object.class,
                String.class, String.class, String.class));
        bind(engine, "selectElement", fake("selectElement", Object.class,
                int.class));
        bind(engine, "selectMap", fake("selectMap", Object.class));
        bind(engine, "fieldVersions", fake("fieldVersions", Object.class,
                String.class, String.class, String.class));
        bind(engine, "elementVersions", fake("elementVersions", Object.class,
                int.class));
        bind(engine, "mapVersions", fake("mapVersions", Object.class));
        bind(engine, "eventLedger", fake("eventLedger"));
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

    private static Method fake(String name, Class<?>... parameters)
            throws Exception {
        return FakeVm.class.getDeclaredMethod(name, parameters);
    }

    private static Object configuration() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "configuration");
        field.setAccessible(true);
        return field.get(null);
    }

    private static Object active(long token) throws Exception {
        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions =
                (Map<Long, Object>) activeRegions.get(null);
        return regions.get(token);
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    private static boolean candidateLive() throws Exception {
        Field field = configuration().getClass().getDeclaredField(
                "candidateLive");
        field.setAccessible(true);
        return ((boolean[]) field.get(configuration()))[0];
    }

    private static boolean occurrenceClaimed() throws Exception {
        Field field = configuration().getClass().getDeclaredField(
                "occurrenceClaimed");
        field.setAccessible(true);
        return ((boolean[]) field.get(configuration()))[0];
    }

    private static void await(CountDownLatch latch) {
        boolean interrupted = false;
        while (true) {
            try {
                latch.await();
                break;
            } catch (InterruptedException ignored) {
                interrupted = true;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static void restore(String property, String value) {
        if (value == null) {
            System.clearProperty(property);
        } else {
            System.setProperty(property, value);
        }
    }

    /** Ordinary-JDK methods used only through the runtime's reflective API. */
    public static final class FakeVm {
        private static volatile boolean outputObservationBuilt;
        private static volatile boolean rawReadOutBuilt;
        private static volatile boolean finishCalled;
        private static volatile boolean workloadSessionClosed;

        public static void pause() { }
        public static void resume() { }
        public static void cleanup() { }
        public static long closeWorkloadSession() {
            workloadSessionClosed = true;
            return 0L;
        }
        public static String finish() {
            finishCalled = true;
            return "{}";
        }
        public static String expression(Object ignored) { return "{}"; }
        public static String fieldExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor, Object value) {
            outputObservationBuilt = true;
            return "{\"expression\":{\"_type\":\"ConstExpr\","
                    + "\"_java_type\":\"I\",\"_exp\":\"Y_I_7\"}}";
        }
        public static long selectField(Object owner, String declaringClass,
                                       String fieldName, String descriptor) {
            return 1L;
        }
        public static long selectElement(Object array, int index) {
            return 1L;
        }
        public static long selectMap(Object map) { return 1L; }
        public static String fieldVersions(
                Object owner, String declaringClass, String fieldName,
                String descriptor) {
            rawReadOutBuilt = true;
            return "{}";
        }
        public static String elementVersions(Object array, int index) {
            rawReadOutBuilt = true;
            return "{}";
        }
        public static String mapVersions(Object map) {
            rawReadOutBuilt = true;
            return "{}";
        }
        public static String eventLedger() {
            rawReadOutBuilt = true;
            String order = outputObservationBuilt
                    ? "OUTPUT_BEFORE_RAW" : "RAW_BEFORE_OUTPUT";
            return "{\"schemaVersion\":1,"
                    + "\"kind\":\"SESSION_EVENT_LEDGER\","
                    + "\"open\":true,\"recording\":true,"
                    + "\"truncated\":false,"
                    + "\"domainSaturated\":false,"
                    + "\"partialOrder\":true,\"acyclic\":true,"
                    + "\"events\":[],\"order\":[],"
                    + "\"testOrder\":\"" + order + "\"}";
        }
    }

    private static final class Carrier {
        @SuppressWarnings("unused")
        private int state = 7;
    }
}
