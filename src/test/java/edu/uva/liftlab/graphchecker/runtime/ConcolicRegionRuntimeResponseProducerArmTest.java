package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
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
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Exact live-exchange admission of a selected RPC response producer. */
public class ConcolicRegionRuntimeResponseProducerArmTest {

    private static final String CONSUMER_TASK = "TASK.response-consumer";
    private static final String PRODUCER_TASK = "TASK.response-producer";
    private static final String PRODUCER_TASK_B = "TASK.response-producer-b";
    private static final String CONSUMER_OCCURRENCE =
            "test/client#epoch0/region/CLIENT#1";
    private static final String PRODUCER_OCCURRENCE =
            "test/server#epoch0/region/SERVER#7";
    private static final String PRODUCER_OCCURRENCE_B =
            "test/server-b#epoch0/region/SERVER_B#3";
    private static final String CONSUMER_ROOT =
            "<example.Client: void call()>";
    private static final String PRODUCER_ROOT =
            "<example.Server: example.Response serve()>";
    private static final String PRODUCER_ROOT_B =
            "<example.Server: example.Response serveB()>";
    private static final String PORT = "XCH.response.resp.keyId";
    private static final String PORT_B = "XCH.response-b.resp.keyId";
    private static final String EFFECT_BINDING =
            "CAPTURE.response-producer.effect";
    private static final String EFFECT_PORT = "SERVER.out.keyId";

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

    @Test
    public void responseProducerNeedsTheSelectedCallersLiveExchangeArm()
            throws Exception {
        loadCampaign();

        // An earlier invocation of the same server method is not the selected
        // producer merely because its root is compatible.
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                PRODUCER_TASK, PRODUCER_ROOT, server("test/server"),
                new Object[0]));

        activate(CONSUMER_TASK, 41L);
        ConcolicRegionRuntime.prepareResponseHandoff(PORT);
        ConcolicRegionRuntime.observeExchangeLeg("SEND", "TEST_RPC",
                "exchange-selected", "REQUEST");
        clearCurrentToken();

        // A different delivery cannot consume the arm.
        ConcolicRegionRuntime.observeExchangeLeg("RECEIVE", "TEST_RPC",
                "exchange-other", "REQUEST");
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                PRODUCER_TASK, PRODUCER_ROOT, server("test/server"),
                new Object[0]));

        // The exact request delivery claims it, after which this producer task
        // (and no value tuple) is authorized.
        ConcolicRegionRuntime.observeExchangeLeg("RECEIVE", "TEST_RPC",
                "exchange-selected", "REQUEST");
        assertEquals(PRODUCER_TASK,
                ConcolicRegionRuntime.admitCampaignTaskForTests(PRODUCER_TASK,
                        PRODUCER_ROOT, server("test/server"),
                        new Object[0]));
    }

    /**
     * A response producer nothing armed says so, instead of saying nothing.
     *
     * <p>HDFS-11741 campaign-takeover-16 and -19 lost a whole task this way:
     * the NameNode's {@code sendHeartbeat} and {@code getBlockKeys} regions
     * are response producers, their callers were not admitted, and this gate
     * refused every compatible activation without noting a candidate.  With
     * no candidate noted the run published no row at all, so the campaign
     * reported {@code REPLAY_TASK_WITHOUT_RESULT} and named no reason -- and
     * the reason was two layers away, in the caller.</p>
     */
    @Test
    public void anUnarmedResponseProducerPublishesANamedSkip()
            throws Exception {
        loadCampaign();

        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                PRODUCER_TASK, PRODUCER_ROOT, server("test/server"),
                new Object[0]));

        ConcolicRegionRuntime.publishRunTotals();

        String reason = "";
        for (String line : Files.readAllLines(Paths.get(
                System.getProperty("causynth.concolic.results")),
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = new JsonParser().parse(line).getAsJsonObject();
            if (!"CONCOLIC_REGION_SKIPPED".equals(
                    row.get("event").getAsString())
                    || !PRODUCER_TASK.equals(
                    row.get("taskId").getAsString())) {
                continue;
            }
            reason = row.get("reason").getAsString();
        }
        assertTrue(reason, reason.contains(
                "served no request this campaign armed as its response "
                        + "producer"));
    }

    @Test
    public void eachResponseCutArmsOnlyItsOwnProducer() throws Exception {
        loadTwoProducerCampaign();

        activate(CONSUMER_TASK, 47L);
        ConcolicRegionRuntime.prepareResponseHandoff(PORT_B);
        ConcolicRegionRuntime.observeExchangeLeg("SEND", "TEST_RPC",
                "exchange-b", "REQUEST");
        clearCurrentToken();
        ConcolicRegionRuntime.observeExchangeLeg("RECEIVE", "TEST_RPC",
                "exchange-b", "REQUEST");

        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                PRODUCER_TASK, PRODUCER_ROOT, server("test/server"),
                new Object[0]));
        assertEquals(PRODUCER_TASK_B,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        PRODUCER_TASK_B, PRODUCER_ROOT_B,
                        server("test/server-b"),
                        new Object[0]));
    }

    @Test
    public void manyMissingResponseCandidatesPublishOneTerminalGap()
            throws Exception {
        loadCampaign();
        Object active = activate(CONSUMER_TASK, 42L);

        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());

        assertEquals(0, handoffGaps(active).size());
        assertEquals(1, pendingHandoffGaps(active).size());
        flushPendingHandoffGaps(active);

        List<JsonObject> gaps = handoffGaps(active);
        assertEquals(1, gaps.size());
        assertEquals("RPC_HANDOFF_UNKNOWN_HANDLE",
                gaps.get(0).get("reason").getAsString());
        assertFalse(gaps.get(0).get("detail").getAsString().isEmpty());
    }

    @Test
    public void missingCandidatesDisappearAfterSelectedPortAttaches()
            throws Exception {
        loadCampaign();
        Object active = activate(CONSUMER_TASK, 43L);

        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        assertEquals(1, pendingHandoffGaps(active).size());

        markHandoffSatisfied(active);
        flushPendingHandoffGaps(active);

        assertEquals(0, handoffGaps(active).size());
        assertEquals(0, pendingHandoffGaps(active).size());
    }

    @Test
    public void laterResponseExchangeIsConcreteAfterSelectedPortAttached()
            throws Exception {
        loadCampaign();
        Object active = activate(CONSUMER_TASK, 44L);

        markHandoffSatisfied(active);

        // A long-lived caller can execute this static attach hook again
        // before its bounded outer loop is cut.  Once the task's selected
        // response component was attached, a later unarmed exchange is not a
        // second required symbolic input.
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());

        assertEquals(0, handoffGaps(active).size());
    }

    @Test
    public void responseHandoffStateIsIndependentAcrossFreshRegions()
            throws Exception {
        loadCampaign();
        Object first = activate(CONSUMER_TASK, 45L);
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        markHandoffSatisfied(first);
        flushPendingHandoffGaps(first);

        Object second = activate(CONSUMER_TASK, 46L);
        ConcolicRegionRuntime.attachCommunicationFieldPath(PORT,
                new Response());
        flushPendingHandoffGaps(second);

        assertEquals(0, handoffGaps(first).size());
        assertEquals(1, handoffGaps(second).size());
    }

    @Test
    public void successfulVmHandoffStartsReceiverBranchRecording()
            throws Exception {
        loadCampaign();
        Object active = activate(CONSUMER_TASK, 48L);
        assertFalse(pathRecordingStarted(active));

        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "RPC_VALUE");
        Method accept = ConcolicRegionRuntime.class.getDeclaredMethod(
                "acceptVmHandoffExpression", active.getClass(),
                CommunicationHandoffSpec.class, long.class, long.class,
                JsonElement.class, String.class, String.class);
        accept.setAccessible(true);
        accept.invoke(null, active, communicationHandoff(active), 17L, 18L,
                expression, PRODUCER_TASK, PRODUCER_OCCURRENCE);

        assertTrue(pathRecordingStarted(active));
        assertEquals(1, vmHandoffs(active).size());
    }

    private void loadCampaign() throws Exception {
        JsonObject consumer = task(CONSUMER_TASK, "CLIENT",
                CONSUMER_OCCURRENCE, CONSUMER_ROOT, Object.class.getName(),
                handoff(false));
        JsonObject edge = new JsonObject();
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("fromOutputPort", PORT);
        edge.addProperty("toInputPort", PORT);
        JsonArray edges = new JsonArray();
        edges.add(edge);
        consumer.add("edgeBindings", edges);

        JsonObject producer = task(PRODUCER_TASK, "SERVER",
                PRODUCER_OCCURRENCE, PRODUCER_ROOT, Server.class.getName(),
                handoff(true));
        Path plan = folder.newFile("execution_task_plan.jsonl").toPath();
        Files.write(plan, (consumer + "\n" + producer + "\n").getBytes(
                StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                CONSUMER_TASK + "," + PRODUCER_TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
        assertEquals(2,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    /**
     * README {@code RPC-1}: the producer's interaction row names the exact VM
     * export it published.
     *
     * <p>Without it the only way from a consumer's handoff reference back to
     * its producer case is a Java-side count of how often each case observed
     * the port, which is a pairing decision and has no answer at all when two
     * cases observed it equally often.  The exact export event is the pairing
     * the VM already made.</p>
     */
    @Test
    public void communicationEffectNamesTheExportItPublished()
            throws Exception {
        loadProducerCaptureCampaign();
        Object active = activate(PRODUCER_TASK, 71L);

        rememberExport(active, EFFECT_PORT, 41L);
        ConcolicRegionRuntime.recordCommunicationEffect(EFFECT_BINDING);

        JsonObject row = onlyOutputCapture(active);
        assertEquals("COMMUNICATION_EFFECT",
                row.get("interactionKind").getAsString());
        assertEquals(41L, row.get("exportEventId").getAsLong());
    }

    /**
     * An occurrence that exported nothing at this port stamps no event, so a
     * missing export reads as an absence rather than as some other export.
     */
    @Test
    public void communicationEffectWithoutAnExportNamesNoEvent()
            throws Exception {
        loadProducerCaptureCampaign();
        Object active = activate(PRODUCER_TASK, 72L);

        rememberExport(active, "XCH.other.resp.keyId", 41L);
        ConcolicRegionRuntime.recordCommunicationEffect(EFFECT_BINDING);

        JsonObject row = onlyOutputCapture(active);
        assertFalse(row.toString(), row.has("exportEventId"));
    }

    /**
     * Versions past the bounded capacity are one named structural gap on the
     * result, not a sentence in {@code unresolvedInputs} for a later layer to
     * parse back.  README's resource rule: truncation of selected evidence is
     * named, never read as the evidence being absent.
     */
    @Test
    public void versionsPastTheBoundedCapacityAreOneStructuralGap()
            throws Exception {
        loadProducerCaptureCampaign();
        Object active = activate(PRODUCER_TASK, 73L);

        int capacity = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
        for (int entry = 0; entry < capacity + 3; entry++) {
            ConcolicRegionRuntime.recordCommunicationEffect(EFFECT_BINDING);
        }

        assertEquals(capacity, outputCaptures(active).size());
        Map<String, JsonObject> gaps = outputVersionGaps(active);
        assertEquals(1, gaps.size());
        JsonObject gap = gaps.get(EFFECT_BINDING);
        assertEquals("OUTPUT_VERSION_ALIGNMENT_GAP",
                gap.get("kind").getAsString());
        assertEquals("BOUNDED_OUTPUT_VERSION_CAPACITY_V1",
                gap.get("authority").getAsString());
        assertEquals(1, gap.get("schemaVersion").getAsInt());
        assertEquals(EFFECT_BINDING,
                gap.get("captureBindingId").getAsString());
        assertEquals(capacity, gap.get("versionCapacity").getAsInt());
        assertEquals(capacity + 3, gap.get("versionsObserved").getAsInt());
        assertTrue(gap.get("reason").getAsString(), gap.get("reason")
                .getAsString().contains("bounded output version capacity"));
        // The prose notice the importer used to parse is gone.
        for (String unresolved : unresolvedInputs(active)) {
            assertFalse(unresolved,
                    unresolved.contains("bounded output version capacity"));
        }
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> outputCaptures(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("outputCaptures");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, JsonObject> outputVersionGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "outputVersionGaps");
        field.setAccessible(true);
        return (Map<String, JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static Set<String> unresolvedInputs(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("unresolved");
        field.setAccessible(true);
        return (Set<String>) field.get(active);
    }

    private void loadProducerCaptureCampaign() throws Exception {
        JsonObject producer = task(PRODUCER_TASK, "SERVER",
                PRODUCER_OCCURRENCE, PRODUCER_ROOT, Server.class.getName(),
                handoff(true));
        producer.addProperty("goalKind", "OUTPUT_RELATION_CLOSURE");
        producer.add("outputClosure", communicationEffectClosure());
        Path plan = folder.newFile("producer_capture_plan.jsonl").toPath();
        Files.write(plan, (producer + "\n").getBytes(
                StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", PRODUCER_TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("captures.jsonl")
                        .toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    /** One producer closure whose single member is a communication effect. */
    private static JsonObject communicationEffectClosure() {
        String cell = PRODUCER_ROOT + ".communication.response";
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", EFFECT_BINDING);
        capture.addProperty("captureKind", "COMMUNICATION_EFFECT");
        capture.addProperty("outputPort", EFFECT_PORT);
        capture.addProperty("outputCell", cell);
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", PRODUCER_ROOT);
        capture.addProperty("outputSiteId", "COMMUNICATION_EFFECT:"
                + PRODUCER_ROOT);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");

        JsonObject output = new JsonObject();
        output.addProperty("portId", EFFECT_PORT);
        output.addProperty("cell", cell);
        output.addProperty("kind", "INTERACTION_EVENT");
        output.addProperty("javaTypeDescriptor", "I");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", EFFECT_PORT);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(PRODUCER_ROOT);
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

    @SuppressWarnings("unchecked")
    private static void rememberExport(Object active, String portId,
                                       long exportEventId) throws Exception {
        Field field = active.getClass().getDeclaredField("exportEventByPort");
        field.setAccessible(true);
        ((Map<String, Long>) field.get(active)).put(portId,
                Long.valueOf(exportEventId));
    }

    private static JsonObject onlyOutputCapture(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("outputCaptures");
        field.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<JsonObject> rows = (List<JsonObject>) field.get(active);
        assertEquals(rows.toString(), 1, rows.size());
        return rows.get(0);
    }

    private void loadTwoProducerCampaign() throws Exception {
        JsonObject consumer = task(CONSUMER_TASK, "CLIENT",
                CONSUMER_OCCURRENCE, CONSUMER_ROOT, Object.class.getName(),
                handoff(false));
        consumer.getAsJsonArray(CommunicationHandoffSpec.FIELD).add(
                handoff(false, PORT_B, PRODUCER_ROOT_B));

        JsonObject producerA = task(PRODUCER_TASK, "SERVER",
                PRODUCER_OCCURRENCE, PRODUCER_ROOT, Server.class.getName(),
                handoff(true));
        JsonArray producerAEdges = new JsonArray();
        producerAEdges.add(edge(PRODUCER_OCCURRENCE, PORT));
        producerA.add("edgeBindings", producerAEdges);
        JsonObject producerB = task(PRODUCER_TASK_B, "SERVER_B",
                PRODUCER_OCCURRENCE_B, PRODUCER_ROOT_B,
                Server.class.getName(), handoff(true, PORT_B,
                        PRODUCER_ROOT_B));
        JsonArray producerBEdges = new JsonArray();
        producerBEdges.add(edge(PRODUCER_OCCURRENCE_B, PORT_B));
        producerB.add("edgeBindings", producerBEdges);
        Path plan = folder.newFile("two-response-producers.jsonl").toPath();
        Files.write(plan, (consumer + "\n" + producerA + "\n"
                + producerB + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", CONSUMER_TASK + ","
                + PRODUCER_TASK + "," + PRODUCER_TASK_B);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "two-producer-results.jsonl").toString());
        assertEquals(3,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static JsonObject edge(String producerOccurrence, String port) {
        JsonObject edge = new JsonObject();
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("fromOccurrenceId", producerOccurrence);
        edge.addProperty("fromOutputPort", port);
        edge.addProperty("toOccurrenceId", CONSUMER_OCCURRENCE);
        edge.addProperty("toInputPort", port);
        return edge;
    }

    private static JsonObject task(String taskId, String regionId,
                                   String occurrenceId, String rootMethod,
                                   String receiverClass, JsonObject handoff) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL." + regionId);
        task.addProperty("sourceKey", occurrenceId.substring(0,
                occurrenceId.indexOf("/region/")));
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", "RELATION." + regionId);
        task.addProperty("regionId", regionId);
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", rootMethod);
        selector.addProperty("receiverClass", receiverClass);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", task.get("sourceKey").getAsString());
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
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add(CommunicationHandoffSpec.FIELD, handoffs);
        return task;
    }

    private static JsonObject handoff(boolean exporting) {
        return handoff(exporting, PORT, PRODUCER_ROOT);
    }

    private static JsonObject handoff(boolean exporting, String port,
                                      String producerRoot) {
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 2);
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", exporting
                ? CommunicationHandoffSpec.ROLE_EXPORT
                : CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", port);
        site.addProperty("handoffLeafPath", "resp/currentKey/keyId");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", "XCH.response");
        site.addProperty("componentOfPortId", "XCH.response.resp");
        site.addProperty("encodingAuthority",
                "CONFIGURED_RESPONSE_FIELD_PATH_V1");
        site.addProperty("definitionMethod",
                exporting ? producerRoot : CONSUMER_ROOT);
        if (!exporting) {
            site.addProperty("definitionUnitIndex", 8);
            site.addProperty("declaredCallee",
                    "<example.Protocol: example.Response serve()>");
        }
        JsonArray path = new JsonArray();
        path.add(fieldStep("<example.Response: example.Key currentKey>"));
        path.add(fieldStep("<example.Key: int keyId>"));
        site.add("handoffPath", path);
        return site;
    }

    private static JsonObject fieldStep(String declaration) {
        JsonObject step = new JsonObject();
        step.addProperty("kind", "FIELD");
        step.addProperty("declaration", declaration);
        return step;
    }

    private static Object activate(String taskId, long token) throws Exception {
        Field configurationField = ConcolicRegionRuntime.class
                .getDeclaredField("configuration");
        configurationField.setAccessible(true);
        Object configuration = configurationField.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, taskId);

        Class<?> taskType = task.getClass();
        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, taskType, Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, new Object(),
                Thread.currentThread());

        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        Map<Long, Object> regions = (Map<Long, Object>) activeRegions.get(null);
        regions.put(token, active);
        currentToken().set(token);
        return active;
    }

    private static void clearCurrentToken() throws Exception {
        currentToken().remove();
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> handoffGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("rpcHandoffGaps");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, JsonObject> pendingHandoffGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "pendingResponseHandoffGaps");
        field.setAccessible(true);
        return (Map<String, JsonObject>) field.get(active);
    }

    private static void markHandoffSatisfied(Object active) throws Exception {
        Method satisfied = active.getClass().getDeclaredMethod(
                "markResponseHandoffSatisfied", String.class);
        satisfied.setAccessible(true);
        satisfied.invoke(active, PORT);
    }

    private static CommunicationHandoffSpec communicationHandoff(
            Object active) throws Exception {
        Field activation = active.getClass().getDeclaredField("activation");
        activation.setAccessible(true);
        Object task = activation.get(active);
        Method lookup = task.getClass().getDeclaredMethod(
                "communicationHandoff", String.class, boolean.class);
        lookup.setAccessible(true);
        return (CommunicationHandoffSpec) lookup.invoke(task, PORT, false);
    }

    private static boolean pathRecordingStarted(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField(
                "pathRecordingStarted");
        field.setAccessible(true);
        return field.getBoolean(active);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> vmHandoffs(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("vmHandoffEvents");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static void flushPendingHandoffGaps(Object active)
            throws Exception {
        Method flush = active.getClass().getDeclaredMethod(
                "flushPendingResponseHandoffGaps");
        flush.setAccessible(true);
        flush.invoke(active);
    }

    private static Server server(String id) {
        Server server = new Server();
        RuntimeTraceContext.registerSource(server,
                new SourceRef("TEST", "SERVER", id, 0L));
        return server;
    }

    private static void restore(String property, String value) {
        if (value == null) {
            System.clearProperty(property);
        } else {
            System.setProperty(property, value);
        }
    }

    private static final class Server {
    }

    private static final class Response {
        @SuppressWarnings("unused")
        private final Key currentKey = new Key();
    }

    private static final class Key {
        @SuppressWarnings("unused")
        private int keyId = 7;
    }
}
