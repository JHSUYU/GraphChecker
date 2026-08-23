package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
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
import java.util.List;
import java.util.Map;

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
                PRODUCER_TASK, PRODUCER_ROOT, new Server(), new Object[0]));

        activate(CONSUMER_TASK, 41L);
        ConcolicRegionRuntime.prepareResponseHandoff(PORT);
        ConcolicRegionRuntime.observeExchangeLeg("SEND", "TEST_RPC",
                "exchange-selected", "REQUEST");
        clearCurrentToken();

        // A different delivery cannot consume the arm.
        ConcolicRegionRuntime.observeExchangeLeg("RECEIVE", "TEST_RPC",
                "exchange-other", "REQUEST");
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                PRODUCER_TASK, PRODUCER_ROOT, new Server(), new Object[0]));

        // The exact request delivery claims it, after which this producer task
        // (and no value tuple) is authorized.
        ConcolicRegionRuntime.observeExchangeLeg("RECEIVE", "TEST_RPC",
                "exchange-selected", "REQUEST");
        assertEquals(PRODUCER_TASK,
                ConcolicRegionRuntime.admitCampaignTaskForTests(PRODUCER_TASK,
                        PRODUCER_ROOT, new Server(), new Object[0]));
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
                PRODUCER_TASK, PRODUCER_ROOT, new Server(), new Object[0]));
        assertEquals(PRODUCER_TASK_B,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        PRODUCER_TASK_B, PRODUCER_ROOT_B, new Server(),
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
                CommunicationHandoffSpec.class, long.class,
                JsonElement.class, String.class, String.class);
        accept.setAccessible(true);
        accept.invoke(null, active, communicationHandoff(active), 17L,
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
