package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * One response port, two senders: which one the replay arms.
 *
 * <p>The scheduler declares an exchange pairing a replay recorded beside the
 * frozen plan's own row for that port, so a receiving port can name two
 * senders.  The recorded pairing carries the two VM ledger events that name
 * this exact send and this exact receive, and that is what decides.  A row
 * without those stamps is judged exactly as before: two of them on one port
 * are the refusal they always were.</p>
 */
public class ConcolicRegionRuntimeAbsorbedResponseProducerTest {

    private static final String CONSUMER_TASK = "TASK.absorbed-consumer";
    private static final String PLANNED_TASK = "TASK.absorbed-planned";
    private static final String RECORDED_TASK = "TASK.absorbed-recorded";
    private static final String CONSUMER_OCCURRENCE =
            "test/client#epoch0/region/CLIENT#1";
    private static final String PLANNED_OCCURRENCE =
            "test/server#epoch0/region/SERVER#7";
    private static final String RECORDED_OCCURRENCE =
            "test/server#epoch0/region/SERVER#3";
    private static final String CONSUMER_ROOT =
            "<example.Client: void call()>";
    private static final String PRODUCER_ROOT =
            "<example.Server: example.Response serve()>";
    private static final String PORT = "XCH.response.resp.keyId";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;
    private int loads;

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

    /** The stamped pairing names the sender the VM saw, so it decides. */
    @Test
    public void aRecordedPairingDecidesTheResponseProducer()
            throws Exception {
        load(edge(PLANNED_OCCURRENCE),
                absorbed(edge(RECORDED_OCCURRENCE), RECORDED_TASK, 41L, 44L));

        assertEquals(RECORDED_OCCURRENCE, responseProducer(CONSUMER_TASK));
    }

    /** With no stamped pairing the frozen plan's own row still decides. */
    @Test
    public void aPlanRowAloneStillDecidesTheResponseProducer()
            throws Exception {
        load(edge(PLANNED_OCCURRENCE));

        assertEquals(PLANNED_OCCURRENCE, responseProducer(CONSUMER_TASK));
    }

    /** Two plan rows on one port are the refusal they always were. */
    @Test
    public void twoPlanRowsOnOnePortAreStillRefused() throws Exception {
        assertRefused(edge(PLANNED_OCCURRENCE), edge(RECORDED_OCCURRENCE));
    }

    /** A row missing any one stamp is a plan row, and is judged as one. */
    @Test
    public void aPartiallyStampedRowIsStillAPlanRow() throws Exception {
        JsonObject partial = absorbed(edge(RECORDED_OCCURRENCE),
                RECORDED_TASK, 41L, 44L);
        partial.remove(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID);
        assertRefused(edge(PLANNED_OCCURRENCE), partial);

        JsonObject unauthorized = absorbed(edge(RECORDED_OCCURRENCE),
                RECORDED_TASK, 41L, 44L);
        unauthorized.addProperty(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD,
                "SOMETHING_ELSE");
        assertRefused(edge(PLANNED_OCCURRENCE), unauthorized);
    }

    /** Two stamped pairings name two senders, so no evidence names one. */
    @Test
    public void twoRecordedPairingsOnOnePortAreRefused() throws Exception {
        assertRefused(
                absorbed(edge(PLANNED_OCCURRENCE), PLANNED_TASK, 41L, 44L),
                absorbed(edge(RECORDED_OCCURRENCE), RECORDED_TASK, 42L, 45L));
    }

    private void assertRefused(JsonObject... edges) throws Exception {
        try {
            load(edges);
            fail("two producer occurrences on one response port must be "
                    + "refused");
        } catch (IllegalStateException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "response handoff port has two producer occurrences"));
        }
    }

    private void load(JsonObject... edges) throws Exception {
        ConcolicRegionRuntime.resetForTests();
        String name = "absorbed-response-" + loads++;
        JsonObject consumer = task(CONSUMER_TASK, "CLIENT",
                CONSUMER_OCCURRENCE, CONSUMER_ROOT, Object.class.getName(),
                handoff(false));
        JsonArray bindings = new JsonArray();
        for (JsonObject edge : edges) bindings.add(edge);
        consumer.add("edgeBindings", bindings);

        JsonObject producer = task(PLANNED_TASK, "SERVER",
                PLANNED_OCCURRENCE, PRODUCER_ROOT, Server.class.getName(),
                handoff(true));
        Path plan = folder.newFile(name + "-plan.jsonl").toPath();
        Files.write(plan, (consumer + "\n" + producer + "\n").getBytes(
                StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                CONSUMER_TASK + "," + PLANNED_TASK);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        name + "-results.jsonl").toString());
        assertEquals(2,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    @SuppressWarnings("unchecked")
    private static String responseProducer(String taskId) throws Exception {
        Field configurationField = ConcolicRegionRuntime.class
                .getDeclaredField("configuration");
        configurationField.setAccessible(true);
        Object configuration = configurationField.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, taskId);
        Field field = task.getClass().getDeclaredField(
                "responseProducerOccurrenceByPort");
        field.setAccessible(true);
        return ((Map<String, String>) field.get(task)).get(PORT);
    }

    private static JsonObject edge(String producerOccurrence) {
        JsonObject edge = new JsonObject();
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("fromOccurrenceId", producerOccurrence);
        edge.addProperty("fromOutputPort", PORT);
        edge.addProperty("toOccurrenceId", CONSUMER_OCCURRENCE);
        edge.addProperty("toInputPort", PORT);
        return edge;
    }

    private static JsonObject absorbed(JsonObject edge, String producerTask,
                                       long export, long attach) {
        edge.addProperty(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD,
                VmHandoffEvidence.ABSORBED_AUTHORITY);
        edge.addProperty(VmHandoffEvidence.ABSORBED_FROM_TASK_ID,
                producerTask);
        edge.addProperty(VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID, export);
        edge.addProperty(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID, attach);
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
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 2);
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", exporting
                ? CommunicationHandoffSpec.ROLE_EXPORT
                : CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", PORT);
        site.addProperty("handoffLeafPath", "resp/currentKey/keyId");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", "XCH.response");
        site.addProperty("componentOfPortId", "XCH.response.resp");
        site.addProperty("encodingAuthority",
                "CONFIGURED_RESPONSE_FIELD_PATH_V1");
        site.addProperty("definitionMethod",
                exporting ? PRODUCER_ROOT : CONSUMER_ROOT);
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

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }

    /** The response producer's receiver type, as the plan names it. */
    public static final class Server {
    }
}
