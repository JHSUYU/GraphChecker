package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Frozen edge/task/port admission of one upstream shared Map state. */
public class ConcolicRegionRuntimeSourceRootAdmissionTest {
    private static final String FIELD =
            "<example.MapHolder: java.util.Map values>";
    private static final String FIELD_KEY = "example.MapHolder#values";
    private static final String INPUT = "CONSUMER.in.values";
    private static final String OUTPUT = "PRODUCER.out.values";
    private static final String SELECTED_EDGE = "RF.selected";
    private static final String CONSUMER = "TASK.consumer";
    private static final String PRODUCER_A = "TASK.producer.a";
    private static final String PRODUCER_B = "TASK.producer.b";
    private static final String PRODUCER_OCCURRENCE =
            "test/node#epoch0/region/PRODUCER#1";
    private static final String FLAG_OWNER = FlagHolder.class.getName();
    private static final String FLAG_FIELD =
            "<" + FLAG_OWNER + ": boolean enabled>";
    private static final String FLAG_FIELD_KEY = FLAG_OWNER + "#enabled";
    private static final String FLAG_INPUT = "CONSUMER.in.enabled";
    private static final String FLAG_OUTPUT = "PRODUCER.out.enabled";
    private static final String FLAG_EDGE = "RF.flag.selected";
    private static final String SOURCE_ID = "SOURCE.keyId";
    private static final String SOURCE_FIELD =
            "<example.Key: int keyId>";
    private static final String PRODUCER_ROOT =
            "<example.Producer: void run()>";
    private static final String SOURCE_HOOK_CALLEE =
            "<example.SourceHook: boolean symbolize()>";
    private static final int SOURCE_UNIT = 3;
    private static final Gson GSON = new Gson();

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
    public void nativeProducerAdmissionRefusalsRemainDistinct() {
        assertEquals("SHARED_STATE_VERSION_NOT_FOUND",
                SharedStateEvidence.reason(
                        SharedStateEvidence.SELECT_VERSION_NOT_FOUND));
        assertEquals("SHARED_STATE_VERSION_AMBIGUOUS",
                SharedStateEvidence.reason(
                        SharedStateEvidence.SELECT_VERSION_AMBIGUOUS));
        assertEquals("SHARED_STATE_INVALID_EDGE",
                SharedStateEvidence.reason(
                        SharedStateEvidence.SELECT_INVALID_EDGE));
    }

    @Test
    public void configuredSourceModelRequiresExactProducerOccurrence()
            throws Exception {
        // Configuration admission runs before a source hook has any owner on
        // which it could perform the modeled field write.
        loadField("CONCRETE", true, true, PRODUCER_OCCURRENCE);

        ConcolicRegionRuntime.resetForTests();
        try {
            loadField("CONCRETE", true, true,
                    "test/node#epoch0/region/PRODUCER#2");
            fail("cross-occurrence source assignment was admitted");
        } catch (IllegalStateException rejected) {
            assertTrue(rejected.getMessage(), rejected.getMessage().contains(
                    "unsupported configured source"));
        }
    }

    @Test
    public void registeredSourceRootRequiresExactReceiverEpochBeforeAdmission()
            throws Exception {
        String taskId = "TASK.registered-source";
        String occurrence =
                "test/node#epoch0/region/REGISTERED_SOURCE#1";
        String root = "<example.Registered: void run()>";
        JsonObject task = baseTask(taskId, "REGISTERED_SOURCE",
                occurrence, root, "TARGET_REACH_CLOSURE");
        task.getAsJsonObject("rootSelector")
                .getAsJsonObject("causalAnchor")
                .addProperty("kind", "REGISTERED_SOURCE");
        Path plan = folder.newFile("registered-source-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "registered-source-results.jsonl").toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());

        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                taskId, root, new Object(), new Object[0]));

        Object stale = new Object();
        RuntimeTraceContext.registerSource(stale, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "test/node", 1L));
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                taskId, root, stale, new Object[0]));

        Object exact = new Object();
        RuntimeTraceContext.registerSource(exact, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "test/node", 0L));
        assertEquals(taskId,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        taskId, root, exact, new Object[0]));
    }

    /**
     * An {@code INHERITED_CONTEXT} root is admitted by the source its thread
     * inherited, and only by that one.
     *
     * <p>HDFS-11741 campaign-takeover-19 planned three
     * {@code cluster0/client0#epoch0} occurrences on the balancer's own worker
     * objects -- {@code Dispatcher$1} and {@code KeyManager$BlockKeyUpdater}.
     * The complete alias set of that trace registers exactly one object for
     * that source, the test's own client anchor, and no balancer class at all,
     * so discovery named those activations from the context their threads
     * inherited from the test thread.  Addressing them as
     * {@code REGISTERED_SOURCE} asked replay to re-check an alias that never
     * existed, and all three were skipped as {@code
     * OCCURRENCE_ANCHOR_UNMATCHED}.</p>
     */
    @Test
    public void inheritedContextRootIsAdmittedByTheSourceItsThreadInherited()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        String taskId = "TASK.inherited-context";
        String occurrence = "test/client#epoch0/region/INHERITED#1";
        String root = "<example.Worker: void run()>";
        JsonObject task = baseTask(taskId, "INHERITED", occurrence, root,
                "TARGET_REACH_CLOSURE");
        task.getAsJsonObject("rootSelector")
                .getAsJsonObject("causalAnchor")
                .addProperty("kind", "INHERITED_CONTEXT");
        Path plan = folder.newFile("inherited-context-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "inherited-context-results.jsonl").toString());

        // No context on this thread: the address names a source nothing here
        // ran under.
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                taskId, root, new Object(), new Object[0]));

        SourceRef other = new SourceRef(
                "CLUSTER_NODE", "DATANODE", "test/node", 0L);
        long otherRequest = RuntimeTraceContext.beginRequest(other, "other");
        assertEquals("", ConcolicRegionRuntime.admitCampaignTaskForTests(
                taskId, root, new Object(), new Object[0]));
        RuntimeTraceContext.endRequest(otherRequest);

        SourceRef client = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L);
        long request = RuntimeTraceContext.beginRequest(client, "workload");
        try {
            // The thread context matches, but this receiver carries an alias
            // of its own naming another node: dn0-versus-dn1 exactness is not
            // weakened by admitting through context.
            Object foreign = new Object();
            RuntimeTraceContext.registerSource(foreign, other);
            assertEquals("",
                    ConcolicRegionRuntime.admitCampaignTaskForTests(
                            taskId, root, foreign, new Object[0]));

            // A receiver with no alias, on a thread that inherited the
            // addressed source: this is the balancer's worker.
            assertEquals(taskId,
                    ConcolicRegionRuntime.admitCampaignTaskForTests(
                            taskId, root, new Object(), new Object[0]));
        } finally {
            RuntimeTraceContext.endRequest(request);
            RuntimeTraceContext.resetForTests();
        }
    }

    @Test
    public void responseProducerWaitsForItsExactRequestExchange()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        String taskId = "TASK.response-producer";
        String occurrence = "test/server#epoch0/region/HTTP_STATUS#4";
        String root = "<example.HttpCall: void writeResponse()>";
        JsonObject task = baseTask(taskId, "HTTP_STATUS", occurrence, root,
                "TARGET_REACH_CLOSURE");
        JsonObject anchor = task.getAsJsonObject("rootSelector")
                .getAsJsonObject("causalAnchor");
        anchor.addProperty("kind", "INHERITED_CONTEXT");
        anchor.addProperty("requestApi", "fetchindex");
        JsonObject response = new JsonObject();
        response.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        response.addProperty("transportKind", "HTTP");
        response.addProperty("direction", "RESPONSE");
        response.addProperty("protocolDirection", "RESPONSE");
        response.addProperty("exchangeLeg",
                "solr-http-9\n9\nRESPONSE");
        response.addProperty("fromOccurrenceId", occurrence);
        response.addProperty("toOccurrenceId",
                "test/client#epoch0/region/HTTP_CLIENT#3");
        task.getAsJsonArray("edgeBindings").add(response);

        Path plan = folder.newFile("response-exchange-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "response-exchange-results.jsonl").toString());

        Object client = new Object();
        Object server = new Object();
        SourceRef clientSource = new SourceRef(
                "CLUSTER_NODE", "FOLLOWER", "test/client", 0L);
        SourceRef serverSource = new SourceRef(
                "CLUSTER_NODE", "LEADER", "test/server", 0L);
        RuntimeTraceContext.registerSource(client, clientSource);
        RuntimeTraceContext.registerSource(server, serverSource);
        long request = RuntimeTraceContext.beginRequest(
                clientSource, "fetchindex");
        String header = RuntimeTraceContext.outboundHeader(client);
        try {
            long stale = RuntimeTraceContext.enterInbound(header, "HTTP",
                    "solr-http-8", "8", "REQUEST", server);
            try {
                assertEquals("",
                        ConcolicRegionRuntime.admitCampaignTaskForTests(
                                taskId, root, server, new Object[0]));
            } finally {
                RuntimeTraceContext.exitInbound(stale);
            }

            long selected = RuntimeTraceContext.enterInbound(header, "HTTP",
                    "solr-http-9", "9", "REQUEST", server);
            try {
                assertEquals(taskId,
                        ConcolicRegionRuntime.admitCampaignTaskForTests(
                                taskId, root, server, new Object[0]));
            } finally {
                RuntimeTraceContext.exitInbound(selected);
            }
        } finally {
            RuntimeTraceContext.endRequest(request);
            RuntimeTraceContext.resetForTests();
        }
    }

    @Test
    public void responseConsumerCancelsOnlyMismatchedRequestExchange()
            throws Exception {
        String consumerId = "TASK.response-consumer";
        String plainId = "TASK.plain-consumer";
        String consumerOccurrence =
                "test/client#epoch0/region/HTTP_CLIENT#4";
        String port = "HTTP.response.status";
        String plainOccurrence = "test/client#epoch0/region/PLAIN#1";
        String root = "<example.HttpClient: void execute()>";
        String plainRoot = "<example.PlainClient: void execute()>";
        JsonObject consumer = baseTask(consumerId, "HTTP_CLIENT",
                consumerOccurrence, root, "TARGET_REACH_CLOSURE");
        JsonObject response = new JsonObject();
        response.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        response.addProperty("transportKind", "HTTP");
        response.addProperty("direction", "RESPONSE");
        response.addProperty("exchangeLeg", "solr-http-9\n9\nRESPONSE");
        response.addProperty("fromOccurrenceId",
                "test/server#epoch0/region/HTTP_STATUS#4");
        response.addProperty("toOccurrenceId", consumerOccurrence);
        response.addProperty("fromOutputPort", port);
        response.addProperty("toInputPort", port);
        consumer.getAsJsonArray("edgeBindings").add(response);
        JsonObject handoff = new JsonObject();
        handoff.addProperty("portId", port);
        handoff.addProperty("handoffLeafPath", port);
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("side", "IN");
        handoff.addProperty("captureKind", "CALL_RETURN");
        handoff.addProperty("definitionMethod", root);
        handoff.addProperty("declaredCallee",
                "<example.StatusLine: int getStatusCode()>");
        handoff.addProperty("definitionUnitIndex", 1);
        handoff.addProperty("javaType", "int");
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        consumer.add("communicationHandoffs", handoffs);
        JsonObject plain = baseTask(plainId, "PLAIN", plainOccurrence,
                plainRoot, "TARGET_REACH_CLOSURE");
        Path plan = folder.newFile("response-consumer-plan.jsonl").toPath();
        Files.write(plan, (consumer + "\n" + plain + "\n")
                .getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                consumerId + "," + plainId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "response-consumer-results.jsonl").toString());
        installCleanupEngine();
        CleanupVm.cleanups = 0;

        Object consumerReceiver = new Object();
        RuntimeTraceContext.registerSource(consumerReceiver, new SourceRef(
                "CLUSTER_NODE", "FOLLOWER", "test/client", 0L));
        assertEquals(consumerId,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        consumerId, root, consumerReceiver, new Object[0]));
        activate(consumerId, consumerReceiver, 101L);
        assertFalse(ConcolicRegionRuntime.retainOutboundExchange(
                "HTTP", "solr-http-8", "8", "REQUEST"));
        assertNull(currentToken().get());

        // Cancellation released the address, so its exact attempt can claim
        // and remain live.
        assertEquals(consumerId,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        consumerId, root, consumerReceiver, new Object[0]));
        activate(consumerId, consumerReceiver, 102L);
        assertTrue(ConcolicRegionRuntime.retainOutboundExchange(
                "HTTP", "solr-http-9", "9", "REQUEST"));
        assertEquals(Long.valueOf(102L), currentToken().get());
        ConcolicRegionRuntime.attachCommunicationLeaf(port,
                new ConcolicRegionRuntime.HandoffLeafCarrier(), "i", "I");
        assertEquals("", unconfirmedAttach(102L));
        assertFalse(ConcolicRegionRuntime.retainOutboundExchange(
                "HTTP", "solr-http-8", "8", "REQUEST"));

        Object plainReceiver = new Object();
        RuntimeTraceContext.registerSource(plainReceiver, new SourceRef(
                "CLUSTER_NODE", "FOLLOWER", "test/client", 0L));
        assertEquals(plainId,
                ConcolicRegionRuntime.admitCampaignTaskForTests(
                        plainId, plainRoot, plainReceiver, new Object[0]));
        activate(plainId, plainReceiver, 103L);
        assertTrue(ConcolicRegionRuntime.retainOutboundExchange(
                "HTTP", "solr-http-8", "8", "REQUEST"));
        assertEquals(Long.valueOf(103L), currentToken().get());
        assertEquals(2, CleanupVm.cleanups);
        activeRegions().remove(103L);
        currentToken().remove();
        ConcolicRegionRuntime.endLiveSelectedRegion();
    }

    /**
     * The thread context never admits a {@code REGISTERED_SOURCE} root: that
     * anchor states the receiver itself was registered, and an object that
     * merely runs under the source is a different occurrence.
     */
    @Test
    public void registeredSourceRootIsNotAdmittedByThreadContextAlone()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        String taskId = "TASK.registered-not-context";
        String occurrence = "test/client#epoch0/region/REGISTERED#1";
        String root = "<example.Server: void run()>";
        JsonObject task = baseTask(taskId, "REGISTERED", occurrence, root,
                "TARGET_REACH_CLOSURE");
        Path plan = folder.newFile("registered-context-plan.jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve(
                        "registered-context-results.jsonl").toString());

        SourceRef client = new SourceRef(
                "EXTERNAL_APP", "HDFS_CLIENT", "test/client", 0L);
        long request = RuntimeTraceContext.beginRequest(client, "workload");
        try {
            assertEquals("",
                    ConcolicRegionRuntime.admitCampaignTaskForTests(
                            taskId, root, new Object(), new Object[0]));

            Object registered = new Object();
            RuntimeTraceContext.registerSource(registered, client);
            assertEquals(taskId,
                    ConcolicRegionRuntime.admitCampaignTaskForTests(
                            taskId, root, registered, new Object[0]));
        } finally {
            RuntimeTraceContext.endRequest(request);
            RuntimeTraceContext.resetForTests();
        }
    }

    @Test
    public void rootAnchorKindAndSourceIdentityAreFailClosed()
            throws Exception {
        assertRootAnchorRejected("UNKNOWN_SOURCE", "test/node#epoch0",
                "test/node#epoch0", "causalAnchor.kind");
        assertRootAnchorRejected("REGISTERED_SOURCE",
                RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                "test/node#epoch0", "causalAnchor.kind");
        assertRootAnchorRejected("UNREGISTERED_SOURCE", "test/node#epoch0",
                "test/node#epoch0", "causalAnchor.kind");
        assertRootAnchorRejected("REGISTERED_SOURCE", "test/other#epoch0",
                "test/node#epoch0", "instead of task source");
    }

    private void load(String firstEdge, String secondEdge) throws Exception {
        load(firstEdge, secondEdge, "CONCRETE");
    }

    private void load(String firstEdge, String secondEdge, String mode)
            throws Exception {
        JsonObject consumer = baseTask(CONSUMER, "CONSUMER",
                "test/client#epoch0/region/CONSUMER#1",
                "<example.Consumer: void run()>",
                "TARGET_REACH_CLOSURE");
        consumer.add("inputActions", inputActions(mode));
        JsonArray carriers = new JsonArray();
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "MAP_STATE");
        carrier.addProperty("declaringClass", "example.MapHolder");
        carrier.addProperty("fieldName", "values");
        carrier.addProperty("descriptor", "Ljava/util/Map;");
        carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        carrier.add("fieldPath", new JsonArray());
        carriers.add(carrier);
        consumer.add("sharedCarriers", carriers);
        JsonArray bindings = new JsonArray();
        bindings.add(binding("RF.unselected.1", "OUT.unselected.1"));
        bindings.add(binding(SELECTED_EDGE, OUTPUT));
        bindings.add(binding("RF.unselected.2", "OUT.unselected.2"));
        consumer.add("edgeBindings", bindings);

        JsonObject producerA = producer(PRODUCER_A, firstEdge);
        JsonObject producerB = producer(PRODUCER_B, secondEdge);
        Path plan = folder.newFile("plan-" + System.nanoTime()
                + ".jsonl").toPath();
        Files.write(plan, (consumer + "\n" + producerA + "\n"
                + producerB + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                CONSUMER + "," + PRODUCER_A + "," + PRODUCER_B);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results-"
                        + System.nanoTime() + ".jsonl").toString());
        assertEquals(3,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private void loadField(String mode, boolean selected) throws Exception {
        loadField(mode, selected, false);
    }

    private void loadField(String mode, boolean selected,
                           boolean source) throws Exception {
        loadField(mode, selected, source, "");
    }

    private void loadField(String mode, boolean selected,
                           boolean source, String assignmentOccurrence)
            throws Exception {
        JsonObject consumer = baseTask(CONSUMER, "CONSUMER",
                "test/client#epoch0/region/CONSUMER#1",
                "<example.Consumer: void run()>",
                "TARGET_REACH_CLOSURE");
        consumer.add("inputActions", fieldInputActions(mode));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", FLAG_OWNER);
        carrier.addProperty("fieldName", "enabled");
        carrier.addProperty("descriptor", "Z");
        carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        carrier.add("fieldPath", new JsonArray());
        JsonArray carriers = new JsonArray();
        carriers.add(carrier);
        consumer.add("sharedCarriers", carriers);
        JsonArray bindings = new JsonArray();
        JsonObject binding = binding(FLAG_EDGE, FLAG_OUTPUT);
        binding.addProperty("toInputPort", FLAG_INPUT);
        binding.addProperty(RecordedReadFrom.EDGE_FIELD, FLAG_FIELD_KEY);
        bindings.add(binding);
        consumer.add("edgeBindings", bindings);

        JsonObject producer = producer(PRODUCER_A,
                selected ? FLAG_EDGE : "RF.flag.other");
        producer.add("outputClosure", fieldOutputClosure(
                selected ? FLAG_EDGE : "RF.flag.other"));
        if (source) {
            // Wave 3: a task declares mint SITES, never selected source rows.
            addSourcePhaseCatalog(producer, PRODUCER_OCCURRENCE,
                    sourcePhaseId(PRODUCER_OCCURRENCE));
        }
        if (!assignmentOccurrence.isEmpty()) {
            String assignmentPhaseId = sourcePhaseId(assignmentOccurrence);
            JsonObject assignment = new JsonObject();
            assignment.addProperty("modelAssignmentKey", "MODEL.keyId");
            assignment.addProperty("engineSymbol",
                    "M_I_field_SRC.example_example/Key");
            assignment.addProperty("inputSymbol", "SOURCE_PHASE:"
                    + assignmentPhaseId);
            assignment.addProperty("configuredSourcePhaseId",
                    assignmentPhaseId);
            assignment.addProperty("configuredSourceId", SOURCE_ID);
            assignment.addProperty("configuredSourceFieldSignature",
                    SOURCE_FIELD);
            assignment.addProperty("valueType", "INT");
            assignment.addProperty("value", "9");
            JsonArray assignments = new JsonArray();
            assignments.add(assignment);
            producer.add("modelAssignments", assignments);
        }
        assertEquals("REGION_ACTIVATION", producer.getAsJsonObject(
                "outputClosure").getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("slice")
                .getAsJsonArray("captureBindings").get(0)
                .getAsJsonObject().get("occurrenceScope").getAsString());
        Path plan = folder.newFile("field-plan-" + System.nanoTime()
                + ".jsonl").toPath();
        Files.write(plan, (consumer + "\n" + producer + "\n")
                .getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id",
                CONSUMER + "," + PRODUCER_A);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("field-results-"
                        + System.nanoTime() + ".jsonl").toString());
        assertEquals(2,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static void addSourcePhaseCatalog(
            JsonObject task, String occurrenceId, String sourcePhaseId) {
        JsonArray declared = new JsonArray();
        declared.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                SOURCE_ID, SOURCE_FIELD, PRODUCER_ROOT, SOURCE_UNIT));
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(declared).get(0);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                declaration, occurrenceId, 1, 1L, 1L, 1L,
                SOURCE_HOOK_CALLEE, Collections.singletonList(1L)));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static String sourcePhaseId(String occurrenceId) {
        return ConfiguredSourcePhaseContract.phaseId(occurrenceId,
                ConfiguredSourcePhaseContract.siteId(PRODUCER_ROOT,
                        SOURCE_UNIT),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static JsonArray inputActions(String mode) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", INPUT);
        action.addProperty("portId", INPUT);
        action.addProperty("cell", FIELD + ".fieldReceiver");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("mode", mode);
        action.addProperty("javaType", "java.util.Map");
        action.addProperty("rootKind", "OBSERVED_FIELD_RECEIVER");
        action.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", FIELD);
        JsonArray path = new JsonArray();
        path.add("values");
        action.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add(FIELD);
        action.add("fieldPathDeclarations", declarations);
        JsonArray sites = new JsonArray();
        sites.add("<example.Consumer: void run()>#u1");
        action.add("accessSites", sites);
        JsonArray result = new JsonArray();
        result.add(action);
        return result;
    }

    private static JsonArray fieldInputActions(String mode) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", FLAG_INPUT);
        action.addProperty("portId", FLAG_INPUT);
        action.addProperty("cell", FLAG_FIELD + ".fieldReceiver");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("mode", mode);
        action.addProperty("javaType", "boolean");
        action.addProperty("rootKind", "OBSERVED_FIELD_RECEIVER");
        action.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", FLAG_FIELD);
        JsonArray path = new JsonArray();
        path.add("enabled");
        action.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add(FLAG_FIELD);
        action.add("fieldPathDeclarations", declarations);
        JsonArray sites = new JsonArray();
        sites.add("<example.Consumer: void run()>#u2");
        action.add("accessSites", sites);
        JsonArray result = new JsonArray();
        result.add(action);
        return result;
    }

    private static JsonObject binding(String edgeId, String outputPort) {
        JsonObject binding = new JsonObject();
        binding.addProperty("kind", "RUNTIME_FIELD_FLOW");
        binding.addProperty("transportKind", "HEAP");
        binding.addProperty("dependencyRole", "VALUE_FRONTIER");
        binding.addProperty("edgeId", edgeId);
        binding.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        binding.addProperty("fromOutputPort", outputPort);
        binding.addProperty("toOccurrenceId",
                "test/client#epoch0/region/CONSUMER#1");
        binding.addProperty("toInputPort", INPUT);
        binding.addProperty(RecordedReadFrom.EDGE_FIELD, FIELD_KEY);
        binding.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        return binding;
    }

    private static JsonObject producer(String taskId, String causalEdge) {
        JsonObject producer = baseTask(taskId, "PRODUCER",
                PRODUCER_OCCURRENCE, "<example.Producer: void run()>",
                "OUTPUT_RELATION_CLOSURE");
        producer.add("outputClosure", outputClosure(causalEdge));
        return producer;
    }

    private static JsonObject outputClosure(String causalEdge) {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + causalEdge);
        capture.addProperty("captureKind", "MUTATION_STATE");
        capture.addProperty("outputPort", OUTPUT);
        capture.addProperty("outputCell", FIELD);
        capture.addProperty("fieldSignature", FIELD);
        capture.addProperty("javaType", "java.util.Map");
        capture.addProperty("definitionMethod",
                "<example.Producer: void run()>");
        capture.addProperty("definitionUnitIndex", 1);
        capture.addProperty("definitionCompletionSeq", 1L);
        capture.addProperty("declaredCallee",
                "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>");
        capture.addProperty("occurrenceScope", "DEFINITION_INVOCATION");
        capture.addProperty("outputBoundaryKind",
                "DEFINITION_INVOCATION_NORMAL_EXIT");
        capture.addProperty("outputSiteId",
                "MUTATION_STATE:<example.Producer: void run()>#u1");
        capture.addProperty("outputOccurrence", 1);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("values");
        capture.add("fieldPath", fieldPath);

        JsonObject output = new JsonObject();
        output.addProperty("portId", OUTPUT);
        output.addProperty("cell", FIELD);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "Ljava/util/Map;");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", OUTPUT);
        slice.addProperty("outputCell", FIELD);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add("<example.Producer: void run()>");
        slice.add("methods", methods);
        JsonArray edges = new JsonArray();
        edges.add(causalEdge);
        slice.add("causalEdgeIds", edges);
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

    private static JsonObject fieldOutputClosure(String causalEdge) {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.FLAG");
        capture.addProperty("captureKind", "FIELD_WRITE_STATE");
        capture.addProperty("outputPort", FLAG_OUTPUT);
        capture.addProperty("outputCell", FLAG_FIELD);
        capture.addProperty("fieldSignature", FLAG_FIELD);
        capture.addProperty("javaType", "boolean");
        capture.addProperty("definitionMethod",
                "<example.Producer: void run()>");
        capture.addProperty("definitionUnitIndex", 2);
        capture.addProperty("definitionCompletionSeq", 2L);
        capture.addProperty("occurrenceScope", "REGION_ACTIVATION");
        capture.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        capture.addProperty("outputSiteId", "FIELD_WRITE:#u2");
        capture.addProperty("outputOccurrence", 1);

        JsonObject output = new JsonObject();
        output.addProperty("portId", FLAG_OUTPUT);
        output.addProperty("cell", FLAG_FIELD);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "Z");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", FLAG_OUTPUT);
        slice.addProperty("outputCell", FLAG_FIELD);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add("<example.Producer: void run()>");
        slice.add("methods", methods);
        JsonArray edges = new JsonArray();
        edges.add(causalEdge);
        slice.add("causalEdgeIds", edges);
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

    private static JsonObject baseTask(String taskId, String regionId,
                                       String occurrenceId,
                                       String rootMethod, String goalKind) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL." + taskId);
        task.addProperty("sourceKey", occurrenceId.substring(0,
                occurrenceId.indexOf("/region/")));
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", "RELATION." + regionId);
        task.addProperty("regionId", regionId);
        task.addProperty("goalKind", goalKind);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", rootMethod);
        selector.addProperty("receiverClass", Object.class.getName());
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
        return task;
    }

    private void assertRootAnchorRejected(String anchorKind,
                                          String anchorSourceKey,
                                          String taskSourceKey,
                                          String expectedMessage)
            throws Exception {
        ConcolicRegionRuntime.resetForTests();
        String taskId = "TASK.bad-anchor." + System.nanoTime();
        JsonObject task = baseTask(taskId, "BAD_ANCHOR",
                taskSourceKey + "/region/BAD_ANCHOR#1",
                "<example.BadAnchor: void run()>",
                "TARGET_REACH_CLOSURE");
        JsonObject anchor = task.getAsJsonObject("rootSelector")
                .getAsJsonObject("causalAnchor");
        anchor.addProperty("kind", anchorKind);
        anchor.addProperty("sourceKey", anchorSourceKey);
        Path plan = folder.newFile("bad-anchor-" + System.nanoTime()
                + ".jsonl").toPath();
        Files.write(plan, (task + "\n").getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskId);
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("bad-anchor-results-"
                        + System.nanoTime() + ".jsonl").toString());
        try {
            ConcolicRegionRuntime.campaignTaskIdsForTests();
            fail("invalid root causal anchor was admitted");
        } catch (IllegalStateException rejected) {
            assertTrue(rejected.getMessage(), rejected.getMessage().contains(
                    expectedMessage));
        }
    }

    private static void activate(String taskId, Object receiver, long token)
            throws Exception {
        Field configured = ConcolicRegionRuntime.class.getDeclaredField(
                "configuration");
        configured.setAccessible(true);
        Object configuration = configured.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, taskId);
        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        activeRegions().put(token, constructor.newInstance(
                token, task, receiver, Thread.currentThread()));
        currentToken().set(token);
        ConcolicRegionRuntime.beginLiveSelectedRegion();
    }

    @SuppressWarnings("unchecked")
    private static Map<Long, Object> activeRegions() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField("ACTIVE");
        field.setAccessible(true);
        return (Map<Long, Object>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    private static String unconfirmedAttach(long token) throws Exception {
        Object active = activeRegions().get(token);
        Method method = active.getClass().getDeclaredMethod(
                "unconfirmedSelectedAttachEndpoint");
        method.setAccessible(true);
        return (String) method.invoke(active);
    }

    private static void installCleanupEngine() throws Exception {
        Class<?> type = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$EngineApi");
        Constructor<?> constructor = type.getDeclaredConstructor();
        constructor.setAccessible(true);
        Object engine = constructor.newInstance();
        for (String name : new String[]{"pausePathCondition",
                "resumePathCondition", "cleanupEnd"}) {
            Field field = type.getDeclaredField(name);
            field.setAccessible(true);
            field.set(engine, CleanupVm.class.getDeclaredMethod(
                    "cleanupEnd".equals(name) ? "cleanup" : name));
        }
        Field installed = ConcolicRegionRuntime.class.getDeclaredField(
                "engineApi");
        installed.setAccessible(true);
        installed.set(null, engine);
    }

    private static void restore(String property, String value) {
        if (value == null) System.clearProperty(property);
        else System.setProperty(property, value);
    }

    private static final class FlagHolder {
        @SuppressWarnings("unused")
        private boolean enabled = true;
    }

    public static final class CleanupVm {
        private static int cleanups;

        public static void pausePathCondition() { }

        public static void resumePathCondition() { }

        public static void cleanup() { cleanups++; }
    }

    @org.junit.Test
    public void aFoldedConstantIsNotAPropagatedExpression() {
        com.google.gson.JsonParser parser = new com.google.gson.JsonParser();
        org.junit.Assert.assertFalse(ConcolicRegionRuntime.isSymbolicExpression(
                parser.parse("{\"_type\":\"ConstExpr\",\"_java_type\":\"I\",\"_exp\":\"Y_I_0\"}")));
        org.junit.Assert.assertFalse(ConcolicRegionRuntime.isSymbolicExpression(null));
        org.junit.Assert.assertTrue(ConcolicRegionRuntime.isSymbolicExpression(
                parser.parse("{\"_type\":\"SymbolExpression\",\"_java_type\":\"I\",\"_exp\":\"M_I_x\"}")));
        org.junit.Assert.assertTrue(ConcolicRegionRuntime.isSymbolicExpression(
                parser.parse("{\"_type\":\"BinaryExpression\",\"_left\":{\"_type\":\"ConstExpr\",\"_exp\":\"1\"},"
                        + "\"_right\":{\"_type\":\"SymbolExpression\",\"_exp\":\"M_I_y\"}}")));
        org.junit.Assert.assertFalse("a field access over a container-derived reference names no root",
                ConcolicRegionRuntime.isSymbolicExpression(parser.parse(
                        "{\"_type\":\"FieldAccessExpression\",\"_java_type\":\"J\",\"ownerClass\":\"x/BlockKey\","
                        + "\"_base\":{\"_type\":\"ContainerExpression\",\"_op\":\"READ\"}}")));
    }
}
