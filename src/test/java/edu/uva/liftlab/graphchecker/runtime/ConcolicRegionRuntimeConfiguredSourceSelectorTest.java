package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourceSelectorContract;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Exact same-session publication of an int source used as a Map selector. */
public class ConcolicRegionRuntimeConfiguredSourceSelectorTest {
    private static final String PRODUCER = "TASK.REPLAY.key-producer";
    private static final String OTHER_PRODUCER =
            "TASK.REPLAY.other-key-producer";
    private static final String CONSUMER = "TASK.key-consumer";
    private static final String OCCURRENCE =
            "test/nn#epoch0/region/KEY_PRODUCER#1";
    private static final String OTHER_OCCURRENCE =
            "test/nn#epoch0/region/KEY_PRODUCER#2";
    private static final String SOURCE = "HDFS11741.CURRENT_KEY_ID";
    private static final String FIELD = "<example.Key: int keyId>";
    private static final String OUTPUT = "KEY_PRODUCER.out.keyId";
    private static final String EDGE = "EDGE.KEY_PRODUCER.CONSUMER";
    private static final String PRODUCER_METHOD =
            "<example.KeyProducer: void run()>";
    private static final String CONSUMER_METHOD =
            "<example.KeyConsumer: void run()>";
    private static final String PUBLISH_SITE = PRODUCER_METHOD + "#u1";
    private static final String CONSUME_SITE = CONSUMER_METHOD + "#u2";
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
    public void valueIsInvisibleUntilTheProducerOccurrenceCommits()
            throws Exception {
        load();
        String raw = rawSymbol();

        assertEquals("ABSENT", ConcolicRegionRuntime
                .configuredSourceSelectorLifecycleForTests(
                        PRODUCER, CONSUMER, publishPhase(OCCURRENCE),
                        consumePhase(consumerOccurrence()), SOURCE, FIELD,
                        raw, 17,
                        false, false));
        assertEquals(PRODUCER + "\n" + raw + "\n17",
                ConcolicRegionRuntime
                        .configuredSourceSelectorLifecycleForTests(
                                PRODUCER, CONSUMER,
                                publishPhase(OCCURRENCE),
                                consumePhase(consumerOccurrence()),
                                SOURCE, FIELD, raw, 17,
                                true, false));
    }

    @Test
    public void acceptedProducerPhaseIsConsumedAtTheExactConsumePhase()
            throws Exception {
        load();
        String raw = rawSymbol();
        assertEquals(PRODUCER + "\n" + raw + "\n41",
                ConcolicRegionRuntime
                        .configuredSourceSelectorLifecycleForTests(
                                PRODUCER, CONSUMER,
                                publishPhase(OCCURRENCE),
                                consumePhase(consumerOccurrence()),
                                SOURCE, FIELD, raw, 41, true, false));

        Object active = activate(CONSUMER, 91L);
        long call = CausynthTraceRecorder.enterMethod(CONSUMER_METHOD,
                new Object());
        long invocation = CausynthTraceRecorder.beginCall(call,
                CONSUMER_METHOD, 2,
                "<example.Hook: int selectedIntValue()>", null);
        try {
            assertEquals(Integer.valueOf(41), ConcolicRegionRuntime
                    .selectedConfiguredSourceIntValue(SOURCE));
        } finally {
            CausynthTraceRecorder.endCall(invocation, null, "");
            CausynthTraceRecorder.exitMethod(call, null, "");
        }
        List<JsonObject> observations = jsonRows(active,
                "configuredSourcePhaseObservations");
        assertEquals(1, observations.size());
        assertTrue(observations.get(0).get("selectedPhase").getAsBoolean());
        assertEquals(consumePhase(consumerOccurrence()), observations.get(0)
                .get("matchedPhaseId").getAsString());
        assertEquals(0, jsonRows(active,
                "configuredSourcePhaseGaps").size());
        assertEquals(1, jsonMap(active,
                "sourceSelectorEvidence").size());
    }

    @Test
    public void rejectedApplicationSelectionNeverBecomesVisible()
            throws Exception {
        load();
        String result = ConcolicRegionRuntime
                .configuredSourceSelectorLifecycleForTests(
                        PRODUCER, CONSUMER, publishPhase(OCCURRENCE),
                        consumePhase(consumerOccurrence()), SOURCE, FIELD,
                        rawSymbol(), 19,
                        true, true);

        assertTrue(result, result.startsWith("REFUSED:"));
        assertTrue(result, result.contains("rejected its application invariant"));
        assertEquals("ABSENT", ConcolicRegionRuntime
                .configuredSourceSelectorLifecycleForTests(
                        PRODUCER, CONSUMER, publishPhase(OCCURRENCE),
                        consumePhase(consumerOccurrence()), SOURCE, FIELD,
                        rawSymbol(), 19,
                        false, false));
    }

    @Test
    public void onlyTheCausallySelectedProducerOccurrenceCanPublish()
            throws Exception {
        JsonObject selectedProducer = producer(PRODUCER, OCCURRENCE);
        JsonObject selectedConsumer = consumer(OCCURRENCE);
        // The selected edge may be retained on either endpoint's task row;
        // runtime indexing uses the frozen task-graph union, not row locality.
        selectedProducer.add("edgeBindings",
                selectedConsumer.remove("edgeBindings"));
        load(selectedProducer,
                producer(OTHER_PRODUCER, OTHER_OCCURRENCE),
                selectedConsumer);
        String otherRaw = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(publishPhase(OTHER_OCCURRENCE),
                SOURCE, FIELD)
                + "example/Key";

        assertEquals("ABSENT", ConcolicRegionRuntime
                .configuredSourceSelectorLifecycleForTests(
                        OTHER_PRODUCER, CONSUMER,
                        publishPhase(OTHER_OCCURRENCE),
                        consumePhase(consumerOccurrence()), SOURCE, FIELD,
                        otherRaw, 23, true, false));
        assertEquals(PRODUCER + "\n" + rawSymbol() + "\n29",
                ConcolicRegionRuntime
                        .configuredSourceSelectorLifecycleForTests(
                                PRODUCER, CONSUMER,
                                publishPhase(OCCURRENCE),
                                consumePhase(consumerOccurrence()),
                                SOURCE, FIELD,
                                rawSymbol(), 29, true, false));
    }

    @Test
    public void duplicateEdgeOwnerRowsResolveOneCurrentProducer()
            throws Exception {
        JsonObject selectedProducer = producer(PRODUCER, OCCURRENCE);
        JsonObject selectedConsumer = consumer(OCCURRENCE);
        selectedProducer.add("edgeBindings",
                selectedConsumer.getAsJsonArray("edgeBindings").deepCopy());

        load(selectedProducer, selectedConsumer);

        assertEquals(PRODUCER + "\n" + rawSymbol() + "\n31",
                ConcolicRegionRuntime
                        .configuredSourceSelectorLifecycleForTests(
                        PRODUCER, CONSUMER, publishPhase(OCCURRENCE),
                        consumePhase(consumerOccurrence()), SOURCE, FIELD,
                        rawSymbol(), 31, true, false));
    }

    @Test
    public void sameOccurrenceDifferentTasksResolveOneCurrentProducer()
            throws Exception {
        load(producer(PRODUCER, OCCURRENCE),
                consumer(OCCURRENCE, OCCURRENCE));

        assertEquals(PRODUCER + "\n" + rawSymbol() + "\n37",
                ConcolicRegionRuntime
                        .configuredSourceSelectorLifecycleForTests(
                                PRODUCER, CONSUMER,
                                publishPhase(OCCURRENCE),
                                consumePhase(OCCURRENCE), SOURCE, FIELD,
                                rawSymbol(), 37, true, false));
    }

    @Test
    public void sameTaskSelfLoopCannotResolveItsOwnSourceVersion()
            throws Exception {
        JsonObject self = producer("TASK.self", OCCURRENCE);
        addConsumePhase(self, OCCURRENCE);
        JsonArray selectors = new JsonArray();
        selectors.add(ConfiguredSourceSelectorContract.exactInt(
                consumePhase(OCCURRENCE), publishPhase(OCCURRENCE),
                OCCURRENCE, SOURCE, FIELD));
        self.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", EDGE);
        edge.addProperty("fromOccurrenceId", OCCURRENCE);
        edge.addProperty("fromOutputPort", OUTPUT);
        edge.addProperty("toOccurrenceId", OCCURRENCE);
        edge.addProperty("toInputPort", "KEY_CONSUMER.in.keyId");
        JsonArray edges = new JsonArray();
        edges.add(edge);
        self.add("edgeBindings", edges);

        try {
            load(self);
            fail("same task must not resolve its own source version");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("TASK.self@" + OCCURRENCE));
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains("found 0 candidates []"));
        }
    }

    @Test(expected = IllegalArgumentException.class)
    public void sameEdgeIdWithConflictingEndpointsIsRejected()
            throws Exception {
        JsonObject selectedProducer = producer(PRODUCER, OCCURRENCE);
        JsonObject selectedConsumer = consumer(OCCURRENCE);
        JsonArray conflictingEdges = selectedConsumer.getAsJsonArray(
                "edgeBindings").deepCopy();
        conflictingEdges.get(0).getAsJsonObject().addProperty(
                "toInputPort", "KEY_CONSUMER.in.conflicting-keyId");
        selectedProducer.add("edgeBindings", conflictingEdges);

        load(selectedProducer, selectedConsumer);
    }

    @Test(expected = IllegalArgumentException.class)
    public void seedAndReplayCannotClaimOneSourceOccurrence()
            throws Exception {
        load(producer("TASK.SEED.key-producer", OCCURRENCE),
                producer(PRODUCER, OCCURRENCE), consumer(OCCURRENCE));
    }

    private void load() throws Exception {
        load(producer(), consumer());
    }

    private void load(JsonObject... tasks) throws Exception {
        Path plan = folder.newFile("source-selector-plan.jsonl").toPath();
        StringBuilder encoded = new StringBuilder();
        StringBuilder taskIds = new StringBuilder();
        for (JsonObject task : tasks) {
            encoded.append(task).append('\n');
            if (taskIds.length() > 0) taskIds.append(',');
            taskIds.append(task.get("taskId").getAsString());
        }
        Files.write(plan, encoded.toString().getBytes(StandardCharsets.UTF_8));
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", taskIds.toString());
        System.setProperty("causynth.concolic.results",
                folder.getRoot().toPath().resolve("results.jsonl").toString());
        assertEquals(tasks.length,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static Object activate(String taskId, long token)
            throws Exception {
        Field configurationField = ConcolicRegionRuntime.class
                .getDeclaredField("configuration");
        configurationField.setAccessible(true);
        Object configuration = configurationField.get(null);
        Method taskById = configuration.getClass().getDeclaredMethod(
                "taskById", String.class);
        taskById.setAccessible(true);
        Object task = taskById.invoke(configuration, taskId);
        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, new Object(),
                Thread.currentThread());
        Field activeRegions = ConcolicRegionRuntime.class.getDeclaredField(
                "ACTIVE");
        activeRegions.setAccessible(true);
        @SuppressWarnings("unchecked")
        java.util.Map<Long, Object> regions =
                (java.util.Map<Long, Object>) activeRegions.get(null);
        regions.put(token, active);
        Field current = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        current.setAccessible(true);
        @SuppressWarnings("unchecked")
        ThreadLocal<Long> currentToken = (ThreadLocal<Long>) current.get(null);
        currentToken.set(token);
        return active;
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> jsonRows(Object active, String fieldName)
            throws Exception {
        Field field = active.getClass().getDeclaredField(fieldName);
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static java.util.Map<String, JsonObject> jsonMap(
            Object active, String fieldName) throws Exception {
        Field field = active.getClass().getDeclaredField(fieldName);
        field.setAccessible(true);
        return (java.util.Map<String, JsonObject>) field.get(active);
    }

    private static JsonObject producer() {
        return producer(PRODUCER, OCCURRENCE);
    }

    private static JsonObject producer(String taskId, String occurrence) {
        JsonObject task = baseTask(taskId, "KEY_PRODUCER", occurrence,
                PRODUCER_METHOD,
                "OUTPUT_RELATION_CLOSURE");
        addPublishPhase(task, occurrence);
        task.add("outputClosure", outputClosure());
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", SOURCE);
        source.addProperty("sourcePhaseId", publishPhase(occurrence));
        source.addProperty("fieldSignature", FIELD);
        source.addProperty("requiredOutputFieldSignature", FIELD);
        JsonArray sources = new JsonArray();
        sources.add(source);
        task.add(SymbolicSourceEvidence.TASK_FIELD, sources);
        return task;
    }

    private static JsonObject consumer() {
        return consumer(OCCURRENCE);
    }

    private static JsonObject consumer(String sourceOccurrence) {
        return consumer(sourceOccurrence,
                "test/dn#epoch0/region/KEY_CONSUMER#1");
    }

    private static JsonObject consumer(
            String sourceOccurrence, String consumerOccurrence) {
        JsonObject task = baseTask(CONSUMER, "KEY_CONSUMER",
                consumerOccurrence,
                CONSUMER_METHOD,
                "TARGET_REACH_CLOSURE");
        addConsumePhase(task, consumerOccurrence);
        JsonArray selectors = new JsonArray();
        selectors.add(ConfiguredSourceSelectorContract.exactInt(
                consumePhase(consumerOccurrence),
                publishPhase(sourceOccurrence), sourceOccurrence,
                SOURCE, FIELD));
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", EDGE);
        edge.addProperty("fromOccurrenceId", sourceOccurrence);
        edge.addProperty("fromOutputPort", OUTPUT);
        edge.addProperty("toOccurrenceId",
                task.get("occurrenceId").getAsString());
        edge.addProperty("toInputPort", "KEY_CONSUMER.in.keyId");
        JsonArray edges = new JsonArray();
        edges.add(edge);
        task.add("edgeBindings", edges);
        return task;
    }

    private static JsonObject outputClosure() {
        JsonObject output = new JsonObject();
        output.addProperty("portId", OUTPUT);
        output.addProperty("cell", FIELD);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", OUTPUT);
        slice.addProperty("outputCell", FIELD);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add("<example.KeyProducer: void run()>");
        slice.add("methods", methods);
        JsonArray edges = new JsonArray();
        edges.add(EDGE);
        slice.add("causalEdgeIds", edges);
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.KEY_PRODUCER");
        producer.addProperty("regionId", "KEY_PRODUCER");
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        JsonArray members = new JsonArray();
        members.add(member);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject baseTask(
            String taskId, String regionId, String occurrenceId,
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
        JsonObject root = new JsonObject();
        root.addProperty("kind", "RECEIVER_CONTEXT");
        root.addProperty("method", rootMethod);
        root.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", task.get("sourceKey").getAsString());
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        root.add("causalAnchor", anchor);
        task.add("rootSelector", root);
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

    private static String rawSymbol() {
        return ConfiguredSourceSelectorContract.expectedRawSymbolPrefix(
                publishPhase(OCCURRENCE), SOURCE, FIELD) + "example/Key";
    }

    private static String consumerOccurrence() {
        return "test/dn#epoch0/region/KEY_CONSUMER#1";
    }

    private static String publishPhase(String occurrence) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence,
                PUBLISH_SITE, ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static String consumePhase(String occurrence) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence,
                CONSUME_SITE, ConfiguredSourcePhaseContract.Phase.CONSUME, 1);
    }

    private static void addPublishPhase(JsonObject task, String occurrence) {
        JsonArray phases = new JsonArray();
        phases.add(GSON.toJsonTree(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(
                        java.util.Collections.singletonList(
                        ConfiguredSourcePhaseContract.declaration(
                        ConfiguredSourcePhaseContract.Phase.PUBLISH,
                        SOURCE, FIELD, PRODUCER_METHOD, 1))).get(0),
                occurrence, 1, 10L, 1L, 2L,
                "<example.Hook: boolean symbolize()>",
                java.util.Collections.singletonList(1L))));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selected = new JsonArray();
        selected.add(publishPhase(occurrence));
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD, selected);
    }

    private static void addConsumePhase(JsonObject task, String occurrence) {
        JsonArray phases = task.has(ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(GSON.toJsonTree(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(
                        java.util.Collections.singletonList(
                        ConfiguredSourcePhaseContract.declaration(
                        ConfiguredSourcePhaseContract.Phase.CONSUME,
                        SOURCE, FIELD, CONSUMER_METHOD, 2))).get(0),
                occurrence, 1, 20L, 3L, 4L,
                "<example.Hook: int selectedIntValue()>",
                java.util.Collections.singletonList(3L))));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        JsonArray selected = task.has(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                ? task.getAsJsonArray(
                ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD)
                : new JsonArray();
        selected.add(consumePhase(occurrence));
        task.add(ConfiguredSourcePhaseContract.SELECTED_PLAN_FIELD, selected);
    }

    private static void restore(String property, String value) {
        if (value == null) System.clearProperty(property);
        else System.setProperty(property, value);
    }
}
