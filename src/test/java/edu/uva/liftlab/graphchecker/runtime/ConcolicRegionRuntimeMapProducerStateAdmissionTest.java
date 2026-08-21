package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Frozen edge/task/port admission of one upstream shared Map state. */
public class ConcolicRegionRuntimeMapProducerStateAdmissionTest {
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
    public void exactCausalEdgeChoosesOnePhaseOfOneOccurrence()
            throws Exception {
        load(SELECTED_EDGE, "RF.other");
        assertEquals(PRODUCER_A + "\n" + OUTPUT + "\n" + SELECTED_EDGE
                        + "\n" + INPUT,
                ConcolicRegionRuntime.plannedMapAdmissionForTests(
                        CONSUMER, FIELD));
    }

    @Test
    public void missingOrAmbiguousProducerMemberRefusesWithoutGuessing()
            throws Exception {
        load("RF.never.a", "RF.never.b", "SYMBOLIC");
        assertTrue(ConcolicRegionRuntime.plannedMapAdmissionForTests(
                CONSUMER, FIELD).startsWith("REFUSED:"));

        ConcolicRegionRuntime.resetForTests();
        load(SELECTED_EDGE, SELECTED_EDGE);
        assertTrue(ConcolicRegionRuntime.plannedMapAdmissionForTests(
                CONSUMER, FIELD).startsWith("REFUSED:"));
    }

    @Test
    public void ancillaryConcreteCandidateDoesNotCreateAnAdmissionOrGap()
            throws Exception {
        load("RF.never.a", "RF.never.b", "CONCRETE");
        assertEquals("NONE", ConcolicRegionRuntime
                .plannedMapAdmissionForTests(CONSUMER, FIELD));
    }

    @Test
    public void rejectedProducerCandidateCannotPublishItsStagedVersion()
            throws Exception {
        load(SELECTED_EDGE, "RF.other");
        assertEquals("ABSENT", ConcolicRegionRuntime
                .mapVersionLifecycleForTests(
                        PRODUCER_A, OUTPUT, 41L, false));
        assertEquals("41", ConcolicRegionRuntime
                .mapVersionLifecycleForTests(
                        PRODUCER_A, OUTPUT, 41L, true));
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
    public void concreteSelectedFieldUsesExactProducerButSymbolicDoesNot()
            throws Exception {
        loadField("CONCRETE", true);
        assertEquals(PRODUCER_A + "\n" + FLAG_OUTPUT + "\n" + FLAG_EDGE
                        + "\n" + FLAG_INPUT,
                ConcolicRegionRuntime.plannedFieldAdmissionForTests(
                        CONSUMER, FLAG_FIELD));
        assertEquals("ABSENT", ConcolicRegionRuntime
                .fieldVersionLifecycleForTests(
                        PRODUCER_A, FLAG_OUTPUT, 73L, false));
        assertEquals("73", ConcolicRegionRuntime
                .fieldVersionLifecycleForTests(
                        PRODUCER_A, FLAG_OUTPUT, 73L, true));

        ConcolicRegionRuntime.resetForTests();
        loadField("SYMBOLIC", true);
        assertEquals("NONE", ConcolicRegionRuntime
                .plannedFieldAdmissionForTests(CONSUMER, FLAG_FIELD));

        ConcolicRegionRuntime.resetForTests();
        loadField("CONCRETE", false);
        assertEquals("NONE", ConcolicRegionRuntime
                .plannedFieldAdmissionForTests(CONSUMER, FLAG_FIELD));
    }

    @Test
    public void exactReferenceOutputCarriesItsConfiguredSourceIdentity()
            throws Exception {
        loadField("CONCRETE", true, true);
        String symbol = ConcolicRegionRuntime.configuredSourceSymbolForTests(
                PRODUCER_OCCURRENCE, SOURCE_ID);
        assertEquals(1, ConcolicRegionRuntime
                .plannedFieldSourceAliasesForTests(CONSUMER, FLAG_FIELD)
                .size());
        assertEquals(PRODUCER_OCCURRENCE + "\n" + SOURCE_ID + "\n"
                        + SOURCE_FIELD + "\n" + symbol,
                ConcolicRegionRuntime
                        .plannedFieldSourceAliasesForTests(
                                CONSUMER, FLAG_FIELD).get(0));

        ConcolicRegionRuntime.resetForTests();
        loadField("CONCRETE", false, true);
        assertTrue(ConcolicRegionRuntime
                .plannedFieldSourceAliasesForTests(CONSUMER, FLAG_FIELD)
                .isEmpty());
    }

    @Test
    public void producerNotYetCommittedReleasesCandidateWithoutConcreteInput()
            throws Exception {
        loadField("CONCRETE", true);
        assertEquals("pending=true,gaps=0,observed=false,"
                        + "selectionRetained=true,"
                        + "pendingAfterLaterAccess=true,abandoned=true,"
                        + "retried=true",
                ConcolicRegionRuntime
                        .plannedFieldPrerequisiteMissForTests(
                                CONSUMER,
                                "<example.Consumer: void run()>", 2,
                                new FlagHolder(), FLAG_FIELD, "enabled"));
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
            JsonObject declaration = new JsonObject();
            declaration.addProperty("authority",
                    "CONFIGURED_EXACT_SOURCE_FIELD_V1");
            declaration.addProperty("sourceId", SOURCE_ID);
            declaration.addProperty("fieldSignature", SOURCE_FIELD);
            declaration.addProperty("requiredOutputFieldSignature",
                    FLAG_FIELD);
            JsonArray declarations = new JsonArray();
            declarations.add(declaration);
            producer.add("symbolicSourceFields", declarations);
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
        capture.addProperty("replayOccurrence", 1);
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
        capture.addProperty("replayOccurrence", 1);

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

    private static void restore(String property, String value) {
        if (value == null) System.clearProperty(property);
        else System.setProperty(property, value);
    }

    private static final class FlagHolder {
        @SuppressWarnings("unused")
        private boolean enabled = true;
    }
}
