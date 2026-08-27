package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerTest {
    private static final Gson GSON = new Gson();
    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void selectedOutputPublishesEarliestExactCallChainContinuation() {
        String serviceLoop = "<example.Actor: void run()>";
        String interaction = "<example.Actor: void pollOnce()>";
        String protocol = "<example.Actor: void receive()>";
        String writer = "<example.Keys: void publish()>";
        List<RuntimeRegionPlanner.MethodEvent> chain = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "actor", 7,
                        serviceLoop, 11, "example.Actor", 10, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "actor", 7,
                        interaction, 11, "example.Actor", 11, 10, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "actor", 7,
                        protocol, 11, "example.Actor", 12, 11, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "actor", 7,
                        writer, 22, "example.Keys", 13, 12, 0, 0L, 0L, 0L, 0L, null, false, "", ""));

        RuntimeRegionPlanner.MethodEvent selected = RuntimeRegionPlanner
                .firstCompatibleReplayContinuation(chain,
                        new LinkedHashSet<>(Arrays.asList(
                                interaction, protocol, writer)));

        assertEquals(interaction, selected.method);
        assertEquals("example.Actor", selected.receiverType);
    }

    @Test
    public void dynamicOutputBoundaryRequiresBothEventAndCallIdentity() {
        JsonObject exact = new JsonObject();
        assertTrue(RuntimeRegionPlanner.addExactOutputBoundary(
                exact, 180L, 84L));
        assertEquals(180L,
                exact.get("selectedRuntimeEventSeq").getAsLong());
        assertEquals(84L,
                exact.get("selectedRuntimeCallId").getAsLong());

        JsonObject missingCall = new JsonObject();
        assertFalse(RuntimeRegionPlanner.addExactOutputBoundary(
                missingCall, 180L, -1L));
        assertFalse(missingCall.has("selectedRuntimeEventSeq"));
        assertFalse(missingCall.has("selectedRuntimeCallId"));
    }

    @Test
    public void callChainContinuationNeverGuessesFromSelectedMethodOrder() {
        String root = "<example.Actor: void run()>";
        String unobserved = "<example.Actor: void configuredOnly()>";
        List<RuntimeRegionPlanner.MethodEvent> chain = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "actor", 7,
                        root, 11, "example.Actor", 10, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "actor", 7,
                        "<example.Actor: void helper()>", 11,
                        "example.Actor", 11, 10, 0, 0L, 0L, 0L, 0L, null, false, "", ""));

        assertEquals(null, RuntimeRegionPlanner
                .firstCompatibleReplayContinuation(chain,
                        Arrays.asList(unobserved, root)));
    }

    /**
     * Hadoop IPC invokes a semantic server method below framework dispatch,
     * not below a selected application root.  The exact receiver entry and its
     * selected subtree are one coarse occurrence on their own; planning must
     * neither reject it nor invent a Java parent occurrence.
     */
    @Test
    public void frameworkDispatchedCommunicationEntryIsIndependentOccurrence()
            throws Exception {
        String dispatch = "<example.Framework: java.lang.Object dispatch()>";
        String receiver = "<example.Server: int receive()>";
        String helper = "<example.Server: int value()>";
        File skeletons = jsonl("communication-entry-skeletons.jsonl", object(
                "schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.receiver", "rootMethod", receiver,
                "rootAuthority", "COMMUNICATION_ENTRY",
                "anchorMethod", receiver,
                "anchorMethods", Arrays.asList(receiver, helper),
                "methods", Arrays.asList(receiver, helper),
                "selection", "PROTOCOL_CONTEXT"));
        SourceRef server = new SourceRef("CLUSTER_NODE", "SERVER",
                "cluster0/server0", 1);
        List<RuntimeRegionPlanner.MethodEvent> trace = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "rpc-worker",
                        7, dispatch, 0, "", 100, 0, 0,
                        7, 10, 0, 0, server, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "rpc-worker",
                        7, receiver, 0, "", 101, 100, 0,
                        7, 10, 0, 0, server, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "rpc-worker",
                        7, helper, 0, "", 102, 101, 0,
                        7, 10, 0, 0, server, false, "", ""));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, trace,
                        Collections.emptyList(), Collections.emptyList());

        assertEquals(1, result.runtimeInstances.size());
        Map<String, Object> activation = result.runtimeInstances.get(0);
        assertEquals(101L, activation.get("rootCallId"));
        assertEquals(receiver, activation.get("rootMethod"));
        assertEquals("COMMUNICATION_ENTRY",
                activation.get("rootAuthority"));
        assertEquals(server.key(), activation.get("sourceKey"));
        assertEquals(Arrays.asList(101L, 102L),
                activation.get("callIds"));
        assertFalse(activation.containsKey("parentActivationId"));
        assertTrue(result.occurrenceLinks.isEmpty());
    }

    /**
     * An adapter-carried component has its own typed leaf and exact storage
     * on each side. Planning retains both endpoint declarations without
     * turning the structured parent's Java value into the component value.
     */
    @Test
    public void componentHandoffKeepsExactRoleLocalCarrier()
            throws Exception {
        String exchange = "XCH.00000000-0000-3000-8000-000000000001";
        String parentId = exchange + ".req.p0";
        String componentId = exchange + ".req.keyId";
        String callee = "<example.Transport: void send(java.lang.String)>";
        Map<String, Object> region = fullRegion();
        region.put("symbolicInputs", Arrays.asList(
                communicationParent(parentId, exchange, "IN",
                        "CONCRETE_STRUCTURE_CARRIER", "ENTRY_PARAMETER",
                        TARGET, -1, "", 0),
                communicationComponent(componentId, parentId, exchange,
                        "IN")));
        region.put("outputs", Arrays.asList(
                communicationParent(parentId, exchange, "OUT",
                        "CONCRETE_STRUCTURE_CARRIER", "CALL_ARGUMENT",
                        ROOT, 7, callee, 3),
                communicationComponent(componentId, parentId, exchange,
                        "OUT")));
        File regions = jsonl("component-regions.jsonl", region);
        File edges = jsonl("component-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("component-refined.jsonl", refined);

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Collections.singletonList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                methods(), runtime(), Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.get(0);
        List<Map<String, Object>> encoded = rows(plan.get(
                CommunicationHandoffSpec.FIELD));
        assertEquals(2, encoded.size());
        Map<String, Object> export = encoded.stream()
                .filter(row -> "EXPORT".equals(row.get("role")))
                .findFirst().get();
        Map<String, Object> attach = encoded.stream()
                .filter(row -> "ATTACH".equals(row.get("role")))
                .findFirst().get();
        assertEquals(componentId, export.get("portId"));
        assertEquals("HANDSHAKE/keyId", export.get("handoffLeafPath"));
        assertEquals(parentId, export.get("componentOfPortId"));
        assertEquals("TEST_ENCODING_V1", export.get("encodingAuthority"));
        assertEquals("example.ExportCarrier",
                export.get("manualCarrierClass"));
        assertEquals("keyId", export.get("manualCarrierField"));
        assertEquals("I", export.get("manualCarrierDescriptor"));
        assertFalse(export.containsKey("definitionMethod"));
        assertFalse(export.containsKey("argumentIndex"));
        assertEquals("example.AttachCarrier",
                attach.get("manualCarrierClass"));

        RegionInstancePlan decoded = RegionInstancePlan.decode(
                GSON.toJsonTree(plan).getAsJsonObject());
        assertEquals(1, decoded.goals().size());
        com.google.gson.JsonObject holder = new com.google.gson.JsonObject();
        holder.add(CommunicationHandoffSpec.FIELD,
                GSON.toJsonTree(encoded));
        List<CommunicationHandoffSpec> sites =
                CommunicationHandoffSpec.decode(holder);
        assertTrue(sites.get(0).component());
        assertTrue(sites.get(0).manualCarrier());
        assertFalse(sites.get(0).exportsCutArgument());
        assertFalse(sites.get(1).attachesEntryParameter());
    }

    /**
     * A declared output port the trace shows no consumer for states a named
     * blocker, and a declared port a consumer did demand states none.
     *
     * <p>The failure bound can only ever speak about an endpoint some
     * recorded consumer demanded, so a port whose consumer was never traced
     * used to leave no blocker, no gap and no row of any kind - a coverage
     * hole that reads exactly like a closed relation.</p>
     */
    @Test
    public void aDeclaredOutputPortNoConsumerDemandedIsNamed()
            throws Exception {
        String producerRoot = "<example.Producer: void publish()>";
        String callee = "<example.Transport: void send(java.lang.String)>";
        String consumedExchange = "XCH.00000000-0000-3000-8000-00000000000a";
        String silentExchange = "XCH.00000000-0000-3000-8000-00000000000b";
        String consumedPort = consumedExchange + ".req.p0";
        String silentPort = silentExchange + ".req.p0";
        String producerOccurrence = retained("REGION.P", 1).get(0);
        String targetOccurrence = retained("REGION.1", 1).get(0);

        Map<String, Object> target = fullRegion();
        target.put("symbolicInputs", Collections.singletonList(
                communicationParent(consumedPort, consumedExchange, "IN",
                        "CONCRETE_STRUCTURE_CARRIER", "ENTRY_PARAMETER",
                        TARGET, -1, "", 0)));
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", "",
                "selection", "STATE_CONTEXT",
                "runtimeOccurrenceIds", retained("REGION.P", 1),
                "methods", Collections.singletonList(producerRoot),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Arrays.asList(
                        ownedByRootCall(communicationParent(consumedPort,
                                consumedExchange, "OUT",
                                "CONCRETE_STRUCTURE_CARRIER",
                                "CALL_ARGUMENT", producerRoot, 7, callee, 3),
                                3),
                        ownedByRootCall(communicationParent(silentPort,
                                silentExchange, "OUT",
                                "CONCRETE_STRUCTURE_CARRIER",
                                "CALL_ARGUMENT", producerRoot, 8, callee, 3),
                                3)),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("declared-without-consumer-regions.jsonl",
                target, producer);
        Map<String, Object> flow = object("schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", "DF.consumed",
                "fromOccurrenceId", producerOccurrence,
                "toOccurrenceId", targetOccurrence,
                "fromPort", consumedPort,
                "toPort", consumedPort,
                "receiverObjectId", 17,
                "writerEventSeq", 1,
                "readerEventSeq", 2,
                "writerLaneId", "1",
                "readerLaneId", "2",
                "programOrderRequired", false);
        File edges = jsonl("declared-without-consumer-edges.jsonl", flow);
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl(
                "declared-without-consumer-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p",
                        8, producerRoot, 30, "example.Producer", 3, 0, 0,
                        0L, 0L, 0L, 0L, null, false, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.P", 3, producerRoot,
                                Collections.singletonList(3L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> producerPlan = null;
        for (Map<String, Object> plan : result.regionPlans) {
            if ("REGION.P".equals(plan.get("regionId"))) producerPlan = plan;
        }
        assertTrue(String.valueOf(result.regionPlans),
                producerPlan != null);
        Map<String, Object> goal = rows(
                producerPlan.get("closureGoals")).get(0);
        assertEquals("OUTPUT_RELATION_CLOSURE", goal.get("kind"));
        Set<Object> stated = new LinkedHashSet<>();
        stated.addAll((List<Object>) goal.get("excludedOutputBlockers"));
        stated.addAll((List<Object>) ((Map<String, Object>)
                goal.get("admission")).get("blockers"));
        assertTrue(String.valueOf(stated), stated.contains(
                "OUTPUT_DECLARED_WITHOUT_CONSUMER:" + silentPort));
        // The demanded port states the reason its own closure failed, and
        // never this one: it had a consumer.
        assertFalse(String.valueOf(stated), stated.contains(
                "OUTPUT_DECLARED_WITHOUT_CONSUMER:" + consumedPort));
        assertTrue(String.valueOf(stated), stated.contains(
                "CUT_ARGUMENT_PORT_INCOMPLETE:" + consumedPort));
    }

    @Test
    public void responseComponentIsDistinctFromConcreteResponseEffect() {
        String occurrence = "cluster0/server0#epoch1/region/REGION.1#3";
        String exchange = "XCH.00000000-0000-3000-8000-000000000002";
        String parentId = exchange + ".resp";
        String componentId = exchange + ".resp.keyId";
        String definition = "<example.Server: example.Response reply()>";
        Map<String, Object> parent = object(
                "portId", parentId,
                "sourceKind", "COMMUNICATION_SITE_PORT",
                "dependencyRole", "CONCRETE_STRUCTURE_CARRIER",
                "direction", "RESPONSE",
                "handoffLeafPath", "resp",
                "exchangeSiteKey", exchange,
                "outputCaptureKind", "ENTRY_RETURN",
                "definitionMethod", definition,
                "occurrenceId", occurrence);
        Map<String, Object> component = object(
                "portId", componentId,
                "sourceKind", "COMMUNICATION_SITE_PORT",
                "dependencyRole", "VALUE_FRONTIER",
                "direction", "RESPONSE",
                "componentOfPortId", parentId,
                "encodingAuthority", "TEST_RESPONSE_ENCODING_V1",
                "handoffLeafPath", "resp/currentKey/keyId",
                "exchangeSiteKey", exchange,
                "outputCaptureKind", "ENTRY_RETURN",
                "definitionMethod", definition,
                "occurrenceId", occurrence);
        StaticProgram.RegionRow region = StaticProgram.regionRows(
                Collections.singletonList(object(
                        "schemaVersion", 3,
                        "kind", "SYMBOLIC_REGION",
                        "regionId", "REGION.semantic-endpoint",
                        "rootMethod", definition,
                        "methods", Collections.singletonList(definition),
                        "outputs", Arrays.asList(parent, component))),
                "SYMBOLIC_REGION", "test").get(0);

        String parentEndpoint = RuntimeRegionPlanner.semanticOutputEndpoint(
                object("fromOutputPort", parentId), region, occurrence);
        String componentEndpoint = RuntimeRegionPlanner
                .semanticOutputEndpoint(
                        object("fromOutputPort", componentId), region,
                        occurrence);

        assertEquals("COMMUNICATION_EFFECT\n" + definition
                + "\nRESPONSE", parentEndpoint);
        assertEquals("HANDOFF_COMPONENT\n" + exchange
                + "\nRESPONSE\nresp/currentKey/keyId",
                componentEndpoint);
        assertFalse(parentEndpoint.equals(componentEndpoint));
    }

    /** One response delivery carries both its concrete parent and component. */
    @Test
    public void exactDeliveryKeepsParentAndComponentDespiteEdgeOrdering() {
        String occurrence = "node/client#epoch0/region/REGION.C#1";
        String producer = "node/server#epoch0/region/REGION.R#2";
        String exchange = "XCH.00000000-0000-3000-8000-000000000003";
        Map<String, Object> parent = object(
                "edgeId", "RPC.100-parent-sorts-first",
                "exchangeSiteKey", exchange,
                "fromOccurrenceId", producer,
                "toOccurrenceId", occurrence,
                "fromOutputPort", exchange + ".resp",
                "toInputPort", exchange + ".resp",
                "attemptId", "0", "direction", "RESPONSE",
                "senderEventSeq", 40L, "receiverEventSeq", 50L);
        Map<String, Object> component = object(
                "edgeId", "RPC.900-component-sorts-last",
                "exchangeSiteKey", exchange,
                "fromOccurrenceId", producer,
                "toOccurrenceId", occurrence,
                "fromOutputPort", exchange + ".resp.keyId",
                "toInputPort", exchange + ".resp.keyId",
                "attemptId", "0", "direction", "RESPONSE",
                "senderEventSeq", 40L, "receiverEventSeq", 50L);
        Map<String, Object> parentDeclaration = object(
                "portId", exchange + ".resp");
        Map<String, Object> componentDeclaration = object(
                "portId", exchange + ".resp.keyId",
                "componentOfPortId", exchange + ".resp");

        Map<String, String> selected = RuntimeRegionPlanner
                .exactProtocolDeliveryInputs(Arrays.asList(
                        parent, component), Arrays.asList(
                        parentDeclaration, componentDeclaration));

        assertEquals(2, selected.size());
        assertEquals("RPC.100-parent-sorts-first",
                selected.get(exchange + ".resp"));
        assertEquals("RPC.900-component-sorts-last",
                selected.get(exchange + ".resp.keyId"));
    }

    /**
     * A component inherits the structured response's value/control frontier,
     * not every trusted read that happened earlier in the handler.
     */
    @Test
    public void responseComponentIntersectsParentReturnAndKeepsExactRfEdges() {
        String occurrence = "node/server#epoch0/region/REGION.R#1";
        String keys = "REGION.R.in.keys";
        String guard = "REGION.R.in.guard";
        String stats = "REGION.R.in.stats";
        List<Map<String, Object>> beforeSend = Arrays.asList(
                object("portId", keys), object("portId", guard),
                object("portId", stats));

        List<Map<String, Object>> retained = RuntimeRegionPlanner
                .retainParentReturnInputs(beforeSend,
                        new LinkedHashSet<>(Arrays.asList(keys, guard)));
        assertEquals(Arrays.asList(keys, guard), Arrays.asList(
                retained.get(0).get("portId"),
                retained.get(1).get("portId")));

        Map<String, Object> goal = object("edgeBindings", Arrays.asList(
                runtimeReadFrom("RF.keys", occurrence, keys, 10, 20),
                runtimeReadFrom("RF.guard", occurrence, guard, 11, 21),
                runtimeReadFrom("RF.stats", occurrence, stats, 12, 22)));
        Set<String> edges = RuntimeRegionPlanner.componentCausalEdgeIds(
                goal, occurrence, 30,
                new LinkedHashSet<>(Arrays.asList(keys, guard)),
                "RPC.component");

        assertEquals(new LinkedHashSet<>(Arrays.asList(
                "RPC.component", "RF.keys", "RF.guard")), edges);
        assertFalse(edges.contains("RF.stats"));

        Map<String, Object> component = object(
                CommunicationCatalogContract.PORT_HANDOFF_PATH,
                Arrays.asList(
                        object("kind", "FIELD", "declaration",
                                "<example.Response: example.Key current>"),
                        object("kind", "UNIQUE_ARRAY_ELEMENT",
                                "runtimeClass", "example.Command"),
                        object("kind", "FIELD", "declaration",
                                "<example.Key: int keyId>")));
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        "<example.Response: example.Key current>",
                        "<example.Key: int keyId>")),
                RuntimeRegionPlanner.handoffPathFieldDeclarations(component));
    }

    /**
     * A closure that succeeds still states what it dropped.  The guard-only
     * enabler is deliberately removed - its guard is already replayed - but
     * the removal reaches the artifact by name instead of leaving a reader
     * unable to tell it from an input that was never in the slice.
     */
    @Test
    public void anAdmittedClosureNamesTheEnablerItDropped() {
        String outputPort = "REGION.1.out.0";
        String enabler = "REGION.1.in.enabler";
        Map<String, Object> input = new LinkedHashMap<>();
        input.put("portId", enabler);
        input.put("occurrenceId", "OCC.1");
        input.put("sourceKind", "ACCESSOR_RETURN");
        input.put("dependencyRole", "VALUE_FRONTIER");
        input.put("symbolicDemand", "BOUNDED_STATE_FRONTIER");
        input.put("boundedStateFrontierAuthority",
                "STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1");
        input.put("boundedMutationGuardSites",
                Collections.singletonList(ROOT + "#u3"));

        Map<String, Object> branch = new LinkedHashMap<>();
        branch.put("siteId", ROOT + "#u3");
        branch.put("policy", "EXPLORE");
        branch.put("observed", Boolean.TRUE);
        branch.put("requiredOutcome", Boolean.TRUE);

        List<String> inputPorts = new ArrayList<>(Arrays.asList(enabler));
        List<String> dropped = new ArrayList<>();
        RuntimeRegionPlanner.removeGuardOnlyPathEnablers(inputPorts,
                new LinkedHashSet<>(Arrays.asList(enabler)),
                Collections.singletonList(input), "OCC.1", outputPort,
                "<example.State: int value>",
                new LinkedHashSet<>(Arrays.asList(ROOT + "#u3")),
                Collections.singletonList(branch), dropped);

        assertTrue(inputPorts.toString(), inputPorts.isEmpty());
        assertEquals(Collections.singletonList(
                "GUARD_ONLY_PATH_ENABLER_REMOVED:" + outputPort + ":"
                        + enabler), dropped);
    }

    @Test
    public void onlyTheActivationThatReachedTheFailureSitePlansATarget()
            throws Exception {
        // `selection` is a property of the static region skeleton, so every
        // concurrent activation of one thread-entry region inherits
        // EXCEPTION_CONTEXT.  Reaching the declared failureTarget site is
        // activation-local: only the activation whose own calls observed it
        // plans a target-reach closure; the other keeps its ordinary
        // output-relation closure and stays a composable producer.
        Map<String, Object> region = fullRegion();
        region.put("branchPolicies", Collections.singletonList(object(
                "siteId", TARGET + "#u4", "method", TARGET, "unitIndex", 4,
                "failureTarget", true, "requiredOutcome", false,
                "policy", "EXPLORE")));
        region.put("runtimeOccurrenceIds", retained("REGION.1", 1, 2));
        File regions = jsonl("per-activation-regions.jsonl", region);
        File edges = jsonl("per-activation-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("per-activation-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "producer",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "producer",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "consumer",
                        8, ROOT, 30, "example.Root", 3, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "consumer",
                        8, TARGET, 40, "example.Target", 4, 3, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        // The fatal site executed in the second activation only.
        List<RuntimeRegionPlanner.RuntimeEvent> observed =
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 4, 0, 0, TARGET + "#u4", "", -1, "", 0,
                                "", Boolean.FALSE, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, observed, Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        assertEquals("OUTPUT_RELATION_CLOSURE",
                goalKind(result.regionPlans.get(0)));
        assertTrue(String.valueOf(result.regionPlans.get(0)
                .get("occurrenceId")).endsWith("#1"));
        assertEquals("TARGET_REACH_CLOSURE",
                goalKind(result.regionPlans.get(1)));
        assertTrue(String.valueOf(result.regionPlans.get(1)
                .get("occurrenceId")).endsWith("#2"));
    }

    @Test
    public void configuredSourcePhasesUseExactSiteOrderAndCallAncestry()
            throws Exception {
        String helper = "<example.Keys: void rotate()>";
        String field = "<example.Key: int keyId>";
        String consumeSite = helper + "#u3";
        String publishSite = helper + "#u7";
        Map<String, Object> region = fullRegion();
        region.put(ConfiguredSourcePhaseContract.DECLARATION_FIELD,
                Arrays.asList(
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", field, helper, 3),
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", field, helper, 7)));
        File regions = jsonl("source-phase-regions.jsonl", region);
        File edges = jsonl("source-phase-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("source-phase-refined.jsonl", refined);

        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t", 7,
                        ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t", 7,
                        TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                // The phase helper is in the recorded root subtree, but not
                // in activation.callIds: it is selected for rich tracing only.
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t", 7,
                        helper, 30, "example.Keys", 3, 2, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                // Same static site in another, unrelated activation must not
                // be admitted merely because its event is later in the trace.
                new RuntimeRegionPlanner.MethodEvent(9, "test", "other", 8,
                        helper, 40, "example.Keys", 99, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(4,
                        "CALL_SITE_ENTER", helper, 3, 301, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(5,
                        "CALL_SITE_ENTER", helper, 3, 302, 0,
                        publishSite, "<example.Hook: void publish()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6,
                        "CALL_SITE_ENTER", helper, 3, 303, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(7,
                        "CALL_SITE_ENTER", helper, 3, 304, 0,
                        publishSite, "<example.Hook: void publish()>",
                        -1, "", 0, "", null, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(8, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(10,
                        "CALL_SITE_ENTER", helper, 99, 901, 0,
                        consumeSite, "<example.Hook: int consume()>",
                        -1, "", 0, "", null, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile,
                Collections.singletonList(activation("REGION.1", 1, ROOT,
                        Arrays.asList(1L, 2L))), methods, runtime,
                Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        List<Map<String, Object>> phases = rows(plan.get(
                ConfiguredSourcePhaseContract.PLAN_FIELD));
        assertEquals(4, phases.size());
        assertEquals(Arrays.asList("PUBLISH", "PUBLISH", "PUBLISH",
                        "PUBLISH"),
                Arrays.asList(phases.get(0).get("phaseKind"),
                        phases.get(1).get("phaseKind"),
                        phases.get(2).get("phaseKind"),
                        phases.get(3).get("phaseKind")));
        assertEquals(Arrays.asList(1L, 1L, 2L, 2L), Arrays.asList(
                ((Number) phases.get(0).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(1).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(2).get("baselineOrdinal")).longValue(),
                ((Number) phases.get(3).get("baselineOrdinal")).longValue()));
        assertEquals(4L, phases.get(0).get("eventSeq"));
        assertEquals(301L, phases.get(0).get("invocationId"));
        assertEquals(3L, phases.get(0).get("ownerCallId"));
        assertEquals(Arrays.asList(3L, 2L, 1L),
                phases.get(0).get("enclosingCallIds"));
        assertEquals(ConfiguredSourcePhaseContract.phaseId(
                        String.valueOf(plan.get("occurrenceId")), consumeSite,
                        ConfiguredSourcePhaseContract.Phase.PUBLISH, 1),
                phases.get(0).get("phaseId"));
        List<Map<String, Object>> plannedBranches = rows(
                ((List<Map<String, Object>>) plan.get("closureGoals"))
                        .get(0).get("branches"));
        assertEquals(2L, plannedBranches.get(0).get("selectedCallId"));
        // The occurrence-level rows survive the strict plan decoder.  The
        // scheduler's task constructor copies this field verbatim.
        assertEquals(4, RegionInstancePlan.decode(
                GSON.toJsonTree(plan).getAsJsonObject()).json()
                .getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .size());
    }

    private static String goalKind(Map<String, Object> plan) {
        List<?> goals = (List<?>) plan.get("closureGoals");
        assertEquals(1, goals.size());
        return String.valueOf(((Map<?, ?>) goals.get(0)).get("kind"));
    }

    /**
     * Two activations of one region template stay two occurrences all the way
     * through: distinct identities and bounded path seeds over one shared
     * source and relation, distinct lanes on the edge that joins them, and an
     * occurrence stamped on every published port artifact.
     */
    @Test
    public void repeatedRootActivationsRemainDistinctOccurrences()
            throws Exception {
        Map<String, Object> region = fullRegion();
        region.put("runtimeOccurrenceIds", retained("REGION.1", 1, 2));
        region.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.call3", "rootCallId", 3,
                "rootKind", "RECEIVER", "sourceKind", "RECEIVER_FIELD")));
        region.put("outputs", Collections.singletonList(object(
                "portId", "REGION.1.out.call1", "rootCallId", 1,
                "rootKind", "RECEIVER", "sourceKind", "RECEIVER_FIELD")));
        File regions = jsonl("reused-regions.jsonl", region);
        File edges = jsonl("reused-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.same-region",
                "fromRegion", "REGION.1", "toRegion", "REGION.1",
                "fromPort", "REGION.1.out.call1",
                "toPort", "REGION.1.in.call3",
                "fromRootCallId", 1, "toRootCallId", 3));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("reused-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        7, 101, 0, 0, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        7, 102, 101, 0, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0,
                        8, 201, 0, 0, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0,
                        8, 202, 201, 0, null, false, "", ""));
        // The two activations decided the same branch site the two opposite
        // ways, so their bounded paths are not the same path.
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.TRUE, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, runtime, Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        assertEquals(2, result.runtimeInstances.size());
        assertEquals(1, result.edgeValidations.size());
        Map<String, Object> first = result.regionPlans.get(0);
        Map<String, Object> second = result.regionPlans.get(1);
        assertEquals(first.get("sourceKey"), second.get("sourceKey"));
        assertEquals(first.get("relationKey"), second.get("relationKey"));
        assertTrue(!first.get("occurrenceId").equals(
                second.get("occurrenceId")));
        assertEquals(1, rows(first.get("closureGoals")).size());
        assertEquals(1, rows(second.get("closureGoals")).size());
        assertFalse(first.containsKey("occurrences"));
        assertFalse(first.containsKey("logicalRegionId"));
        String binding = String.valueOf(result.edgeValidations.get(0));
        assertTrue(binding.contains(String.valueOf(first.get("occurrenceId"))));
        assertTrue(binding.contains(String.valueOf(second.get("occurrenceId"))));
        assertTrue(binding.contains("REGION.1.out.call1"));
        assertTrue(binding.contains("REGION.1.in.call3"));
        assertTrue(binding.contains("fromLaneId=7"));
        assertTrue(binding.contains("toLaneId=8"));

        // Every published occurrence decodes as one region instance plan.
        for (Map<String, Object> plan : result.regionPlans) {
            RegionInstancePlan.decode(
                    GSON.toJsonTree(plan).getAsJsonObject());
        }

        // The recorded call id is resolved once, at activation binding.
        // Every published port then names the occurrence that owns it, so
        // nothing downstream can separate two activations by a trace id.
        Map<String, Object> catalog = result.regionCatalog.get(0);
        assertEquals(second.get("occurrenceId"),
                rows(catalog.get("symbolicInputs")).get(0)
                        .get("occurrenceId"));
        assertEquals(first.get("occurrenceId"),
                rows(catalog.get("outputs")).get(0).get("occurrenceId"));
    }

    /**
     * Identity comes from the selected target event's source, while admission
     * still counts every compatible root entry the workload made -- including
     * the activations the failure closure discarded.
     */
    @Test
    public void targetOccurrenceUsesSelectedTargetSourceAndCausalAnchor()
            throws Exception {
        Map<String, Object> region = fullRegion();
        rows(region.get("branchPolicies")).get(0).put(
                "failureTarget", true);
        // The identity prefix is the selected target event's source, so the
        // retained occurrence of this region is named on that source.
        region.put("runtimeOccurrenceIds", Collections.singletonList(
                "cluster0/dn1#epoch1/region/REGION.1#1"));
        File regions = jsonl("target-source-regions.jsonl", region);
        File edges = jsonl("target-source-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("target-source-refined.jsonl", refined);
        SourceRef client = new SourceRef("EXTERNAL_APP", "CLIENT",
                "cluster0/client0", 0);
        SourceRef server = new SourceRef("CLUSTER_NODE", "DATANODE",
                "cluster0/dn1", 1);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        7, 101, 0, 0, client, true, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        8, 202, 101, 150, server, false,
                        "request#1", "api"));
        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Collections.singletonList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))), events,
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 2, 0, 0, TARGET + "#u4", "", -1,
                                "", 0, "", Boolean.FALSE, null, "", "")),
                Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.get(0);
        assertEquals(server.key(), plan.get("sourceKey"));
        assertTrue(String.valueOf(plan.get("occurrenceId"))
                .startsWith(server.key() + "/region/"));
        assertEquals("SELECTED_TARGET_EVENT_SOURCE",
                plan.get("sourceAuthority"));
        Map<?, ?> anchor = (Map<?, ?>) ((Map<?, ?>) plan.get("rootSelector"))
                .get("causalAnchor");
        // The address names the source the activation ran on and the request
        // scope it ran inside, and holds no invocation ordinal at all.
        assertEquals(client.key(), anchor.get("sourceKey"));
        // The address is the stable source and nothing else: a request scope
        // is ambient context a replay of a long-lived service never republishes.
        // REGISTERED_SOURCE because this root's own receiver named that
        // source; see the INHERITED_CONTEXT case below for the other half.
        assertEquals("REGISTERED_SOURCE", anchor.get("kind"));
        assertFalse(anchor.containsKey("requestKeys"));
        assertFalse(((Map<?, ?>) plan.get("rootSelector"))
                .containsKey("occurrenceIndex"));

        // A replay address must survive an activation the failure closure
        // discarded: the retained activation is the second entry of its root
        // here, and an address that counted entries would have to say so.
        // This one does not - it names the same source and scope whichever
        // position the activation happens to occupy.
        Map<String, Object> discarding = fullRegion();
        discarding.put("runtimeOccurrenceIds", retained("REGION.1", 2));
        File discardedRegions = jsonl("discarded-regions.jsonl", discarding);
        File discardedEdges = jsonl("discarded-edges.jsonl");
        File discardedRefined = jsonl("discarded-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> repeated = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t",
                        7, ROOT, 30, "example.Root", 3, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t",
                        7, TARGET, 40, "example.Target", 4, 3, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> observed = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""));

        RuntimeRegionPlanner.Result discarded = planFiles(
                discardedRegions, discardedEdges, discardedRefined,
                Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                repeated, observed, Collections.emptyList());

        assertEquals(1, discarded.regionPlans.size());
        Map<String, Object> retainedPlan = discarded.regionPlans.get(0);
        assertTrue(String.valueOf(retainedPlan.get("occurrenceId"))
                .endsWith("#2"));
        Map<?, ?> retainedSelector =
                (Map<?, ?>) retainedPlan.get("rootSelector");
        assertFalse(retainedSelector.containsKey("occurrenceIndex"));
        Map<?, ?> retainedAnchor =
                (Map<?, ?>) retainedSelector.get("causalAnchor");
        assertEquals(RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                retainedAnchor.get("sourceKey"));
        assertEquals("UNREGISTERED_SOURCE", retainedAnchor.get("kind"));
    }

    /**
     * A root whose source is the context its thread inherited is addressed as
     * {@code INHERITED_CONTEXT}, not as a registration it does not have.
     *
     * <p>HDFS-11741 campaign-takeover-19 planned the balancer's own
     * {@code Dispatcher$1} and {@code KeyManager$BlockKeyUpdater} activations
     * on {@code cluster0/client0#epoch0}.  That trace registers exactly one
     * object for that source -- the test's client anchor -- and aliases no
     * balancer class at all, so the stamp came from the thread the test
     * started.  Addressing it as {@code REGISTERED_SOURCE} asked replay to
     * match an alias that never existed and skipped all three tasks.</p>
     */
    @Test
    public void aContextStampedRootIsAddressedAsInheritedContext()
            throws Exception {
        Map<String, Object> region = fullRegion();
        rows(region.get("branchPolicies")).get(0).put(
                "failureTarget", true);
        region.put("runtimeOccurrenceIds", Collections.singletonList(
                "cluster0/dn1#epoch1/region/REGION.1#1"));
        File regions = jsonl("inherited-regions.jsonl", region);
        File edges = jsonl("inherited-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("inherited-refined.jsonl", refined);
        SourceRef client = new SourceRef("EXTERNAL_APP", "CLIENT",
                "cluster0/client0", 0);
        SourceRef server = new SourceRef("CLUSTER_NODE", "DATANODE",
                "cluster0/dn1", 1);
        // The same fixture as the REGISTERED_SOURCE case above, and the only
        // difference is the one that matters: this root's receiver named no
        // source of its own.
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        7, 101, 0, 0, client, false, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        8, 202, 101, 150, server, false,
                        "request#1", "api"));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Collections.singletonList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))), events,
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 2, 0, 0, TARGET + "#u4", "", -1,
                                "", 0, "", Boolean.FALSE, null, "", "")),
                Collections.emptyList());

        Map<?, ?> anchor = (Map<?, ?>) ((Map<?, ?>) result.regionPlans.get(0)
                .get("rootSelector")).get("causalAnchor");
        assertEquals(client.key(), anchor.get("sourceKey"));
        assertEquals("INHERITED_CONTEXT", anchor.get("kind"));
    }

    @Test
    public void semanticSourceOwnsTheOccurrenceOrdinalNamespace()
            throws Exception {
        Map<String, Object> region = fullRegion();
        rows(region.get("branchPolicies")).get(0).put(
                "failureTarget", true);
        SourceRef dn0 = new SourceRef("CLUSTER_NODE", "DATANODE",
                "cluster0/dn0", 1);
        SourceRef dn1 = new SourceRef("CLUSTER_NODE", "DATANODE",
                "cluster0/dn1", 1);
        SourceRef client = new SourceRef("EXTERNAL_APP", "CLIENT",
                "cluster0/client0", 0);
        region.put("runtimeOccurrenceIds", Arrays.asList(
                OccurrenceMinter.occurrenceId(client.key(), "REGION.1", 1),
                OccurrenceMinter.occurrenceId(client.key(), "REGION.1", 2)));

        File regions = jsonl("semantic-ordinal-regions.jsonl", region);
        File edges = jsonl("semantic-ordinal-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("semantic-ordinal-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "dn0",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        7, 101, 0, 0, dn0, false, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "dn0",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        7, 101, 0, 0, client, false, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "dn1",
                        8, ROOT, 30, "example.Root", 3, 0, 0,
                        8, 202, 0, 0, dn1, false, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "dn1",
                        8, TARGET, 40, "example.Target", 4, 3, 0,
                        8, 202, 0, 0, client, false, "request#1", "api"));
        List<RuntimeRegionPlanner.RuntimeEvent> observed = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, observed, Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        assertEquals(OccurrenceMinter.occurrenceId(
                        client.key(), "REGION.1", 1),
                result.regionPlans.get(0).get("occurrenceId"));
        assertEquals(OccurrenceMinter.occurrenceId(
                        client.key(), "REGION.1", 2),
                result.regionPlans.get(1).get("occurrenceId"));
        Map<?, ?> firstAnchor = (Map<?, ?>) ((Map<?, ?>) result.regionPlans
                .get(0).get("rootSelector")).get("causalAnchor");
        Map<?, ?> secondAnchor = (Map<?, ?>) ((Map<?, ?>) result.regionPlans
                .get(1).get("rootSelector")).get("causalAnchor");
        assertEquals(dn0.key(), firstAnchor.get("sourceKey"));
        assertEquals(dn1.key(), secondAnchor.get("sourceKey"));
    }

    @SuppressWarnings("unchecked")
    /**
     * README {@code OCC-1}, ambiguity half.  Two activations of one root on
     * one source inside one request scope produce two occurrence identities
     * and <em>one</em> replay address; the plan carries both rows.
     */
    @Test
    public void repeatedActivationsSharingOneReplayAddressStayTwoPlans()
            throws Exception {
        Map<String, Object> region = fullRegion();
        region.put("runtimeOccurrenceIds", retained("REGION.1", 1, 2));
        File regions = jsonl("ambiguous-address-regions.jsonl", region);
        File edges = jsonl("ambiguous-address-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("ambiguous-address-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
        List<RuntimeRegionPlanner.RuntimeEvent> observed = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.FALSE, null, "", ""),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", "", -1, "", 0, "", Boolean.TRUE, null, "", ""));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, observed, Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        Map<String, Object> first = result.regionPlans.get(0);
        Map<String, Object> second = result.regionPlans.get(1);
        // Two identities, one address: the exact shape the gap is about.
        assertFalse(first.get("occurrenceId").equals(
                second.get("occurrenceId")));
        assertEquals(first.get("rootSelector"), second.get("rootSelector"));
    }

    /**
     * README {@code STATE-1}: two receiver paths to one declared field are
     * two locations.  Deduping carrier declarations by
     * {@code declaringClass#fieldName} kept whichever port was enumerated
     * first and dropped the other with no row of any kind - the HDFS-11741
     * {@code allKeys} shape, where the dropped owner is as likely to be the
     * one the target reads.
     */
    @Test
    public void twoReceiverPathsToOneFieldStayTwoDeclaredCarriers()
            throws Exception {
        String allKeys = "<example.Node: java.util.Map allKeys>";
        Map<String, Object> region = fullRegion();
        region.put("symbolicInputs", Arrays.asList(
                object("portId", "REGION.1.in.nn", "rootCallId", 1,
                        "rootKind", "RECEIVER", "sourceKind",
                        "RECEIVER_FIELD",
                        "fieldPath", Arrays.asList("nn", "allKeys"),
                        "fieldPathDeclarations", Arrays.asList(
                                "<example.Holder: example.Node nn>",
                                allKeys)),
                object("portId", "REGION.1.in.dn", "rootCallId", 1,
                        "rootKind", "RECEIVER", "sourceKind",
                        "RECEIVER_FIELD",
                        "fieldPath", Arrays.asList("dn", "allKeys"),
                        "fieldPathDeclarations", Arrays.asList(
                                "<example.Holder: example.Node dn>",
                                allKeys))));
        File regions = jsonl("two-owner-carrier-regions.jsonl", region);
        File edges = jsonl("two-owner-carrier-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("two-owner-carrier-refined.jsonl", refined);
        Map<String, Object> seed = activation("REGION.1", 1, ROOT,
                Arrays.asList(1L, 2L));
        seed.put(RuntimeRegionPlanner.ADMISSION_BASIS,
                RuntimeRegionPlanner.SHARED_LOCATION_DEMAND_ADMISSION);
        seed.put(RuntimeRegionPlanner.DEMANDED_SHARED_LOCATIONS,
                Collections.singletonList("example.Node#allKeys"));

        RuntimeRegionPlanner.Result result = planFiles(
                regions, edges, refinedFile,
                Collections.singletonList(seed), methods(), runtime(),
                Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        Map<String, Object> goal = rows(result.regionPlans.get(0)
                .get("closureGoals")).get(0);
        List<Map<String, Object>> carriers = rows(goal.get("sharedCarriers"));
        assertEquals(String.valueOf(carriers), 2, carriers.size());
        Set<Object> paths = new LinkedHashSet<>();
        for (Map<String, Object> carrier : carriers) {
            assertEquals("example.Node", carrier.get("declaringClass"));
            assertEquals("allKeys", carrier.get("fieldName"));
            paths.add(carrier.get("fieldPath"));
        }
        assertEquals(2, paths.size());
        assertTrue(paths.contains(Arrays.asList("nn", "allKeys")));
        assertTrue(paths.contains(Arrays.asList("dn", "allKeys")));

    }


    /**
     * README REGION-1: a port written in several bounded phases of one local
     * occurrence stays one demand of one coarse task.  Every recorded write
     * version is still modelled - in recorded write order - and the versions
     * a declared bound cannot hold are counted rather than dropped in
     * silence.
     */
    @Test
    public void repeatedWritesOfOneOccurrenceStayVersionsOfOneDemand() {
        String endpoint = "HEAP\nDECLARED_FIELD_ACCESS\n" + ROOT
                + "#u5\n\n<example.Node: int state>";
        Map<String, Object> first = object("edgeId", "RF.first",
                "fromOutputPort", "REGION.1.out.state",
                "writerEventSeq", 30L);
        Map<String, Object> second = object("edgeId", "RF.second",
                "fromOutputPort", "REGION.1.out.state",
                "writerEventSeq", 90L);
        Map<String, List<Map<String, Object>>> byEndpoint =
                new LinkedHashMap<>();
        byEndpoint.put(endpoint, Arrays.asList(second, first));

        Map<String, List<List<Map<String, Object>>>> versions =
                RuntimeRegionPlanner.demandedBindingVersions(
                        Collections.singletonList(endpoint), byEndpoint, 8);

        assertEquals(2, versions.get(endpoint).size());
        assertEquals("RF.first", versions.get(endpoint).get(0).get(0)
                .get("edgeId"));
        assertEquals("RF.second", versions.get(endpoint).get(1).get(0)
                .get("edgeId"));

        Map<String, List<List<Map<String, Object>>>> boundedVersions =
                RuntimeRegionPlanner.demandedBindingVersions(
                        Collections.singletonList(endpoint), byEndpoint, 1);

        assertEquals(1, boundedVersions.get(endpoint).size());
    }

    /**
     * The bounded versions of one endpoint fold into the single closure
     * member REGION-1 requires, and the fold subtracts nothing: every
     * version's causal delivery edge, input port and method stays in the
     * demand, the member stays anchored on the last recorded write - the
     * only single boundary that covers all of them - and every version's own
     * dynamic boundary is carried beside it in recorded write order.
     *
     * <p>The anchor alone was the loss the {@code OUTPUT_VERSION_ALIGNMENT_GAP}
     * declared.  With the whole ledger carried there is nothing left for it
     * to declare, so it is no longer published.</p>
     */
    @Test
    public void foldedOutputVersionsKeepEveryVersionsOwnEvidence() {
        OutputClosureContract early = versionClosure("RF.first",
                "REGION.1.in.early", "<example.Node: void early()>", 1, 30L);
        OutputClosureContract late = versionClosure("RF.second",
                "REGION.1.in.late", "<example.Node: void late()>", 2, 90L);

        OutputClosureContract folded =
                RuntimeRegionPlanner.coarseOccurrenceOutputVersions(
                        Arrays.asList(early, late));

        assertEquals(1, folded.members().size());
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().causalEdgeIds().containsAll(
                        Arrays.asList("RF.first", "RF.second")));
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().inputPorts().containsAll(
                        Arrays.asList("REGION.1.in.early",
                                "REGION.1.in.late")));
        assertTrue(String.valueOf(folded.toJson()),
                folded.executionScope().methods().containsAll(
                        Arrays.asList("<example.Node: void early()>",
                                "<example.Node: void late()>")));

        OutputClosureContract.Member member = folded.members().get(0);
        assertEquals(90L, member.slice().get("selectedRuntimeEventSeq")
                .getAsLong());
        assertEquals(2, member.slice().get("activationLocalOccurrence")
                .getAsInt());
        assertFalse(String.valueOf(member.slice()),
                member.slice().has("alignmentGaps"));

        // One version is still one member, byte for byte what it was before
        // any fold existed.
        assertEquals(late.closureFingerprint(),
                RuntimeRegionPlanner.coarseOccurrenceOutputVersions(
                        Collections.singletonList(late))
                        .closureFingerprint());
    }

    /** One recorded write version of one demanded heap output port. */
    private static OutputClosureContract versionClosure(
            String edgeId, String inputPort, String method,
            int occurrence, long writeSeq) {
        return versionClosure(edgeId, inputPort, method, occurrence,
                writeSeq, 7L);
    }

    private static OutputClosureContract versionClosure(
            String edgeId, String inputPort, String method,
            int occurrence, long writeSeq, long callId) {
        String port = "REGION.1.out.state";
        String cell = "<example.Node: int state>";
        String site = OutputCaptureSpec.FIELD_WRITE_STATE + ":"
                + ROOT + "#u5:" + cell;
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings(inputPort));
        slice.add("sites", strings(method + "#u1"));
        slice.add("staticSites", strings(ROOT + "#u5"));
        slice.add("methods", strings(method));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("activationLocalOccurrence", occurrence);
        slice.addProperty("selectedRuntimeEventSeq", writeSeq);
        slice.addProperty("selectedRuntimeCallId", callId);
        slice.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.state");
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings("state"));
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", ROOT);
        capture.addProperty("definitionUnitIndex", 5);
        capture.addProperty("outputSiteId", site);
        capture.addProperty("outputOccurrence", occurrence);
        capture.addProperty("replayOccurrence", occurrence);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.REGION_ACTIVATION_SCOPE);
        capture.addProperty("outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);

        return OutputClosureCodec.singleton("REL.REGION.1", "REGION.1", Collections.<String>emptyList(),
                port, cell, "HEAP_STATE", "int", slice);
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Object integral(Object value) {
        if (value instanceof Double && ((Double) value) % 1 == 0) {
            return ((Double) value).longValue();
        }
        if (value instanceof Map) {
            for (Map.Entry<String, Object> entry
                    : ((Map<String, Object>) value).entrySet()) {
                entry.setValue(integral(entry.getValue()));
            }
        } else if (value instanceof List) {
            List<Object> list = (List<Object>) value;
            for (int i = 0; i < list.size(); i++) {
                list.set(i, integral(list.get(i)));
            }
        }
        return value;
    }

    private static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> out = new java.util.ArrayList<>();
        for (Object e : (List<?>) value) {
            if (e instanceof com.google.gson.JsonElement) {
                Map<String, Object> row = new com.google.gson.Gson().fromJson(
                        (com.google.gson.JsonElement) e,
                        new com.google.gson.reflect.TypeToken<
                                LinkedHashMap<String, Object>>() {}.getType());
                out.add((Map<String, Object>) integral(row));
            } else {
                out.add((Map<String, Object>) e);
            }
        }
        return out;
    }

    private static List<RuntimeRegionPlanner.MethodEvent> methods() {
        return Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0, 0L, 0L, 0L, 0L, null, false, "", ""),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0, 0L, 0L, 0L, 0L, null, false, "", ""));
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> runtime() {
        return Collections.singletonList(new RuntimeRegionPlanner.RuntimeEvent(
                3, "BRANCH", TARGET, 2, 0, 0, TARGET + "#u4", "", -1,
                "", 0, "", Boolean.FALSE, null, "", ""));
    }

    private static Map<String, Object> activation(
            String region, long call, String method, List<Long> calls) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_REGION_ACTIVATION",
                "regionId", region,
                "rootCallId", call,
                "rootMethod", method,
                "selection", "STATE_CONTEXT",
                "callIds", calls,
                "observedMethods", method.equals(ROOT)
                        ? Arrays.asList(ROOT, TARGET)
                        : Collections.singletonList(method));
    }

    /**
     * Identities the region finalizer mints for the numbered observed
     * activations of {@code regionId} in a workload that registered no
     * source.  Retention is stated by identity, never by a recorded call.
     */
    private static List<String> retained(String regionId, int... ordinals) {
        List<String> result = new ArrayList<>();
        for (int ordinal : ordinals) {
            result.add("workload/unregistered#epoch0/region/" + regionId
                    + "#" + ordinal);
        }
        return result;
    }

    private static Map<String, Object> fullRegion() {
        Map<String, Object> branch = object("siteId", TARGET + "#u4",
                "method", TARGET, "unitIndex", 4,
                "requiredOutcome", false, "policy", "EXPLORE");
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1", "rootMethod", ROOT,
                "anchorMethod", TARGET,
                "selection", "EXCEPTION_CONTEXT",
                "runtimeOccurrenceIds", retained("REGION.1", 1),
                "methods", Arrays.asList(ROOT, TARGET),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.singletonList(branch));
    }

    private static Map<String, Object> communicationParent(
            String portId, String exchange, String side, String role,
            String capture, String method, int unitIndex, String callee,
            int argumentIndex) {
        Map<String, Object> port = object(
                "portId", portId,
                "sourceKind", "COMMUNICATION_SITE_PORT",
                "dependencyRole", role,
                "javaType", "java.lang.String",
                "direction", "REQUEST",
                "handoffLeafPath", "p0",
                "exchangeSiteKey", exchange,
                "outputCaptureKind", capture,
                "definitionMethod", method,
                "argumentIndex", argumentIndex);
        if (unitIndex >= 0) port.put("definitionUnitIndex", unitIndex);
        if (!callee.isEmpty()) port.put("declaredCallee", callee);
        return port;
    }

    private static Map<String, Object> communicationComponent(
            String portId, String parentId, String exchange, String side) {
        return object(
                "portId", portId,
                "sourceKind", "COMMUNICATION_SITE_PORT",
                "dependencyRole", "VALUE_FRONTIER",
                "javaType", "int",
                "direction", "REQUEST",
                "componentOfPortId", parentId,
                "encodingAuthority", "TEST_ENCODING_V1",
                "handoffLeafPath", "HANDSHAKE/keyId",
                "exchangeSiteKey", exchange,
                "manualCarrierClass", "OUT".equals(side)
                        ? "example.ExportCarrier" : "example.AttachCarrier",
                "manualCarrierField", "keyId",
                "manualCarrierDescriptor", "I");
    }

    private static Map<String, Object> candidateEdge() {
        return object("schemaVersion", 3, "id", "DF.1",
                "kind", "exception_guard", "transferKind", "GUARD",
                "method", TARGET, "siteId", TARGET + "#u4",
                "fromCell", "guard", "toCell", "exception");
    }

    private static Map<String, Object> runtimeReadFrom(
            String edgeId, String occurrence, String inputPort,
            long writerSeq, long readerSeq) {
        return object("schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", edgeId,
                "evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1",
                "correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                "fromOccurrenceId", "node/writer#epoch0/region/REGION.W#1",
                "toOccurrenceId", occurrence,
                "fromOutputPort", "REGION.W.out." + edgeId,
                "toInputPort", inputPort,
                "receiverObjectId", 17,
                "writerEventSeq", writerSeq,
                "readerEventSeq", readerSeq,
                "writerLaneId", "1",
                "readerLaneId", "2",
                "programOrderRequired", false);
    }

    @SafeVarargs
    private final File jsonl(String name, Map<String, Object>... rows)
            throws Exception {
        List<String> lines = new ArrayList<>();
        for (Map<String, Object> row : rows) {
            lines.add(GSON.toJson(row));
        }
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), lines, StandardCharsets.UTF_8);
        return file;
    }

    /** The recorded root call the finalizer stamps this port's owner from. */
    private static Map<String, Object> ownedByRootCall(
            Map<String, Object> port, long rootCallId) {
        port.put("rootCallId", rootCallId);
        return port;
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }

    private static RuntimeRegionPlanner.Result planFiles(
            File regionFile, File regionEdgeFile, File refinedGraphFile,
            Collection<Map<String, Object>> runtimeSeeds,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents,
            List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents) {
        return RuntimeRegionPlanner.plan(
                RuntimeRegionPlanner.read(regionFile),
                RuntimeRegionPlanner.read(regionEdgeFile),
                RuntimeRegionPlanner.RefinedFlowIndex.read(refinedGraphFile),
                String.valueOf(regionFile), String.valueOf(regionEdgeFile),
                runtimeSeeds, methods, runtimeEvents, fieldEvents,
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList());
    }

    /**
     * The failure-directed bound on heap-write capture demands.
     *
     * <p>A write is demanded when the fatal occurrence reads it, or when a
     * producer of something the fatal occurrence reads states it in the
     * dependency slice that closed that output, or when it writes an object
     * some already demanded write also states.  A write on no such chain is
     * not demanded, and with no fatal occurrence at all nothing is bounded.
     * </p>
     */
    @Test
    public void heapWriteDemandIsBoundedByWhatTheFailureReads() {
        List<Map<String, Object>> plans = Arrays.asList(
                targetPlan("occ.T", "R.T.in.key"),
                producerPlan("occ.P"), producerPlan("occ.C"),
                producerPlan("occ.N"), producerPlan("occ.M"),
                producerPlan("occ.X"));
        List<Map<String, Object>> edges = Arrays.asList(
                // The fatal occurrence reads this write.
                flowEdge("occ.P", "R.P.out.key", "occ.T", "R.T.in.key",
                        11L, 12L),
                // Same object as the demanded write: one object's state.
                flowEdge("occ.P", "R.P.out.sibling", "occ.X", "R.X.in.s",
                        11L, 0L),
                // Publishes the demanded object to its reader.
                flowEdge("occ.C", "R.C.out.holder", "occ.X", "R.X.in.h",
                        31L, 11L),
                // The demanded output's own slice states this input.
                flowEdge("occ.C", "R.C.out.v", "occ.P", "R.P.in.v",
                        21L, 0L),
                // An input of the same producer its slice does not state.
                flowEdge("occ.N", "R.N.out.noise", "occ.P", "R.P.in.noise",
                        41L, 0L),
                // Read only by an occurrence nothing fatal depends on.
                flowEdge("occ.M", "R.M.out.metric", "occ.X", "R.X.in.m",
                        99L, 0L));
        Map<String, List<String>> sliceInputs = new LinkedHashMap<>();
        sliceInputs.put("occ.P\nR.P.out.key",
                Collections.singletonList("R.P.in.v"));
        sliceInputs.put("occ.P\nR.P.out.sibling",
                Collections.<String>emptyList());
        sliceInputs.put("occ.C\nR.C.out.v", Collections.<String>emptyList());
        sliceInputs.put("occ.C\nR.C.out.holder",
                Collections.<String>emptyList());
        sliceInputs.put("occ.N\nR.N.out.noise",
                Collections.<String>emptyList());
        sliceInputs.put("occ.M\nR.M.out.metric",
                Collections.<String>emptyList());
        List<String> heapOutputs = new ArrayList<>(sliceInputs.keySet());

        Set<String> demanded = RuntimeRegionPlanner.failureDemandedOutputs(
                plans, edges, sliceInputs, heapOutputs);

        assertTrue(String.valueOf(demanded),
                demanded.contains("occ.P\nR.P.out.key"));
        assertTrue(String.valueOf(demanded),
                demanded.contains("occ.C\nR.C.out.v"));
        assertTrue(String.valueOf(demanded),
                demanded.contains("occ.P\nR.P.out.sibling"));
        assertTrue(String.valueOf(demanded),
                demanded.contains("occ.C\nR.C.out.holder"));
        assertFalse(String.valueOf(demanded),
                demanded.contains("occ.N\nR.N.out.noise"));
        assertFalse(String.valueOf(demanded),
                demanded.contains("occ.M\nR.M.out.metric"));

        // No fatal occurrence, so no failure to direct the bound: every
        // demand stands, exactly as it did before the bound existed.
        List<Map<String, Object>> withoutTarget = new ArrayList<>(plans);
        withoutTarget.set(0, producerPlan("occ.T"));
        assertEquals(null, RuntimeRegionPlanner.failureDemandedOutputs(
                withoutTarget, edges, sliceInputs, heapOutputs));
    }

    private static Map<String, Object> targetPlan(String occurrenceId,
                                                  String inputPort) {
        Map<String, Object> symbol = new LinkedHashMap<>();
        symbol.put("portId", inputPort);
        Map<String, Object> goal = new LinkedHashMap<>();
        goal.put("kind", "TARGET_REACH_CLOSURE");
        goal.put("symbolize", Collections.singletonList(symbol));
        return occurrencePlan(occurrenceId, goal);
    }

    private static Map<String, Object> producerPlan(String occurrenceId) {
        Map<String, Object> goal = new LinkedHashMap<>();
        goal.put("kind", "OUTPUT_RELATION_CLOSURE");
        return occurrencePlan(occurrenceId, goal);
    }

    private static Map<String, Object> occurrencePlan(String occurrenceId,
                                                     Map<String, Object> goal) {
        Map<String, Object> plan = new LinkedHashMap<>();
        plan.put("occurrenceId", occurrenceId);
        plan.put("closureGoals", Collections.singletonList(goal));
        return plan;
    }

    private static Map<String, Object> flowEdge(
            String producer, String output, String consumer, String input,
            long receiverObjectId, long valueObjectId) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", "RUNTIME_FIELD_FLOW");
        edge.put("fromOccurrenceId", producer);
        edge.put("fromOutputPort", output);
        edge.put("toOccurrenceId", consumer);
        edge.put("toInputPort", input);
        edge.put("receiverObjectId", receiverObjectId);
        edge.put("valueObjectId", valueObjectId);
        return edge;
    }
}
