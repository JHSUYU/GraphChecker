package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
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
                        serviceLoop, 11, "example.Actor", 10, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "actor", 7,
                        interaction, 11, "example.Actor", 11, 10, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "actor", 7,
                        protocol, 11, "example.Actor", 12, 11, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "actor", 7,
                        writer, 22, "example.Keys", 13, 12, 0));

        RuntimeRegionPlanner.MethodEvent selected = RuntimeRegionPlanner
                .firstCompatibleReplayContinuation(chain,
                        new LinkedHashSet<>(Arrays.asList(
                                interaction, protocol, writer)));

        assertEquals(interaction, selected.method);
        assertEquals("example.Actor", selected.receiverType);
    }

    @Test
    public void callChainContinuationNeverGuessesFromSelectedMethodOrder() {
        String root = "<example.Actor: void run()>";
        String unobserved = "<example.Actor: void configuredOnly()>";
        List<RuntimeRegionPlanner.MethodEvent> chain = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "actor", 7,
                        root, 11, "example.Actor", 10, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "actor", 7,
                        "<example.Actor: void helper()>", 11,
                        "example.Actor", 11, 10, 0));

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
                        7, 10, 0, 0, server),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "rpc-worker",
                        7, receiver, 0, "", 101, 100, 0,
                        7, 10, 0, 0, server),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "rpc-worker",
                        7, helper, 0, "", 102, 101, 0,
                        7, 10, 0, 0, server));

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
        assertTrue(result.gaps.isEmpty());
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

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
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
        Map<String, Object> region = object("outputs",
                Arrays.asList(parent, component));

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
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "producer",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "consumer",
                        8, ROOT, 30, "example.Root", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "consumer",
                        8, TARGET, 40, "example.Target", 4, 3, 0));
        // The fatal site executed in the second activation only.
        List<RuntimeRegionPlanner.RuntimeEvent> observed =
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 4, 0, 0, TARGET + "#u4", -1, "", 0,
                                "", true, false));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
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
                        7, 101, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        7, 102, 101, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0,
                        8, 201, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0,
                        8, 202, 201, 0));
        // The two activations decided the same branch site the two opposite
        // ways, so their bounded paths are not the same path.
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        true));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
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
                        7, 101, 0, 0, client, "request#1", "api"),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        8, 202, 101, 150, server,
                        "request#1", "api"));
        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Collections.singletonList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))), events,
                Collections.singletonList(
                        new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH",
                                TARGET, 2, 0, 0, TARGET + "#u4", -1,
                                "", 0, "", true, false)),
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
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "t",
                        7, ROOT, 30, "example.Root", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "t",
                        7, TARGET, 40, "example.Target", 4, 3, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> observed = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", -1, "", 0, "", true, false),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", -1, "", 0, "", true, false));

        RuntimeRegionPlanner.Result discarded = RuntimeRegionPlanner.plan(
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

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        return (List<Map<String, Object>>) value;
    }

    private static List<RuntimeRegionPlanner.MethodEvent> methods() {
        return Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0));
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> runtime() {
        return Collections.singletonList(new RuntimeRegionPlanner.RuntimeEvent(
                3, "BRANCH", TARGET, 2, 0, 0, TARGET + "#u4", -1,
                "", 0, "", true, false));
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

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }
}
