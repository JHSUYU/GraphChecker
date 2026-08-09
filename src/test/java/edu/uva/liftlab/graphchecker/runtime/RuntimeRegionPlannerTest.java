package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import edu.uva.liftlab.graphchecker.causynth.ProtocolCarrierReconstruction;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
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
import static org.junit.Assert.fail;

public class RuntimeRegionPlannerTest {
    private static final Gson GSON = new Gson();
    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String RPC = "<example.Rpc: void receive()>";
    private static final String CALLBACK = "<example.Callback: void handle()>";
    private static final String WRITER = "<example.Writer: void update()>";
    private static final String STATE_UPDATE =
            "<example.State: void update(java.lang.Object)>";
    private static final String RPC_RESULT =
            "<example.Rpc: java.lang.Object receive()>";
    private static final String SERVER_RETURN =
            "<example.Server: example.Response reply()>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void firstPassSelectsConcreteActivation() throws Exception {
        File skeletons = jsonl("skeletons.jsonl", skeleton());
        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, methods());

        assertEquals(1, result.staticRegionCount);
        assertEquals(1, result.runtimeInstances.size());
        Map<String, Object> activation = result.runtimeInstances.get(0);
        assertEquals(1L, ((Number) activation.get("rootCallId")).longValue());
        assertEquals(Collections.singletonList("REGION.1"),
                activation.get("regionIds"));
        assertTrue(String.valueOf(activation.get("observedMethods"))
                .contains(TARGET));
    }

    @Test
    public void firstPassRejectsNonAuthoritativeStaticRoot()
            throws Exception {
        Map<String, Object> broad = skeleton();
        broad.put("rootMethod", "<example.Unobserved: void setup()>");
        broad.remove("rootAuthority");
        File skeletons = jsonl("broad-skeletons.jsonl", broad);

        try {
            RuntimeRegionPlanner.planSkeletonGraph(skeletons, methods());
            fail("non-authoritative root must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("authoritative"));
        }
    }

    @Test
    public void protocolAnchorRemainsInsideAuthoritativeActivation()
            throws Exception {
        Map<String, Object> protocol = skeleton();
        protocol.put("rootMethod", ROOT);
        protocol.put("selection", "PROTOCOL_CONTEXT");
        File skeletons = jsonl("protocol-skeletons.jsonl", protocol);

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, methods());

        assertEquals(1, result.runtimeInstances.size());
        assertEquals(ROOT,
                result.runtimeInstances.get(0).get("rootMethod"));
        assertEquals(Arrays.asList(ROOT, TARGET),
                result.runtimeInstances.get(0).get("observedMethods"));
    }

    @Test
    public void repeatedLoopHelperCallsStayInOneRegionInstance()
            throws Exception {
        File skeletons = jsonl("loop-skeletons.jsonl", skeleton());
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 3, 1, 0));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, events);

        assertEquals(1, result.runtimeInstances.size());
        assertEquals(Arrays.asList(1L, 2L, 3L),
                result.runtimeInstances.get(0).get("callIds"));
    }

    @Test
    public void repeatedTaskActivationCreatesTwoInstancesOfOneRegion()
            throws Exception {
        File skeletons = jsonl("activation-skeletons.jsonl", skeleton());
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 4, 3, 0));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, events);

        assertEquals(2, result.runtimeInstances.size());
        assertEquals("REGION.1", result.runtimeInstances.get(0).get("regionId"));
        assertEquals("REGION.1", result.runtimeInstances.get(1).get("regionId"));
    }

    @Test
    public void configuredRpcHandlerRemainsItsOwnActivation()
            throws Exception {
        Map<String, Object> owner = object("schemaVersion", 3,
                "kind", "REGION_SKELETON", "regionId", "REGION.OWNER",
                "rootMethod", ROOT, "rootAuthority", "TASK_ENTRY",
                "anchorMethod", ROOT,
                "anchorMethods", Collections.singletonList(ROOT),
                "methods", Collections.singletonList(ROOT),
                "selection", "STATE_CONTEXT");
        Map<String, Object> rpc = object("schemaVersion", 3,
                "kind", "REGION_SKELETON", "regionId", "REGION.RPC",
                "rootMethod", RPC, "rootAuthority", "RPC_HANDLER",
                "anchorMethod", TARGET,
                "anchorMethods", Collections.singletonList(TARGET),
                "methods", Arrays.asList(RPC, TARGET),
                "selection", "EXCEPTION_CONTEXT");
        File skeletons = jsonl("nested-rpc-skeletons.jsonl", owner, rpc);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, RPC, 20, "example.Rpc", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t",
                        7, TARGET, 30, "example.Target", 3, 2, 0));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, events);

        assertEquals(2, result.runtimeInstances.size());
        Map<String, Object> ownerActivation = result.runtimeInstances.get(0);
        Map<String, Object> rpcActivation = result.runtimeInstances.get(1);
        assertEquals("REGION.OWNER", ownerActivation.get("regionId"));
        assertEquals(ROOT, ownerActivation.get("rootMethod"));
        assertEquals("REGION.RPC", rpcActivation.get("regionId"));
        assertEquals(RPC, rpcActivation.get("rootMethod"));
        assertEquals("EXCEPTION_CONTEXT", rpcActivation.get("selection"));
        assertEquals(TARGET, rpcActivation.get("anchorMethod"));
    }

    @Test
    public void explicitNestedFragmentBindsToNearestAuthoritativeActivation()
            throws Exception {
        Map<String, Object> owner = object("schemaVersion", 3,
                "kind", "REGION_SKELETON", "regionId", "REGION.OWNER",
                "rootMethod", ROOT, "rootAuthority", "TASK_ENTRY",
                "anchorMethod", "",
                "anchorMethods", Collections.emptyList(),
                "methods", Collections.singletonList(ROOT),
                "selection", "AUTHORITY_ENVELOPE");
        Map<String, Object> nested = object("schemaVersion", 3,
                "kind", "REGION_SKELETON", "regionId", "REGION.NESTED",
                "rootMethod", RPC, "rootAuthority", "NESTED_CALL",
                "anchorMethod", TARGET,
                "anchorMethods", Collections.singletonList(TARGET),
                "methods", Arrays.asList(RPC, TARGET),
                "selection", "EXCEPTION_CONTEXT");
        File skeletons = jsonl("nested-fragment-skeletons.jsonl",
                owner, nested);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, CALLBACK, 20, "example.Callback", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t",
                        7, RPC, 30, "example.Rpc", 3, 2, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t",
                        7, TARGET, 40, "example.Target", 4, 3, 0));

        RuntimeRegionPlanner.Result result =
                RuntimeRegionPlanner.planSkeletonGraph(skeletons, events);

        assertEquals(1, result.runtimeInstances.size());
        Map<String, Object> activation = result.runtimeInstances.get(0);
        assertEquals("REGION.OWNER", activation.get("regionId"));
        assertEquals(ROOT, activation.get("rootMethod"));
        assertEquals("EXCEPTION_CONTEXT", activation.get("selection"));
        assertEquals(TARGET, activation.get("anchorMethod"));
        assertEquals(Arrays.asList(1L, 2L, 3L, 4L),
                activation.get("callIds"));
        assertEquals(Arrays.asList(ROOT, CALLBACK, RPC, TARGET),
                activation.get("observedMethods"));
        assertEquals(Arrays.asList("REGION.OWNER", "REGION.NESTED"),
                activation.get("regionIds"));
    }

    @Test
    public void fullPlanningConsumesOnlyRefinedGraph() throws Exception {
        File regions = jsonl("regions.jsonl", fullRegion());
        File edges = jsonl("edges.jsonl");
        File candidate = jsonl("candidate.jsonl", candidateEdge());
        try {
            RuntimeRegionPlanner.plan(regions, edges, candidate, seeds(),
                    methods(),
                    runtime(), Collections.emptyList());
            fail("candidate graph must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("runtime-refined"));
        }

        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("refined.jsonl", refined);
        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, seeds(), methods(), runtime(),
                Collections.emptyList());
        assertEquals(1, result.regionPlans.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        assertEquals(3, plan.get("schemaVersion"));
        assertEquals("CONCOLIC_REGION_PLAN", plan.get("kind"));
        assertTrue(!((Map<?, ?>) plan.get("rootSelector"))
                .containsKey("thread"));
        assertTrue(String.valueOf(plan.get("closureGoals"))
                .contains("TARGET_REACH_CLOSURE"));
    }

    @Test
    public void fullPlanningSkipsActivationRemovedByFailureClosure()
            throws Exception {
        File regions = jsonl("retained-regions.jsonl", fullRegion());
        File edges = jsonl("retained-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("retained-refined.jsonl", refined);
        List<Map<String, Object>> activationSeeds = new ArrayList<>(seeds());
        activationSeeds.add(activation("REGION.1", 2, TARGET,
                Collections.singletonList(2L)));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, activationSeeds, methods(),
                runtime(), Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        assertTrue(String.valueOf(result.regionPlans.get(0)
                .get("regionInstanceId")).contains("#call1"));
    }

    @Test
    public void repeatedRootActivationsShareOneLogicalVmPlan()
            throws Exception {
        Map<String, Object> region = fullRegion();
        region.put("runtimeRootCallIds", Arrays.asList(1, 3));
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
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        99, 7, 101, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        99, 7, 102, 101, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0,
                        99, 8, 201, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0,
                        99, 8, 202, 201, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, runtime, Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        assertEquals(2, result.runtimeInstances.size());
        assertEquals(1, result.edgeValidations.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        assertEquals("REGION.1@owner99", plan.get("logicalRegionId"));
        assertEquals(Arrays.asList(1L, 3L), plan.get("logicalRootCallIds"));
        assertEquals(2, plan.get("logicalInstanceCount"));
        assertTrue(String.valueOf(plan.get("regionInstanceId"))
                .endsWith("#call1"));
        List<Map<String, Object>> occurrences = rows(plan.get(
                "occurrences"));
        assertEquals(2, occurrences.size());
        assertEquals(Arrays.asList(1L, 3L), Arrays.asList(
                ((Number) occurrences.get(0).get("rootCallId")).longValue(),
                ((Number) occurrences.get(1).get("rootCallId")).longValue()));
        assertEquals(Arrays.asList(7L, 8L), Arrays.asList(
                ((Number) occurrences.get(0).get("laneId")).longValue(),
                ((Number) occurrences.get(1).get("laneId")).longValue()));
        assertEquals(Arrays.asList(101L, 201L), Arrays.asList(
                ((Number) occurrences.get(0).get("spanId")).longValue(),
                ((Number) occurrences.get(1).get("spanId")).longValue()));
        assertEquals(1, rows(plan.get("closureGoals")).size());
        Map<String, Object> sharedGoal = rows(
                plan.get("closureGoals")).get(0);
        assertTrue(String.valueOf(sharedGoal.get("pathSeedKey"))
                .startsWith("PATH.SEED."));
        assertEquals(2, RegionInstancePlan.decode(
                GSON.toJsonTree(plan).getAsJsonObject()).goals().get(0)
                .occurrenceInstantiationCatalog()
                .getAsJsonArray("occurrences").size());
        String binding = String.valueOf(result.edgeValidations.get(0)
                .get("bindings"));
        assertTrue(binding.contains("REGION.1@test#call1"));
        assertTrue(binding.contains("REGION.1@test#call3"));
        assertTrue(binding.contains("REGION.1.out.call1"));
        assertTrue(binding.contains("REGION.1.in.call3"));
        assertTrue(binding.contains("fromLaneId=7"));
        assertTrue(binding.contains("toLaneId=8"));
    }

    @Test
    public void repeatedRootActivationsKeepDistinctBoundedPathSeeds()
            throws Exception {
        Map<String, Object> region = fullRegion();
        region.put("runtimeRootCallIds", Arrays.asList(1, 3));
        File regions = jsonl("path-seed-regions.jsonl", region);
        File edges = jsonl("path-seed-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("path-seed-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        99, 7, 101, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        99, 7, 102, 101, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0,
                        99, 8, 201, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0,
                        99, 8, 202, 201, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", -1, "", 0, "", false,
                        false));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, runtime, Collections.emptyList());

        assertEquals(1, result.regionPlans.size());
        Map<String, Object> plan = result.regionPlans.get(0);
        List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
        assertEquals(2, goals.size());
        Set<String> seeds = new LinkedHashSet<>();
        for (Map<String, Object> goal : goals) {
            seeds.add(String.valueOf(goal.get("pathSeedKey")));
        }
        assertEquals(2, seeds.size());
        RegionInstancePlan decoded = RegionInstancePlan.decode(
                GSON.toJsonTree(plan).getAsJsonObject());
        for (RegionInstancePlan.Goal goal : decoded.goals()) {
            assertEquals(1, goal.occurrenceInstantiationCatalog()
                    .getAsJsonArray("occurrences").size());
        }
    }

    @Test
    public void repeatedRootActivationsWithDifferentOwnersStaySeparate()
            throws Exception {
        Map<String, Object> region = fullRegion();
        region.put("runtimeRootCallIds", Arrays.asList(1, 3));
        File regions = jsonl("owner-regions.jsonl", region);
        File edges = jsonl("owner-edges.jsonl");
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("owner-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0,
                        99, 7, 101, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0,
                        99, 7, 102, 101, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t2",
                        7, ROOT, 30, "example.Root", 3, 0, 0,
                        100, 8, 201, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t2",
                        7, TARGET, 40, "example.Target", 4, 3, 0,
                        100, 8, 202, 201, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5, "BRANCH", TARGET,
                        2, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false),
                new RuntimeRegionPlanner.RuntimeEvent(6, "BRANCH", TARGET,
                        4, 0, 0, TARGET + "#u4", -1, "", 0, "", true,
                        false));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L)),
                        activation("REGION.1", 3, ROOT,
                                Arrays.asList(3L, 4L))),
                events, runtime, Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        Set<String> logical = new LinkedHashSet<>();
        for (Map<String, Object> plan : result.regionPlans) {
            logical.add(String.valueOf(plan.get("logicalRegionId")));
            assertEquals(1, plan.get("logicalInstanceCount"));
            assertEquals(1, rows(plan.get("occurrences")).size());
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                "REGION.1@owner99", "REGION.1@owner100")), logical);
    }

    @Test
    public void carrierReconstructionOutputDemandsItsResponsePort()
            throws Exception {
        String field = "<example.State: int value>";
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(field))));
        // The write at event 5 happens between the request send and the
        // caller's own result, so it only rebuilt the decoded reply.
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", WRITER,
                "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Collections.singletonList(WRITER),
                "symbolicInputs", Arrays.asList(
                        object("portId", "REGION.2.in.seed",
                                "cell", "writer-input",
                                "rootCallId", 3, "rootMethod", WRITER,
                                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                                "rootKind", "OBSERVED_FIELD_RECEIVER",
                                "rootObjectId", 78,
                                "fieldReceiverObjectId", 78,
                                "siteId", WRITER + "#u1",
                                "fieldPath",
                                Collections.singletonList("seed"),
                                "fieldPathDeclarations",
                                Collections.singletonList(
                                        "<example.Other: int seed>")),
                        object("portId", "REGION.2.in.response",
                                "cell", WRITER + "::$decoded",
                                "sourceKind", "PROTOCOL_INPUT",
                                "protocolDirection", "RESPONSE",
                                "authority",
                                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                                "mappingId", "example.response",
                                "port", "response",
                                "transportKind", "RPC",
                                "dependencyRole", "VALUE_FRONTIER",
                                "fromRegionId", "REGION.P",
                                "toRegionId", "REGION.2",
                                "fromRootCallId", 9, "toRootCallId", 3,
                                "callerSiteEventSeq", 1,
                                "sendEventSeq", 2, "receiveEventSeq", 3,
                                "callerResultEventSeq", 8)),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.value", "cell", "writer",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "bindingKind", "DECLARED_FIELD_ACCESS",
                        "rootObjectId", 77,
                        "fieldReceiverObjectId", 77,
                        "siteId", WRITER + "#u2",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations",
                        Collections.singletonList(field),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", WRITER + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "fieldReceiverObjectId", 77,
                                "fieldPathDeclarations",
                                Collections.singletonList(field))))),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("carrier-regions.jsonl", reader, writer);
        File edges = jsonl("carrier-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.1",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77,
                "writerEventSeq", 5, "readerEventSeq", 6,
                "fieldPathDeclarations",
                Collections.singletonList(field)));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("carrier-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, WRITER, 30, "example.Writer", 3, 0, 0));
        events.addAll(methods());

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.2", 3, WRITER,
                                Collections.singletonList(3L)),
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> writerPlan = null;
        for (Map<String, Object> candidate : result.regionPlans) {
            if ("REGION.2".equals(candidate.get("regionId"))) {
                writerPlan = candidate;
            }
        }
        assertTrue(writerPlan != null);
        String closure = String.valueOf(rows(
                writerPlan.get("closureGoals")).get(0).get("outputClosure"));
        assertTrue(closure.contains("inputPorts=[REGION.2.in.response]"));
    }

    @Test
    public void selectedCarrierLeafPullsInItsResponsePort() throws Exception {
        String field = "<example.State: int value>";
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(field))));
        // The write itself is local production, but the prior state it reads
        // back was rebuilt from a decoded reply.
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", WRITER,
                "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Collections.singletonList(WRITER),
                "symbolicInputs", Arrays.asList(
                        object("portId", "REGION.2.in.value",
                                "cell", "writer-input",
                                "rootCallId", 3, "rootMethod", WRITER,
                                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                                "rootKind", "OBSERVED_FIELD_RECEIVER",
                                "rootObjectId", 77,
                                "fieldReceiverObjectId", 77,
                                "eventSeq", 4,
                                "siteId", WRITER + "#u1",
                                "fieldPath",
                                Collections.singletonList("value"),
                                "fieldPathDeclarations",
                                Collections.singletonList(field),
                                "protocolCarrierResponsePort",
                                "REGION.2.in.response",
                                "protocolCarrierMappingId",
                                "example.response",
                                "protocolCarrierAuthority",
                                "TRUSTED_CONFIGURED_RPC_MAPPING_V1"),
                        object("portId", "REGION.2.in.response",
                                "cell", WRITER + "::$decoded",
                                "sourceKind", "PROTOCOL_INPUT",
                                "protocolDirection", "RESPONSE",
                                "authority",
                                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                                "mappingId", "example.response",
                                "port", "response",
                                "transportKind", "RPC",
                                "dependencyRole", "VALUE_FRONTIER",
                                "fromRegionId", "REGION.P",
                                "toRegionId", "REGION.2",
                                "fromRootCallId", 9, "toRootCallId", 3,
                                "callerSiteEventSeq", 1,
                                "sendEventSeq", 2, "receiveEventSeq", 3,
                                "callerResultEventSeq", 8)),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.value", "cell", "writer",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "bindingKind", "DECLARED_FIELD_ACCESS",
                        "rootObjectId", 77,
                        "fieldReceiverObjectId", 77,
                        "siteId", WRITER + "#u2",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations",
                        Collections.singletonList(field),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 20,
                                "staticAccessSiteId", WRITER + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "fieldReceiverObjectId", 77,
                                "fieldPathDeclarations",
                                Collections.singletonList(field))))),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("carrier-leaf-regions.jsonl", reader, writer);
        File edges = jsonl("carrier-leaf-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.1",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77,
                "writerEventSeq", 20, "readerEventSeq", 21,
                "fieldPathDeclarations",
                Collections.singletonList(field)));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("carrier-leaf-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, WRITER, 30, "example.Writer", 3, 0, 0));
        events.addAll(methods());

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.2", 3, WRITER,
                                Collections.singletonList(3L)),
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> writerPlan = null;
        for (Map<String, Object> candidate : result.regionPlans) {
            if ("REGION.2".equals(candidate.get("regionId"))) {
                writerPlan = candidate;
            }
        }
        assertTrue(writerPlan != null);
        String closure = String.valueOf(rows(
                writerPlan.get("closureGoals")).get(0).get("outputClosure"));
        assertTrue(closure.contains(
                "inputPorts=[REGION.2.in.value, REGION.2.in.response]"));
    }

    @Test
    public void exactScalarProjectionDoesNotDemandWholeResponseCarrier() {
        Map<String, Object> projected = projectedCarrierInput(
                "REGION.2.in.value",
                "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1");
        List<String> selected = new ArrayList<>(
                Collections.singletonList("REGION.2.in.value"));

        RuntimeRegionPlanner.addProtocolCarrierPorts(selected,
                Collections.singletonList(projected), 3L);

        assertEquals(Collections.singletonList("REGION.2.in.value"),
                selected);

        projected.put(ProtocolCarrierReconstruction.PROJECTION_GAP,
                "MISSING_EXACT_PROTOCOL_CARRIER_PROJECTION");
        selected = new ArrayList<>(
                Collections.singletonList("REGION.2.in.value"));
        RuntimeRegionPlanner.addProtocolCarrierPorts(selected,
                Collections.singletonList(projected), 3L);
        assertEquals(Arrays.asList("REGION.2.in.value",
                "REGION.2.in.response"), selected);
    }

    @Test
    public void carrierSuppressionIsPerSelectedProjectedInput() {
        Map<String, Object> projected = projectedCarrierInput(
                "REGION.2.in.keys",
                "STATIC_DEF_USE_CONTAINER_PROJECTION_V1");
        projected.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        Map<String, Object> unprojected = object(
                "portId", "REGION.2.in.version", "rootCallId", 3,
                "protocolCarrierResponsePort", "REGION.2.in.response",
                "protocolCarrierMappingId", "example.response",
                "protocolCarrierAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        List<String> selected = new ArrayList<>(Arrays.asList(
                "REGION.2.in.keys", "REGION.2.in.version"));

        RuntimeRegionPlanner.addProtocolCarrierPorts(selected,
                Arrays.asList(projected, unprojected), 3L);

        assertEquals(Arrays.asList("REGION.2.in.keys",
                "REGION.2.in.version", "REGION.2.in.response"), selected);
    }

    @Test
    public void fieldFlowIsBoundToExactRegionActivations() throws Exception {
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(
                        "<example.State: int value>"))));
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", WRITER,
                "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Collections.singletonList(WRITER),
                "symbolicInputs", Collections.singletonList(object(
                        "portId", "REGION.2.in.value",
                        "cell", "writer-input",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                        "rootKind", "OBSERVED_FIELD_RECEIVER",
                        "rootObjectId", 77,
                        "fieldReceiverObjectId", 77,
                        "siteId", WRITER + "#u1",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations", Collections.singletonList(
                                "<example.State: int value>"))),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.value", "cell", "writer",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "bindingKind", "DECLARED_FIELD_ACCESS",
                        "rootObjectId", 77,
                        "fieldReceiverObjectId", 77,
                        "siteId", WRITER + "#u2",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations", Collections.singletonList(
                                "<example.State: int value>"),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", WRITER + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "fieldReceiverObjectId", 77,
                                "fieldPathDeclarations",
                                Collections.singletonList(
                                "<example.State: int value>"))))),
                "branchPolicies", Collections.singletonList(object(
                        "siteId", WRITER + "#u3", "method", WRITER,
                        "unitIndex", 3, "policy", "EXPLORE")));
        File regions = jsonl("flow-regions.jsonl", reader, writer);
        File edges = jsonl("flow-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.1",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77,
                "writerEventSeq", 5, "readerEventSeq", 6,
                "fieldPathDeclarations", Collections.singletonList(
                        "<example.State: int value>")));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("flow-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, WRITER, 30, "example.Writer", 3, 0, 0));
        events.addAll(methods());

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.2", 3, WRITER,
                                Collections.singletonList(3L)),
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(),
                Collections.emptyList());

        assertEquals(2, result.regionPlans.size());
        assertEquals(1, result.edgeValidations.size());
        Map<String, Object> validation = result.edgeValidations.get(0);
        assertEquals("CONFIRMED_RUNTIME_IDENTITY", validation.get("state"));
        assertTrue(String.valueOf(validation.get("bindings"))
                .contains("REGION.2@test#call3"));
        assertTrue(String.valueOf(validation.get("bindings"))
                .contains("REGION.1@test#call1"));

        Map<String, Object> writerPlan = null;
        for (Map<String, Object> candidate : result.regionPlans) {
            if ("REGION.2".equals(candidate.get("regionId"))) {
                writerPlan = candidate;
            }
        }
        assertTrue(writerPlan != null);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> goals =
                (List<Map<String, Object>>) writerPlan.get("closureGoals");
        assertEquals(1, goals.size());
        assertEquals("READY", ((Map<?, ?>) goals.get(0).get("admission"))
                .get("state"));
        assertTrue(goals.get(0).containsKey("outputClosure"));
        assertEquals(1, ((List<?>) goals.get(0).get("symbolize")).size());
        assertEquals(1, ((List<?>) goals.get(0).get("branches")).size());
    }

    @Test
    public void boundedContainerMutationWithoutPreStateFailsClosed()
            throws Exception {
        String ownerField = "<example.Writer: example.State state>";
        String valueField = "<example.State: java.util.Map value>";
        String mutator = "<java.util.Map: java.lang.Object put("
                + "java.lang.Object,java.lang.Object)>";
        List<String> path = Arrays.asList("state", "value");
        List<String> declarations = Arrays.asList(ownerField, valueField);
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 88,
                "siteId", TARGET + "#u1", "fieldPath", path,
                "fieldPathDeclarations", declarations)));
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", WRITER, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(WRITER, STATE_UPDATE),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.value", "cell", "writer",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "bindingKind", "CONTAINER_MUTATION",
                        "rootObjectId", 77, "fieldReceiverObjectId", 88,
                        "siteId", STATE_UPDATE + "#u2",
                        "fieldPath", path,
                        "fieldPathDeclarations", declarations,
                        "javaType", "java.util.Map",
                        "symbolicDemand", "BOUNDED_CONTAINER_STATE",
                        "boundedContainerStateAdmission", "BLOCKED",
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", STATE_UPDATE + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "CONTAINER_MUTATION",
                                "mutationCompletionSeq", 5,
                                "mutatorDeclaredCallee", mutator,
                                "fieldReceiverObjectId", 88,
                                "fieldPathDeclarations", declarations)))),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("nested-flow-regions.jsonl", reader, writer);
        File edges = jsonl("nested-flow-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.nested",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 88, "writerEventSeq", 5,
                "readerEventSeq", 6,
                "mutationCompletionSeq", 5,
                "mutatorDeclaredCallee", mutator,
                "fieldPathDeclarations", declarations));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("nested-flow-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, WRITER, 30, "example.Writer", 3, 0, 0));
        events.addAll(methods());

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        activation("REGION.2", 3, WRITER,
                                Collections.singletonList(3L)),
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.2".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("DISCOVERED", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        assertTrue(String.valueOf(((Map<?, ?>) goal.get("admission"))
                .get("blockers")).contains(
                "MISSING_EXACT_CONTAINER_MUTATION_INVOCATION"));
        assertFalse(goal.containsKey("outputClosure"));
        assertEquals(Collections.emptyList(), rows(goal.get("symbolize")));
    }

    @Test
    public void exactMutationUsesDefinitionExitAndObservedIntermediary()
            throws Exception {
        String root = "<example.Service: void run()>";
        String intermediary =
                "<example.BlockPool: void add(example.Response)>";
        String definition =
                "<example.Keys: void add(example.Response)>";
        String sibling = "<example.Service: void unrelated()>";
        String mutator = "<java.util.Map: java.lang.Object put("
                + "java.lang.Object,java.lang.Object)>";
        String stateField = "<example.Keys: java.util.Map allKeys>";
        String protocolCell = intermediary + ".param0:example.Response";
        String intermediaryLocal = intermediary + "::r1";
        String definitionParameter = definition
                + ".param0:example.Response";
        String definitionLocal = definition + "::r2";
        String guardOperand = definition + "::z0";

        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.keys", "cell", stateField,
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("allKeys"),
                "fieldPathDeclarations",
                Collections.singletonList(stateField))));
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", root,
                "anchorMethod", definition, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                // The static candidate omitted the forwarding helper.  The
                // exact observed call corridor may admit it, but not sibling.
                "methods", Arrays.asList(root, definition, sibling),
                "symbolicInputs", Arrays.asList(object(
                                "portId", "REGION.P.in.response",
                                "cell", protocolCell,
                                "sourceKind", "PROTOCOL_INPUT",
                                "dependencyRole",
                                "CONCRETE_STRUCTURE_CARRIER",
                                "toRootCallId", 3, "receiveEventSeq", 10,
                                "protocolDirection", "RESPONSE",
                                "mappingId", "example.keys"),
                        object("portId", "REGION.P.in.prestate",
                                "cell", stateField, "rootCallId", 3,
                                "rootMethod", definition,
                                "sourceKind",
                                "ACTIVATION_FIELD_RECEIVER",
                                "rootKind", "OBSERVED_FIELD_RECEIVER",
                                "rootObjectId", 77,
                                "fieldReceiverObjectId", 77,
                                "valueObjectId", 88,
                                "siteId", definition + "#u2",
                                "fieldPath", Collections.singletonList(
                                        "allKeys"),
                                "fieldPathDeclarations",
                                Collections.singletonList(stateField),
                                "javaType", "java.util.Map",
                                "symbolicDemand",
                                "BOUNDED_CONTAINER_STATE",
                                "dependencyRole", "VALUE_FRONTIER",
                                "containerCapacity", LoopBoundPolicy
                                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY,
                                "boundedContainerStateAuthority",
                                "EXACT_RUNTIME_CONTAINER_MUTATION_STATE_CHAIN_V1",
                                "runtimeAccesses", Arrays.asList(
                                        object("rootCallId", 3,
                                                "callId", 99,
                                                "eventSeq", 8,
                                                "staticAccessSiteId",
                                                definition + "#u2",
                                                "fieldReceiverObjectId", 77,
                                                "valueObjectId", 88,
                                                "fieldPathDeclarations",
                                                Collections.singletonList(
                                                        stateField)),
                                        object("rootCallId", 3,
                                                "callId", 5,
                                                "eventSeq", 17,
                                                "staticAccessSiteId",
                                                definition + "#u2",
                                                "fieldReceiverObjectId", 77,
                                                "valueObjectId", 88,
                                                "fieldPathDeclarations",
                                                Collections.singletonList(
                                                        stateField)),
                                        object("rootCallId", 3,
                                                "callId", 5,
                                                "eventSeq", 18,
                                                "staticAccessSiteId",
                                                definition + "#u2",
                                                "fieldReceiverObjectId", 77,
                                                "valueObjectId", 88,
                                                "fieldPathDeclarations",
                                                Collections.singletonList(
                                                        stateField))))),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.P.out.keys", "cell", stateField,
                        "rootCallId", 3, "rootMethod", definition,
                        "bindingKind", "CONTAINER_MUTATION",
                        "rootObjectId", 77, "fieldReceiverObjectId", 77,
                        "valueObjectId", 88, "siteId", definition + "#u4",
                        "fieldPath", Collections.singletonList("allKeys"),
                        "fieldPathDeclarations",
                        Collections.singletonList(stateField),
                        "javaType", "java.util.Map",
                        "symbolicDemand", "BOUNDED_CONTAINER_STATE",
                        "containerCapacity", LoopBoundPolicy
                                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY,
                        "boundedContainerStateAdmission", "PROVED",
                        "boundedContainerPreStatePorts",
                        Collections.singletonList(
                                "REGION.P.in.prestate"),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 22,
                                "staticAccessSiteId", definition + "#u4",
                                // This was the twenty-sixth use in the
                                // long-lived root — far past the replay loop
                                // bound — but the first in exact call 5.  The
                                // recorded ordinal is provenance, not replay
                                // identity: a demanded mutation writer must
                                // not be dropped because the recording
                                // reached its site often.
                                "activationLocalStaticSiteOccurrence", 26,
                                "bindingKind", "CONTAINER_MUTATION",
                                "mutationCompletionSeq", 22,
                                "mutatorDeclaredCallee", mutator,
                                "fieldReceiverObjectId", 77,
                                "valueObjectId", 88,
                                "fieldPathDeclarations",
                                Collections.singletonList(stateField))))),
                "branchPolicies", Collections.singletonList(object(
                        "siteId", definition + "#u3",
                        "method", definition, "unitIndex", 3,
                        "operandCells",
                        Collections.singletonList(guardOperand),
                        "policy", "EXPLORE")));
        File regions = jsonl("mutation-fold-regions.jsonl",
                producer, consumer);
        File regionEdges = jsonl("mutation-fold-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.fold",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", "REGION.P.out.keys",
                "toPort", "REGION.1.in.keys",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77, "writerEventSeq", 22,
                "readerEventSeq", 40, "mutationCompletionSeq", 22,
                "mutatorDeclaredCallee", mutator,
                "fieldPathDeclarations",
                Collections.singletonList(stateField)));
        File refined = jsonl("mutation-fold-refined.jsonl",
                refinedEdge("DF.protocol", "VALUE_PASS", protocolCell,
                        intermediaryLocal, intermediary,
                        intermediary + "#u1", 1),
                refinedEdge("DF.forward", "IDENTITY_BINDING",
                        intermediaryLocal, definitionParameter,
                        intermediary, intermediary + "#u2", 2),
                refinedEdge("DF.parameter", "VALUE_PASS",
                        definitionParameter, definitionLocal, definition,
                        definition + "#u1", 1),
                refinedEdge("DF.guard", "GUARD", guardOperand,
                        definitionLocal, definition,
                        definition + "#u3", 3),
                refinedEdge("DF.write", "HEAP_WRITE", definitionLocal,
                        stateField, definition, definition + "#u4", 4));
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, root, 30, "example.Service", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "w",
                        8, intermediary, 31, "example.BlockPool", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "w",
                        8, definition, 32, "example.Keys", 5, 4, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "r",
                        7, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "r",
                        7, TARGET, 41, "example.Target", 2, 1, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                branchEvent(19, definition, 5, definition + "#u3", true),
                new RuntimeRegionPlanner.RuntimeEvent(20,
                        "CALL_SITE_ENTER", definition, 5, 100, 0,
                        definition + "#u4", mutator, -1, "", 88, "",
                        false, false),
                new RuntimeRegionPlanner.RuntimeEvent(22,
                        "CALL_SITE_RETURN", definition, 5, 100, 0,
                        definition + "#u4", mutator, -1, "", 0, "",
                        false, false),
                branchEvent(23, definition, 5, definition + "#u3", true),
                new RuntimeRegionPlanner.RuntimeEvent(24,
                        "CALL_SITE_ENTER", definition, 5, 101, 0,
                        definition + "#u4", mutator, -1, "", 88, "",
                        false, false),
                new RuntimeRegionPlanner.RuntimeEvent(26,
                        "CALL_SITE_RETURN", definition, 5, 101, 0,
                        definition + "#u4", mutator, -1, "", 0, "",
                        false, false),
                new RuntimeRegionPlanner.RuntimeEvent(30,
                        "METHOD_EXIT_NORMAL", definition, 5, 0, 0,
                        "", -1, "", 0, "", false, false));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, root, Arrays.asList(3L, 4L, 5L));
        producerActivation.put("observedMethods",
                Arrays.asList(root, intermediary, definition));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                methods, runtime, Collections.emptyList());
        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> slice = (Map<String, Object>) rows(
                closure.get("members")).get(0).get("slice");
        assertEquals("DEFINITION_INVOCATION_NORMAL_EXIT",
                slice.get("outputBoundaryKind"));
        assertEquals(30L, ((Number) slice.get(
                "definitionCompletionSeq")).longValue());
        assertEquals(26L, ((Number) slice.get(
                "lastMutationCompletionSeq")).longValue());
        assertEquals(2, ((Number) slice.get(
                "foldedMutationCount")).intValue());
        assertEquals(1, ((Number) slice.get(
                "activationLocalOccurrence")).intValue());
        assertTrue(String.valueOf(slice.get("methods"))
                .contains(intermediary));
        assertTrue(!String.valueOf(slice.get("methods")).contains(sibling));
        assertTrue(String.valueOf(slice.get("inputPorts"))
                .contains("REGION.P.in.response"));
        assertTrue(String.valueOf(slice.get("inputPorts"))
                .contains("REGION.P.in.prestate"));
        assertEquals(17L, ((Number) slice.get(
                "containerPreStateEventSeq")).longValue());
        assertEquals("EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1",
                slice.get("containerPreStateAuthority"));
        Map<String, Object> preStateAction = rows(goal.get("symbolize"))
                .stream().filter(action -> "REGION.P.in.prestate".equals(
                        action.get("symbol"))).findFirst().get();
        assertEquals(Collections.singletonList(definition + "#u2"),
                preStateAction.get("accessSites"));
        assertEquals(17L, ((Number) preStateAction.get(
                "selectedRuntimeEventSeq")).longValue());
        Map<String, Object> capture = rows(slice.get("captureBindings"))
                .get(0);
        assertEquals("DEFINITION_INVOCATION",
                capture.get("occurrenceScope"));
        assertEquals(1, ((Number) capture.get(
                "replayOccurrence")).intValue());
        Map<String, Object> replay = rows(slice.get("branchReplay")).get(0);
        assertEquals(2, ((Number) replay.get(
                "selectedOccurrence")).intValue());
    }

    @Test
    public void accessorMaterializationUsesLatestPrecedingOccurrence() {
        List<Map<String, Object>> inputs = Arrays.asList(
                accessorPort("old", 3, 2, STATE_UPDATE + "#u1"),
                accessorPort("other", 3, 3, STATE_UPDATE + "#u2"),
                accessorPort("latest", 3, 4, STATE_UPDATE + "#u1"),
                accessorPort("future", 3, 6, STATE_UPDATE + "#u1"),
                accessorPort("other-root", 4, 5,
                        STATE_UPDATE + "#u3"));
        List<String> ports = new ArrayList<>(
                Collections.singletonList("already-sliced"));

        RuntimeRegionPlanner.addReachingAccessorMaterializations(
                ports, inputs, 3, Collections.singleton(STATE_UPDATE), 5);

        assertEquals(Arrays.asList("already-sliced", "latest", "other"),
                ports);
    }

    @Test
    public void fieldAssignmentEvidenceOverridesAccessPortLabel()
            throws Exception {
        String ownerField = "<example.Writer: example.State state>";
        String keyField = "<example.State: example.Key currentKey>";
        List<String> path = Arrays.asList("state", "currentKey");
        List<String> declarations = Arrays.asList(ownerField, keyField);
        Map<String, Object> reader = fullRegion();
        reader.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.current", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 91, "fieldReceiverObjectId", 88,
                "siteId", TARGET + "#u1", "fieldPath", path,
                "fieldPathDeclarations", declarations)));
        Map<String, Object> writer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.2", "rootMethod", WRITER,
                "anchorMethod", STATE_UPDATE, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(WRITER, STATE_UPDATE),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.2.out.current", "cell", "writer",
                        "rootCallId", 3, "rootMethod", WRITER,
                        "sourceKind", "RECEIVER_FIELD",
                        "rootKind", "RECEIVER", "rootObjectId", 77,
                        "fieldReceiverObjectId", 88,
                        "valueObjectId", 200,
                        "boundaryState", "REGION_ROOTED",
                        "authority",
                        "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                        "bindingKind", "ACTIVATION_FIELD_ACCESS",
                        "siteId", STATE_UPDATE + "#u2",
                        "fieldPath", path,
                        "fieldPathDeclarations", declarations,
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", STATE_UPDATE + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                                "fieldReceiverObjectId", 88,
                                "valueObjectId", 200,
                                "fieldPathDeclarations", declarations)))),
                "branchPolicies", Collections.emptyList());
        File regions = jsonl("assignment-flow-regions.jsonl", reader, writer);
        File edges = jsonl("assignment-flow-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.assignment",
                "fromRegion", "REGION.2", "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.current",
                "toPort", "REGION.1.in.current",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 9,
                "receiverObjectId", 88, "valueObjectId", 200,
                "writerEventSeq", 5, "readerEventSeq", 6,
                "fieldPathDeclarations", declarations));
        Map<String, Object> refined = candidateEdge();
        refined.put("refinementSchemaVersion", 1);
        refined.put("graphKind", "RUNTIME_REFINED_DATAFLOW");
        File refinedFile = jsonl("assignment-flow-refined.jsonl", refined);
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                        8, WRITER, 30, "example.Writer", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, STATE_UPDATE, 31, "example.State", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "r",
                        9, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "r",
                        9, TARGET, 41, "example.Target", 2, 1, 0));
        Map<String, Object> writerActivation = activation(
                "REGION.2", 3, WRITER, Arrays.asList(3L, 4L));
        writerActivation.put("observedMethods",
                Arrays.asList(WRITER, STATE_UPDATE));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refinedFile, Arrays.asList(
                        writerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.singletonList(
                        new RuntimeRegionPlanner.FieldAccessEvent(5,
                                "FIELD_WRITE", STATE_UPDATE, 4, 2,
                                STATE_UPDATE + "#u2", keyField, 88, 200,
                                "")));

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.2".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        List<Map<String, Object>> actions = rows(goal.get("symbolize"));
        assertEquals(0, actions.size());
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        assertEquals(Collections.emptyList(), slice.get("inputPorts"));
        Map<String, Object> capture = rows(slice.get("captureBindings"))
                .get(0);
        assertEquals(Collections.singletonList("currentKey"),
                capture.get("fieldPath"));
        assertEquals("FIELD_WRITE_STATE", capture.get("captureKind"));
        assertEquals(STATE_UPDATE, capture.get("definitionMethod"));
        assertEquals(2, ((Number) capture.get(
                "definitionUnitIndex")).intValue());
        assertTrue(!capture.containsKey("accessRootInputPort"));
    }

    @Test
    public void trustedRpcContainerProjectionCapturesExactFieldWriteAndInput()
            throws Exception {
        String producerRoot = "<example.Producer: void run()>";
        String definition =
                "<example.Response: void <init>(example.Key[])>";
        String arrayField = "<example.Response: example.Key[] keys>";
        String producerInput = definition + ".param0:example.Key[]";
        String producerLocal = definition + "::$keys";
        String consumerLocal = TARGET + "::$keys";
        String producerPort = "REGION.P.out.projected-keys";
        String consumerPort = "REGION.1.in.projected-keys";
        String mapping = "example.fetch.response";

        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", definition, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, definition),
                "symbolicInputs", Collections.singletonList(object(
                        "portId", "REGION.P.in.keys", "cell", producerInput,
                        "rootCallId", 3, "rootMethod", definition,
                        "sourceKind", "PARAMETER", "rootKind", "PARAMETER",
                        "rootParameterIndex", 0,
                        "javaType", "example.Key[]",
                        "symbolicDemand", "BOUNDED_CONTAINER_STATE",
                        "containerCapacity", LoopBoundPolicy
                                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY)),
                "outputs", Collections.singletonList(object(
                        "portId", producerPort, "cell",
                        definition + "#u2.fieldReceiver",
                        "rootCallId", 3, "rootMethod", producerRoot,
                        "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                        "rootKind", "OBSERVED_FIELD_RECEIVER",
                        "rootObjectId", 100, "fieldReceiverObjectId", 100,
                        "valueObjectId", 200,
                        "bindingKind", "ACTIVATION_FIELD_ACCESS",
                        "fieldPath", Collections.singletonList("keys"),
                        "fieldPathDeclarations",
                        Collections.singletonList(arrayField),
                        "javaType", "example.Key[]",
                        "symbolicDemand", "BOUNDED_CONTAINER_STATE",
                        "rpcDescendantProjectionOutput", true,
                        "rpcProjectionAuthority",
                        "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                        "rpcProjectionSelectionAuthority",
                        "STATIC_DEF_USE_CONTAINER_PROJECTION_V1",
                        "rpcProjectionMappingId", mapping,
                        "rpcProjectionFieldDeclaration", arrayField,
                        "rpcProjectionStaticAccessSiteId",
                        definition + "#u2",
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", definition + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                                "fieldReceiverObjectId", 100,
                                "valueObjectId", 200,
                                "fieldPathDeclarations",
                                Collections.singletonList(arrayField))))),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", consumerPort, "cell",
                TARGET + "#u1.fieldReceiver",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 300, "fieldReceiverObjectId", 300,
                "valueObjectId", 400,
                "fieldPath", Collections.singletonList("keys"),
                "fieldPathDeclarations", Collections.singletonList(
                        arrayField), "javaType", "example.Key[]",
                "symbolicDemand", "BOUNDED_CONTAINER_STATE",
                "containerCapacity", LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY,
                "rpcDescendantProjectionInput", true,
                "rpcProjectionAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "rpcProjectionSelectionAuthority",
                "STATIC_DEF_USE_CONTAINER_PROJECTION_V1",
                "rpcProjectionMappingId", mapping)));

        File regions = jsonl("projected-container-regions.jsonl",
                producer, consumer);
        File regionEdges = jsonl("projected-container-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_PROTOCOL_FLOW",
                "transportKind", "RPC", "edgeId", "RP.projected-keys",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", producerPort, "toPort", consumerPort,
                "fromRootCallId", 3, "toRootCallId", 1,
                "direction", "RESPONSE", "mappingId", mapping,
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "callerSiteEventSeq", 10, "sendEventSeq", 11,
                "receiveEventSeq", 12,
                "dependencyRole", "VALUE_FRONTIER",
                "projectionKind", "BOUNDED_CONTAINER_STATE",
                "rpcDescendantProjection", true,
                "projectionSelectionAuthority",
                "STATIC_DEF_USE_CONTAINER_PROJECTION_V1",
                "producerProjectionSiteId", definition + "#u2",
                "consumerProjectionSiteId", TARGET + "#u1",
                "fieldPathDeclarations",
                Collections.singletonList(arrayField),
                "javaType", "example.Key[]"));
        Map<String, Object> failure = targetRefinedEdge(
                "DF.target.failure", "GUARD", consumerLocal, "exception",
                TARGET, TARGET + "#u4", 4);
        failure.put("kind", "exception_guard");
        File refined = jsonl("projected-container-refined.jsonl",
                refinedEdge("DF.producer.value", "VALUE_PASS",
                        producerInput, producerLocal, definition,
                        definition + "#u1", 1),
                refinedEdge("DF.producer.write", "HEAP_WRITE",
                        producerLocal, arrayField, definition,
                        definition + "#u2", 2),
                targetRefinedEdge("DF.target.read", "HEAP_READ",
                        arrayField, consumerLocal, TARGET,
                        TARGET + "#u1", 1),
                failure);
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                        8, producerRoot, 30, "example.Producer", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, definition, 31, "example.Response", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "r",
                        9, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "r",
                        9, TARGET, 41, "example.Target", 2, 1, 0));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, definition));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                methods, Collections.singletonList(branchEvent(
                        20, TARGET, 2, TARGET + "#u4", false)),
                Collections.singletonList(
                        new RuntimeRegionPlanner.FieldAccessEvent(5,
                                "FIELD_WRITE", definition, 4, 2,
                                definition + "#u2", arrayField, 100, 200,
                                "")));

        Map<String, Object> producerPlan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> producerGoal = rows(
                producerPlan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) producerGoal.get("admission"))
                .get("state"));
        Map<String, Object> closure = (Map<String, Object>) producerGoal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        Map<String, Object> capture = rows(slice.get("captureBindings")).get(0);
        assertEquals("FIELD_WRITE_STATE", capture.get("captureKind"));
        assertEquals(definition, capture.get("definitionMethod"));
        assertEquals(2, ((Number) capture.get("definitionUnitIndex"))
                .intValue());
        assertEquals("example.Key[]", capture.get("javaType"));
        assertEquals(Collections.singletonList("REGION.P.in.keys"),
                slice.get("inputPorts"));
        assertEquals(Boolean.TRUE, rows(closure.get("causalEdges")).get(0)
                .get("rpcDescendantProjection"));

        Map<String, Object> consumerPlan = result.regionPlans.stream()
                .filter(row -> "REGION.1".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> consumerGoal = rows(
                consumerPlan.get("closureGoals")).get(0);
        Map<String, Object> action = rows(consumerGoal.get("symbolize")).get(0);
        assertEquals(consumerPort, action.get("symbol"));
        assertEquals("BOUNDED_CONTAINER_STATE",
                action.get("symbolicDemand"));
        assertEquals("example.Key[]", action.get("javaType"));
        assertEquals(LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY,
                ((Number) action.get("containerCapacity")).intValue());
    }

    @Test
    public void trustedRpcScalarLeafProjectionClosesItsProducerWrite()
            throws Exception {
        String producerRoot = "<example.Producer: void run()>";
        String definition = "<example.Response: void <init>(int)>";
        String leafField = "<example.Response: int keyId>";
        String carrierField =
                "<example.Producer: example.Response activeKey>";
        String wireCarrierField =
                "<example.WireResponse: example.Response currentKey>";
        String producerInput = definition + ".param0:int";
        String producerLocal = definition + "::$keyId";
        String consumerLocal = TARGET + "::$keyId";
        String producerPort = "REGION.P.out.projected-keyId";
        String consumerPort = "REGION.1.in.projected-keyId";
        String mapping = "example.fetch.response";

        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", definition, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, definition),
                "symbolicInputs", Collections.singletonList(object(
                        "portId", "REGION.P.in.keyId", "cell", producerInput,
                        "rootCallId", 3, "rootMethod", definition,
                        "sourceKind", "PARAMETER", "rootKind", "PARAMETER",
                        "rootParameterIndex", 0, "javaType", "int")),
                "outputs", Collections.singletonList(object(
                        "portId", producerPort, "cell",
                        definition + "#u2.fieldReceiver",
                        "rootCallId", 3, "rootMethod", producerRoot,
                        "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                        "rootKind", "OBSERVED_FIELD_RECEIVER",
                        "rootObjectId", 100, "fieldReceiverObjectId", 100,
                        "valueObjectId", 0, "primitiveValue", "7",
                        "bindingKind", "ACTIVATION_FIELD_ACCESS",
                        "fieldPath", Collections.singletonList("keyId"),
                        "fieldPathDeclarations",
                        Collections.singletonList(leafField),
                        "javaType", "int",
                        "rpcDescendantProjectionOutput", true,
                        "rpcProjectionAuthority",
                        "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                        "rpcProjectionSelectionAuthority",
                        "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1",
                        "rpcProjectionMappingId", mapping,
                        "rpcProjectionFieldDeclaration", leafField,
                        "rpcProjectionStaticAccessSiteId",
                        definition + "#u2",
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", definition + "#u2",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "ACTIVATION_FIELD_ACCESS",
                                "fieldReceiverObjectId", 100,
                                "valueObjectId", 0,
                                "fieldPathDeclarations",
                                Collections.singletonList(leafField))))),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", consumerPort, "cell",
                TARGET + "#u1.fieldReceiver",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 300, "fieldReceiverObjectId", 300,
                "valueObjectId", 0, "primitiveValue", "7",
                "fieldPath", Collections.singletonList("keyId"),
                "fieldPathDeclarations", Collections.singletonList(
                        leafField), "javaType", "int",
                "rpcDescendantProjectionInput", true,
                "rpcProjectionAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "rpcProjectionSelectionAuthority",
                "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1",
                "rpcProjectionMappingId", mapping)));

        File regions = jsonl("projected-scalar-regions.jsonl",
                producer, consumer);
        File regionEdges = jsonl("projected-scalar-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_PROTOCOL_FLOW",
                "transportKind", "RPC", "edgeId", "RP.projected-keyId",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", producerPort, "toPort", consumerPort,
                "fromRootCallId", 3, "toRootCallId", 1,
                "direction", "RESPONSE", "mappingId", mapping,
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "callerSiteEventSeq", 10, "sendEventSeq", 11,
                "receiveEventSeq", 12,
                "dependencyRole", "VALUE_FRONTIER",
                "projectionKind", "SCALAR_LEAF_VALUE",
                "rpcDescendantProjection", true,
                "projectionSelectionAuthority",
                "STATIC_DEF_USE_SCALAR_LEAF_PROJECTION_V1",
                "producerProjectionSiteId", definition + "#u2",
                "consumerProjectionSiteId", TARGET + "#u1",
                "fieldPathDeclarations",
                Arrays.asList(wireCarrierField, leafField),
                "javaType", "int"));
        Map<String, Object> failure = targetRefinedEdge(
                "DF.target.failure", "GUARD", consumerLocal, "exception",
                TARGET, TARGET + "#u4", 4);
        failure.put("kind", "exception_guard");
        File refined = jsonl("projected-scalar-refined.jsonl",
                refinedEdge("DF.producer.value", "VALUE_PASS",
                        producerInput, producerLocal, definition,
                        definition + "#u1", 1),
                refinedEdge("DF.producer.write", "HEAP_WRITE",
                        producerLocal, leafField, definition,
                        definition + "#u2", 2),
                refinedEdge("DF.producer.publish", "HEAP_WRITE",
                        definition + ".receiver", carrierField,
                        producerRoot, producerRoot + "#u3", 3),
                targetRefinedEdge("DF.target.read", "HEAP_READ",
                        leafField, consumerLocal, TARGET,
                        TARGET + "#u1", 1),
                failure);
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                        8, producerRoot, 30, "example.Producer", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, definition, 31, "example.Response", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "r",
                        9, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "r",
                        9, TARGET, 41, "example.Target", 2, 1, 0));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, definition));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                methods, Collections.singletonList(branchEvent(
                        20, TARGET, 2, TARGET + "#u4", false)),
                Arrays.asList(
                        new RuntimeRegionPlanner.FieldAccessEvent(5,
                                "FIELD_WRITE", definition, 4, 2,
                                definition + "#u2", leafField, 100, 0,
                                "7"),
                        new RuntimeRegionPlanner.FieldAccessEvent(6,
                                "FIELD_WRITE", producerRoot, 3, 3,
                                producerRoot + "#u3", carrierField, 30,
                                100, "")));

        Map<String, Object> producerPlan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> producerGoal = rows(
                producerPlan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) producerGoal.get("admission"))
                .get("state"));
        Map<String, Object> closure = (Map<String, Object>) producerGoal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        Map<String, Object> capture = rows(slice.get("captureBindings")).get(0);
        assertEquals("FIELD_WRITE_STATE", capture.get("captureKind"));
        assertEquals(producerRoot, capture.get("definitionMethod"));
        assertEquals(3, ((Number) capture.get("definitionUnitIndex"))
                .intValue());
        assertEquals(carrierField,
                capture.get("definitionFieldSignature"));
        assertEquals(leafField, capture.get("leafFieldSignature"));
        assertEquals(Arrays.asList("activeKey", "keyId"),
                capture.get("fieldPath"));
        assertEquals("int", capture.get("javaType"));
        assertEquals(Collections.singletonList("REGION.P.in.keyId"),
                slice.get("inputPorts"));

        Map<String, Object> consumerPlan = result.regionPlans.stream()
                .filter(row -> "REGION.1".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> consumerGoal = rows(
                consumerPlan.get("closureGoals")).get(0);
        Map<String, Object> action = rows(consumerGoal.get("symbolize")).get(0);
        assertEquals(consumerPort, action.get("symbol"));
        assertEquals("int", action.get("javaType"));
        assertEquals(null, action.get("symbolicDemand"));
        assertEquals(null, action.get("containerCapacity"));
    }

    @Test
    public void rpcCarrierPublicationDeduplicatesRoleAndFailsOnAmbiguity() {
        String constructor = "<example.Key: void <init>(int)>";
        String producer = "<example.Producer: void run()>";
        String leafField = "<example.Key: int keyId>";
        String activeKey = "<example.Producer: example.Key activeKey>";
        RuntimeRegionPlanner.FieldAccessEvent leaf =
                new RuntimeRegionPlanner.FieldAccessEvent(5,
                        "FIELD_WRITE", constructor, 4, 2,
                        constructor + "#u2", leafField, 100, 0, "7");
        List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>(Arrays.asList(leaf,
                        new RuntimeRegionPlanner.FieldAccessEvent(6,
                                "FIELD_WRITE", producer, 3, 3,
                                producer + "#u3", activeKey,
                                30, 100, ""),
                        new RuntimeRegionPlanner.FieldAccessEvent(7,
                                "FIELD_WRITE", producer, 3, 3,
                                producer + "#u3", activeKey,
                                30, 100, "")));
        Set<Long> invocation = new LinkedHashSet<>(Arrays.asList(3L, 4L));
        RuntimeRegionPlanner.FieldAccessEvent selected =
                RuntimeRegionPlanner.uniqueRpcCarrierPublication(
                        leaf, invocation, fields);
        assertEquals(6L, selected.seq);

        fields.add(new RuntimeRegionPlanner.FieldAccessEvent(8,
                "FIELD_WRITE", producer, 3, 4, producer + "#u4",
                "<example.Producer: example.Key backupKey>",
                30, 100, ""));
        assertEquals(null, RuntimeRegionPlanner
                .uniqueRpcCarrierPublication(leaf, invocation, fields));
    }

    @Test
    public void selectedDecodeWriteUsesItsEventSpecificHelperArgument()
            throws Exception {
        String producerRoot = "<example.Decoder: void run()>";
        String constructor = "<example.Key: void <init>(int)>";
        String parameter = constructor + ".param0:int";
        String local = constructor + "::i0";
        String field = "<example.Key: int keyId>";
        String producerPort = "REGION.P.out.keyId";
        String decodePort = "REGION.P.in.decoded-keyId.25";
        String responsePort = "REGION.P.in.response.4";
        String consumerPort = "REGION.1.in.keyId";

        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", constructor, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, constructor),
                "symbolicInputs", Arrays.asList(object(
                        "portId", decodePort, "cell", parameter,
                        "rootCallId", 3, "sourceKind", "RPC_DECODE_VALUE",
                        "rootKind", "ACTIVATION_LOCAL",
                        "dependencyRole", "VALUE_FRONTIER",
                        "transportKind", "ACTIVATION_LOCAL",
                        "javaType", "int", "helperMethod", constructor,
                        "helperArgumentIndex", 0,
                        "replayOccurrence", 25,
                        "activationLocalStaticSiteOccurrence", 25,
                        "fieldPath", Collections.emptyList(),
                        "fieldPathDeclarations",
                        Collections.singletonList(field)),
                        object("portId", responsePort,
                                "cell", producerRoot + "::$response",
                                "rootCallId", 3,
                                "sourceKind", "PROTOCOL_INPUT",
                                "dependencyRole",
                                "CONCRETE_STRUCTURE_CARRIER",
                                "transportKind", "RPC",
                                "protocolDirection", "RESPONSE",
                                "direction", "RESPONSE",
                                "authority",
                                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                                "mappingId", "example.fetch",
                                "sendEventSeq", 10,
                                "callerResultEventSeq", 105)),
                "outputs", Collections.singletonList(object(
                        "portId", producerPort, "cell",
                        constructor + "#u2.fieldReceiver",
                        "rootCallId", 3, "rootMethod", producerRoot,
                        "rootKind", "OBSERVED_FIELD_RECEIVER",
                        "bindingKind", "ACTIVATION_FIELD_ACCESS",
                        "fieldPath", Collections.singletonList("keyId"),
                        "fieldPathDeclarations",
                        Collections.singletonList(field),
                        "rpcDecodedLeafInputs", Collections.singletonList(
                                object("writerEventSeq", 100,
                                        "inputPort", decodePort,
                                        "protocolCarrierResponsePort",
                                        responsePort,
                                        "authority",
                                        "TRUSTED_DECLARED_CARRIER_PROJECTION_V1")),
                        "runtimeAccesses", Arrays.asList(
                                object("rootCallId", 3, "eventSeq", 50,
                                        "staticAccessSiteId",
                                        constructor + "#u2",
                                        "activationLocalStaticSiteOccurrence",
                                        1, "bindingKind",
                                        "ACTIVATION_FIELD_ACCESS",
                                        "fieldReceiverObjectId", 100,
                                        "valueObjectId", 0,
                                        "fieldPathDeclarations",
                                        Collections.singletonList(field)),
                                object("rootCallId", 3, "eventSeq", 100,
                                        "staticAccessSiteId",
                                        constructor + "#u2",
                                        "activationLocalStaticSiteOccurrence",
                                        25, "bindingKind",
                                        "ACTIVATION_FIELD_ACCESS",
                                        "fieldReceiverObjectId", 200,
                                        "valueObjectId", 0,
                                        "fieldPathDeclarations",
                                        Collections.singletonList(field))))),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", consumerPort, "cell", TARGET + "#u1.fieldReceiver",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 200, "fieldReceiverObjectId", 200,
                "eventSeq", 110,
                "fieldPath", Collections.singletonList("keyId"),
                "fieldPathDeclarations", Collections.singletonList(field))));

        File regions = jsonl("decoded-leaf-regions.jsonl", producer,
                consumer);
        File edges = jsonl("decoded-leaf-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.decoded-keyId",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", producerPort, "toPort", consumerPort,
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 200, "valueObjectId", 0,
                "writerEventSeq", 100, "readerEventSeq", 110,
                "fieldPathDeclarations", Collections.singletonList(field)));
        Map<String, Object> parameterIdentity = refinedEdge(
                "DF.parameter", "VALUE_PASS", parameter, local,
                constructor, constructor + "#u1", 1);
        parameterIdentity.put("valueFlowAuthority",
                "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1");
        parameterIdentity.put("directCopyKind", "PARAMETER_IDENTITY");
        Map<String, Object> failure = targetRefinedEdge(
                "DF.target.failure", "GUARD", TARGET + "::$keyId",
                "exception", TARGET, TARGET + "#u4", 4);
        failure.put("kind", "exception_guard");
        File refined = jsonl("decoded-leaf-refined.jsonl",
                parameterIdentity,
                refinedEdge("DF.write", "HEAP_WRITE", local, field,
                        constructor, constructor + "#u2", 2),
                targetRefinedEdge("DF.target.read", "HEAP_READ", field,
                        TARGET + "::$keyId", TARGET, TARGET + "#u1", 1),
                failure);
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                        8, producerRoot, 30, "example.Decoder", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, constructor, 31, "example.Key", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "r",
                        7, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "r",
                        7, TARGET, 41, "example.Target", 2, 1, 0));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, constructor));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, edges, refined, Arrays.asList(producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))), methods,
                Collections.singletonList(branchEvent(
                        120, TARGET, 2, TARGET + "#u4", false)),
                Collections.singletonList(
                        new RuntimeRegionPlanner.FieldAccessEvent(100,
                                "FIELD_WRITE", constructor, 4, 2,
                                constructor + "#u2", field, 200, 0,
                                "7")));

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        Map<String, Object> action = rows(goal.get("symbolize")).stream()
                .filter(row -> decodePort.equals(row.get("symbol")))
                .findFirst().get();
        assertEquals(decodePort, action.get("symbol"));
        assertEquals(parameter, action.get("cell"));
        assertEquals("PROTOCOL_ARGUMENT", action.get("location"));
        assertEquals(25, ((Number) action.get("replayOccurrence"))
                .intValue());
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        assertEquals(Arrays.asList(decodePort, responsePort),
                slice.get("inputPorts"));
        assertEquals(100L, ((Number) slice.get("selectedRuntimeEventSeq"))
                .longValue());
    }

    @Test(expected = IllegalStateException.class)
    public void decodedLeafLedgerNeverFallsBackToAnotherOccurrence() {
        Map<String, Object> output = object(
                "rpcDecodedLeafInputs", Collections.singletonList(object(
                        "writerEventSeq", 100,
                        "inputPort", "REGION.P.in.exact",
                        "protocolCarrierResponsePort",
                        "REGION.P.in.response",
                        "authority",
                        "TRUSTED_DECLARED_CARRIER_PROJECTION_V1")));

        RuntimeRegionPlanner.decodedLeafPortsFor(output, 101);
    }

    @Test(expected = IllegalStateException.class)
    public void decodedLeafLedgerRequiresItsProtocolCarrier() {
        Map<String, Object> output = object(
                "rpcDecodedLeafInputs", Collections.singletonList(object(
                        "writerEventSeq", 100,
                        "inputPort", "REGION.P.in.exact",
                        "authority",
                        "TRUSTED_DECLARED_CARRIER_PROJECTION_V1")));

        RuntimeRegionPlanner.decodedLeafPortsFor(output, 100);
    }

    @Test
    public void exactOutputCorridorExcludesEarlierSiblingInvocation()
            throws Exception {
        String producerRoot = "<example.Service: void run()>";
        String sibling = "<example.Service: void register()>";
        String update = "<example.Service: void update()>";
        String expiry = "<example.Keys: void removeExpired()>";
        String stateField = "<example.State: int value>";
        String expiryField = "<example.Key: long expiry>";
        String noiseField = "<example.Registry: boolean enabled>";
        String updated = update + "::i0";
        String expired = expiry + "::z0";
        String noise = sibling + "::z0";

        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", "reader",
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations",
                Collections.singletonList(stateField))));
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", update, "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, sibling, update,
                        expiry),
                "symbolicInputs", Arrays.asList(
                        object("portId", "REGION.P.in.base",
                                "cell", updated, "rootCallId", 3,
                                "rootMethod", update,
                                "sourceKind", "PARAMETER",
                                "rootKind", "PARAMETER",
                                "rootParameterIndex", 0),
                        heapPort("REGION.P.in.expiry", 3, expiry,
                                expiry + "#u1", 12, 88, expiryField,
                                "expiry"),
                        heapPort("REGION.P.in.noise", 3, sibling,
                                sibling + "#u1", 8, 99, noiseField,
                                "enabled")),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.P.out.value", "cell", "writer",
                        "rootCallId", 3, "rootMethod", update,
                        "bindingKind", "DECLARED_FIELD_ACCESS",
                        "rootObjectId", 77, "fieldReceiverObjectId", 77,
                        "siteId", update + "#u4",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations",
                        Collections.singletonList(stateField),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 20,
                                "staticAccessSiteId", update + "#u4",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "fieldReceiverObjectId", 77,
                                "fieldPathDeclarations",
                                Collections.singletonList(stateField))))),
                "branchPolicies", Arrays.asList(
                        object("siteId", expiry + "#u2",
                                "method", expiry, "unitIndex", 2,
                                "operandCells",
                                Collections.singletonList(expired),
                                "policy", "EXPLORE"),
                        object("siteId", sibling + "#u2",
                                "method", sibling, "unitIndex", 2,
                                "operandCells",
                                Collections.singletonList(noise),
                                "policy", "EXPLORE")));
        File regions = jsonl("corridor-regions.jsonl", producer, consumer);
        File regionEdges = jsonl("corridor-region-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.corridor",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", "REGION.P.out.value",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77, "writerEventSeq", 20,
                "readerEventSeq", 30,
                "fieldPathDeclarations",
                Collections.singletonList(stateField)));
        File refined = jsonl("corridor-refined.jsonl",
                refinedEdge("DF.write", "HEAP_WRITE", updated,
                        stateField, update, update + "#u4", 4),
                refinedEdge("DF.expiry-control", "GUARD", expired,
                        updated, expiry, expiry + "#u2", 2),
                refinedEdge("DF.expiry-read", "HEAP_READ", expiryField,
                        expired, expiry, expiry + "#u1", 1),
                refinedEdge("DF.sibling-control", "GUARD", noise,
                        updated, sibling, sibling + "#u2", 2),
                refinedEdge("DF.sibling-read", "HEAP_READ", noiseField,
                        noise, sibling, sibling + "#u1", 1));
        List<RuntimeRegionPlanner.MethodEvent> methods = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, producerRoot, 30, "example.Service", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "w",
                        8, sibling, 30, "example.Service", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "w",
                        8, update, 30, "example.Service", 5, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "w",
                        8, expiry, 31, "example.Keys", 6, 5, 0),
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "r",
                        7, ROOT, 40, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(6, "test", "p", "r",
                        7, TARGET, 41, "example.Target", 2, 1, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                branchEvent(8, sibling, 4, sibling + "#u2", true),
                branchEvent(12, expiry, 6, expiry + "#u2", true),
                new RuntimeRegionPlanner.RuntimeEvent(20,
                        "CALL_SITE_RETURN", update, 5, 20, 0,
                        update + "#u4", -1, "", 0, "", false, false));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot,
                Arrays.asList(3L, 4L, 5L, 6L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, sibling, update, expiry));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                methods, runtime, Collections.emptyList());
        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);

        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        String definitions = String.valueOf(
                goal.get("runtimeDefinitionMethods"));
        assertTrue(definitions.contains(update));
        assertTrue(definitions.contains(expiry));
        assertTrue(!definitions.contains(sibling));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        String ports = String.valueOf(slice.get("inputPorts"));
        assertTrue(ports.contains("REGION.P.in.base"));
        assertTrue(ports.contains("REGION.P.in.expiry"));
        assertTrue(!ports.contains("REGION.P.in.noise"));
        String sites = String.valueOf(slice.get("sites"));
        assertTrue(sites.contains(expiry + "#u2"));
        assertTrue(!sites.contains(sibling + "#u2"));
        assertTrue(String.valueOf(slice.get("methods")).contains(expiry));
        List<Map<String, Object>> exactBranches = rows(
                slice.get("branchReplay"));
        assertEquals(1, exactBranches.size());
        Map<String, Object> exactExpiry = exactBranches.get(0);
        assertEquals(expiry + "#u2", exactExpiry.get("siteId"));
        assertEquals(1, ((Number) exactExpiry.get(
                "selectedOccurrence")).intValue());
        assertEquals(12L, ((Number) exactExpiry.get(
                "selectedRuntimeEventSeq")).longValue());
        assertEquals(6L, ((Number) exactExpiry.get(
                "selectedCallId")).longValue());
        for (Map<String, Object> occurrence
                : rows(exactExpiry.get("occurrences"))) {
            assertTrue(((Number) occurrence.get("eventSeq")).longValue()
                    <= 20L);
            assertEquals(6L,
                    ((Number) occurrence.get("callId")).longValue());
        }
    }

    @Test
    public void producerClosureUsesReachableProtocolReturnBoundary()
            throws Exception {
        String stateField = "<example.State: int value>";
        String rpcCell = RPC_RESULT + "::$r0";
        String parameter = STATE_UPDATE + ".param0:java.lang.Object";
        String local = STATE_UPDATE + "::r1";
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", WRITER,
                "anchorMethod", STATE_UPDATE,
                "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(WRITER, STATE_UPDATE, RPC_RESULT),
                "symbolicInputs", Arrays.asList(
                        object("portId", "REGION.P.in.state",
                                "cell", stateField, "rootCallId", 3,
                                "rootMethod", STATE_UPDATE,
                                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                                "rootKind", "OBSERVED_FIELD_RECEIVER",
                                "rootObjectId", 77,
                                "fieldReceiverObjectId", 77,
                                "siteId", STATE_UPDATE + "#u2",
                                "fieldPath", Collections.singletonList(
                                "value"),
                                "fieldPathDeclarations",
                                Collections.singletonList(stateField)),
                        object("portId", "REGION.P.in.rpc",
                                "cell", rpcCell,
                                "sourceKind", "PROTOCOL_INPUT",
                                "toRootCallId", 3,
                                "receiveEventSeq", 4,
                                "protocolDirection", "RESPONSE",
                                "mappingId", "example.rpc")),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.P.out.state", "cell", stateField,
                        "rootCallId", 3, "rootMethod", STATE_UPDATE,
                        "bindingKind", "DECLARED_FIELD_ACCESS",
                        "rootObjectId", 77, "fieldReceiverObjectId", 77,
                        "siteId", STATE_UPDATE + "#u4",
                        "fieldPath", Collections.singletonList("value"),
                        "fieldPathDeclarations",
                        Collections.singletonList(stateField),
                        "runtimeAccesses", Collections.singletonList(object(
                                "rootCallId", 3, "eventSeq", 5,
                                "staticAccessSiteId", STATE_UPDATE + "#u4",
                                "activationLocalStaticSiteOccurrence", 1,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "fieldReceiverObjectId", 77,
                                "fieldPathDeclarations",
                                Collections.singletonList(stateField))))),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.value", "cell", stateField,
                "rootCallId", 1, "rootMethod", TARGET,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", 77, "fieldReceiverObjectId", 77,
                "siteId", TARGET + "#u1",
                "fieldPath", Collections.singletonList("value"),
                "fieldPathDeclarations", Collections.singletonList(
                stateField))));
        File regions = jsonl("protocol-boundary-regions.jsonl",
                producer, consumer);
        File regionEdges = jsonl("protocol-boundary-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_FIELD_FLOW",
                "transportKind", "HEAP", "edgeId", "RF.protocol-boundary",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", "REGION.P.out.state",
                "toPort", "REGION.1.in.value",
                "fromRootCallId", 3, "toRootCallId", 1,
                "fromLaneId", 8, "toLaneId", 7,
                "receiverObjectId", 77,
                "writerEventSeq", 5, "readerEventSeq", 6,
                "fieldPathDeclarations", Collections.singletonList(
                stateField)));
        File refined = jsonl("protocol-boundary-refined.jsonl",
                refinedEdge("DF.write", "HEAP_WRITE", local, stateField,
                        STATE_UPDATE, STATE_UPDATE + "#u4", 4),
                refinedEdge("DF.param", "VALUE_PASS", parameter, local,
                        STATE_UPDATE, STATE_UPDATE + "#u1", 1),
                refinedEdge("DF.rpc", "IDENTITY_BINDING", rpcCell,
                        parameter, RPC_RESULT, RPC_RESULT + "#u2", 2));
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "w",
                        8, WRITER, 30, "example.Writer", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "w",
                        8, RPC_RESULT, 40, "example.Rpc", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(5, "test", "p", "w",
                        8, STATE_UPDATE, 50, "example.State", 5, 3, 0));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, WRITER, Arrays.asList(3L, 4L, 5L));
        producerActivation.put("observedMethods",
                Arrays.asList(WRITER, RPC_RESULT, STATE_UPDATE));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        assertEquals(Arrays.asList("REGION.P.in.state", "REGION.P.in.rpc"),
                slice.get("inputPorts"));
        assertTrue(String.valueOf(slice.get("methods")).contains(RPC_RESULT));
        assertTrue(String.valueOf(slice.get("staticSites"))
                .contains(RPC_RESULT + "#u2"));
        List<Map<String, Object>> symbolize = rows(goal.get("symbolize"));
        assertEquals(2, symbolize.size());
        assertEquals("PROTOCOL_RETURN", symbolize.stream()
                .filter(row -> "REGION.P.in.rpc".equals(row.get("symbol")))
                .findFirst().get().get("location"));
    }

    @Test
    public void completeProtocolEqualityBuildsServerReturnClosure()
            throws Exception {
        String stateField = "<example.State: java.lang.Object values>";
        String local = SERVER_RETURN + "::r1";
        String response = SERVER_RETURN + "::r2";
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", SERVER_RETURN,
                "anchorMethod", SERVER_RETURN,
                "selection", "STATE_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Collections.singletonList(SERVER_RETURN),
                "symbolicInputs", Arrays.asList(object(
                        "portId", "REGION.P.in.values",
                        "cell", SERVER_RETURN + ".receiver",
                        "rootCallId", 3, "rootMethod", SERVER_RETURN,
                        "sourceKind", "RECEIVER_FIELD",
                        "rootKind", "OBSERVED_FIELD_RECEIVER",
                        "rootObjectId", 70, "fieldReceiverObjectId", 77,
                        "siteId", SERVER_RETURN + "#u1",
                        "fieldPath", Collections.singletonList("values"),
                        "fieldPathDeclarations",
                        Collections.singletonList(stateField)),
                        object("portId", "REGION.P.in.ambiguous-a",
                                "cell", local, "rootCallId", 3,
                                "rootMethod", SERVER_RETURN,
                                "sourceKind", "PARAMETER"),
                        object("portId", "REGION.P.in.ambiguous-b",
                                "cell", local, "rootCallId", 3,
                                "rootMethod", SERVER_RETURN,
                                "sourceKind", "PARAMETER")),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.P.out.response",
                        "cell", SERVER_RETURN + ".return",
                        "sourceKind", "PROTOCOL_INPUT",
                        "protocolDirection", "RESPONSE",
                        "fromRootCallId", 3)),
                "branchPolicies", Collections.singletonList(object(
                        "siteId", SERVER_RETURN + "#u4",
                        "method", SERVER_RETURN, "unitIndex", 4,
                        "policy", "EXPLORE")));
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.response",
                "cell", "<example.Client: example.Response call()>.return",
                "sourceKind", "PROTOCOL_INPUT",
                "protocolDirection", "RESPONSE", "toRootCallId", 1)));
        File regions = jsonl("return-regions.jsonl", producer, consumer);
        File regionEdges = jsonl("return-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_PROTOCOL_FLOW",
                "transportKind", "RPC", "edgeId", "RP.response",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", "REGION.P.out.response",
                "toPort", "REGION.1.in.response",
                "fromRootCallId", 3, "toRootCallId", 1,
                "direction", "RESPONSE", "mappingId", "example.rpc",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "callerSiteEventSeq", 4, "sendEventSeq", 5,
                "receiveEventSeq", 6));
        File refined = jsonl("return-refined.jsonl",
                refinedEdge("DF.return", "VALUE_PASS", response,
                        SERVER_RETURN + ".return", SERVER_RETURN,
                        SERVER_RETURN + "#u3", 3),
                refinedEdge("DF.construct", "CONSTRUCT", local, response,
                        SERVER_RETURN, SERVER_RETURN + "#u2", 2),
                refinedEdge("DF.read", "HEAP_READ", stateField, local,
                        SERVER_RETURN, SERVER_RETURN + "#u1", 1));
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(0, "test", "p", "w",
                8, SERVER_RETURN, 30, "example.Server", 3, 0, 0));
        events.addAll(methods());
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, SERVER_RETURN,
                Collections.singletonList(3L));
        producerActivation.put("observedMethods",
                Collections.singletonList(SERVER_RETURN));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        assertEquals("RETURN", ((Map<?, ?>) member.get("output"))
                .get("kind"));
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        assertEquals(Collections.singletonList("REGION.P.in.values"),
                slice.get("inputPorts"));
        assertEquals(Collections.emptyList(), slice.get("captureBindings"));
        assertEquals(Collections.singletonList(SERVER_RETURN),
                slice.get("methods"));
        assertEquals(1, ((List<?>) goal.get("symbolize")).size());
        assertEquals(1, ((List<?>) goal.get("branches")).size());
    }

    @Test
    public void completeProtocolRequestBuildsCallArgumentClosure()
            throws Exception {
        String producerRoot = "<example.Producer: void run()>";
        String producerMethod =
                "<example.Producer: void build(java.lang.String)>";
        String wireMethod = "<example.Wire: void send(java.lang.String)>";
        String inputCell = producerMethod + ".param0:java.lang.String";
        String outputCell = producerMethod + "::r1";
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", producerMethod,
                "selection", "PROTOCOL_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, producerMethod),
                "symbolicInputs", Collections.singletonList(object(
                        "portId", "REGION.P.in.payload", "cell", inputCell,
                        "rootCallId", 3, "rootMethod", producerRoot,
                        "sourceKind", "PARAMETER", "rootKind", "PARAMETER",
                        "rootParameterIndex", 0)),
                "outputs", Collections.singletonList(object(
                        "portId", "REGION.P.out.request", "cell", outputCell,
                        "sourceKind", "PROTOCOL_INPUT",
                        "protocolDirection", "REQUEST",
                        "fromRootCallId", 3)),
                "branchPolicies", Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.request",
                "cell", "<example.Server: void receive(java.lang.String)>"
                        + ".param0:java.lang.String",
                "sourceKind", "PROTOCOL_INPUT",
                "protocolDirection", "REQUEST", "toRootCallId", 1)));
        File regions = jsonl("request-regions.jsonl", producer, consumer);
        File regionEdges = jsonl("request-edges.jsonl", object(
                "schemaVersion", 3, "kind", "RUNTIME_PROTOCOL_FLOW",
                "transportKind", "RPC", "edgeId", "RP.request",
                "fromRegion", "REGION.P", "toRegion", "REGION.1",
                "fromPort", "REGION.P.out.request",
                "toPort", "REGION.1.in.request",
                "fromRootCallId", 3, "toRootCallId", 1,
                "direction", "REQUEST", "mappingId", "example.rpc",
                "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "callerSiteEventSeq", 4, "sendEventSeq", 5,
                "receiveEventSeq", 6,
                "callerMethod", producerMethod,
                "callerSiteId", producerMethod + "#u3",
                "callerUnitIndex", 3,
                "callerInvocationId", 4,
                "callerDeclaredCallee", wireMethod,
                "clientArgumentIndex", 0,
                "serverParameterIndex", 0));
        File refined = jsonl("request-refined.jsonl",
                refinedEdge("DF.request-value", "VALUE_PASS", inputCell,
                        outputCell, producerMethod, producerMethod + "#u2", 2));
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                8, producerRoot, 30, "example.Producer", 3, 0, 0));
        events.add(new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "w",
                8, producerMethod, 30, "example.Producer", 4, 3, 0));
        events.addAll(methods());
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, producerMethod));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());

        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> goal = rows(plan.get("closureGoals")).get(0);
        assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                .get("state"));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = rows(closure.get("members")).get(0);
        assertEquals("REGION_OUTPUT", ((Map<?, ?>) member.get("output"))
                .get("kind"));
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        assertEquals(Collections.singletonList("REGION.P.in.payload"),
                slice.get("inputPorts"));
        Map<String, Object> capture = rows(slice.get("captureBindings"))
                .get(0);
        assertEquals("CALL_ARGUMENT", capture.get("captureKind"));
        assertEquals(producerMethod, capture.get("definitionMethod"));
        assertEquals(wireMethod, capture.get("declaredCallee"));
        assertEquals(0, ((Number) capture.get("argumentIndex")).intValue());

        Map<String, Object> consumerPlan = result.regionPlans.stream()
                .filter(row -> "REGION.1".equals(row.get("regionId")))
                .findFirst().get();
        Map<String, Object> consumerGoal = rows(
                consumerPlan.get("closureGoals")).get(0);
        List<Map<String, Object>> incoming = rows(
                consumerGoal.get("edgeBindings"));
        assertEquals(1, incoming.size());
        assertEquals("REGION.1.in.request",
                incoming.get(0).get("toInputPort"));
        assertEquals("TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                incoming.get(0).get("evidenceKind"));
    }

    @Test
    public void repeatedProtocolPortsAtOneEndpointBecomeSixAlternatives()
            throws Exception {
        String producerRoot = "<example.Producer: void run()>";
        String producerMethod =
                "<example.Producer: void build(java.lang.String)>";
        String wireMethod = "<example.Wire: void send(java.lang.String)>";
        String inputCell = producerMethod + ".param0:java.lang.String";
        String outputCell = producerMethod + "::r1";
        List<Map<String, Object>> outputs = new ArrayList<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        for (int occurrence = 1; occurrence <= 6; occurrence++) {
            String port = "REGION.P.out.request." + occurrence;
            outputs.add(object("portId", port, "cell", outputCell,
                    "sourceKind", "PROTOCOL_INPUT",
                    "protocolDirection", "REQUEST",
                    "fromRootCallId", 3));
            long caller = occurrence * 10L;
            edges.add(object("schemaVersion", 3,
                    "kind", "RUNTIME_PROTOCOL_FLOW",
                    "transportKind", "RPC",
                    "edgeId", "RP.request." + occurrence,
                    "fromRegion", "REGION.P", "toRegion", "REGION.1",
                    "fromPort", port, "toPort", "REGION.1.in.request",
                    "fromRootCallId", 3, "toRootCallId", 1,
                    "direction", "REQUEST", "mappingId", "example.rpc",
                    "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                    "callerSiteEventSeq", caller,
                    "sendEventSeq", caller + 1,
                    "receiveEventSeq", caller + 2,
                    "callerMethod", producerMethod,
                    "callerSiteId", producerMethod + "#u3",
                    "callerUnitIndex", 3,
                    "callerInvocationId", caller,
                    "callerDeclaredCallee", wireMethod,
                    "clientArgumentIndex", 0,
                    "serverParameterIndex", 0));
        }
        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", producerMethod,
                "selection", "PROTOCOL_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, producerMethod),
                "symbolicInputs", Collections.singletonList(object(
                        "portId", "REGION.P.in.payload", "cell", inputCell,
                        "rootCallId", 3, "rootMethod", producerRoot,
                        "sourceKind", "PARAMETER", "rootKind", "PARAMETER",
                        "rootParameterIndex", 0)),
                "outputs", outputs, "branchPolicies",
                Collections.emptyList());
        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Collections.singletonList(object(
                "portId", "REGION.1.in.request",
                "cell", "<example.Server: void receive(java.lang.String)>"
                        + ".param0:java.lang.String",
                "sourceKind", "PROTOCOL_INPUT",
                "protocolDirection", "REQUEST", "toRootCallId", 1)));
        File regions = jsonl("repeated-request-regions.jsonl",
                producer, consumer);
        File regionEdges = jsonl("repeated-request-edges.jsonl",
                edges.toArray(new Map[0]));
        File refined = jsonl("repeated-request-refined.jsonl",
                refinedEdge("DF.request-value", "VALUE_PASS", inputCell,
                        outputCell, producerMethod,
                        producerMethod + "#u2", 2));
        List<RuntimeRegionPlanner.MethodEvent> events = new ArrayList<>();
        events.add(new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                8, producerRoot, 30, "example.Producer", 3, 0, 0));
        events.add(new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "w",
                8, producerMethod, 30, "example.Producer", 4, 3, 0));
        events.addAll(methods());
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, producerMethod));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());
        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
        assertEquals(6, goals.size());
        Set<Long> occurrences = new LinkedHashSet<>();
        for (Map<String, Object> goal : goals) {
            assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                    .get("state"));
            assertEquals(1, rows(goal.get("edgeBindings")).size());
            @SuppressWarnings("unchecked")
            Map<String, Object> closure = (Map<String, Object>) goal.get(
                    "outputClosure");
            List<Map<String, Object>> members = rows(closure.get("members"));
            assertEquals(1, members.size());
            @SuppressWarnings("unchecked")
            Map<String, Object> output = (Map<String, Object>) members.get(0)
                    .get("output");
            occurrences.add(((Number) output.get(
                    "outputOccurrence")).longValue());
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                1L, 2L, 3L, 4L, 5L, 6L)),
                occurrences);
    }

    @Test
    public void targetReachClosureKeepsOnlyFailureDependencyFrontier()
            throws Exception {
        String parse = "<example.Protocol: int decode(java.lang.String)>";
        String expiry = "<example.Keys: boolean expired()>";
        String noise = "<example.Protobuf: void readUnknownFields()>";
        String unrelated = "<example.Metrics: boolean enabled()>";
        String allKeys = "<example.Keys: java.util.Map allKeys>";
        String expiryField = "<example.Key: long expiry>";
        String noiseField = "<example.Protobuf: java.lang.Object input>";
        String unrelatedField = "<example.Metrics: boolean enabled>";
        String protocolInput = parse + ".param0:java.lang.String";
        String keyId = parse + "::i0";
        String map = TARGET + "::$r1";
        String lookup = TARGET + "::$r2";
        String result = TARGET + "::r3";
        String expired = expiry + "::z0";
        String ignored = noise + "::$r0";
        String metric = unrelated + "::z0";
        String loop = TARGET + "::i9";

        Map<String, Object> region = fullRegion();
        region.put("methods", Arrays.asList(ROOT, TARGET, parse, expiry,
                noise, unrelated));
        region.put("symbolicInputs", Arrays.asList(
                heapPort("REGION.1.in.allKeys", 1, TARGET,
                        TARGET + "#u2", 10, 77, allKeys, "allKeys"),
                object("portId", "REGION.1.in.username",
                        "cell", protocolInput,
                        "sourceKind", "PROTOCOL_INPUT",
                        "protocolDirection", "REQUEST",
                        "toRootCallId", 1),
                heapPort("REGION.1.in.expiry", 1, expiry,
                        expiry + "#u1", 11, 88, expiryField, "expiry"),
                heapPort("REGION.1.in.protobuf", 1, noise,
                        noise + "#u1", 12, 99, noiseField, "input"),
                heapPort("REGION.1.in.metrics", 1, unrelated,
                        unrelated + "#u1", 13, 100, unrelatedField,
                        "enabled"),
                object("portId", "REGION.1.in.loop", "cell", loop,
                        "rootCallId", 1, "rootMethod", TARGET,
                        "sourceKind", "PARAMETER", "rootKind", "PARAMETER",
                        "rootParameterIndex", 0)));
        region.put("outputs", Collections.emptyList());
        region.put("branchPolicies", Arrays.asList(
                object("siteId", TARGET + "#u8", "method", TARGET,
                        "unitIndex", 8, "failureTarget", true,
                        "operandCells", Collections.singletonList(result),
                        "requiredOutcome", false,
                        "loopControlGuard", false,
                        "policy", "PATH_ASSUMPTION"),
                object("siteId", expiry + "#u2", "method", expiry,
                        "unitIndex", 2, "failureTarget", false,
                        "operandCells", Collections.singletonList(expired),
                        "loopControlGuard", false, "policy", "EXPLORE"),
                object("siteId", noise + "#u2", "method", noise,
                        "unitIndex", 2, "failureTarget", false,
                        "operandCells", Collections.singletonList(ignored),
                        "loopControlGuard", false, "policy", "EXPLORE"),
                object("siteId", unrelated + "#u2", "method", unrelated,
                        "unitIndex", 2, "failureTarget", false,
                        "operandCells", Collections.singletonList(metric),
                        "loopControlGuard", false, "policy", "EXPLORE"),
                object("siteId", TARGET + "#u9", "method", TARGET,
                        "unitIndex", 9, "failureTarget", false,
                        "operandCells", Collections.singletonList(loop),
                        "loopControlGuard", true, "policy", "EXPLORE")));

        File regions = jsonl("target-slice-regions.jsonl", region);
        File regionEdges = jsonl("target-slice-region-edges.jsonl");
        File refined = jsonl("target-slice-refined.jsonl",
                targetRefinedEdge("DF.target-result", "VALUE_PASS", lookup,
                        result, TARGET, TARGET + "#u7", 7),
                targetRefinedEdge("DF.lookup-map", "MODEL_TRANSFORM", map,
                        lookup, TARGET, TARGET + "#u6", 6),
                targetRefinedEdge("DF.lookup-key", "MODEL_TRANSFORM", keyId,
                        lookup, TARGET, TARGET + "#u6", 6),
                targetRefinedEdge("DF.map-read", "HEAP_READ", allKeys, map,
                        TARGET, TARGET + "#u2", 2),
                targetRefinedEdge("DF.decode", "IDENTITY_BINDING",
                        protocolInput, keyId, parse, parse + "#u1", 1),
                targetRefinedEdge("DF.expiry-control", "GUARD", expired,
                        lookup, expiry, expiry + "#u2", 2),
                targetRefinedEdge("DF.expiry-read", "HEAP_READ",
                        expiryField, expired, expiry, expiry + "#u1", 1),
                targetRefinedEdge("DF.noise-read", "HEAP_READ", noiseField,
                        ignored, noise, noise + "#u1", 1),
                targetRefinedEdge("DF.noise-control", "GUARD", ignored,
                        lookup, noise, noise + "#u2", 2),
                targetRefinedEdge("DF.metrics-read", "HEAP_READ",
                        unrelatedField, metric, unrelated,
                        unrelated + "#u1", 1),
                targetRefinedEdge("DF.loop-control", "GUARD", loop, lookup,
                        TARGET, TARGET + "#u9", 9));
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "t",
                        7, parse, 21, "example.Protocol", 3, 2, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "t",
                        7, expiry, 22, "example.Keys", 4, 2, 0));
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = Arrays.asList(
                branchEvent(10, TARGET, 2, TARGET + "#u8", true),
                branchEvent(11, expiry, 4, expiry + "#u2", false),
                branchEvent(13, TARGET, 2, TARGET + "#u9", true));
        Map<String, Object> seed = activation("REGION.1", 1, ROOT,
                Arrays.asList(1L, 2L, 3L, 4L));
        seed.put("observedMethods", Arrays.asList(ROOT, TARGET, parse,
                expiry));

        RuntimeRegionPlanner.Result planned = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined,
                Collections.singletonList(seed), events, runtime,
                Collections.emptyList());
        Map<String, Object> goal = rows(planned.regionPlans.get(0)
                .get("closureGoals")).get(0);

        String symbols = String.valueOf(goal.get("symbolize"));
        assertTrue(symbols.contains("REGION.1.in.allKeys"));
        assertTrue(symbols.contains("REGION.1.in.username"));
        assertTrue(symbols.contains("REGION.1.in.expiry"));
        assertTrue(symbols.contains("REGION.1.in.protobuf"));
        assertTrue(!symbols.contains("REGION.1.in.metrics"));
        assertTrue(!symbols.contains("REGION.1.in.loop"));
        String selectedBranches = String.valueOf(goal.get("branches"));
        assertTrue(selectedBranches.contains(TARGET + "#u8"));
        assertTrue(selectedBranches.contains(expiry + "#u2"));
        assertTrue(selectedBranches.contains(noise + "#u2"));
        assertTrue(!selectedBranches.contains(unrelated + "#u2"));
        assertTrue(!selectedBranches.contains(TARGET + "#u9"));
        String definitions = String.valueOf(
                goal.get("runtimeDefinitionMethods"));
        assertTrue(definitions.contains(ROOT));
        assertTrue(definitions.contains(TARGET));
        assertTrue(definitions.contains(parse));
        assertTrue(definitions.contains(expiry));
        assertTrue(definitions.contains(noise));
        assertTrue(!definitions.contains(unrelated));
        assertTrue(!String.valueOf(goal.get("baselineObservedMethods"))
                .contains(noise));
        Map<String, Object> username = rows(goal.get("symbolize")).stream()
                .filter(row -> "REGION.1.in.username".equals(
                        row.get("symbol")))
                .findFirst().get();
        assertEquals("java.lang.String", username.get("javaType"));
        assertEquals("VALUE_FRONTIER", username.get("dependencyRole"));
        Map<String, Object> expiryAction = rows(goal.get("symbolize"))
                .stream().filter(row -> "REGION.1.in.expiry".equals(
                        row.get("symbol"))).findFirst().get();
        assertEquals("VALUE_FRONTIER",
                expiryAction.get("dependencyRole"));
        Map<String, Object> objectCarrier = rows(goal.get("symbolize"))
                .stream().filter(row -> "REGION.1.in.protobuf".equals(
                        row.get("symbol"))).findFirst().get();
        assertEquals("CONCRETE_STRUCTURE_CARRIER",
                objectCarrier.get("dependencyRole"));
    }

    @Test
    public void dependencyRoleKeepsBoundedContainersAndCompactLeavesOnly() {
        assertEquals("VALUE_FRONTIER",
                RuntimeRegionPlanner.effectiveDependencyRole(object(
                        "dependencyRole", "VALUE_FRONTIER",
                        "symbolicDemand", "BOUNDED_CONTAINER_STATE"),
                        "java.util.Map"));
        assertEquals("VALUE_FRONTIER",
                RuntimeRegionPlanner.effectiveDependencyRole(object(
                        "dependencyRole", "VALUE_FRONTIER"), "int[]"));
        assertEquals("VALUE_FRONTIER",
                RuntimeRegionPlanner.effectiveDependencyRole(object(
                        "dependencyRole", "VALUE_FRONTIER"),
                        "java.lang.String"));
        assertEquals("CONCRETE_STRUCTURE_CARRIER",
                RuntimeRegionPlanner.effectiveDependencyRole(object(
                        "dependencyRole", "VALUE_FRONTIER"),
                        "example.PendingMove"));
        assertEquals("CONCRETE_STRUCTURE_CARRIER",
                RuntimeRegionPlanner.effectiveDependencyRole(object(
                        "dependencyRole", "VALUE_FRONTIER"),
                        "example.Response"));
    }

    @Test
    public void exactObservedGuardOnlyBoundedFrontierIsNotAMemberInput() {
        String guard = "<example.Producer: example.Keys reply()>#u4";
        Map<String, Object> input = boundedGuardInput(
                "REGION.1.in.enabled", guard,
                Collections.singletonList("REGION.1.out.other"),
                Collections.singletonList("<example.State: int other>"));
        Map<String, Object> staticPolicy = prefixBranch(guard);
        List<String> ports = new ArrayList<>(Arrays.asList(
                "REGION.1.in.keys", "REGION.1.in.enabled"));

        // Static policy construction precedes runtime replay and deliberately
        // carries no observation authority.  It must fail closed.
        RuntimeRegionPlanner.removeGuardOnlyPathEnablers(ports,
                Collections.singleton("REGION.1.in.enabled"),
                Collections.singletonList(input), 11L,
                "REGION.1.out.keys", "<example.Response: int[] keys>",
                Collections.singleton(guard),
                Collections.singletonList(staticPolicy));

        assertEquals(Arrays.asList("REGION.1.in.keys",
                "REGION.1.in.enabled"), ports);

        // exactBranchReplay enriches a copy only after observing this
        // activation.  That enriched policy is the pruning authority.
        Map<String, Object> exactReplay = new LinkedHashMap<>(staticPolicy);
        exactReplay.put("observed", true);
        exactReplay.put("observedOutcome", true);
        exactReplay.put("selectedOccurrence", 1);
        RuntimeRegionPlanner.removeGuardOnlyPathEnablers(ports,
                Collections.singleton("REGION.1.in.enabled"),
                Collections.singletonList(input), 11L,
                "REGION.1.out.keys", "<example.Response: int[] keys>",
                Collections.singleton(guard),
                Collections.singletonList(exactReplay));

        assertEquals(Collections.singletonList("REGION.1.in.keys"), ports);
        assertTrue(!staticPolicy.containsKey("observed"));
    }

    @Test
    public void guardThatAlsoFeedsSelectedValueRemainsAMemberInput() {
        String guard = "<example.Producer: example.Keys reply()>#u4";
        Map<String, Object> input = boundedGuardInput(
                "REGION.1.in.enabled", guard,
                Collections.singletonList("REGION.1.out.other"),
                Collections.singletonList("<example.State: int other>"));
        List<String> ports = new ArrayList<>(Collections.singletonList(
                "REGION.1.in.enabled"));

        RuntimeRegionPlanner.removeGuardOnlyPathEnablers(ports,
                Collections.<String>emptySet(),
                Collections.singletonList(input), 11L,
                "REGION.1.out.keys", "<example.Response: int[] keys>",
                Collections.singleton(guard), Collections.singletonList(
                        observedPrefixBranch(guard)));

        assertEquals(Collections.singletonList("REGION.1.in.enabled"),
                ports);
    }

    @Test
    public void guardForSelectedBoundedMutationRemainsAMemberInput() {
        String guard = "<example.Producer: example.Keys reply()>#u4";
        String outputPort = "REGION.1.out.keys";
        String outputCell = "<example.Response: int[] keys>";
        Map<String, Object> input = boundedGuardInput(
                "REGION.1.in.expired", guard,
                Collections.singletonList(outputPort),
                Collections.singletonList(outputCell));
        List<String> ports = new ArrayList<>(Collections.singletonList(
                "REGION.1.in.expired"));

        RuntimeRegionPlanner.removeGuardOnlyPathEnablers(ports,
                Collections.singleton("REGION.1.in.expired"),
                Collections.singletonList(input), 11L,
                outputPort, outputCell, Collections.singleton(guard),
                Collections.singletonList(observedPrefixBranch(guard)));

        assertEquals(Collections.singletonList("REGION.1.in.expired"),
                ports);
    }

    @Test
    public void multiOutputClosureSharesEarlierWriteInputAndGuard()
            throws Exception {
        String producerRoot = "<example.Producer: void run()>";
        String build = "<example.Cache: example.Key build()>";
        String source = "<example.Source: int keyId()>";
        String noise = "<example.Noise: void record()>";
        String wire = "<example.Wire: void send(example.Key)>";
        String cacheField = "<example.Cache: example.Key cached>";
        String bookkeepingField =
                "<example.Cache: java.util.Map bookkeeping>";
        String sourceField = "<example.Source: int keyId>";
        String before = build + "::$r1";
        String generated = build + "::$r3";
        String after = build + "::$r5";
        String request = build + "::$r9";
        String rpcValue = producerRoot + "::$r7";

        Map<String, Object> producer = object(
                "schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.P", "rootMethod", producerRoot,
                "anchorMethod", build, "selection", "PROTOCOL_CONTEXT",
                "runtimeRootCallIds", Collections.singletonList(3),
                "methods", Arrays.asList(producerRoot, build, source, noise),
                "symbolicInputs", Arrays.asList(
                        heapPort("REGION.P.in.cache-before", 3, build,
                                build + "#u1", 10, 77, cacheField,
                                "cached"),
                        heapPort("REGION.P.in.source", 3, source,
                                source + "#u1", 15, 88, sourceField,
                                "keyId"),
                        heapPort("REGION.P.in.cache-after", 3, build,
                                build + "#u5", 30, 77, cacheField,
                                "cached"),
                        object("portId", "REGION.P.in.rpc.1",
                                "cell", rpcValue,
                                "sourceKind", "PROTOCOL_INPUT",
                                "toRootCallId", 3,
                                "receiveEventSeq", 11,
                                "protocolDirection", "RESPONSE",
                                "mappingId", "example.rpc"),
                        object("portId", "REGION.P.in.rpc.2",
                                "cell", rpcValue,
                                "sourceKind", "PROTOCOL_INPUT",
                                "toRootCallId", 3,
                                "receiveEventSeq", 20,
                                "protocolDirection", "RESPONSE",
                                "mappingId", "example.rpc"),
                        object("portId", "REGION.P.in.rpc.3",
                                "cell", rpcValue,
                                "sourceKind", "PROTOCOL_INPUT",
                                "toRootCallId", 3,
                                "receiveEventSeq", 29,
                                "protocolDirection", "RESPONSE",
                                "mappingId", "example.rpc")),
                "outputs", Arrays.asList(
                        object("portId", "REGION.P.out.cache",
                                "cell", build + "#u4.fieldReceiver",
                                "rootCallId", 3, "rootMethod", build,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "rootObjectId", 77,
                                "fieldReceiverObjectId", 77,
                                "valueObjectId", 99,
                                "eventSeq", 25,
                                "siteId", build + "#u4",
                                "fieldPath", Collections.singletonList(
                                "cached"),
                                "fieldPathDeclarations",
                                Collections.singletonList(cacheField),
                                "runtimeAccesses", Arrays.asList(
                                object("rootCallId", 3, "eventSeq", 18,
                                        "staticAccessSiteId", build + "#u4",
                                        "activationLocalStaticSiteOccurrence",
                                        1,
                                        "bindingKind",
                                        "DECLARED_FIELD_ACCESS",
                                        "fieldReceiverObjectId", 77,
                                        "valueObjectId", 98,
                                        "fieldPathDeclarations",
                                        Collections.singletonList(
                                                cacheField)),
                                object("rootCallId", 3, "eventSeq", 25,
                                        "staticAccessSiteId", build + "#u4",
                                        "activationLocalStaticSiteOccurrence",
                                        2,
                                        "bindingKind",
                                        "DECLARED_FIELD_ACCESS",
                                        "fieldReceiverObjectId", 77,
                                        "valueObjectId", 99,
                                        "fieldPathDeclarations",
                                        Collections.singletonList(
                                                cacheField)))),
                        object("portId", "REGION.P.out.request",
                                "cell", request,
                                "sourceKind", "PROTOCOL_INPUT",
                                "protocolDirection", "REQUEST",
                                "fromRootCallId", 3),
                        // Runtime selected this unrelated heap endpoint, but
                        // its exact activation-local write was not retained.
                        // It must remain a diagnostic instead of poisoning
                        // the two executable outputs above.
                        object("portId", "REGION.P.out.bookkeeping",
                                "cell", build + "#u8.fieldReceiver",
                                "rootCallId", 3, "rootMethod", build,
                                "bindingKind", "DECLARED_FIELD_ACCESS",
                                "rootObjectId", 77,
                                "fieldReceiverObjectId", 77,
                                "eventSeq", 35, "siteId", build + "#u8",
                                "fieldPath", Collections.singletonList(
                                "bookkeeping"),
                                "fieldPathDeclarations",
                                Collections.singletonList(
                                bookkeepingField))),
                "branchPolicies", Collections.singletonList(object(
                        "siteId", build + "#u2", "method", build,
                        "unitIndex", 2, "policy", "EXPLORE",
                        "loopControlGuard", false,
                        "operandCells", Collections.singletonList(before))));

        Map<String, Object> consumer = fullRegion();
        consumer.put("symbolicInputs", Arrays.asList(
                heapPort("REGION.1.in.cache.early", 1, TARGET,
                        TARGET + "#u0", 19, 77, cacheField, "cached"),
                heapPort("REGION.1.in.cache", 1, TARGET,
                        TARGET + "#u1", 40, 77, cacheField, "cached"),
                heapPort("REGION.1.in.bookkeeping", 1, TARGET,
                        TARGET + "#u8", 41, 77, bookkeepingField,
                        "bookkeeping"),
                object("portId", "REGION.1.in.request",
                        "cell", "<example.Server: void receive(example.Key)>"
                                + ".param0:example.Key",
                        "sourceKind", "PROTOCOL_INPUT",
                        "protocolDirection", "REQUEST",
                        "toRootCallId", 1)));
        File regions = jsonl("reaching-write-regions.jsonl", producer,
                consumer);
        File regionEdges = jsonl("reaching-write-edges.jsonl",
                object("schemaVersion", 3,
                        "kind", "RUNTIME_FIELD_FLOW",
                        "transportKind", "HEAP",
                        "edgeId", "RF.cache.early",
                        "fromRegion", "REGION.P",
                        "toRegion", "REGION.1",
                        "fromPort", "REGION.P.out.cache",
                        "toPort", "REGION.1.in.cache.early",
                        "fromRootCallId", 3, "toRootCallId", 1,
                        "fromLaneId", 8, "toLaneId", 7,
                        "receiverObjectId", 77, "valueObjectId", 98,
                        "writerEventSeq", 18, "readerEventSeq", 19,
                        "fieldPathDeclarations",
                        Collections.singletonList(cacheField)),
                object("schemaVersion", 3,
                        "kind", "RUNTIME_FIELD_FLOW",
                        "transportKind", "HEAP",
                        "edgeId", "RF.bookkeeping",
                        "fromRegion", "REGION.P",
                        "toRegion", "REGION.1",
                        "fromPort", "REGION.P.out.bookkeeping",
                        "toPort", "REGION.1.in.bookkeeping",
                        "fromRootCallId", 3, "toRootCallId", 1,
                        "fromLaneId", 8, "toLaneId", 7,
                        "receiverObjectId", 77, "valueObjectId", 101,
                        "writerEventSeq", 35, "readerEventSeq", 41,
                        "fieldPathDeclarations",
                        Collections.singletonList(bookkeepingField)),
                object("schemaVersion", 3,
                        "kind", "RUNTIME_FIELD_FLOW",
                        "transportKind", "HEAP",
                        "edgeId", "RF.cache",
                        "fromRegion", "REGION.P",
                        "toRegion", "REGION.1",
                        "fromPort", "REGION.P.out.cache",
                        "toPort", "REGION.1.in.cache",
                        "fromRootCallId", 3, "toRootCallId", 1,
                        "fromLaneId", 8, "toLaneId", 7,
                        "receiverObjectId", 77, "valueObjectId", 99,
                        "writerEventSeq", 25, "readerEventSeq", 40,
                        "fieldPathDeclarations",
                        Collections.singletonList(cacheField)),
                object("schemaVersion", 3,
                        "kind", "RUNTIME_PROTOCOL_FLOW",
                        "transportKind", "RPC",
                        "edgeId", "RP.request",
                        "fromRegion", "REGION.P",
                        "toRegion", "REGION.1",
                        "fromPort", "REGION.P.out.request",
                        "toPort", "REGION.1.in.request",
                        "fromRootCallId", 3, "toRootCallId", 1,
                        "direction", "REQUEST",
                        "mappingId", "example.rpc",
                        "authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                        "callerSiteEventSeq", 31, "sendEventSeq", 32,
                        "receiveEventSeq", 33,
                        "callerMethod", build,
                        "callerSiteId", build + "#u7",
                        "callerUnitIndex", 7,
                        "callerInvocationId", 31,
                        "callerDeclaredCallee", wire,
                        "clientArgumentIndex", 0,
                        "serverParameterIndex", 0));
        File refined = jsonl("reaching-write-refined.jsonl",
                refinedEdge("DF.request", "VALUE_PASS", after, request,
                        build, build + "#u6", 6),
                refinedEdge("DF.after", "HEAP_READ", cacheField, after,
                        build, build + "#u5", 5),
                refinedEdge("DF.write", "HEAP_WRITE", generated,
                        cacheField, build, build + "#u4", 4),
                refinedEdge("DF.rpc-value", "VALUE_PASS", rpcValue,
                        generated, build, build + "#u3", 3),
                refinedEdge("DF.source", "HEAP_READ", sourceField,
                        generated, source, source + "#u1", 1),
                refinedEdge("DF.guard", "HEAP_READ", cacheField, before,
                        build, build + "#u1", 1),
                refinedEdge("DF.control", "GUARD", before, cacheField,
                        build, build + "#u2", 2));
        List<RuntimeRegionPlanner.MethodEvent> events = Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "w",
                        8, producerRoot, 1, "example.Producer", 3, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "w",
                        8, build, 2, "example.Cache", 4, 3, 0),
                new RuntimeRegionPlanner.MethodEvent(3, "test", "p", "r",
                        7, ROOT, 3, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(4, "test", "p", "r",
                        7, TARGET, 4, "example.Target", 2, 1, 0));
        Map<String, Object> producerActivation = activation(
                "REGION.P", 3, producerRoot, Arrays.asList(3L, 4L));
        producerActivation.put("observedMethods",
                Arrays.asList(producerRoot, build));

        RuntimeRegionPlanner.Result result = RuntimeRegionPlanner.plan(
                regions, regionEdges, refined, Arrays.asList(
                        producerActivation,
                        activation("REGION.1", 1, ROOT,
                                Arrays.asList(1L, 2L))),
                events, runtime(), Collections.emptyList());
        Map<String, Object> plan = result.regionPlans.stream()
                .filter(row -> "REGION.P".equals(row.get("regionId")))
                .findFirst().get();
        List<Map<String, Object>> goals = rows(plan.get("closureGoals"));
        assertEquals(2, goals.size());
        Set<String> outputPorts = new LinkedHashSet<>();
        Set<String> captureIds = new LinkedHashSet<>();
        Set<String> goalIds = new LinkedHashSet<>();
        Set<Long> cacheOccurrences = new LinkedHashSet<>();
        for (Map<String, Object> goal : goals) {
            goalIds.add(String.valueOf(goal.get("goalId")));
            assertEquals("READY", ((Map<?, ?>) goal.get("admission"))
                    .get("state"));
            Map<String, Object> closure = (Map<String, Object>) goal.get(
                    "outputClosure");
            List<Map<String, Object>> members = rows(
                    closure.get("members"));
            assertEquals(2, members.size());
            for (Map<String, Object> member : members) {
                Map<String, Object> output = (Map<String, Object>) member.get(
                        "output");
                outputPorts.add(String.valueOf(output.get("portId")));
                Map<String, Object> slice = (Map<String, Object>) member.get(
                        "slice");
                String ports = String.valueOf(slice.get("inputPorts"));
                assertTrue(ports.contains("REGION.P.in.source"));
                assertTrue(ports.contains("REGION.P.in.cache-before"));
                assertTrue(!ports.contains("REGION.P.in.cache-after"));
                assertTrue(String.valueOf(slice.get("sites"))
                        .contains(build + "#u2"));
                assertTrue(String.valueOf(slice.get("methods"))
                        .contains(source));
                for (Map<String, Object> capture : rows(
                        slice.get("captureBindings"))) {
                    captureIds.add(String.valueOf(
                            capture.get("captureBindingId")));
                }
                long occurrence = ((Number) output.get(
                        "outputOccurrence")).longValue();
                if ("REGION.P.out.cache".equals(output.get("portId"))) {
                    cacheOccurrences.add(occurrence);
                    assertTrue(ports.contains(occurrence == 1
                            ? "REGION.P.in.rpc.1"
                            : "REGION.P.in.rpc.2"));
                    assertTrue(!ports.contains("REGION.P.in.rpc.3"));
                } else {
                    assertEquals(1L, occurrence);
                    assertTrue(ports.contains("REGION.P.in.rpc.3"));
                }
            }
            assertEquals(2, rows(goal.get("edgeBindings")).size());
            assertTrue(String.valueOf(goal.get(
                    "excludedOutputBlockers"))
                    .contains("REGION.P.out.bookkeeping"));
            assertEquals(1, rows(goal.get("branches")).size());
            String definitions = String.valueOf(
                    goal.get("runtimeDefinitionMethods"));
            assertTrue(definitions.contains(source));
            assertTrue(!definitions.contains(noise));
            assertTrue(!String.valueOf(
                    goal.get("baselineObservedMethods")).contains(source));
        }
        assertEquals(2, goalIds.size());
        assertEquals(new LinkedHashSet<>(Arrays.asList(1L, 2L)),
                cacheOccurrences);
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                "REGION.P.out.cache", "REGION.P.out.request")),
                outputPorts);
        assertEquals(2, captureIds.size());
    }

    private static Map<String, Object> heapPort(
            String port, long rootCallId, String rootMethod, String site,
            long eventSeq, long receiver, String declaration, String field) {
        return object("portId", port, "cell", site + ".fieldReceiver",
                "rootCallId", rootCallId, "rootMethod", rootMethod,
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "rootKind", "OBSERVED_FIELD_RECEIVER",
                "rootObjectId", receiver,
                "fieldReceiverObjectId", receiver,
                "eventSeq", eventSeq, "siteId", site,
                "fieldPath", Collections.singletonList(field),
                "fieldPathDeclarations",
                Collections.singletonList(declaration));
    }

    private static Map<String, Object> accessorPort(
            String port, long rootCallId, long eventSeq, String site) {
        int separator = site.lastIndexOf("#u");
        String method = site.substring(0, separator);
        int unit = Integer.parseInt(site.substring(separator + 2));
        String field = "<example.Payload: int value>";
        return object("portId", port, "cell", field,
                "rootCallId", rootCallId, "eventSeq", eventSeq,
                "sourceKind", "ACCESSOR_RETURN",
                "javaType", "int", "declaredFieldSignature", field,
                "fieldPath", Collections.singletonList("value"),
                "callerMethod", method, "unitIndex", unit,
                "declaredCallee", "<example.Payload: int getValue()>",
                "accessorImplementationMethod",
                "<example.Payload: int getValue()>");
    }

    private static Map<String, Object> refinedEdge(
            String id, String transfer, String from, String to,
            String method, String site, int unit) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW", "id", id,
                "kind", "local_def_use", "transferKind", transfer,
                "fromCell", from, "toCell", to, "method", method,
                "siteId", site, "unitIndex", unit,
                "unit", to + " = " + from,
                "regionIds", Collections.singletonList("REGION.P"),
                "runtimeObserved", true);
    }

    private static Map<String, Object> targetRefinedEdge(
            String id, String transfer, String from, String to,
            String method, String site, int unit) {
        Map<String, Object> edge = refinedEdge(id, transfer, from, to,
                method, site, unit);
        edge.put("regionIds", Collections.singletonList("REGION.1"));
        return edge;
    }

    private static RuntimeRegionPlanner.RuntimeEvent branchEvent(
            long seq, String method, long callId, String site,
            boolean outcome) {
        return new RuntimeRegionPlanner.RuntimeEvent(seq, "BRANCH", method,
                callId, 0, 0, site, -1, "", 0, "", true, outcome);
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> rows(Object value) {
        return (List<Map<String, Object>>) value;
    }

    private static List<RuntimeRegionPlanner.MethodEvent> methods() {
        return Arrays.asList(
                new RuntimeRegionPlanner.MethodEvent(1, "test", "p", "t",
                        7, ROOT, 10, "example.Root", 1, 0, 0),
                new RuntimeRegionPlanner.MethodEvent(2, "test", "p", "t",
                        7, TARGET, 20, "example.Target", 2, 1, 0));
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> runtime() {
        return Collections.singletonList(new RuntimeRegionPlanner.RuntimeEvent(
                3, "BRANCH", TARGET, 2, 0, 0, TARGET + "#u4", -1,
                "", 0, "", true, false));
    }

    private static List<Map<String, Object>> seeds() {
        return Collections.singletonList(activation("REGION.1", 1, ROOT,
                Arrays.asList(1L, 2L)));
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

    private static Map<String, Object> skeleton() {
        return object("schemaVersion", 3, "kind", "REGION_SKELETON",
                "regionId", "REGION.1", "rootMethod", ROOT,
                "rootAuthority", "TASK_ENTRY", "anchorMethod", TARGET,
                "anchorMethods", Collections.singletonList(TARGET),
                "methods", Arrays.asList(ROOT, TARGET),
                "selection", "EXCEPTION_CONTEXT");
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
                "runtimeRootCallIds", Collections.singletonList(1),
                "methods", Arrays.asList(ROOT, TARGET),
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList(),
                "branchPolicies", Collections.singletonList(branch));
    }

    private static Map<String, Object> candidateEdge() {
        return object("schemaVersion", 3, "id", "DF.1",
                "kind", "exception_guard", "transferKind", "GUARD",
                "method", TARGET, "siteId", TARGET + "#u4",
                "fromCell", "guard", "toCell", "exception");
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

    private static Map<String, Object> projectedCarrierInput(
            String portId, String selectionAuthority) {
        return object(
                "portId", portId, "rootCallId", 3,
                "protocolCarrierResponsePort", "REGION.2.in.response",
                "protocolCarrierMappingId", "example.response",
                "protocolCarrierAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "rpcDescendantProjectionInput", true,
                "rpcProjectionAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "rpcProjectionSelectionAuthority", selectionAuthority,
                "rpcProjectionMappingId", "example.response");
    }

    private static Map<String, Object> boundedGuardInput(
            String portId, String guardSite, List<String> outputPorts,
            List<String> outputCells) {
        return object(
                "portId", portId, "rootCallId", 11L,
                "sourceKind", "ACCESSOR_RETURN",
                "dependencyRole", "VALUE_FRONTIER",
                "symbolicDemand", "BOUNDED_STATE_FRONTIER",
                "boundedStateFrontierAuthority",
                "STATIC_ACCESSOR_SEMANTIC_MUTATION_GUARD_V1",
                "boundedMutationGuardSites",
                Collections.singletonList(guardSite),
                "boundedMutationOutputPorts", outputPorts,
                "boundedMutationOutputCells", outputCells);
    }

    private static Map<String, Object> observedPrefixBranch(String site) {
        Map<String, Object> result = prefixBranch(site);
        result.put("observed", true);
        return result;
    }

    private static Map<String, Object> prefixBranch(String site) {
        return object("siteId", site, "policy", "EXPLORE",
                "failureTarget", false, "loopControlGuard", false,
                "requiredOutcome", true);
    }
}
