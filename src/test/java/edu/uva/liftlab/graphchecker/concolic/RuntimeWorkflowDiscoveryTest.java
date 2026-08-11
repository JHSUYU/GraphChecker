package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class RuntimeWorkflowDiscoveryTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void rankedWorkflowReusesDecodedRowsAndIsOrderStable()
            throws Exception {
        String targetInstance = "REGION.T@test#call9";
        File forward = writePlans("ranked-forward.jsonl",
                leafProducerPlan("REGION.P", 3, targetInstance,
                        "REGION.T.in.value"),
                targetPlanWithInput(targetInstance));
        List<JsonObject> rows = ArtifactIO.readJsonl(forward.toPath());
        RuntimeWorkflowDiscovery.RankedWorkflow ranked =
                RuntimeWorkflowDiscovery.rankedWorkflow(rows);

        assertEquals(2, ranked.selections().size());
        assertTrue(ranked.selections().get(0).producerProjection == null);
        assertTrue(ranked.selections().get(1).producerProjection != null);
        assertEquals("REGION.T", ranked.selections().get(0).regionId);
        assertEquals("REGION.P", ranked.selections().get(1).regionId);

        Collections.reverse(rows);
        RuntimeWorkflowDiscovery.RankedWorkflow reversed =
                RuntimeWorkflowDiscovery.rankedWorkflow(rows);
        assertEquals(ranked.targetBinding(), reversed.targetBinding());
        assertEquals(ranked.closureBindings(), reversed.closureBindings());
    }

    @Test
    public void exactInvocationAndPathMergeSingletonProducerTasksAtomically()
            throws Exception {
        String targetInstance = "REGION.T@test#call9";
        List<String> targetPorts = Arrays.asList(
                "REGION.T.in.0", "REGION.T.in.1", "REGION.T.in.2",
                "REGION.T.in.3", "REGION.T.in.4");
        Map<String, Object> producer = singletonGoalProducerPlan(
                targetInstance, targetPorts, false);
        RuntimeWorkflowDiscovery.RankedWorkflow ranked =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        GSON.toJsonTree(producer).getAsJsonObject(),
                        GSON.toJsonTree(targetPlanWithInputs(
                                targetInstance, targetPorts))
                                .getAsJsonObject()));

        assertEquals(2, ranked.scheduledTaskCount());
        assertEquals(2, ranked.closureBindings().size());
        assertTrue(ranked.closureBindings().get(1).contains("#call3"));
        Map<String, JsonObject> components = producerComponents(producer,
                ranked);
        JsonObject complementaryEdge = new JsonObject();
        complementaryEdge.addProperty("edgeId", "EDGE.P.0");
        complementaryEdge.addProperty("fromOutputCell", "value0");
        for (JsonObject component : components.values()) {
            JsonArray edges = component.getAsJsonArray("edgeBindings");
            if ("EDGE.P.0".equals(edges.get(0).getAsJsonObject()
                    .get("edgeId").getAsString())) {
                edges.add(complementaryEdge);
                break;
            }
        }
        List<JsonObject> atomic = ConcolicScheduler
                .atomicProducerTasksForTests(ranked, components);
        assertEquals(1, atomic.size());
        JsonObject task = atomic.get(0);
        assertEquals("REGION.P@test#call2",
                task.get("regionInstanceId").getAsString());
        assertEquals(5, task.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").size());
        int[] expectedOccurrences = {1, 1, 2, 2, 3};
        for (JsonElement memberElement : task.getAsJsonObject(
                "outputClosure").getAsJsonArray("members")) {
            JsonObject member = memberElement.getAsJsonObject();
            JsonObject output = member.getAsJsonObject("output");
            int index = Integer.parseInt(output.get("portId").getAsString()
                    .substring(output.get("portId").getAsString()
                            .lastIndexOf('.') + 1));
            int expectedOccurrence = expectedOccurrences[index];
            JsonObject capture = member.getAsJsonObject("slice")
                    .getAsJsonArray("captureBindings").get(0)
                    .getAsJsonObject();
            assertEquals(expectedOccurrence,
                    capture.get("outputOccurrence").getAsInt());
            assertEquals(expectedOccurrence,
                    capture.get("replayOccurrence").getAsInt());
        }
        assertEquals(7, task.getAsJsonArray("edgeBindings").size());
        JsonObject mergedEdge = null;
        int internalReadFrom = 0;
        for (JsonElement edgeElement : task.getAsJsonArray(
                "edgeBindings")) {
            JsonObject edge = edgeElement.getAsJsonObject();
            if ("EDGE.P.0".equals(edge.get("edgeId").getAsString())) {
                mergedEdge = edge;
            }
            if (edge.get("edgeId").getAsString().startsWith(
                    "RF.INTERNAL.")) {
                internalReadFrom++;
                assertEquals("FIELD_ASSIGNMENT_READ_FROM_V1",
                        edge.get("evidenceKind").getAsString());
                assertEquals("REGION.P@test#call3",
                        edge.get("fromRegionInstance").getAsString());
                assertEquals("REGION.P@test#call3",
                        edge.get("toRegionInstance").getAsString());
            }
        }
        assertEquals(2, internalReadFrom);
        assertTrue(mergedEdge != null);
        assertEquals("rpc.p.0", mergedEdge.get("mappingId").getAsString());
        assertEquals("value0", mergedEdge.get("fromOutputCell")
                .getAsString());
        assertEquals(5, task.getAsJsonObject("producerProjection")
                .getAsJsonArray("outputPorts").size());
        assertEquals(5, task.getAsJsonObject("producerProjection")
                .getAsJsonArray("edgeIds").size());
        assertEquals(3, task.getAsJsonArray("inputActions").size());
        assertEquals(5, task.getAsJsonObject(
                "occurrenceInstantiationCatalog")
                .getAsJsonArray("occurrences").get(0).getAsJsonObject()
                .getAsJsonArray("outputPortMap").size());
        assertEquals(3, task.getAsJsonObject(
                "occurrenceInstantiationCatalog")
                .getAsJsonArray("occurrences").get(0).getAsJsonObject()
                .getAsJsonArray("inputPortMap").size());
        assertEquals(7, task.getAsJsonObject(
                "occurrenceInstantiationCatalog")
                .getAsJsonArray("occurrences").get(0).getAsJsonObject()
                .getAsJsonArray("bindingIds").size());
        int composedInputs = 0;
        for (JsonElement actionElement : task.getAsJsonArray(
                "inputActions")) {
            JsonObject action = actionElement.getAsJsonObject();
            if (action.has("intraRegionSourceOutputPort")) {
                composedInputs++;
                assertEquals("EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                        action.get("intraRegionReadFromAuthority")
                                .getAsString());
            }
        }
        assertEquals(2, composedInputs);

        Map<String, JsonObject> conflicting = producerComponents(producer,
                ranked);
        for (JsonObject component : conflicting.values()) {
            JsonArray edges = component.getAsJsonArray("edgeBindings");
            if ("EDGE.P.0".equals(edges.get(0).getAsJsonObject()
                    .get("edgeId").getAsString())) {
                JsonObject conflict = complementaryEdge.deepCopy();
                conflict.addProperty("mappingId", "rpc.conflict");
                edges.add(conflict);
                break;
            }
        }
        try {
            ConcolicScheduler.atomicProducerTasksForTests(ranked,
                    conflicting);
            fail("expected conflicting edge binding field to fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "conflicting edge binding EDGE.P.0 field mappingId"));
        }

        Map<String, Object> splitPath = singletonGoalProducerPlan(
                targetInstance, targetPorts, true);
        RuntimeWorkflowDiscovery.RankedWorkflow separated =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        GSON.toJsonTree(splitPath).getAsJsonObject(),
                        GSON.toJsonTree(targetPlanWithInputs(
                                targetInstance, targetPorts))
                                .getAsJsonObject()));
        assertEquals(3, separated.scheduledTaskCount());
        assertEquals(2, ConcolicScheduler.atomicProducerTasksForTests(
                separated, producerComponents(splitPath, separated)).size());
    }

    @Test
    @SuppressWarnings("unchecked")
    public void scheduleIndexBindsIdentitiesAndRejectsMissingProducerOccurrence()
            throws Exception {
        String targetInstance = "REGION.T@test#call9";
        Map<String, Object> producer = leafProducerPlan("REGION.P", 3,
                targetInstance, "REGION.T.in.value");
        Map<String, Object> target = targetPlanWithInput(targetInstance);
        RuntimeWorkflowDiscovery.RankedWorkflow ranked =
                RuntimeWorkflowDiscovery.rankedWorkflow(Arrays.asList(
                        GSON.toJsonTree(producer).getAsJsonObject(),
                        GSON.toJsonTree(target).getAsJsonObject()));

        Map<String, Object> targetTask = targetTask("TASK.TARGET",
                "REGION.T", targetInstance, "GOAL.TARGET");
        Map<String, Object> targetCatalog = (Map<String, Object>)
                targetTask.get("occurrenceInstantiationCatalog");
        ((Map<String, Object>) ((List<Map<String, Object>>)
                targetCatalog.get("occurrences")).get(0)).put(
                "rootCallId", 9);

        RuntimeWorkflowDiscovery.Selection producerSelection =
                ranked.selections().get(1);
        Map<String, Object> selectedProducerTask = producerTask(producer,
                producerSelection.producerProjection.json(),
                "REGION.P@test#call3", 3);
        JsonObject regionIdentity = new JsonObject();
        regionIdentity.addProperty("sha256", "region-plan-hash");
        JsonObject taskIdentity = new JsonObject();
        taskIdentity.addProperty("sha256", "task-plan-hash");
        JsonObject index = ranked.scheduleIndex(Arrays.asList(
                        GSON.toJsonTree(targetTask).getAsJsonObject(),
                        GSON.toJsonTree(selectedProducerTask)
                                .getAsJsonObject()),
                regionIdentity, taskIdentity);
        assertEquals("RUNTIME_TARGET_FIRST_SCHEDULE_INDEX",
                index.get("kind").getAsString());
        assertEquals("region-plan-hash", index.getAsJsonObject(
                "regionPlan").get("sha256").getAsString());
        assertEquals("task-plan-hash", index.getAsJsonObject(
                "executionTaskPlan").get("sha256").getAsString());
        assertEquals("TASK.TARGET", index.getAsJsonObject("target")
                .get("taskId").getAsString());
        assertEquals("TASK.PRODUCER", index.getAsJsonArray("producers")
                .get(0).getAsJsonObject().get("taskId").getAsString());

        Map<String, Object> tamperedProducerTask = producerTask(producer,
                producerSelection.producerProjection.json(),
                "REGION.P@test#call3", 3);
        Map<String, Object> tamperedCatalog = (Map<String, Object>)
                tamperedProducerTask.get("occurrenceInstantiationCatalog");
        Map<String, Object> tamperedOccurrence =
                ((List<Map<String, Object>>) tamperedCatalog.get(
                        "occurrences")).get(0);
        ((List<Map<String, Object>>) tamperedOccurrence.get("outputPortMap"))
                .get(0).put("exactPort", "REGION.P.out.tampered");
        try {
            ranked.scheduleIndex(Arrays.asList(
                            GSON.toJsonTree(targetTask).getAsJsonObject(),
                            GSON.toJsonTree(tamperedProducerTask)
                                    .getAsJsonObject()),
                    new JsonObject(), new JsonObject());
            fail("selected producer occurrence port map must be exact");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "port/binding map does not match selected runtime evidence"));
        }

        Map<String, Object> producerTask = producerTask(producer,
                producerSelection.producerProjection.json(),
                "REGION.P@test#call4", 4);
        List<JsonObject> tasks = Arrays.asList(
                GSON.toJsonTree(targetTask).getAsJsonObject(),
                GSON.toJsonTree(producerTask).getAsJsonObject());

        try {
            ranked.scheduleIndex(tasks, new JsonObject(),
                    new JsonObject());
            fail("selected exact producer occurrence must be catalogued");
        } catch (IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "instance=REGION.P@test#call3"));
        }
    }

    @Test
    public void causalDiscoveryFollowsValuesButNotStructureCarriers() {
        JsonObject protocol = new JsonObject();
        protocol.addProperty("sourceKind", "PROTOCOL_INPUT");
        protocol.addProperty("dependencyRole", "VALUE_FRONTIER");
        assertTrue(RuntimeWorkflowDiscovery.causalAction(protocol));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("dependencyRole",
                "CONCRETE_STRUCTURE_CARRIER");
        assertTrue(!RuntimeWorkflowDiscovery.causalAction(carrier));
        JsonObject responseCarrier = carrier.deepCopy();
        responseCarrier.addProperty("sourceKind", "PROTOCOL_INPUT");
        responseCarrier.addProperty("protocolDirection", "RESPONSE");
        responseCarrier.addProperty("authority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        responseCarrier.addProperty("mappingId", "rpc.keys.response");
        assertTrue(RuntimeWorkflowDiscovery.causalAction(responseCarrier));
        try {
            RuntimeWorkflowDiscovery.causalAction(new JsonObject());
            fail("missing dependency role must fail closed");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("dependencyRole"));
        }
    }

    @Test
    public void structureCarrierStaysInTargetButDoesNotDemandProducer()
            throws Exception {
        String targetInstance = "REGION.T@test#call2";
        Map<String, Object> target = targetPlanWithInput(targetInstance,
                "CONCRETE_STRUCTURE_CARRIER");
        @SuppressWarnings("unchecked")
        Map<String, Object> targetGoal = ((List<Map<String, Object>>)
                target.get("closureGoals")).get(0);
        targetGoal.put("symbolize", Arrays.asList(
                ((List<?>) targetGoal.get("symbolize")).get(0),
                object("portId", "REGION.T.in.scalar",
                        "symbol", "REGION.T.in.scalar",
                        "cell", "<T: int scalar>",
                        "javaType", "int",
                        "location", "HEAP_OBJECT_FIELD",
                        "sourceKind", "FIELD_READ",
                        "dependencyRole", "VALUE_FRONTIER")));
        File plans = writePlans("carrier-producer.jsonl",
                readyCarrierProducerPlan(targetInstance),
                leafProducerPlan("REGION.S", 3, targetInstance,
                        "REGION.T.in.scalar"),
                target);

        String discovery = run(plans, "discover");

        assertTrue(discovery.contains("\tREGION.S\t"));
        assertTrue(!discovery.contains("\tREGION.P\t"));
        assertTrue(discovery.contains("TARGET\t"));
        assertTrue(String.valueOf(targetGoal.get("symbolize"))
                .contains("REGION.T.in.value"));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void onlyTrustedResponseCarrierExtendsProducerClosure()
            throws Exception {
        String targetInstance = "REGION.T@test#call2";
        String producerInstance = "REGION.P@test#call1";
        Map<String, Object> ordinary = readyCarrierProducerPlan(
                targetInstance);
        Map<String, Object> upstream = leafProducerPlan("REGION.N", 3,
                producerInstance, "REGION.P.in.registry");
        Map<String, Object> target = targetPlanWithInput(targetInstance,
                "VALUE_FRONTIER");
        File ordinaryPlans = writePlans("ordinary-conduit.jsonl",
                ordinary, upstream, target);

        String ordinaryDiscovery = run(ordinaryPlans, "discover");
        assertTrue(ordinaryDiscovery.contains("\tREGION.P\t"));
        assertTrue(!ordinaryDiscovery.contains("\tREGION.N\t"));

        Map<String, Object> trusted = readyCarrierProducerPlan(
                targetInstance);
        Map<String, Object> producerGoal = ((List<Map<String, Object>>)
                trusted.get("closureGoals")).get(0);
        Map<String, Object> response = ((List<Map<String, Object>>)
                producerGoal.get("symbolize")).get(0);
        response.put("sourceKind", "PROTOCOL_INPUT");
        response.put("protocolDirection", "RESPONSE");
        response.put("authority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        response.put("mappingId", "rpc.keys.response");
        File trustedPlans = writePlans("trusted-conduit.jsonl",
                trusted, leafProducerPlan("REGION.N", 3,
                        producerInstance, "REGION.P.in.registry"),
                targetPlanWithInput(targetInstance, "VALUE_FRONTIER"));

        String trustedDiscovery = run(trustedPlans, "discover");
        assertTrue(trustedDiscovery.contains("\tREGION.P\t"));
        assertTrue(trustedDiscovery.contains("\tREGION.N\t"));
    }

    @Test
    public void exactTrustedRpcProjectionExtendsConcreteCarrier()
            throws Exception {
        String target = "REGION.T@test#call2";
        Map<String, Object> projected = projectedLeafProducerPlan(
                "REGION.N", 3, "REGION.P@test#call1",
                "REGION.P.in.registry", true);
        File plans = writePlans("projected-carrier.jsonl",
                readyCarrierProducerPlan(target), projected,
                targetPlanWithInput(target));

        String discovery = run(plans, "discover");

        assertTrue(discovery.contains("\tREGION.P\t"));
        assertTrue(discovery.contains("\tREGION.N\t"));
    }

    @Test
    public void untrustedRpcProjectionDoesNotExtendConcreteCarrier()
            throws Exception {
        String target = "REGION.T@test#call2";
        Map<String, Object> untrusted = projectedLeafProducerPlan(
                "REGION.N", 3, "REGION.P@test#call1",
                "REGION.P.in.registry", false);
        File plans = writePlans("untrusted-projected-carrier.jsonl",
                readyCarrierProducerPlan(target), untrusted,
                targetPlanWithInput(target));

        String discovery = run(plans, "discover");

        assertTrue(discovery.contains("\tREGION.P\t"));
        assertTrue(!discovery.contains("\tREGION.N\t"));
    }

    @Test
    public void boundedContainersAndScalarLeavesDemandProducers()
            throws Exception {
        String targetInstance = "REGION.T@test#call9";
        List<String> ports = Arrays.asList("REGION.T.in.map",
                "REGION.T.in.array", "REGION.T.in.scalar");
        Map<String, Object> target = targetPlanWithInputs(targetInstance,
                ports);
        @SuppressWarnings("unchecked")
        Map<String, Object> goal = ((List<Map<String, Object>>)
                target.get("closureGoals")).get(0);
        @SuppressWarnings("unchecked")
        List<Map<String, Object>> actions = (List<Map<String, Object>>)
                goal.get("symbolize");
        actions.get(0).put("javaType", "java.util.Map");
        actions.get(0).put("symbolicDemand",
                "BOUNDED_CONTAINER_STATE");
        actions.get(1).put("javaType", "example.Key[]");
        actions.get(1).put("symbolicDemand",
                "BOUNDED_CONTAINER_STATE");

        File plans = writePlans("value-frontier-producers.jsonl",
                leafProducerPlan("REGION.M", 1, targetInstance,
                        ports.get(0)),
                leafProducerPlan("REGION.A", 2, targetInstance,
                        ports.get(1)),
                leafProducerPlan("REGION.S", 3, targetInstance,
                        ports.get(2)), target);

        String discovery = run(plans, "discover");
        assertTrue(discovery.contains("\tREGION.M\t"));
        assertTrue(discovery.contains("\tREGION.A\t"));
        assertTrue(discovery.contains("\tREGION.S\t"));
    }

    @Test
    public void listsAllTargetsAndRequiresSelectionForTargetCommands()
            throws Exception {
        File plans = writePlans("multi.jsonl",
                targetPlan("REGION.1", "REGION.1@test#call1", "GOAL.1"),
                targetPlan("REGION.2", "REGION.2@test#call2",
                        "GOAL.2A", "GOAL.2B"));

        String bindings = run(plans, "target-bindings");
        assertEquals(3, bindings.trim().split("\\R").length);
        assertTrue(bindings.contains("REGION.1@test#call1\tGOAL.1"));
        assertTrue(bindings.contains("REGION.2@test#call2\tGOAL.2A"));
        assertTrue(bindings.contains("REGION.2@test#call2\tGOAL.2B"));

        assertAmbiguous(plans, "target-binding");
        assertAmbiguous(plans, "producer-demands");

        String selected = run(plans, "target-binding",
                "--target-instance", "REGION.1@test#call1");
        assertTrue(selected.contains("\tREGION.1\t"
                + "REGION.1@test#call1\tGOAL.1"));

        try {
            run(plans, "target-binding", "--target-instance",
                    "REGION.2@test#call2");
            fail("instance with two target goals must remain ambiguous");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("exactly one"));
        }

        selected = run(plans, "target-binding",
                "--target-instance", "REGION.2@test#call2",
                "--target-goal", "GOAL.2B");
        assertTrue(selected.contains("\tREGION.2\t"
                + "REGION.2@test#call2\tGOAL.2B"));
    }

    @Test
    public void selectorScopesScheduledTargetTask() throws Exception {
        File plans = writePlans("scheduled-plans.jsonl",
                targetPlan("REGION.1", "REGION.1@test#call1", "GOAL.1"),
                targetPlan("REGION.2", "REGION.2@test#call2",
                        "GOAL.2A", "GOAL.2B"));
        File tasks = writeRows("tasks.jsonl", Arrays.asList(
                targetTask("TASK.2A", "REGION.2",
                        "REGION.2@test#call2", "GOAL.2A"),
                targetTask("TASK.2B", "REGION.2",
                        "REGION.2@test#call2", "GOAL.2B")));

        String task = run(plans, "scheduled-target-task",
                "--target-instance", "REGION.2@test#call2",
                "--target-goal", "GOAL.2B",
                "--task-plan", tasks.getPath());
        assertEquals("TASK.2B", task.trim());

        assertAmbiguous(plans, "scheduled-target-task",
                "--task-plan", tasks.getPath());
    }

    @Test
    public void singleTargetKeepsOldTargetBindingBehavior() throws Exception {
        File plans = writePlans("single.jsonl",
                targetPlan("REGION.1", "REGION.1@test#call1", "GOAL.1"));
        String binding = run(plans, "target-binding");
        assertTrue(binding.contains("\tREGION.1\t"
                + "REGION.1@test#call1\tGOAL.1"));
    }

    @Test
    public void logicalTargetExposesExactFrontierButUsesOneTask()
            throws Exception {
        String first = "REGION.1@test#call1";
        String second = "REGION.1@test#call2";
        File plans = writePlans("logical-target.jsonl",
                logicalTargetPlan(first, second));
        File tasks = writeRows("logical-task.jsonl",
                Collections.singletonList(logicalTargetTask(first, second,
                        true)));

        String bindings = run(plans, "target-bindings");
        assertEquals(2, bindings.trim().split("\\R").length);
        assertTrue(bindings.contains("\tREGION.1\t" + first
                + "\tGOAL.LOGICAL"));
        assertTrue(bindings.contains("\tREGION.1\t" + second
                + "\tGOAL.LOGICAL"));
        String task = run(plans, "scheduled-target-task",
                "--target-instance", second,
                "--task-plan", tasks.getPath());
        assertEquals("TASK.LOGICAL", task.trim());
    }

    @Test
    public void selectedTargetMissingFromTaskCatalogFailsClosed()
            throws Exception {
        String first = "REGION.1@test#call1";
        String second = "REGION.1@test#call2";
        File plans = writePlans("logical-target-missing.jsonl",
                logicalTargetPlan(first, second));
        File tasks = writeRows("logical-task-missing.jsonl",
                Collections.singletonList(logicalTargetTask(first, second,
                        false)));

        try {
            run(plans, "scheduled-target-task",
                    "--target-instance", second,
                    "--task-plan", tasks.getPath());
            fail("selected exact target occurrence must be catalogued");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "no exact occurrence"));
        }
    }

    @Test
    public void relevantPendingProducerFailsClosedWithoutDecodingCatalog()
            throws Exception {
        String targetInstance = "REGION.T@test#call2";
        File plans = writePlans("pending-producer.jsonl",
                pendingLogicalProducerPlan(targetInstance),
                targetPlanWithInput(targetInstance));

        try {
            run(plans, "producer-demands");
            fail("pending producer must not become an executable demand");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "blocked exact producer closure"));
            assertTrue(expected.getMessage().contains(
                    "OUTPUT_CLOSURE_PENDING"));
            assertTrue(!expected.getMessage().contains(
                    "invalid logical producer occurrence catalog"));
        }
    }

    @Test
    public void unrelatedPendingProducerRemainsDiagnosticNoise()
            throws Exception {
        String target = "REGION.T@test#call2";
        File plans = writePlans("unrelated-pending.jsonl",
                pendingLogicalProducerPlan(
                        "REGION.UNRELATED@test#call99"),
                leafProducerPlan("REGION.GOOD", 3, target,
                        "REGION.T.in.value"),
                targetPlanWithInput(target));

        String campaigns = run(plans, "producer-demands");

        assertEquals(1, campaigns.trim().split("\\R").length);
        assertTrue(campaigns.contains("REGION.GOOD"));
    }

    @Test
    public void readyAlternativeDischargesEndpointWithPendingAlternative()
            throws Exception {
        String target = "REGION.T@test#call2";
        File plans = writePlans("ready-and-pending.jsonl",
                pendingLogicalProducerPlan(target),
                leafProducerPlan("REGION.GOOD", 3, target,
                        "REGION.T.in.value"),
                targetPlanWithInput(target));

        String campaigns = run(plans, "producer-demands");

        assertEquals(1, campaigns.trim().split("\\R").length);
        assertTrue(campaigns.contains("REGION.GOOD"));
    }

    @Test
    public void selectsOneReadyAlternativeForOneExactInput()
            throws Exception {
        String target = "REGION.T@test#call20";
        List<Map<String, Object>> rows = Arrays.asList(
                leafProducerPlan("REGION.B", 4, target,
                        "REGION.T.in.value"),
                targetPlanWithInput(target),
                leafProducerPlan("REGION.A", 3, target,
                        "REGION.T.in.value"));
        File forward = writeRows("alternative-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("alternative-backward.jsonl", reversed);

        String first = run(forward, "producer-demands");
        String second = run(backward, "producer-demands");

        assertEquals(first, second);
        assertEquals(1, first.trim().split("\\R").length);
        assertTrue(first.contains("REGION.A"));
        assertTrue(!first.contains("REGION.B"));
    }

    @Test
    public void oneMultiOutputRelationDischargesTwoExactInputs()
            throws Exception {
        String target = "REGION.T@test#call20";
        List<String> inputs = Arrays.asList("REGION.T.in.left",
                "REGION.T.in.right");
        File plans = writePlans("multi-output.jsonl",
                multiOutputProducerPlan("REGION.P", 3, target, inputs),
                targetPlanWithInputs(target, inputs));

        String campaigns = run(plans, "producer-demands");

        assertEquals(1, campaigns.trim().split("\\R").length);
        assertTrue(campaigns.contains("REGION.P"));
        JsonObject projection = GSON.fromJson(run(plans,
                "producer-projection", "--campaign", campaigns.trim()),
                JsonObject.class);
        assertEquals(2, projection.getAsJsonArray("outputPorts").size());
        assertEquals(2, projection.getAsJsonArray("edgeIds").size());
    }

    @Test
    public void producerBindingLedgerDoesNotTurnIncomingEdgeIntoOutput()
            throws Exception {
        String target = "REGION.T@test#call20";
        String middleInput = "REGION.MID.in.value";
        Map<String, Object> upstream = leafProducerPlan(
                "REGION.UP", 2, "REGION.MID@test#call3", middleInput);
        Map<String, Object> middle = producerWithIncomingDependencyPlan(
                target, middleInput, upstream);
        File plans = writePlans("producer-direction.jsonl", upstream,
                middle, targetPlanWithInput(target));

        String campaigns = run(plans, "producer-demands");

        assertEquals(2, campaigns.trim().split("\\R").length);
        assertTrue(campaigns.contains("REGION.UP"));
        assertTrue(campaigns.contains("REGION.MID"));
    }

    @Test
    public void multiOutputSelectionIgnoresInputAndPlanRowOrder()
            throws Exception {
        String target = "REGION.T@test#call20";
        List<String> forwardInputs = Arrays.asList("REGION.T.in.left",
                "REGION.T.in.right");
        List<String> backwardInputs = Arrays.asList("REGION.T.in.right",
                "REGION.T.in.left");
        List<Map<String, Object>> rows = Arrays.asList(
                leafProducerPlan("REGION.LEFT", 4, target,
                        "REGION.T.in.left"),
                targetPlanWithInputs(target, forwardInputs),
                multiOutputProducerPlan("REGION.BOTH", 3, target,
                        forwardInputs),
                leafProducerPlan("REGION.RIGHT", 5, target,
                        "REGION.T.in.right"));
        File forward = writeRows("multi-order-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>();
        reversed.add(rows.get(3));
        reversed.add(multiOutputProducerPlan("REGION.BOTH", 3, target,
                backwardInputs));
        reversed.add(targetPlanWithInputs(target, backwardInputs));
        reversed.add(rows.get(0));
        File backward = writeRows("multi-order-backward.jsonl", reversed);

        String first = run(forward, "producer-demands");
        String second = run(backward, "producer-demands");

        assertEquals(first, second);
        assertEquals(1, first.trim().split("\\R").length);
        assertTrue(first.contains("REGION.BOTH"));
    }

    @Test
    public void rankingPlacesCompleteClosureAheadOfBlockedExactProducer()
            throws Exception {
        String blocked = "REGION.T@test#call2";
        String complete = "REGION.T@test#call9";
        File plans = writePlans("rank-blocked.jsonl",
                targetPlanWithInput(blocked),
                pendingLogicalProducerPlan(blocked),
                targetPlanWithInput(complete),
                leafProducerPlan("REGION.GOOD", 10, complete,
                        "REGION.T.in.value"));

        String bindings = run(plans, "target-bindings");

        assertTrue(bindings.split("\\R")[0].contains(
                complete + "\tGOAL.TARGET"));
        try {
            run(plans, "producer-demands", "--target-instance", blocked);
            fail("explicitly selected blocked closure must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "blocked exact producer closure"));
            assertTrue(expected.getMessage().contains(
                    "GOAL.PENDING.LOGICAL"));
        }
    }

    @Test
    public void targetBindingsPreferLowerResidualFreedomDeterministically()
            throws Exception {
        String residual = "REGION.T@test#call1";
        String closed = "REGION.T@test#call9";
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInputs(residual, Arrays.asList(
                        "REGION.T.in.value", "REGION.T.in.unbound")),
                leafProducerPlan("REGION.P1", 2, residual,
                        "REGION.T.in.value"),
                targetPlanWithInputs(closed, Arrays.asList(
                        "REGION.T.in.value", "REGION.T.in.other")),
                leafProducerPlan("REGION.P2", 10, closed,
                        "REGION.T.in.value"),
                leafProducerPlan("REGION.P3", 11, closed,
                        "REGION.T.in.other"));
        File forward = writeRows("rank-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-backward.jsonl", reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                closed + "\tGOAL.TARGET"));
    }

    @Test
    public void targetBindingsPreferObservedSemanticGuardsInSelectedSlice()
            throws Exception {
        String noisy = "REGION.T@test#call1";
        String semantic = "REGION.T@test#call9";
        Map<String, Object> noisyProducer = leafProducerPlan(
                "REGION.NOISY", 2, noisy, "REGION.T.in.value");
        markSelectedSemanticGuardEvidence(noisyProducer, false);
        Map<String, Object> semanticProducer = leafProducerPlan(
                "REGION.SEMANTIC", 10, semantic, "REGION.T.in.value");
        markSelectedSemanticGuardEvidence(semanticProducer, true);
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInput(noisy), noisyProducer,
                targetPlanWithInput(semantic), semanticProducer);
        File forward = writeRows("rank-semantic-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-semantic-backward.jsonl", reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                semantic + "\tGOAL.TARGET"));
    }

    @Test
    public void equalResidualTargetsPreferLowerReplayCostDeterministically()
            throws Exception {
        String small = "REGION.T@test#call9";
        String large = "REGION.T@test#call1";
        Map<String, Object> upstream = leafProducerPlan(
                "REGION.UP", 2, "REGION.MID@test#call3",
                "REGION.MID.in.value");
        Map<String, Object> middle = producerWithIncomingDependencyPlan(
                large, "REGION.MID.in.value", upstream);
        List<Map<String, Object>> rows = Arrays.asList(
                protocolTargetPlanWithInput(large),
                upstream,
                middle,
                protocolTargetPlanWithInput(small),
                leafProducerPlan("REGION.ONE", 10, small,
                        "REGION.T.in.value"));
        File forward = writeRows("rank-cost-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-cost-backward.jsonl", reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                small + "\tGOAL.TARGET"));
    }

    @Test
    public void provedStatefulClosureBeatsCheaperStatelessClosure()
            throws Exception {
        String stateless = "REGION.T@test#call1";
        String stateful = "REGION.T@test#call9";
        Map<String, Object> state = provedBoundedStateProducerPlan(
                "REGION.STATE", 3, "REGION.MID@test#call3",
                "REGION.MID.in.value");
        Map<String, Object> presentation =
                producerWithIncomingDependencyPlan(stateful,
                        "REGION.MID.in.value", state);
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInput(stateless),
                leafProducerPlan("REGION.CHEAP", 2, stateless,
                        "REGION.T.in.value"),
                targetPlanWithInput(stateful), state, presentation);
        File forward = writeRows("rank-state-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-state-backward.jsonl", reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                stateful + "\tGOAL.TARGET"));
        String demands = run(forward, "producer-demands",
                "--target-instance", stateful);
        assertEquals(2, demands.trim().split("\\R").length);
        assertTrue(demands.contains("REGION.STATE"));
        assertTrue(demands.contains("REGION.MID"));
    }

    @Test
    public void exactSameLogicalHeapHandoffBeatsStatelessClosure()
            throws Exception {
        String stateless = "REGION.T@test#call1";
        String stateful = "REGION.T@test#call9";
        String later = "REGION.STATE@test#call11";
        String cachedInput = "REGION.STATE.in.cached";
        Map<String, Object> earlier = leafProducerPlan(
                "REGION.STATE", 10, later, cachedInput);
        Map<String, Object> presentation =
                producerWithIncomingDependencyPlan("REGION.STATE", 11,
                        stateful, "REGION.T.in.value", cachedInput,
                        earlier);
        markExactHeapStateHandoff(earlier, presentation,
                "REGION.STATE@owner7", "REGION.STATE@owner7");
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInput(stateless),
                leafProducerPlan("REGION.CHEAP", 2, stateless,
                        "REGION.T.in.value"),
                targetPlanWithInput(stateful), earlier, presentation);
        File forward = writeRows("rank-heap-state-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-heap-state-backward.jsonl",
                reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                stateful + "\tGOAL.TARGET"));
    }

    @Test
    public void exactHeapHandoffAcrossLogicalProducersDoesNotBiasRank()
            throws Exception {
        String stateless = "REGION.T@test#call1";
        String unrelated = "REGION.T@test#call9";
        String later = "REGION.STATE@test#call11";
        String cachedInput = "REGION.STATE.in.cached";
        Map<String, Object> earlier = leafProducerPlan(
                "REGION.STATE", 10, later, cachedInput);
        Map<String, Object> presentation =
                producerWithIncomingDependencyPlan("REGION.STATE", 11,
                        unrelated, "REGION.T.in.value", cachedInput,
                        earlier);
        markExactHeapStateHandoff(earlier, presentation,
                "REGION.STATE@owner7", "REGION.STATE@owner8");
        File plans = writePlans("rank-unrelated-heap-state.jsonl",
                targetPlanWithInput(stateless),
                leafProducerPlan("REGION.CHEAP", 2, stateless,
                        "REGION.T.in.value"),
                targetPlanWithInput(unrelated), earlier, presentation);

        String bindings = run(plans, "target-bindings");

        assertTrue(bindings.split("\\R")[0].contains(
                stateless + "\tGOAL.TARGET"));
    }

    @Test
    public void stateEvidenceMustCoverEachFatalOperandBeforeCostWins()
            throws Exception {
        String oneBacked = "REGION.T@test#call1";
        String twoBacked = "REGION.T@test#call9";

        String oneMiddle = "REGION.ONE.MID@test#call3";
        String oneInput = "REGION.ONE.MID.in.state";
        Map<String, Object> oneState = provedBoundedStateProducerPlan(
                "REGION.ONE.STATE", 2, oneMiddle, oneInput);
        Map<String, Object> onePresentation =
                producerWithIncomingDependencyPlan("REGION.ONE.MID", 3,
                        oneBacked, "REGION.T.in.left", oneInput, oneState);

        String leftMiddle = "REGION.TWO.LEFT@test#call11";
        String leftInput = "REGION.TWO.LEFT.in.state";
        Map<String, Object> leftState = provedBoundedStateProducerPlan(
                "REGION.TWO.LEFT.STATE", 10, leftMiddle, leftInput);
        Map<String, Object> leftPresentation =
                producerWithIncomingDependencyPlan("REGION.TWO.LEFT", 11,
                        twoBacked, "REGION.T.in.left", leftInput,
                        leftState);
        String rightMiddle = "REGION.TWO.RIGHT@test#call13";
        String rightInput = "REGION.TWO.RIGHT.in.state";
        Map<String, Object> rightState = provedBoundedStateProducerPlan(
                "REGION.TWO.RIGHT.STATE", 12, rightMiddle, rightInput);
        Map<String, Object> rightPresentation =
                producerWithIncomingDependencyPlan("REGION.TWO.RIGHT", 13,
                        twoBacked, "REGION.T.in.right", rightInput,
                        rightState);

        List<String> fatalInputs = Arrays.asList("REGION.T.in.left",
                "REGION.T.in.right");
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInputs(oneBacked, fatalInputs), oneState,
                onePresentation, leafProducerPlan("REGION.ONE.PLAIN", 4,
                        oneBacked, "REGION.T.in.right"),
                targetPlanWithInputs(twoBacked, fatalInputs), leftState,
                leftPresentation, rightState, rightPresentation);
        File forward = writeRows("rank-state-coverage-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-state-coverage-backward.jsonl",
                reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                twoBacked + "\tGOAL.TARGET"));
    }

    @Test
    public void targetLocalStateTransitionDoesNotBiasTargetRank()
            throws Exception {
        String directState = "REGION.T@test#call1";
        String cheap = "REGION.T@test#call9";
        Map<String, Object> upstream = leafProducerPlan(
                "REGION.UP", 2, "REGION.MID@test#call3",
                "REGION.MID.in.value");
        Map<String, Object> direct = producerWithIncomingDependencyPlan(
                directState, "REGION.MID.in.value", upstream);
        markProvedBoundedStateTransition(direct);
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInput(directState), upstream, direct,
                targetPlanWithInput(cheap),
                leafProducerPlan("REGION.CHEAP", 10, cheap,
                        "REGION.T.in.value"));
        File forward = writeRows("rank-target-state-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-target-state-backward.jsonl",
                reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                cheap + "\tGOAL.TARGET"));
    }

    @Test
    public void exactProtocolPresentationBeatsCheaperForwardingClosure()
            throws Exception {
        String forwarding = "REGION.T@test#call9";
        String presented = "REGION.T@test#call1";
        Map<String, Object> upstream = leafProducerPlan(
                "REGION.UP", 2, "REGION.MID@test#call3",
                "REGION.MID.in.value");
        Map<String, Object> middle = producerWithIncomingDependencyPlan(
                presented, "REGION.MID.in.value", upstream);
        File plans = writePlans("rank-presentation.jsonl",
                targetPlanWithInput(forwarding),
                leafProducerPlan("REGION.CHEAP", 10, forwarding,
                        "REGION.T.in.value"),
                protocolTargetPlanWithInput(presented),
                upstream, middle);

        String bindings = run(plans, "target-bindings");

        assertTrue(bindings.split("\\R")[0].contains(
                presented + "\tGOAL.TARGET"));
    }

    @Test
    public void unrelatedMalformedReadyProducerDoesNotBlockTargetClosure()
            throws Exception {
        String target = "REGION.T@test#call2";
        File plans = writePlans("unrelated-malformed.jsonl",
                malformedProducerPlan("REGION.BAD", 1,
                        "REGION.UNRELATED@test#call99",
                        "REGION.UNRELATED.in.value"),
                leafProducerPlan("REGION.GOOD", 3, target,
                        "REGION.T.in.value"),
                targetPlanWithInput(target));

        String campaigns = run(plans, "producer-demands");

        assertEquals(1, campaigns.trim().split("\\R").length);
        assertTrue(campaigns.contains("REGION.GOOD"));
    }

    @Test
    public void relevantMalformedReadyProducerStillFailsClosed()
            throws Exception {
        String target = "REGION.T@test#call2";
        File plans = writePlans("relevant-malformed.jsonl",
                malformedProducerPlan("REGION.BAD", 1, target,
                        "REGION.T.in.value"),
                targetPlanWithInput(target));

        try {
            run(plans, "producer-demands");
            fail("a malformed producer on the exact frontier must fail");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "invalid logical producer occurrence catalog"));
        }
    }

    private void assertAmbiguous(File plans, String command,
                                 String... extra) throws Exception {
        try {
            run(plans, command, extra);
            fail(command + " must fail closed for multiple targets");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "multiple target reach closures"));
        }
    }

    private String run(File plans, String command, String... extra)
            throws Exception {
        List<String> args = new ArrayList<>();
        args.add("--region-plan");
        args.add(plans.getPath());
        args.add("--command");
        args.add(command);
        Collections.addAll(args, extra);
        ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        PrintStream prior = System.out;
        try {
            System.setOut(new PrintStream(bytes, true, "UTF-8"));
            RuntimeWorkflowDiscovery.main(args.toArray(new String[0]));
        } finally {
            System.setOut(prior);
        }
        return new String(bytes.toByteArray(), StandardCharsets.UTF_8);
    }

    private File writePlans(String name, Map<String, Object>... rows)
            throws Exception {
        return writeRows(name, Arrays.asList(rows));
    }

    private File writeRows(String name, List<Map<String, Object>> rows)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        List<String> lines = new ArrayList<>();
        for (Map<String, Object> row : rows) {
            lines.add(GSON.toJson(row));
        }
        Files.write(file.toPath(), lines, StandardCharsets.UTF_8);
        return file;
    }

    private static Map<String, Object> targetPlan(String region,
                                                   String instance,
                                                   String... goals) {
        List<Map<String, Object>> closures = new ArrayList<>();
        for (String goal : goals) {
            closures.add(object("goalId", goal,
                    "kind", "TARGET_REACH_CLOSURE",
                    "runtimeDefinitionMethods",
                    Collections.singletonList("<T: void run()>"),
                    "admission", object("state", "READY", "blockers",
                            Collections.emptyList()),
                    "symbolize", Collections.emptyList(),
                    "branches", Collections.emptyList(),
                    "edgeBindings", Collections.emptyList()));
        }
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", region,
                "regionInstanceId", instance,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void run()>", "ordinal", 1),
                "closureGoals", closures);
    }

    private static Map<String, Object> targetTask(String taskId,
                                                   String region,
                                                   String instance,
                                                   String goal) {
        return object("taskId", taskId,
                "goalId", goal,
                "goalKind", "TARGET_REACH_CLOSURE",
                "regionId", region,
                "regionInstanceId", instance,
                "logicalRegionId", instance,
                "summaryReuseKey", instance,
                "inputActions", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "occurrenceInstantiationCatalog", object(
                        "schemaVersion", 1,
                        "kind", "LOGICAL_SUMMARY_OCCURRENCE_CATALOG",
                        "logicalRegionId", instance,
                        "summaryReuseKey", instance,
                        "canonicalRegionInstanceId", instance,
                        "occurrences", Collections.singletonList(object(
                                "regionInstanceId", instance,
                                "inputPortMap", Collections.emptyList(),
                                "outputPortMap", Collections.emptyList(),
                                "bindingIds", Collections.emptyList()))),
                "loopBound", object("schemaVersion", 1,
                        "kind", "CFG_BACKEDGE",
                        "scope", "ALL_EXECUTION_SCOPE_LOOPS",
                        "maxBackedgeTraversals", 8,
                        "onLimit", "CUT_PATH"),
                "admission", object("state", "EXECUTABLE"));
    }

    private static Map<String, Object> singletonGoalProducerPlan(
            String targetInstance, List<String> targetPorts,
            boolean splitLastPath) {
        String region = "REGION.P";
        String instance = region + "@test#call3";
        List<Map<String, Object>> goals = new ArrayList<>();
        for (int index = 0; index < targetPorts.size(); index++) {
            String output = region + ".out." + index;
            String edgeId = "EDGE.P." + index;
            int inputOrdinal = index % 3;
            String input = region + ".in." + inputOrdinal;
            Map<String, Object> action = object(
                    "symbol", input,
                    "portId", input,
                    "cell", "<example.Key: int keyId>",
                    "javaType", "int",
                    "location", "HEAP_OBJECT_FIELD",
                    "sourceKind", "ACCESSOR_RETURN",
                    "dependencyRole", "VALUE_FRONTIER",
                    "bindingMode", "FIELD_ACCESS",
                    "accessFieldSignature", "<example.Key: int keyId>",
                    "declaredFieldSignature",
                    "<example.Key: int keyId>",
                    "fieldReceiverObjectId", 900L + inputOrdinal,
                    "eventSeq", 1000L + inputOrdinal,
                    "rootCallId", 3,
                    "fieldPath", Collections.singletonList("keyId"),
                    "accessSites", Collections.singletonList(
                            "<P: void run()>#u7"),
                    "accessorCallerMethod", "<P: void run()>",
                    "accessorCallUnitIndex", 7,
                    "accessorDeclaredCallee",
                    "<example.Key: int getKeyId()>",
                    "accessorImplementationMethod",
                    "<example.Key: int getKeyId()>",
                    "replayOccurrence", inputOrdinal + 1,
                    "helperActivationBoundedOccurrence", 1,
                    "mode", "SYMBOLIC");
            Map<String, Object> edge = object(
                    "schemaVersion", 3,
                    "edgeId", edgeId,
                    "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                    "correlationAuthority",
                    "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                    "mappingId", "rpc.p." + index,
                    "fromRegionInstance", instance,
                    "fromOutputPort", output,
                    "toRegionInstance", targetInstance,
                    "toInputPort", targetPorts.get(index),
                    "callerSiteEventSeq", 30 + index * 3,
                    "sendEventSeq", 31 + index * 3,
                    "receiveEventSeq", 32 + index * 3);
            String captureSite = "CALL_ARGUMENT:<P: void run()>#u"
                    + (index % 2 == 0 ? 10 : 20)
                    + ":<P: void sink(int)>#arg0";
            int outputOccurrence = index % 2 == 0
                    ? index / 2 + 1 : (index + 1) / 2;
            Map<String, Object> capture = object(
                    "captureBindingId", "CAPTURE.P." + index,
                    "captureKind", "CALL_ARGUMENT",
                    "outputPort", output,
                    "outputCell", "<example.Key: int keyId>",
                    "javaType", "int",
                    "definitionMethod", "<P: void run()>",
                    "definitionUnitIndex", index % 2 == 0 ? 10 : 20,
                    "declaredCallee", "<P: void sink(int)>",
                    "argumentIndex", 0,
                    "outputSiteId", captureSite,
                    "outputOccurrence", outputOccurrence,
                    "replayOccurrence", outputOccurrence,
                    "occurrenceScope", "REGION_ACTIVATION");
            Map<String, Object> member = object(
                    "output", object("portId", output,
                            "cell", "<example.Key: int keyId>",
                            "kind", "REGION_OUTPUT",
                            "javaTypeDescriptor", "I",
                            "outputSiteId", captureSite,
                            "outputOccurrence", outputOccurrence,
                            "replayOccurrence", outputOccurrence),
                    "slice", object("outputPort", output,
                            "outputCell", "<example.Key: int keyId>",
                            "inputPorts", Collections.singletonList(input),
                            "sites", Collections.emptyList(),
                            "staticSites", Collections.emptyList(),
                            "methods", Collections.singletonList(
                                    "<P: void run()>"),
                            "causalEdgeIds", Collections.singletonList(
                                    edgeId),
                            "selectedRuntimeEventSeq",
                            index % 2 == 0
                                    ? 100L * (index / 2 + 1)
                                    : 100L * ((index + 1) / 2) + 10L,
                            "selectedFieldReceiverObjectId",
                            index == 0 ? 901L : index == 1 ? 902L : 0L,
                            "captureBindings",
                            Collections.singletonList(capture),
                            "captureBindingIssues",
                            Collections.emptyList()));
            goals.add(object(
                    "goalId", "GOAL.P." + index,
                    "kind", "OUTPUT_RELATION_CLOSURE",
                    "pathSeedKey", splitLastPath
                            && index == targetPorts.size() - 1
                            ? "PATH.OTHER" : "PATH.SHARED",
                    "runtimeDefinitionMethods",
                    Collections.singletonList("<P: void run()>"),
                    "admission", object("state", "READY", "blockers",
                            Collections.emptyList()),
                    "symbolize", Collections.singletonList(action),
                    "branches", Collections.emptyList(),
                    "edgeBindings", Collections.singletonList(edge),
                    "outputClosure", object(
                            "schemaVersion", 2,
                            "kind", "OUTPUT_CLOSURE_CONTRACT",
                            "producer", object("regionId", region,
                                    "regionInstanceId", instance,
                                    "rootCallId", 3),
                            "causalEdges", Collections.singletonList(edge),
                            "members", Collections.singletonList(member))));
        }
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", region,
                "regionInstanceId", instance,
                "rootCallId", 3,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<P: void run()>", "ordinal", 1),
                "closureGoals", goals);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, JsonObject> producerComponents(
            Map<String, Object> producerPlan,
            RuntimeWorkflowDiscovery.RankedWorkflow ranked) {
        Map<String, Map<String, Object>> goals = new LinkedHashMap<>();
        for (Map<String, Object> goal : (List<Map<String, Object>>)
                producerPlan.get("closureGoals")) {
            goals.put((String) goal.get("goalId"), goal);
        }
        String instance = (String) producerPlan.get("regionInstanceId");
        String canonicalInstance = "REGION.P@test#call2";
        String logical = (String) producerPlan.getOrDefault(
                "logicalRegionId", instance);
        Map<String, JsonObject> result = new LinkedHashMap<>();
        int ordinal = 0;
        for (RuntimeWorkflowDiscovery.Selection selection
                : ranked.selections()) {
            if (selection.producerProjection == null) continue;
            Map<String, Object> goal = goals.get(selection.goalId);
            Map<String, Object> closure = (Map<String, Object>)
                    goal.get("outputClosure");
            Map<String, Object> member = ((List<Map<String, Object>>)
                    closure.get("members")).get(0);
            String output = (String) ((Map<String, Object>)
                    member.get("output")).get("portId");
            Map<String, Object> edge = ((List<Map<String, Object>>)
                    goal.get("edgeBindings")).get(0);
            String edgeId = (String) edge.get("edgeId");
            Map<String, Object> input = ((List<Map<String, Object>>)
                    goal.get("symbolize")).get(0);
            String inputPort = (String) input.get("symbol");
            JsonObject taskClosure = GSON.toJsonTree(closure)
                    .getAsJsonObject();
            JsonObject taskProducer = taskClosure.getAsJsonObject(
                    "producer");
            taskProducer.addProperty("regionInstanceId",
                    canonicalInstance);
            taskProducer.addProperty("rootCallId", 2);
            JsonObject task = GSON.toJsonTree(object(
                    "taskId", "TASK.COMPONENT." + ordinal++,
                    "goalId", selection.goalId,
                    "goalKind", "OUTPUT_RELATION_CLOSURE",
                    "regionId", selection.regionId,
                    "regionInstanceId", canonicalInstance,
                    "logicalRegionId", logical,
                    "summaryReuseKey", logical,
                    "rootCallId", 2,
                    "laneId", "lane.1",
                    "rootSelector", producerPlan.get("rootSelector"),
                    "pathSeedKey",
                    edu.uva.liftlab.graphchecker.contract.BoundedPathSeed
                            .key(new com.google.gson.JsonArray()),
                    "inputActions", Collections.singletonList(input),
                    "branches", Collections.emptyList(),
                    "edgeBindings", Collections.singletonList(edge),
                    "outputClosure", taskClosure,
                    "producerProjection",
                    selection.producerProjection.json(),
                    "occurrenceInstantiationCatalog", object(
                            "schemaVersion", 1,
                            "kind", "LOGICAL_SUMMARY_OCCURRENCE_CATALOG",
                            "logicalRegionId", logical,
                            "summaryReuseKey", logical,
                            "canonicalRegionInstanceId", canonicalInstance,
                            "canonicalRootCallId", 2,
                            "occurrences", Arrays.asList(object(
                                    "regionInstanceId", instance,
                                    "rootCallId", 3,
                                    "inputPortMap",
                                    Collections.singletonList(object(
                                            "canonicalPort", inputPort,
                                            "exactPort", inputPort)),
                                    "outputPortMap",
                                    Collections.singletonList(object(
                                            "canonicalPort", output,
                                            "exactPort", output)),
                                    "bindingIds",
                                    Collections.singletonList(edgeId)),
                                    object("regionInstanceId",
                                            canonicalInstance,
                                            "rootCallId", 2,
                                            "inputPortMap",
                                            Collections.emptyList(),
                                            "outputPortMap",
                                            Collections.emptyList(),
                                            "bindingIds",
                                            Collections.emptyList()))),
                    "loopBound", object("schemaVersion", 1,
                            "kind", "CFG_BACKEDGE",
                            "scope", "ALL_EXECUTION_SCOPE_LOOPS",
                            "maxBackedgeTraversals", 8,
                            "onLimit", "CUT_PATH"),
                    "admission", object("state", "EXECUTABLE")))
                    .getAsJsonObject();
            result.put(selection.campaignId, task);
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> producerTask(
            Map<String, Object> producerPlan, JsonObject projection,
            String catalogInstance, long catalogRootCallId) {
        String region = (String) producerPlan.get("regionId");
        String canonicalInstance = (String) producerPlan.get(
                "regionInstanceId");
        String logical = (String) producerPlan.getOrDefault(
                "logicalRegionId", canonicalInstance);
        Map<String, Object> goal = ((List<Map<String, Object>>)
                producerPlan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>)
                goal.get("outputClosure");
        Map<String, Object> member = ((List<Map<String, Object>>)
                closure.get("members")).get(0);
        String output = (String) ((Map<String, Object>)
                member.get("output")).get("portId");
        String edgeId = (String) ((List<Map<String, Object>>)
                goal.get("edgeBindings")).get(0).get("edgeId");
        return object("taskId", "TASK.PRODUCER",
                "goalId", goal.get("goalId"),
                "goalKind", "OUTPUT_RELATION_CLOSURE",
                "regionId", region,
                "regionInstanceId", canonicalInstance,
                "logicalRegionId", logical,
                "summaryReuseKey", logical,
                "rootCallId", producerPlan.get("rootCallId"),
                "inputActions", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "edgeBindings", goal.get("edgeBindings"),
                "outputClosure", closure,
                "producerProjection", projection.deepCopy(),
                "occurrenceInstantiationCatalog", object(
                        "schemaVersion", 1,
                        "kind", "LOGICAL_SUMMARY_OCCURRENCE_CATALOG",
                        "logicalRegionId", logical,
                        "summaryReuseKey", logical,
                        "canonicalRegionInstanceId", canonicalInstance,
                        "occurrences", Collections.singletonList(object(
                                "regionInstanceId", catalogInstance,
                                "rootCallId", catalogRootCallId,
                                "inputPortMap", Collections.emptyList(),
                                "outputPortMap", Collections.singletonList(
                                        object("canonicalPort", output,
                                                "exactPort", output)),
                                "bindingIds", Collections.singletonList(
                                        edgeId)))),
                "loopBound", object("schemaVersion", 1,
                        "kind", "CFG_BACKEDGE",
                        "scope", "ALL_EXECUTION_SCOPE_LOOPS",
                        "maxBackedgeTraversals", 8,
                        "onLimit", "CUT_PATH"),
                "admission", object("state", "EXECUTABLE"));
    }

    private static Map<String, Object> logicalTargetTask(
            String first, String second, boolean includeSelected) {
        List<Map<String, Object>> occurrences = new ArrayList<>();
        occurrences.add(object("regionInstanceId", first,
                "rootCallId", 1,
                "inputPortMap", Collections.emptyList(),
                "outputPortMap", Collections.emptyList(),
                "bindingIds", Collections.emptyList()));
        if (includeSelected) {
            occurrences.add(object("regionInstanceId", second,
                    "rootCallId", 2,
                    "inputPortMap", Collections.emptyList(),
                    "outputPortMap", Collections.emptyList(),
                    "bindingIds", Collections.emptyList()));
        }
        return object("taskId", "TASK.LOGICAL",
                "goalId", "GOAL.LOGICAL",
                "goalKind", "TARGET_REACH_CLOSURE",
                "regionId", "REGION.1",
                "regionInstanceId", first,
                "logicalRegionId", "REGION.1@owner7",
                "summaryReuseKey", "REGION.1@owner7",
                "inputActions", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList(),
                "occurrenceInstantiationCatalog", object(
                        "schemaVersion", 1,
                        "kind", "LOGICAL_SUMMARY_OCCURRENCE_CATALOG",
                        "logicalRegionId", "REGION.1@owner7",
                        "summaryReuseKey", "REGION.1@owner7",
                        "canonicalRegionInstanceId", first,
                        "canonicalRootCallId", 1,
                        "occurrences", occurrences),
                "loopBound", object("schemaVersion", 1,
                        "kind", "CFG_BACKEDGE",
                        "scope", "ALL_EXECUTION_SCOPE_LOOPS",
                        "maxBackedgeTraversals", 8,
                        "onLimit", "CUT_PATH"),
                "admission", object("state", "EXECUTABLE"));
    }

    private static Map<String, Object> logicalTargetPlan(
            String first, String second) {
        Map<String, Object> exactGoal = object(
                "goalId", "GOAL.EXACT",
                "kind", "TARGET_REACH_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<T: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                // The scheduled task below deliberately projects this
                // unused input away.  Its exact occurrence remains the same
                // runtime activation, but its compact adapter is a subset of
                // this full logical occurrence catalog.
                "symbolize", Collections.singletonList(object(
                        "symbol", "REGION.1.in.unused",
                        "cell", "<T: int unused>",
                        "javaType", "int",
                        "location", "HEAP_OBJECT_FIELD",
                        "sourceKind", "FIELD_READ",
                        "dependencyRole", "VALUE_FRONTIER")),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList());
        Map<String, Object> logicalGoal = new LinkedHashMap<>(exactGoal);
        logicalGoal.put("goalId", "GOAL.LOGICAL");
        logicalGoal.put("executionOccurrence", object(
                "regionInstanceId", first, "rootCallId", 1,
                "laneId", 11, "spanId", 101));
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", first,
                "logicalRegionId", "REGION.1@owner7",
                "summaryReuseKey", "REGION.1@owner7",
                "logicalInstanceCount", 2,
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void run()>", "ordinal", 1),
                "occurrences", Arrays.asList(
                        object("regionInstanceId", first,
                                "rootCallId", 1, "ownerId", 7,
                                "laneId", 11, "spanId", 101,
                                "closureGoals", Collections.singletonList(
                                        exactGoal)),
                        object("regionInstanceId", second,
                                "rootCallId", 2, "ownerId", 7,
                                "laneId", 12, "spanId", 102,
                                "closureGoals", Collections.singletonList(
                                        exactGoal))),
                "closureGoals", Collections.singletonList(logicalGoal));
    }

    private static Map<String, Object> targetPlanWithInput(
            String instance) {
        return targetPlanWithInput(instance, "VALUE_FRONTIER");
    }

    private static Map<String, Object> targetPlanWithInput(
            String instance, String dependencyRole) {
        long rootCallId = Long.parseLong(instance.substring(
                instance.lastIndexOf("#call") + 5));
        boolean carrier = "CONCRETE_STRUCTURE_CARRIER".equals(
                dependencyRole);
        Map<String, Object> goal = object(
                "goalId", "GOAL.TARGET",
                "kind", "TARGET_REACH_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<T: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.singletonList(object(
                        "portId", "REGION.T.in.value",
                        "symbol", "REGION.T.in.value",
                        "cell", carrier ? "<T: java.util.Map value>"
                                : "<T: int value>",
                        "javaType", carrier ? "java.util.Map" : "int",
                        "location", "HEAP_OBJECT_FIELD",
                        "sourceKind", "FIELD_READ",
                        "dependencyRole", dependencyRole)),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList());
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.T",
                "regionInstanceId", instance,
                "rootCallId", rootCallId,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void run()>", "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> protocolTargetPlanWithInput(
            String instance) {
        Map<String, Object> plan = targetPlanWithInput(instance);
        Map<String, Object> goal = ((List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> input = ((List<Map<String, Object>>)
                goal.get("symbolize")).get(0);
        input.put("sourceKind", "PROTOCOL_INPUT");
        return plan;
    }

    private static Map<String, Object> targetPlanWithInputs(
            String instance, List<String> ports) {
        long rootCallId = Long.parseLong(instance.substring(
                instance.lastIndexOf("#call") + 5));
        List<Map<String, Object>> symbolize = new ArrayList<>();
        for (String port : ports) {
            symbolize.add(object(
                    "portId", port,
                    "symbol", port,
                    "cell", "<T: int " + port + ">",
                    "javaType", "int",
                    "location", "HEAP_OBJECT_FIELD",
                    "sourceKind", "FIELD_READ",
                    "dependencyRole", "VALUE_FRONTIER"));
        }
        Map<String, Object> goal = object(
                "goalId", "GOAL.TARGET",
                "kind", "TARGET_REACH_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<T: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", symbolize,
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList());
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.T",
                "regionInstanceId", instance,
                "rootCallId", rootCallId,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void run()>", "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> multiOutputProducerPlan(
            String region, long call, String targetInstance,
            List<String> targetPorts) {
        String instance = region + "@test#call" + call;
        List<Map<String, Object>> edges = new ArrayList<>();
        List<Map<String, Object>> members = new ArrayList<>();
        int index = 0;
        for (String targetPort : targetPorts) {
            String outputPort = region + ".out.value" + index;
            String edgeId = "EDGE." + region + "." + index;
            Map<String, Object> edge = object(
                    "schemaVersion", 3,
                    "edgeId", edgeId,
                    "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                    "correlationAuthority",
                    "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                    "mappingId", "rpc." + region + "." + index,
                    "fromRegionInstance", instance,
                    "fromOutputPort", outputPort,
                    "toRegionInstance", targetInstance,
                    "toInputPort", targetPort,
                    "callerSiteEventSeq", call * 10 + index * 3,
                    "sendEventSeq", call * 10 + index * 3 + 1,
                    "receiveEventSeq", call * 10 + index * 3 + 2);
            edges.add(edge);
            members.add(object(
                    "output", object("portId", outputPort,
                            "cell", "value" + index,
                            "kind", "REGION_OUTPUT",
                            "javaTypeDescriptor", "I"),
                    "slice", object("outputPort", outputPort,
                            "outputCell", "value" + index,
                            "inputPorts", Collections.emptyList(),
                            "sites", Collections.emptyList(),
                            "staticSites", Collections.emptyList(),
                            "methods", Collections.singletonList(
                                    "<P: void run()>"),
                            "causalEdgeIds",
                            Collections.singletonList(edgeId),
                            "captureBindings", Collections.emptyList(),
                            "captureBindingIssues",
                            Collections.emptyList())));
            index++;
        }
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", region,
                        "regionInstanceId", instance,
                        "rootCallId", call),
                "causalEdges", edges,
                "members", members);
        Map<String, Object> goal = object(
                "goalId", "GOAL.PRODUCER",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<P: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "edgeBindings", edges,
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", region,
                "regionInstanceId", instance,
                "rootCallId", call,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<P: void run()>", "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> readyCarrierProducerPlan(
            String targetInstance) {
        String producerInstance = "REGION.P@test#call1";
        String inputPort = "REGION.P.in.registry";
        String outputPort = "REGION.P.out.registry";
        String targetPort = "REGION.T.in.value";
        Map<String, Object> edge = object(
                "schemaVersion", 3,
                "edgeId", "EDGE.RPC.CARRIER",
                "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", "rpc.carrier",
                "fromRegionInstance", producerInstance,
                "fromOutputPort", outputPort,
                "toRegionInstance", targetInstance,
                "toInputPort", targetPort,
                "callerSiteEventSeq", 10,
                "sendEventSeq", 11,
                "receiveEventSeq", 12);
        Map<String, Object> input = object(
                "portId", inputPort,
                "symbol", inputPort,
                "cell", "<P: java.util.Map registry>",
                "javaType", "java.util.Map",
                "location", "RECEIVER_FIELD",
                "sourceKind", "RECEIVER_FIELD",
                "dependencyRole", "CONCRETE_STRUCTURE_CARRIER");
        Map<String, Object> slice = object(
                "outputPort", outputPort,
                "outputCell", "registry",
                "inputPorts", Collections.singletonList(inputPort),
                "sites", Collections.emptyList(),
                "staticSites", Collections.emptyList(),
                "methods", Collections.singletonList("<P: void run()>"),
                "causalEdgeIds", Collections.singletonList(
                        "EDGE.RPC.CARRIER"),
                "captureBindings", Collections.emptyList(),
                "captureBindingIssues", Collections.emptyList());
        Map<String, Object> member = object(
                "output", object("portId", outputPort,
                        "cell", "registry", "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "Ljava/util/Map;"),
                "slice", slice);
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", "REGION.P",
                        "regionInstanceId", producerInstance,
                        "rootCallId", 1),
                "causalEdges", Collections.singletonList(edge),
                "members", Collections.singletonList(member));
        Map<String, Object> goal = object(
                "goalId", "GOAL.PRODUCER",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<P: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.singletonList(input),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.singletonList(edge),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.P",
                "regionInstanceId", producerInstance,
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<P: void run()>", "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> pendingLogicalProducerPlan(
            String targetInstance) {
        String producerInstance = "REGION.P@test#call1";
        Map<String, Object> edge = object(
                "schemaVersion", 3,
                "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", "rpc.map",
                "fromRegionInstance", producerInstance,
                "fromOutputPort", "REGION.P.out.value",
                "toRegionInstance", targetInstance,
                "toInputPort", "REGION.T.in.value",
                "callerSiteEventSeq", 10,
                "sendEventSeq", 11,
                "receiveEventSeq", 12);
        Map<String, Object> pending = object(
                "goalId", "GOAL.PENDING.EXACT.1",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods", Collections.emptyList(),
                "admission", object("state", "DISCOVERED", "blockers",
                        Collections.singletonList(
                                "OUTPUT_CLOSURE_PENDING")),
                "symbolize", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.singletonList(edge));
        Map<String, Object> duplicate = new LinkedHashMap<>(pending);
        duplicate.put("goalId", "GOAL.PENDING.EXACT.2");
        Map<String, Object> logical = new LinkedHashMap<>(pending);
        logical.put("goalId", "GOAL.PENDING.LOGICAL");
        logical.put("executionOccurrence", object(
                "regionInstanceId", producerInstance,
                "rootCallId", 1));
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.P",
                "regionInstanceId", producerInstance,
                "logicalRegionId", "REGION.P@owner7",
                "summaryReuseKey", "REGION.P@owner7",
                "logicalInstanceCount", 1,
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<P: void run()>", "ordinal", 1),
                "occurrences", Collections.singletonList(object(
                        "regionInstanceId", producerInstance,
                        "rootCallId", 1,
                        "closureGoals", Arrays.asList(
                                pending, duplicate))),
                "closureGoals", Collections.singletonList(logical));
    }

    private static Map<String, Object> leafProducerPlan(
            String region, long call, String targetInstance,
            String targetPort) {
        String instance = region + "@test#call" + call;
        String outputPort = region + ".out.value";
        String edgeId = "EDGE." + region + "." + call;
        Map<String, Object> edge = object(
                "schemaVersion", 3,
                "edgeId", edgeId,
                "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", "rpc." + region,
                "fromRegionInstance", instance,
                "fromOutputPort", outputPort,
                "toRegionInstance", targetInstance,
                "toInputPort", targetPort,
                "callerSiteEventSeq", call * 10,
                "sendEventSeq", call * 10 + 1,
                "receiveEventSeq", call * 10 + 2);
        Map<String, Object> slice = object(
                "outputPort", outputPort,
                "outputCell", "value",
                "inputPorts", Collections.emptyList(),
                "sites", Collections.emptyList(),
                "staticSites", Collections.emptyList(),
                "methods", Collections.singletonList("<P: void run()>"),
                "causalEdgeIds", Collections.singletonList(edgeId),
                "captureBindings", Collections.emptyList(),
                "captureBindingIssues", Collections.emptyList());
        Map<String, Object> member = object(
                "output", object("portId", outputPort,
                        "cell", "value", "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "I"),
                "slice", slice);
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", region,
                        "regionInstanceId", instance,
                        "rootCallId", call),
                "causalEdges", Collections.singletonList(edge),
                "members", new ArrayList<>(
                        Collections.singletonList(member)));
        Map<String, Object> goal = object(
                "goalId", "GOAL.PRODUCER",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<P: void run()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.emptyList(),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.singletonList(edge),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", region,
                "regionInstanceId", instance,
                "rootCallId", call,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<P: void run()>", "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> projectedLeafProducerPlan(
            String region, long call, String targetInstance,
            String targetPort, boolean trusted) {
        Map<String, Object> plan = leafProducerPlan(region, call,
                targetInstance, targetPort);
        Map<String, Object> goal = ((List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> edge = ((List<Map<String, Object>>)
                goal.get("edgeBindings")).get(0);
        edge.put("rpcDescendantProjection", true);
        edge.put("projectionOfEdgeId", "EDGE.RPC.BASE");
        edge.put("fieldPathDeclarations", Collections.singletonList(
                "<Wire: java.lang.Object projected>"));
        if (!trusted) {
            edge.put("correlationAuthority", "UNTRUSTED");
        }
        return plan;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> provedBoundedStateProducerPlan(
            String region, long call, String targetInstance,
            String targetPort) {
        Map<String, Object> plan = leafProducerPlan(region, call,
                targetInstance, targetPort);
        markProvedBoundedStateTransition(plan);
        return plan;
    }

    @SuppressWarnings("unchecked")
    private static void markProvedBoundedStateTransition(
            Map<String, Object> plan) {
        Map<String, Object> goal = ((List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>)
                goal.get("outputClosure");
        Map<String, Object> member = ((List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>)
                member.get("slice");
        slice.put("outputBoundaryKind",
                "DEFINITION_INVOCATION_NORMAL_EXIT");
        slice.put("containerPreStateAuthority",
                "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1");
        slice.put("foldedMutationCount", 1);
    }

    @SuppressWarnings("unchecked")
    private static void markExactHeapStateHandoff(
            Map<String, Object> producer, Map<String, Object> consumer,
            String producerLogicalRegion, String consumerLogicalRegion) {
        producer.put("logicalRegionId", producerLogicalRegion);
        consumer.put("logicalRegionId", consumerLogicalRegion);
        Map<String, Object> producerGoal = ((List<Map<String, Object>>)
                producer.get("closureGoals")).get(0);
        Map<String, Object> consumerGoal = ((List<Map<String, Object>>)
                consumer.get("closureGoals")).get(0);
        producerGoal.put("goalId", "GOAL.PRODUCER.EARLIER");
        consumerGoal.put("goalId", "GOAL.PRODUCER.LATER");

        Map<String, Object> edge = ((List<Map<String, Object>>)
                producerGoal.get("edgeBindings")).get(0);
        edge.put("fromRegion", producer.get("regionId"));
        edge.put("toRegion", consumer.get("regionId"));
        edge.put("transportKind", "HEAP");
        edge.put("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.put("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.put("receiverObjectId", 41);
        edge.put("writerEventSeq", 100);
        edge.put("readerEventSeq", 200);
        edge.put("writerLaneId", 1);
        edge.put("readerLaneId", 2);
        edge.put("programOrderRequired", false);

        Map<String, Object> closure = (Map<String, Object>)
                producerGoal.get("outputClosure");
        Map<String, Object> member = ((List<Map<String, Object>>)
                closure.get("members")).get(0);
        ((Map<String, Object>) member.get("output"))
                .put("kind", "HEAP_STATE");
        ((Map<String, Object>) member.get("slice")).put(
                "outputBoundaryKind",
                "EXACT_FIELD_WRITE_AFTER_ASSIGNMENT");
    }

    @SuppressWarnings("unchecked")
    private static void markSelectedSemanticGuardEvidence(
            Map<String, Object> plan, boolean includeSemanticGuard) {
        Map<String, Object> goal = ((List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>)
                goal.get("outputClosure");
        Map<String, Object> member = ((List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>)
                member.get("slice");
        if (includeSemanticGuard) {
            String site = "<P: void run()>#u1";
            slice.put("sites", Collections.singletonList(site));
            goal.put("branches", Collections.singletonList(object(
                    "siteId", site,
                    "policy", "EXPLORE",
                    "observed", true,
                    "failureTarget", false,
                    "loopControlGuard", false,
                    "loopControlOnly", false)));
            return;
        }

        String unobserved = "<P: void run()>#u2";
        String loop = "<P: void run()>#u3";
        String failure = "<P: void run()>#u4";
        String replay = "<P: void run()>#u5";
        String outsideSelectedSlice = "<P: void run()>#u6";
        slice.put("sites", Arrays.asList(unobserved, loop, failure,
                replay));
        goal.put("branches", Arrays.asList(
                object("siteId", unobserved, "policy", "EXPLORE",
                        "observed", false, "failureTarget", false,
                        "loopControlGuard", false,
                        "loopControlOnly", false),
                object("siteId", loop, "policy", "EXPLORE",
                        "observed", true, "failureTarget", false,
                        "loopControlGuard", true,
                        "loopControlOnly", false),
                object("siteId", failure, "policy", "EXPLORE",
                        "observed", true, "failureTarget", true,
                        "loopControlGuard", false,
                        "loopControlOnly", false),
                object("siteId", replay, "policy", "PATH_ASSUMPTION",
                        "observed", true, "failureTarget", false,
                        "loopControlGuard", false,
                        "loopControlOnly", false),
                object("siteId", outsideSelectedSlice,
                        "policy", "EXPLORE", "observed", true,
                        "failureTarget", false,
                        "loopControlGuard", false,
                        "loopControlOnly", false)));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> producerWithIncomingDependencyPlan(
            String targetInstance, String inputPort,
            Map<String, Object> upstream) {
        return producerWithIncomingDependencyPlan("REGION.MID", 3,
                targetInstance, "REGION.T.in.value", inputPort, upstream);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> producerWithIncomingDependencyPlan(
            String region, long call, String targetInstance,
            String targetPort, String inputPort,
            Map<String, Object> upstream) {
        Map<String, Object> middle = leafProducerPlan(
                region, call, targetInstance, targetPort);
        Map<String, Object> goal = ((List<Map<String, Object>>)
                middle.get("closureGoals")).get(0);
        goal.put("symbolize", Collections.singletonList(object(
                "portId", inputPort,
                "symbol", inputPort,
                "cell", "<MID: int value>",
                "javaType", "int",
                "location", "HEAP_OBJECT_FIELD",
                "sourceKind", "FIELD_READ",
                "dependencyRole", "VALUE_FRONTIER")));
        Map<String, Object> closure = (Map<String, Object>)
                goal.get("outputClosure");
        Map<String, Object> member = ((List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>)
                member.get("slice");
        slice.put("inputPorts", Collections.singletonList(inputPort));

        Map<String, Object> upstreamGoal = ((List<Map<String, Object>>)
                upstream.get("closureGoals")).get(0);
        Map<String, Object> incoming = ((List<Map<String, Object>>)
                upstreamGoal.get("edgeBindings")).get(0);
        List<Map<String, Object>> ledger = new ArrayList<>(
                (List<Map<String, Object>>) goal.get("edgeBindings"));
        ledger.add(incoming);
        goal.put("edgeBindings", ledger);
        return middle;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> malformedProducerPlan(
            String region, long call, String targetInstance,
            String targetPort) {
        Map<String, Object> plan = leafProducerPlan(region, call,
                targetInstance, targetPort);
        Map<String, Object> goal = ((List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>)
                goal.get("outputClosure");
        List<Map<String, Object>> members = (List<Map<String, Object>>)
                closure.get("members");
        String secondPort = region + ".out.duplicate";
        members.add(object(
                "output", object("portId", secondPort,
                        "cell", "value", "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "I"),
                "slice", object("outputPort", secondPort,
                        "outputCell", "value",
                        "inputPorts", Collections.emptyList(),
                        "sites", Collections.emptyList(),
                        "staticSites", Collections.emptyList(),
                        "methods", Collections.singletonList(
                                "<P: void run()>"),
                        "causalEdgeIds", Collections.emptyList(),
                        "captureBindings", Collections.emptyList(),
                        "captureBindingIssues", Collections.emptyList())));
        return plan;
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put((String) values[index], values[index + 1]);
        }
        return result;
    }
}
