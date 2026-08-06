package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
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
    public void causalDiscoveryFollowsBothRolesAndRejectsMissingRole() {
        JsonObject protocol = new JsonObject();
        protocol.addProperty("sourceKind", "PROTOCOL_INPUT");
        protocol.addProperty("dependencyRole", "VALUE_FRONTIER");
        assertTrue(RuntimeWorkflowDiscovery.causalAction(protocol));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("dependencyRole",
                "CONCRETE_STRUCTURE_CARRIER");
        assertTrue(RuntimeWorkflowDiscovery.causalAction(carrier));
        try {
            RuntimeWorkflowDiscovery.causalAction(new JsonObject());
            fail("missing dependency role must fail closed");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("dependencyRole"));
        }
    }

    @Test
    public void structureCarrierStillDiscoversItsProducer() throws Exception {
        String targetInstance = "REGION.T@test#call2";
        File plans = writePlans("carrier-producer.jsonl",
                readyCarrierProducerPlan(targetInstance),
                targetPlanWithInput(targetInstance,
                        "CONCRETE_STRUCTURE_CARRIER"));

        String discovery = run(plans, "discover");

        assertTrue(discovery.contains("PRODUCER\t"));
        assertTrue(discovery.contains("\tREGION.P\t"
                + "REGION.P@test#call1\tGOAL.PRODUCER"));
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
    public void targetBindingsPreferRicherExactCausalClosureDeterministically()
            throws Exception {
        String shallow = "REGION.T@test#call1";
        String rich = "REGION.T@test#call9";
        List<Map<String, Object>> rows = Arrays.asList(
                targetPlanWithInput(shallow),
                leafProducerPlan("REGION.P1", 2, shallow,
                        "REGION.T.in.value"),
                targetPlanWithInputs(rich, Arrays.asList(
                        "REGION.T.in.value", "REGION.T.in.other")),
                leafProducerPlan("REGION.P2", 10, rich,
                        "REGION.T.in.value"),
                leafProducerPlan("REGION.P3", 11, rich,
                        "REGION.T.in.other"));
        File forward = writeRows("rank-forward.jsonl", rows);
        List<Map<String, Object>> reversed = new ArrayList<>(rows);
        Collections.reverse(reversed);
        File backward = writeRows("rank-backward.jsonl", reversed);

        String forwardBindings = run(forward, "target-bindings");
        String backwardBindings = run(backward, "target-bindings");

        assertEquals(forwardBindings, backwardBindings);
        assertTrue(forwardBindings.split("\\R")[0].contains(
                rich + "\tGOAL.TARGET"));
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
                "symbolize", Collections.emptyList(),
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
    private static Map<String, Object> producerWithIncomingDependencyPlan(
            String targetInstance, String inputPort,
            Map<String, Object> upstream) {
        Map<String, Object> middle = leafProducerPlan(
                "REGION.MID", 3, targetInstance, "REGION.T.in.value");
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
