package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicSchedulerTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void targetStructureCarrierRemainsConcrete() throws Exception {
        File regions = write("carrier-regions.jsonl", region());
        File plans = write("carrier-plans.jsonl", carrierTargetPlan());
        File edges = writeEmpty("carrier-edges.jsonl");
        File refined = write("carrier-refined.jsonl", refinedEdge());
        File output = folder.newFolder("carrier-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.registry"));
    }

    @Test
    public void loopControlOnlyInputRemainsConcrete() throws Exception {
        File regions = write("loop-input-regions.jsonl", region());
        File plans = write("loop-input-plans.jsonl", loopInputTargetPlan());
        File edges = writeEmpty("loop-input-edges.jsonl");
        File refined = write("loop-input-refined.jsonl", refinedEdge());
        File output = folder.newFolder("loop-input-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.running"));
    }

    @Test
    public void unclosedReferenceBoundaryLeafRemainsConcrete()
            throws Exception {
        Map<String, Object> action = heapLeaf(
                "REGION.1.in.value", "example.Payload", "int", "value");
        action.put("referenceBoundaryLeaf", true);
        action.put("symbolicDemand",
                "CONCRETE_REFERENCE_BOUNDARY_REPLAY");
        action.put("replayAuthority",
                "EXACT_TRACE_REFERENCE_LEAF_UNDER_APPROX_V1");
        File regions = write("reference-leaf-regions.jsonl", region());
        File plans = write("reference-leaf-plans.jsonl",
                targetPlanWithActions(action));
        File edges = writeEmpty("reference-leaf-edges.jsonl");
        File refined = write("reference-leaf-refined.jsonl", refinedEdge());
        File output = folder.newFolder("reference-leaf-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject scheduled = inputAction(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"), "REGION.1.in.value");
        assertEquals("CONCRETE", scheduled.get("mode").getAsString());
        assertEquals("EXACT_TRACE_REFERENCE_LEAF_UNDER_APPROX_V1",
                scheduled.get("replayAuthority").getAsString());
    }

    @Test
    public void leafNoExploredGuardReadsStaysConcrete() throws Exception {
        String method = "<T: void f()>";
        String guarded = "<example.Owner: int guarded>";
        String payload = "<example.Owner: int payload>";
        File regions = write("payload-regions.jsonl", region());
        File plans = write("payload-plans.jsonl", guardOperandTargetPlan(
                heapLeaf("REGION.1.in.guarded", "example.Owner", "int",
                        "guarded"),
                heapLeaf("REGION.1.in.payload", "example.Owner", "int",
                        "payload")));
        File edges = writeEmpty("payload-edges.jsonl");
        File refined = writeRows("payload-refined.jsonl", refinedEdge(),
                transferEdge("DF.guarded", guarded, method + "::$i1"),
                transferEdge("DF.payload", payload, method + "::$i9"));
        File output = folder.newFolder("payload-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.guarded"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.payload"));
    }

    @Test
    public void protocolArgumentBecomesAnExactMethodArgument() throws Exception {
        File regions = write("protocol-argument-regions.jsonl", region());
        File plans = write("protocol-argument-plans.jsonl",
                protocolArgumentTargetPlan());
        File edges = writeEmpty("protocol-argument-edges.jsonl");
        File refined = write("protocol-argument-refined.jsonl",
                refinedEdge());
        File output = folder.newFolder("protocol-argument-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject action = result.executionTasks.get(0)
                .getAsJsonArray("inputActions").get(0).getAsJsonObject();
        assertEquals("SYMBOLIC", action.get("mode").getAsString());
        assertEquals("METHOD_ARGUMENT",
                action.get("bindingMode").getAsString());
        assertEquals("<T: void decode(java.lang.String)>",
                action.get("method").getAsString());
        assertEquals(0, action.get("index").getAsInt());
        assertEquals("java.lang.String", action.get("javaType").getAsString());
        assertEquals(1, result.executionTasks.get(0)
                .getAsJsonArray("edgeBindings").size());
    }

    @Test
    public void protocolArgumentWithoutTrustedProducerStaysConcrete()
            throws Exception {
        File regions = write("unbound-protocol-regions.jsonl", region());
        File plans = write("unbound-protocol-plans.jsonl",
                protocolArgumentTargetPlan(false));
        File edges = writeEmpty("unbound-protocol-edges.jsonl");
        File refined = write("unbound-protocol-refined.jsonl",
                refinedEdge());
        File output = folder.newFolder("unbound-protocol-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals("CONCRETE", mode(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"),
                "REGION.1.in.protocol"));
    }

    @Test
    public void producerStructureCarrierRemainsConcrete() throws Exception {
        File regions = write("producer-carrier-regions.jsonl", outputRegion());
        Map<String, Object> plan = outputPlan();
        setDependencyRole(plan, "REGION.1.in.demanded",
                "CONCRETE_STRUCTURE_CARRIER");
        File plans = write("producer-carrier-plans.jsonl", plan);
        File edges = writeEmpty("producer-carrier-edges.jsonl");
        File refined = write("producer-carrier-refined.jsonl", refinedEdge());
        File output = folder.newFolder("producer-carrier-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals("CONCRETE", mode(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"),
                "REGION.1.in.demanded"));
    }

    @Test
    public void onlyExactSupportedLeavesBecomeSymbolic() throws Exception {
        Map<String, Object> expiry = object(
                "symbol", "REGION.1.in.expiry",
                "cell", "<Key: long expiry>",
                "location", "HEAP_OBJECT_FIELD",
                "sourceKind", "ACCESSOR_RETURN",
                "javaType", "long", "observed", true,
                "dependencyRole", "VALUE_FRONTIER",
                "fieldPath", Collections.singletonList("expiry"),
                "fieldPaths", Collections.singletonList(
                        Collections.singletonList("expiry")),
                "leafFieldSignature", "<Key: long expiry>",
                "accessFieldSignature", "<Key: long expiry>");
        Map<String, Object> owner = object(
                "symbol", "REGION.1.in.manager",
                "cell", "<Service: example.Manager manager>",
                "location", "RECEIVER_FIELD",
                "sourceKind", "RECEIVER_FIELD",
                "javaType", "example.Manager", "observed", true,
                "dependencyRole", "VALUE_FRONTIER",
                "fieldPath", Collections.singletonList("manager"),
                "fieldPaths", Collections.singletonList(
                        Collections.singletonList("manager")),
                "leafFieldSignature",
                "<Service: example.Manager manager>");
        Map<String, Object> assertion = object(
                "symbol", "REGION.1.in.assertions",
                "cell", "<Service: boolean $assertionsDisabled>",
                "location", "HEAP_OBJECT_FIELD",
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "javaType", "boolean", "observed", true,
                "dependencyRole", "VALUE_FRONTIER",
                "fieldPath", Collections.singletonList(
                        "$assertionsDisabled"),
                "fieldPaths", Collections.singletonList(
                        Collections.singletonList("$assertionsDisabled")),
                "leafFieldSignature",
                "<Service: boolean $assertionsDisabled>");
        File regions = write("leaf-regions.jsonl", region());
        File plans = write("leaf-plans.jsonl", targetPlanWithActions(
                expiry, owner, assertion));
        File edges = writeEmpty("leaf-edges.jsonl");
        File refined = write("leaf-refined.jsonl", refinedEdge());
        File output = folder.newFolder("leaf-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");

        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.expiry"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.manager"));
        assertEquals("CONCRETE", mode(actions,
                "REGION.1.in.assertions"));
    }

    @Test
    public void structureControlValuesReplayConcreteWhileSemanticLeavesStaySymbolic()
            throws Exception {
        Map<String, Object> switchTable = heapLeaf(
                "REGION.1.in.switchTable", "Compiler$1", "int[]",
                "$SwitchMap$example$State");
        switchTable.put("sourceKind", "ACTIVATION_FIELD_RECEIVER");

        Map<String, Object> ordinal = heapLeaf(
                "REGION.1.in.ordinal", "java.lang.Enum", "int",
                "ordinal");
        ordinal.put("sourceKind", "ACCESSOR_RETURN");
        ordinal.put("declaredCallee", "<example.State: int ordinal()>");
        ordinal.put("accessorImplementationMethod",
                "<java.lang.Enum: int ordinal()>");

        Map<String, Object> size = heapLeaf(
                "REGION.1.in.size", "example.CustomCollection", "int",
                "size");
        size.put("sourceKind", "ACCESSOR_RETURN");
        size.put("declaredCallee",
                "<example.CustomCollection: int size()>");

        Map<String, Object> expiry = heapLeaf(
                "REGION.1.in.expiry", "example.Key", "long",
                "expiryDate");
        Map<String, Object> keyId = heapLeaf(
                "REGION.1.in.keyId", "example.Key", "int", "keyId");

        File regions = write("structure-regions.jsonl", region());
        File plans = write("structure-plans.jsonl", targetPlanWithActions(
                switchTable, ordinal, size, expiry, keyId));
        File edges = writeEmpty("structure-edges.jsonl");
        File refined = write("structure-refined.jsonl", refinedEdge());
        File output = folder.newFolder("structure-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");

        assertEquals("CONCRETE", mode(actions,
                "REGION.1.in.switchTable"));
        assertEquals("COMPILER_SWITCH_DISPATCH_TABLE",
                inputAction(actions, "REGION.1.in.switchTable")
                        .get("structureControlReason").getAsString());
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.ordinal"));
        assertEquals("ENUM_DISPATCH_ORDINAL",
                inputAction(actions, "REGION.1.in.ordinal")
                        .get("structureControlReason").getAsString());
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.size"));
        assertEquals("FIXED_CONTAINER_CARDINALITY",
                inputAction(actions, "REGION.1.in.size")
                        .get("structureControlReason").getAsString());
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.expiry"));
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.keyId"));
    }

    @Test
    public void missingDependencyRoleFailsClosed() throws Exception {
        Map<String, Object> action = object(
                "symbol", "REGION.1.in.value",
                "cell", "<T: void f(int)>.param0:int",
                "location", "ARGUMENT", "index", 0,
                "javaType", "int", "observed", true);
        File regions = write("missing-role-regions.jsonl", region());
        File plans = write("missing-role-plans.jsonl",
                targetPlanWithActions(action));
        File edges = writeEmpty("missing-role-edges.jsonl");
        File refined = write("missing-role-refined.jsonl", refinedEdge());
        File output = folder.newFolder("missing-role-schedule");

        try {
            ConcolicScheduler.schedule(arguments(regions, plans, edges,
                    refined, output));
            fail("missing dependency role must fail closed");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("dependencyRole"));
        }
    }

    @Test
    public void schedulerAcceptsOnlyRuntimeRefinedGraph() throws Exception {
        File regions = write("regions.jsonl", region());
        File plans = write("plans.jsonl", plan());
        File edges = writeEmpty("edges.jsonl");
        File refined = write("refined.jsonl", refinedEdge());
        File output = folder.newFolder("schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        assertEquals(1, result.executionTasks.size());
        JsonArray branches = result.executionTasks.get(0)
                .getAsJsonArray("branches");
        assertEquals("PATH_ASSUMPTION",
                branches.get(0).getAsJsonObject().get("policy").getAsString());
        assertEquals("EXPLORE",
                branches.get(1).getAsJsonObject().get("policy").getAsString());

        Map<String, Object> candidate = refinedEdge();
        candidate.remove("refinementSchemaVersion");
        candidate.remove("graphKind");
        File candidateFile = write("candidate.jsonl", candidate);
        try {
            ConcolicScheduler.schedule(arguments(regions, plans, edges,
                    candidateFile, output));
            fail("candidate graph must be rejected");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("runtime-refined"));
        }
    }

    @Test
    @SuppressWarnings("unchecked")
    public void selectedFailureTargetOverridesStructureAssumption()
            throws Exception {
        Map<String, Object> targetPlan = plan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                targetPlan.get("closureGoals")).get(0);
        java.util.List<Map<String, Object>> branches =
                (java.util.List<Map<String, Object>>) goal.get("branches");
        Map<String, Object> target = branches.get(1);
        target.put("policy", "PATH_ASSUMPTION");
        target.put("policyReason", "STRUCTURE_CARRIER_GUARD");
        target.put("observedOutcome", true);
        target.put("occurrences", Collections.singletonList(
                object("occurrence", 1, "outcome", true)));

        File regions = write("assumed-target-regions.jsonl", region());
        File plans = write("assumed-target-plans.jsonl", targetPlan);
        File edges = writeEmpty("assumed-target-edges.jsonl");
        File refined = write("assumed-target-refined.jsonl", refinedEdge());
        File output = folder.newFolder("assumed-target-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        JsonObject scheduledTarget = result.executionTasks.get(0)
                .getAsJsonArray("branches").get(1).getAsJsonObject();

        assertTrue(scheduledTarget.get("failureTarget").getAsBoolean());
        assertEquals("EXPLORE",
                scheduledTarget.get("policy").getAsString());
        assertEquals("TARGET_REACH_SELECTED_FAILURE_BRANCH",
                scheduledTarget.get("policyReason").getAsString());
    }

    @Test
    public void preservesEveryRuntimeTargetOccurrence() throws Exception {
        File regions = write("occurrence-regions.jsonl", region());
        Map<String, Object> first = plan();
        Map<String, Object> second = plan();
        second.put("regionInstanceId", "REGION.1@test#call2");
        second.put("rootSelector", object("kind", "GLOBAL_INVOCATION",
                "method", "<T: void f()>", "ordinal", 2));
        File plans = writeRows("occurrence-plans.jsonl", first, second);
        File edges = writeEmpty("occurrence-edges.jsonl");
        File refined = write("occurrence-refined.jsonl", refinedEdge());
        File output = folder.newFolder("occurrence-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals(2, result.executionTasks.size());
        java.util.Set<String> instances = new java.util.LinkedHashSet<>();
        for (JsonObject task : result.executionTasks) {
            instances.add(task.get("regionInstanceId").getAsString());
        }
        assertTrue(instances.contains("REGION.1@test#call1"));
        assertTrue(instances.contains("REGION.1@test#call2"));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void schedulesDistinctSemanticPathSeedsInParallel()
            throws Exception {
        Map<String, Object> logical = plan();
        java.util.List<Map<String, Object>> original =
                (java.util.List<Map<String, Object>>) logical.get(
                        "closureGoals");
        Map<String, Object> first = original.get(0);
        first.put("pathSeedKey", "PATH.SEED.FALSE");
        Map<String, Object> second = GSON.fromJson(
                GSON.toJson(first), Map.class);
        second.put("goalId", "GOAL.2");
        second.put("pathSeedKey", "PATH.SEED.TRUE");
        // Two seeds are distinct because their decisions differ, not because
        // they were labelled differently: the second goal drives the prefix
        // guard the other way.
        ((Map<String, Object>) ((java.util.List<Map<String, Object>>)
                ((java.util.List<Map<String, Object>>) second.get("branches"))
                        .get(0).get("occurrences")).get(0))
                .put("outcome", true);
        java.util.List<Map<String, Object>> goals =
                new java.util.ArrayList<>();
        goals.add(first);
        goals.add(second);
        logical.put("closureGoals", goals);
        logical.put("logicalRegionId", "REGION.1@owner7");
        logical.put("summaryReuseKey", "REGION.1@owner7");

        File regions = write("path-seeds-regions.jsonl", region());
        File plans = write("path-seeds-plans.jsonl", logical);
        File edges = writeEmpty("path-seeds-edges.jsonl");
        File refined = write("path-seeds-refined.jsonl", refinedEdge());
        File output = folder.newFolder("path-seeds-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals(2, result.executionTasks.size());
        java.util.Set<String> seeds = new java.util.LinkedHashSet<>();
        java.util.Set<String> tasks = new java.util.LinkedHashSet<>();
        for (JsonObject task : result.executionTasks) {
            seeds.add(task.get("pathSeedKey").getAsString());
            tasks.add(task.get("taskId").getAsString());
            // The published name is the name of the published contract.
            assertEquals(edu.uva.liftlab.graphchecker.contract.BoundedPathSeed
                            .key(task.getAsJsonArray("branches")),
                    task.get("pathSeedKey").getAsString());
        }
        assertEquals(2, seeds.size());
        assertEquals(2, tasks.size());
    }

    @Test
    @SuppressWarnings("unchecked")
    public void taskIdentitySurvivesReRecordedTraceOrdinals()
            throws Exception {
        // A fresh recording renames every trace ordinal: root call ids,
        // runtime owner ids (and thus logicalRegionId), and the goal ids
        // minted from instance ids.  The task identity is a pure semantic
        // hash (region content x path seed x port set x target predicate),
        // so the semantically unchanged closure keeps its task id and
        // previously imported summaries stay addressable.
        Map<String, Object> first = plan();
        first.put("logicalRegionId", "REGION.1@owner7");
        first.put("summaryReuseKey", "REGION.1@owner7");
        File output1 = folder.newFolder("stable-id-1");
        ConcolicScheduler.Result run1 = ConcolicScheduler.schedule(
                arguments(write("stable-id-regions-1.jsonl", region()),
                        write("stable-id-plans-1.jsonl", first),
                        writeEmpty("stable-id-edges-1.jsonl"),
                        write("stable-id-refined-1.jsonl", refinedEdge()),
                        output1));

        Map<String, Object> second = plan();
        // Same semantics, different recording: every trace-run ordinal
        // moves.
        second.put("regionInstanceId", "REGION.1@test#call4242");
        second.put("rootCallId", 4242L);
        second.put("logicalRegionId", "REGION.1@owner93");
        second.put("summaryReuseKey", "REGION.1@owner93");
        java.util.List<Map<String, Object>> goals =
                (java.util.List<Map<String, Object>>) second.get(
                        "closureGoals");
        goals.get(0).put("goalId", "GOAL.RENAMED.BY.RERECORDING");
        File output2 = folder.newFolder("stable-id-2");
        ConcolicScheduler.Result run2 = ConcolicScheduler.schedule(
                arguments(write("stable-id-regions-2.jsonl", region()),
                        write("stable-id-plans-2.jsonl", second),
                        writeEmpty("stable-id-edges-2.jsonl"),
                        write("stable-id-refined-2.jsonl", refinedEdge()),
                        output2));

        assertEquals(1, run1.executionTasks.size());
        assertEquals(1, run2.executionTasks.size());
        assertEquals(
                run1.executionTasks.get(0).get("taskId").getAsString(),
                run2.executionTasks.get(0).get("taskId").getAsString());

        // A semantic change (different explored branch site) must move the
        // identity.
        Map<String, Object> changed = plan();
        java.util.List<Map<String, Object>> changedGoals =
                (java.util.List<Map<String, Object>>) changed.get(
                        "closureGoals");
        for (Map<String, Object> branch
                : (java.util.List<Map<String, Object>>) changedGoals.get(0)
                .get("branches")) {
            if (Boolean.TRUE.equals(branch.get("failureTarget"))) {
                branch.put("siteId", "<T: void f()>#u9");
            }
        }
        File output3 = folder.newFolder("stable-id-3");
        ConcolicScheduler.Result run3 = ConcolicScheduler.schedule(
                arguments(write("stable-id-regions-3.jsonl", region()),
                        write("stable-id-plans-3.jsonl", changed),
                        writeEmpty("stable-id-edges-3.jsonl"),
                        write("stable-id-refined-3.jsonl", refinedEdge()),
                        output3));
        assertEquals(1, run3.executionTasks.size());
        assertFalse(run1.executionTasks.get(0).get("taskId").getAsString()
                .equals(run3.executionTasks.get(0).get("taskId")
                        .getAsString()));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void logicalPlanSchedulesOneSummaryAndCarriesEveryOccurrence()
            throws Exception {
        File regions = write("logical-regions.jsonl", region());
        Map<String, Object> logical = plan();
        logical.put("logicalRegionId", "REGION.1@owner7");
        logical.put("summaryReuseKey", "REGION.1@owner7");
        logical.put("logicalInstanceCount", 2);
        logical.put("logicalRootCallIds", java.util.Arrays.asList(1L, 2L));
        logical.put("logicalActivationIds", java.util.Arrays.asList(
                "ACT.1", "ACT.2"));
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                logical.get("closureGoals")).get(0);
        Map<String, Object> exactGoal1 = GSON.fromJson(GSON.toJson(goal),
                Map.class);
        Map<String, Object> exactGoal2 = GSON.fromJson(GSON.toJson(goal),
                Map.class);
        logical.put("occurrences", java.util.Arrays.asList(
                object("regionInstanceId", "REGION.1@test#call1",
                        "rootCallId", 1, "laneId", 11, "spanId", 101,
                        "closureGoals", Collections.singletonList(
                                exactGoal1)),
                object("regionInstanceId", "REGION.1@test#call2",
                        "rootCallId", 2, "laneId", 12, "spanId", 102,
                        "closureGoals", Collections.singletonList(
                                exactGoal2))));
        goal.put("executionOccurrence", object(
                "regionInstanceId", "REGION.1@test#call2",
                "rootCallId", 2,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void f()>", "ordinal", 2),
                "laneId", 12, "spanId", 102));
        File plans = write("logical-plans.jsonl", logical);
        File edges = writeEmpty("logical-edges.jsonl");
        File refined = write("logical-refined.jsonl", refinedEdge());
        File output = folder.newFolder("logical-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals(1, result.executionTasks.size());
        JsonObject task = result.executionTasks.get(0);
        assertEquals("REGION.1@owner7",
                task.get("logicalRegionId").getAsString());
        assertEquals(2, task.get("logicalInstanceCount").getAsInt());
        assertTrue(!task.has("occurrences"));
        JsonObject catalog = task.getAsJsonObject(
                "occurrenceInstantiationCatalog");
        assertEquals(2, catalog.getAsJsonArray("occurrences").size());
        assertEquals("REGION.1@test#call2",
                task.get("regionInstanceId").getAsString());
        assertEquals(2, task.get("rootCallId").getAsLong());
        assertEquals(12, task.get("laneId").getAsLong());
        assertEquals(102, task.get("spanId").getAsLong());
        for (JsonElement element : catalog.getAsJsonArray("occurrences")) {
            assertTrue(!element.getAsJsonObject().has("closureGoals"));
        }
    }

    @Test
    @SuppressWarnings("unchecked")
    public void selectedOccurrenceScopesQueryButVmTaskRemainsCanonical()
            throws Exception {
        String first = "REGION.1@test#call1";
        String second = "REGION.1@test#call2";
        Map<String, Object> logical = plan();
        logical.put("logicalRegionId", "REGION.1@owner7");
        logical.put("summaryReuseKey", "REGION.1@owner7");
        logical.put("logicalInstanceCount", 2);
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                logical.get("closureGoals")).get(0);
        Map<String, Object> exactFirst = GSON.fromJson(GSON.toJson(goal),
                Map.class);
        Map<String, Object> exactSecond = GSON.fromJson(GSON.toJson(goal),
                Map.class);
        logical.put("occurrences", java.util.Arrays.asList(
                object("regionInstanceId", first, "rootCallId", 1,
                        "closureGoals", Collections.singletonList(
                                exactFirst)),
                object("regionInstanceId", second, "rootCallId", 2,
                        "closureGoals", Collections.singletonList(
                                exactSecond))));
        goal.put("executionOccurrence", object(
                "regionInstanceId", first, "rootCallId", 1));

        File regions = write("selected-query-regions.jsonl", region());
        File plans = write("selected-query-plans.jsonl", logical);
        File edges = writeEmpty("selected-query-edges.jsonl");
        File refined = write("selected-query-refined.jsonl", refinedEdge());
        File summaries = write("selected-query-summaries.jsonl", object(
                "schemaVersion", 1,
                "kind", "CONCOLIC_REGION_SUMMARY",
                "summaryId", "SUMMARY.1",
                "goalId", "GOAL.1",
                "goalKind", "TARGET_REACH_CLOSURE",
                "regionId", "REGION.1",
                "regionInstanceId", first,
                "relationallyComplete", true,
                "pathCondition", Collections.emptyList(),
                "branchMappings", Collections.emptyList()));
        File output = folder.newFolder("selected-query-schedule");
        ConcolicScheduler.Arguments arguments =
                ConcolicScheduler.Arguments.parse(new String[]{
                        "--regions", regions.getPath(),
                        "--region-plan", plans.getPath(),
                        "--edge-validations", edges.getPath(),
                        "--refined-graph", refined.getPath(),
                        "--summaries", summaries.getPath(),
                        "--output-dir", output.getPath(),
                        "--region-id", "REGION.1",
                        "--region-instance-id", second,
                        "--goal-id", "GOAL.1",
                        "--max-jobs", "1",
                        "--max-loop-iterations", "8"});

        ConcolicScheduler.Result result =
                ConcolicScheduler.schedule(arguments);

        assertEquals(1, result.executionTasks.size());
        assertEquals(first, result.executionTasks.get(0)
                .get("regionInstanceId").getAsString());
        assertEquals(1, result.queries.size());
        assertEquals(second, result.queries.get(0)
                .get("regionInstanceId").getAsString());
        assertEquals(first, result.queries.get(0)
                .get("canonicalRegionInstanceId").getAsString());
        assertEquals(second, result.queries.get(0)
                .getAsJsonObject("selectedTargetOccurrence")
                .get("regionInstanceId").getAsString());
    }

    @Test
    public void schedulerComposesOnlySchemaThreeRuntimeFieldFlow() {
        Map<String, Object> binding = object(
                "schemaVersion", 3,
                "evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1",
                "fromRegionInstance", "REGION.2@test#call2",
                "toRegionInstance", "REGION.1@test#call1",
                "fromOutputPort", "REGION.2.out.value",
                "toInputPort", "REGION.1.in.value",
                "correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                "receiverObjectId", 77,
                "writerLaneId", "lane.writer",
                "readerLaneId", "lane.reader",
                "programOrderRequired", false,
                "writerEventSeq", 5,
                "readerEventSeq", 6);
        Map<String, Object> row = object(
                "schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", "RF.1",
                "transportKind", "HEAP",
                "state", "CONFIRMED_RUNTIME_IDENTITY",
                "fromRegion", "REGION.2",
                "toRegion", "REGION.1",
                "fromPort", "REGION.2.out.value",
                "toPort", "REGION.1.in.value",
                "bindings", Collections.singletonList(binding));
        JsonObject edge = GSON.toJsonTree(row).getAsJsonObject();
        assertTrue(AutomaticRegionEdge.composable(edge));

        edge.addProperty("schemaVersion", 2);
        assertTrue(!AutomaticRegionEdge.composable(edge));
    }

    @Test
    public void outputClosureSymbolizesOnlyDemandedInputs() throws Exception {
        File regions = write("output-regions.jsonl", outputRegion());
        File plans = write("output-plans.jsonl", outputPlan());
        File edges = writeEmpty("output-edges.jsonl");
        File refined = write("output-refined.jsonl", refinedEdge());
        File output = folder.newFolder("output-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals(1, result.executionTasks.size());
        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.demanded"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.unrelated"));
        JsonObject occurrence = result.executionTasks.get(0)
                .getAsJsonObject("occurrenceInstantiationCatalog")
                .getAsJsonArray("occurrences").get(0).getAsJsonObject();
        assertEquals(2, occurrence.getAsJsonArray("inputPortMap").size());
        assertEquals(1, occurrence.getAsJsonArray("outputPortMap").size());
        assertEquals(8, LoopBoundPolicy.decode(
                result.executionTasks.get(0)).maxBackedgeTraversals());
    }

    @Test
    public void producerProjectionShrinksEveryTaskLedgerTogether()
            throws Exception {
        File regions = write("projected-regions.jsonl",
                projectableOutputRegion());
        File plans = write("projected-plans.jsonl",
                projectableMultiOutputPlan());
        File edges = writeEmpty("projected-edges.jsonl");
        File refined = write("projected-refined.jsonl", refinedEdge());
        File projection = write("producer-projection.jsonl",
                producerProjection(Collections.singleton(
                        "REGION.1.out.keep"), Collections.singleton(
                        "EDGE.KEEP")));
        File output = folder.newFolder("projected-schedule");
        File unprojectedOutput = folder.newFolder("unprojected-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output,
                        projection));
        ConcolicScheduler.Result unprojected = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined,
                        unprojectedOutput));

        assertEquals(1, result.executionTasks.size());
        JsonObject task = result.executionTasks.get(0);
        assertEquals(1, task.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").size());
        assertEquals("REGION.1.out.keep", task
                .getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("output").get("portId").getAsString());
        assertEquals(1, task.getAsJsonArray("inputActions").size());
        assertEquals("REGION.1.in.keep", task
                .getAsJsonArray("inputActions").get(0).getAsJsonObject()
                .get("symbol").getAsString());
        assertEquals(1, task.getAsJsonArray("branches").size());
        assertEquals("<T: void f(int,int)>#u1", task
                .getAsJsonArray("branches").get(0).getAsJsonObject()
                .get("siteId").getAsString());
        assertEquals(1, task.getAsJsonArray("edgeBindings").size());
        assertEquals("EDGE.KEEP", task.getAsJsonArray("edgeBindings")
                .get(0).getAsJsonObject().get("edgeId").getAsString());
        JsonObject occurrence = task.getAsJsonObject(
                "occurrenceInstantiationCatalog")
                .getAsJsonArray("occurrences").get(0).getAsJsonObject();
        assertEquals(1, occurrence.getAsJsonArray("inputPortMap").size());
        assertEquals(1, occurrence.getAsJsonArray("outputPortMap").size());
        assertEquals(1, occurrence.getAsJsonArray("bindingIds").size());
        assertTrue(task.has("producerProjection"));
        assertTrue(!task.get("taskId").getAsString().equals(
                unprojected.executionTasks.get(0).get("taskId")
                        .getAsString()));
        // Projection drops a guard, so the projected task walks a narrower
        // bounded path than the goal did.  Its published name must be the
        // name of the contract it publishes, not of the one it dropped.
        JsonObject whole = unprojected.executionTasks.get(0);
        assertEquals(2, whole.getAsJsonArray("branches").size());
        assertEquals(edu.uva.liftlab.graphchecker.contract.BoundedPathSeed
                        .key(task.getAsJsonArray("branches")),
                task.get("pathSeedKey").getAsString());
        assertEquals(edu.uva.liftlab.graphchecker.contract.BoundedPathSeed
                        .key(whole.getAsJsonArray("branches")),
                whole.get("pathSeedKey").getAsString());
        assertTrue(!task.get("pathSeedKey").getAsString().equals(
                whole.get("pathSeedKey").getAsString()));
    }

    @Test
    public void producerProjectionRetainsJointlyDemandedOutputsInOneTask()
            throws Exception {
        File regions = write("joint-regions.jsonl",
                projectableOutputRegion());
        File plans = write("joint-plans.jsonl",
                projectableMultiOutputPlan());
        File edges = writeEmpty("joint-edges.jsonl");
        File refined = write("joint-refined.jsonl", refinedEdge());
        java.util.Set<String> outputs = new java.util.LinkedHashSet<>();
        outputs.add("REGION.1.out.keep");
        outputs.add("REGION.1.out.drop");
        java.util.Set<String> edgeIds = new java.util.LinkedHashSet<>();
        edgeIds.add("EDGE.KEEP");
        edgeIds.add("EDGE.DROP");
        File projection = write("joint-projection.jsonl",
                producerProjection(outputs, edgeIds));
        File output = folder.newFolder("joint-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output,
                        projection));

        assertEquals(1, result.executionTasks.size());
        JsonObject task = result.executionTasks.get(0);
        assertEquals(2, task.getAsJsonObject("outputClosure")
                .getAsJsonArray("members").size());
        assertEquals(2, task.getAsJsonArray("inputActions").size());
        assertEquals(2, task.getAsJsonArray("branches").size());
        assertEquals(2, task.getAsJsonArray("edgeBindings").size());
    }

    @Test
    public void rootedOutputCaptureDeclarationRemainsConcrete()
            throws Exception {
        File regions = write("capture-root-regions.jsonl", outputRegion());
        File plans = write("capture-root-plans.jsonl",
                captureRootOutputPlan());
        File edges = writeEmpty("capture-root-edges.jsonl");
        File refined = write("capture-root-refined.jsonl", refinedEdge());
        File output = folder.newFolder("capture-root-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.demanded"));
        assertEquals("CONCRETE", mode(actions, "CAPTURE_ROOT.1"));
    }

    @Test
    public void protocolReturnUsesItsExactLocalDefinition() throws Exception {
        File regions = write("protocol-regions.jsonl", outputRegion());
        File plans = write("protocol-plans.jsonl", protocolOutputPlan());
        File edges = writeEmpty("protocol-edges.jsonl");
        File refined = write("protocol-refined.jsonl",
                protocolRefinedEdge());
        File output = folder.newFolder("protocol-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject action = result.executionTasks.get(0)
                .getAsJsonArray("inputActions").get(0).getAsJsonObject();
        assertEquals("SYMBOLIC", action.get("mode").getAsString());
        assertEquals("LOCAL_DEFINITION",
                action.get("bindingMode").getAsString());
        assertEquals("$r0", action.get("local").getAsString());
        assertEquals(3, action.getAsJsonArray("definitionSites")
                .get(0).getAsJsonObject().get("unitIndex").getAsInt());
    }

    @Test
    public void exactClosureMayTrackABoundedObjectArrayState()
            throws Exception {
        File regions = write("bounded-array-regions.jsonl", outputRegion());
        File plans = write("bounded-array-plans.jsonl",
                boundedArrayOutputPlan(true));
        File edges = writeEmpty("bounded-array-edges.jsonl");
        File refined = write("bounded-array-refined.jsonl",
                boundedArrayRefinedEdge());
        File output = folder.newFolder("bounded-array-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject action = inputAction(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"),
                "REGION.1.in.demanded");
        assertEquals("SYMBOLIC", action.get("mode").getAsString());
        assertEquals("LOCAL_DEFINITION",
                action.get("bindingMode").getAsString());
        assertEquals("example.Key[]", action.get("javaType").getAsString());
    }

    @Test
    public void objectArrayWithoutExactBoundedStateDemandStaysConcrete()
            throws Exception {
        File regions = write("plain-array-regions.jsonl", outputRegion());
        File plans = write("plain-array-plans.jsonl",
                boundedArrayOutputPlan(false));
        File edges = writeEmpty("plain-array-edges.jsonl");
        File refined = write("plain-array-refined.jsonl",
                boundedArrayRefinedEdge());
        File output = folder.newFolder("plain-array-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        assertEquals("CONCRETE", mode(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"),
                "REGION.1.in.demanded"));
    }

    @Test
    public void exactMutationMapPreStateIsASymbolicFieldState()
            throws Exception {
        File regions = write("bounded-map-regions.jsonl", outputRegion());
        File plans = write("bounded-map-plans.jsonl",
                boundedMapFieldOutputPlan());
        File edges = writeEmpty("bounded-map-edges.jsonl");
        File refined = write("bounded-map-refined.jsonl",
                boundedMapRefinedEdge());
        File output = folder.newFolder("bounded-map-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject action = inputAction(result.executionTasks.get(0)
                        .getAsJsonArray("inputActions"),
                "REGION.1.in.demanded");
        assertEquals("SYMBOLIC", action.get("mode").getAsString());
        assertEquals("FIELD_ACCESS",
                action.get("bindingMode").getAsString());
        assertEquals("java.util.Map",
                action.get("javaType").getAsString());
        assertEquals("BOUNDED_CONTAINER_STATE",
                action.get("symbolicDemand").getAsString());
        assertEquals("EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1",
                action.get("preStateSelectionAuthority").getAsString());
    }

    private ConcolicScheduler.Arguments arguments(
            File regions, File plans, File edges, File graph, File output) {
        return ConcolicScheduler.Arguments.parse(new String[]{
                "--regions", regions.getPath(),
                "--region-plan", plans.getPath(),
                "--edge-validations", edges.getPath(),
                "--refined-graph", graph.getPath(),
                "--output-dir", output.getPath(),
                "--max-jobs", "16",
                "--max-loop-iterations", "8"
        });
    }

    private ConcolicScheduler.Arguments arguments(
            File regions, File plans, File edges, File graph, File output,
            File projection) {
        return ConcolicScheduler.Arguments.parse(new String[]{
                "--regions", regions.getPath(),
                "--region-plan", plans.getPath(),
                "--edge-validations", edges.getPath(),
                "--refined-graph", graph.getPath(),
                "--producer-projection", projection.getPath(),
                "--output-dir", output.getPath(),
                "--max-jobs", "16",
                "--max-loop-iterations", "8"
        });
    }

    private static Map<String, Object> region() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", Collections.emptyList(),
                "outputs", Collections.emptyList());
    }

    private static Map<String, Object> outputRegion() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", java.util.Arrays.asList(
                        port("REGION.1.in.demanded", "param0"),
                        port("REGION.1.in.unrelated", "param1")),
                "outputs", Collections.singletonList(
                        port("REGION.1.out.value", "result")));
    }

    private static Map<String, Object> projectableOutputRegion() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", java.util.Arrays.asList(
                        port("REGION.1.in.keep", "param0"),
                        port("REGION.1.in.drop", "param1")),
                "outputs", java.util.Arrays.asList(
                        port("REGION.1.out.keep", "keep"),
                        port("REGION.1.out.drop", "drop")));
    }

    private static Map<String, Object> plan() {
        Map<String, Object> occurrence = object("occurrence", 1,
                "outcome", false);
        Map<String, Object> prefix = object("siteId", "<T: void f()>#u0",
                "policy", "EXPLORE", "requiredOutcome", false,
                "observed", true, "observedOutcome", false,
                "selectedOccurrence", 1,
                "occurrences", Collections.singletonList(occurrence));
        Map<String, Object> branch = object("siteId", "<T: void f()>#u1",
                "failureTarget", true,
                "policy", "EXPLORE", "requiredOutcome", false,
                "observed", true, "observedOutcome", false,
                "selectedOccurrence", 1,
                "occurrences", Collections.singletonList(occurrence));
        Map<String, Object> goal = object("goalId", "GOAL.1",
                "kind", "TARGET_REACH_CLOSURE",
                "runtimeDefinitionMethods",
                Collections.singletonList("<T: void f()>"),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.emptyList(),
                "branches", java.util.Arrays.asList(prefix, branch),
                "edgeBindings", Collections.emptyList());
        return object("schemaVersion", 3, "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", "<T: void f()>", "ordinal", 1),
                "targetMethod", "<T: void f()>",
                "closureGoals", Collections.singletonList(goal));
    }

    @SafeVarargs
    @SuppressWarnings("unchecked")
    private static Map<String, Object> targetPlanWithActions(
            Map<String, Object>... actions) {
        Map<String, Object> result = plan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        goal.put("symbolize", java.util.Arrays.asList(actions));
        return result;
    }

    @SafeVarargs
    @SuppressWarnings("unchecked")
    private static Map<String, Object> guardOperandTargetPlan(
            Map<String, Object>... actions) {
        Map<String, Object> result = targetPlanWithActions(actions);
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        java.util.List<Map<String, Object>> branches =
                (java.util.List<Map<String, Object>>) goal.get("branches");
        branches.get(0).put("operandCells",
                Collections.singletonList("<T: void f()>::$i0"));
        branches.get(1).put("operandCells",
                Collections.singletonList("<T: void f()>::$i1"));
        return result;
    }

    @SuppressWarnings("unchecked")
    private static void setDependencyRole(
            Map<String, Object> plan, String symbol, String role) {
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        for (Map<String, Object> action
                : (java.util.List<Map<String, Object>>) goal.get(
                "symbolize")) {
            if (symbol.equals(action.get("symbol"))) {
                action.put("dependencyRole", role);
                return;
            }
        }
        throw new IllegalArgumentException("missing action " + symbol);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> carrierTargetPlan() {
        Map<String, Object> result = plan();
        java.util.List<Map<String, Object>> goals =
                (java.util.List<Map<String, Object>>) result.get(
                        "closureGoals");
        goals.get(0).put("symbolize", Collections.singletonList(object(
                "symbol", "REGION.1.in.registry",
                "cell", "<T: java.util.Map registry>",
                "location", "RECEIVER_FIELD",
                "javaType", "java.util.Map", "observed", true,
                "dependencyRole", "CONCRETE_STRUCTURE_CARRIER")));
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> loopInputTargetPlan() {
        Map<String, Object> result = plan();
        java.util.List<Map<String, Object>> goals =
                (java.util.List<Map<String, Object>>) result.get(
                        "closureGoals");
        goals.get(0).put("symbolize", Collections.singletonList(object(
                "symbol", "REGION.1.in.running",
                "cell", "<T: boolean running>",
                "location", "RECEIVER_FIELD",
                "javaType", "boolean", "observed", true,
                "dependencyRole", "VALUE_FRONTIER",
                "loopControlOnly", true)));
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> protocolArgumentTargetPlan() {
        return protocolArgumentTargetPlan(true);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> protocolArgumentTargetPlan(
            boolean trusted) {
        Map<String, Object> result = plan();
        java.util.List<Map<String, Object>> goals =
                (java.util.List<Map<String, Object>>) result.get(
                        "closureGoals");
        goals.get(0).put("symbolize", Collections.singletonList(object(
                "symbol", "REGION.1.in.protocol",
                "cell", "<T: void decode(java.lang.String)>.param0:java.lang.String",
                "location", "PROTOCOL_ARGUMENT",
                "serverParameterIndex", 0,
                "javaType", "java.lang.Object", "observed", true,
                "dependencyRole", "VALUE_FRONTIER")));
        goals.get(0).put("edgeBindings", trusted
                ? Collections.singletonList(trustedProtocolBinding())
                : Collections.emptyList());
        return result;
    }

    private static Map<String, Object> trustedProtocolBinding() {
        return object(
                "schemaVersion", 3,
                "edgeId", "EDGE.RPC.PROTOCOL",
                "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", "rpc.protocol",
                "fromRegion", "REGION.P",
                "toRegion", "REGION.1",
                "fromRegionInstance", "REGION.P@test#call9",
                "toRegionInstance", "REGION.1@test#call1",
                "fromOutputPort", "REGION.P.out.protocol",
                "toInputPort", "REGION.1.in.protocol",
                "callerSiteEventSeq", 10,
                "sendEventSeq", 11,
                "receiveEventSeq", 12);
    }

    private static Map<String, Object> outputPlan() {
        String method = "<T: void f(int,int)>";
        Map<String, Object> demanded = object(
                "symbol", "REGION.1.in.demanded",
                "cell", method + ".param0:int",
                "location", "ARGUMENT", "index", 0,
                "javaType", "int", "observed", true,
                "dependencyRole", "VALUE_FRONTIER");
        Map<String, Object> unrelated = object(
                "symbol", "REGION.1.in.unrelated",
                "cell", method + ".param1:int",
                "location", "ARGUMENT", "index", 1,
                "javaType", "int", "observed", true,
                "dependencyRole", "VALUE_FRONTIER");

        Map<String, Object> slice = object(
                "outputPort", "REGION.1.out.value",
                "outputCell", "result",
                "inputPorts", Collections.singletonList(
                        "REGION.1.in.demanded"),
                "sites", Collections.emptyList(),
                "staticSites", Collections.emptyList(),
                "methods", Collections.singletonList(method),
                "causalEdgeIds", Collections.emptyList(),
                "captureBindings", Collections.emptyList(),
                "captureBindingIssues", Collections.emptyList());
        Map<String, Object> member = object(
                "output", object("portId", "REGION.1.out.value",
                        "cell", "result", "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "I"),
                "slice", slice);
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", "REGION.1",
                        "regionInstanceId", "REGION.1@test#call1",
                        "rootCallId", 1),
                "causalEdges", Collections.emptyList(),
                "members", Collections.singletonList(member));
        Map<String, Object> goal = object(
                "goalId", "GOAL.OUTPUT",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods", Collections.singletonList(method),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", java.util.Arrays.asList(demanded, unrelated),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList(),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", method, "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> projectableMultiOutputPlan() {
        String method = "<T: void f(int,int)>";
        Map<String, Object> keepEdge = projectedEdge("EDGE.KEEP",
                "REGION.1.out.keep", "REGION.T.in.keep", 10);
        Map<String, Object> dropEdge = projectedEdge("EDGE.DROP",
                "REGION.1.out.drop", "REGION.T.in.drop", 20);
        Map<String, Object> keep = projectedMember("REGION.1.out.keep",
                "keep", "REGION.1.in.keep", method + "#u1",
                "EDGE.KEEP");
        Map<String, Object> drop = projectedMember("REGION.1.out.drop",
                "drop", "REGION.1.in.drop", method + "#u2",
                "EDGE.DROP");
        Map<String, Object> closure = object(
                "schemaVersion", 2,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", "REGION.1",
                        "regionInstanceId", "REGION.1@test#call1",
                        "rootCallId", 1),
                "causalEdges", java.util.Arrays.asList(keepEdge, dropEdge),
                "members", java.util.Arrays.asList(keep, drop));
        Map<String, Object> goal = object(
                "goalId", "GOAL.PROJECTABLE",
                "pathSeedKey", "PATH.PROJECTABLE",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods", Collections.singletonList(method),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", java.util.Arrays.asList(
                        projectedInput("REGION.1.in.keep", 0, method),
                        projectedInput("REGION.1.in.drop", 1, method)),
                "branches", java.util.Arrays.asList(
                        projectedBranch(method + "#u1"),
                        projectedBranch(method + "#u2")),
                "edgeBindings", java.util.Arrays.asList(keepEdge, dropEdge),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", method, "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    private static Map<String, Object> projectedInput(
            String symbol, int index, String method) {
        return object("symbol", symbol,
                "cell", method + ".param" + index + ":int",
                "location", "ARGUMENT", "index", index,
                "javaType", "int", "observed", true,
                "dependencyRole", "VALUE_FRONTIER");
    }

    private static Map<String, Object> projectedBranch(String siteId) {
        return object("siteId", siteId,
                "policy", "EXPLORE", "requiredOutcome", true,
                "observed", true, "observedOutcome", true,
                "selectedOccurrence", 1,
                "occurrences", Collections.singletonList(object(
                        "occurrence", 1, "outcome", true)));
    }

    private static Map<String, Object> projectedMember(
            String output, String cell, String input, String site,
            String edgeId) {
        return object("output", object("portId", output,
                        "cell", cell, "kind", "REGION_OUTPUT",
                        "javaTypeDescriptor", "I"),
                "slice", object("outputPort", output,
                        "outputCell", cell,
                        "inputPorts", Collections.singletonList(input),
                        "sites", Collections.singletonList(site),
                        "staticSites", Collections.emptyList(),
                        "methods", Collections.singletonList(
                                "<T: void f(int,int)>"),
                        "causalEdgeIds", Collections.singletonList(edgeId),
                        "captureBindings", Collections.emptyList(),
                        "captureBindingIssues", Collections.emptyList()));
    }

    private static Map<String, Object> projectedEdge(
            String edgeId, String output, String input, long sequence) {
        return object("schemaVersion", 3,
                "edgeId", edgeId,
                "evidenceKind", "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "correlationAuthority",
                "TRUSTED_CONFIGURED_RPC_MAPPING_V1",
                "mappingId", "rpc." + edgeId,
                "fromRegion", "REGION.1",
                "toRegion", "REGION.T",
                "fromRegionInstance", "REGION.1@test#call1",
                "toRegionInstance", "REGION.T@test#call9",
                "fromOutputPort", output,
                "toInputPort", input,
                "callerSiteEventSeq", sequence,
                "sendEventSeq", sequence + 1,
                "receiveEventSeq", sequence + 2);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> producerProjection(
            java.util.Set<String> outputs, java.util.Set<String> edgeIds) {
        JsonObject encoded = ProducerOutputProjection.create(
                "CAMPAIGN.1", "REGION.1", "REGION.1@test#call1",
                "GOAL.PROJECTABLE", "PATH.PROJECTABLE", outputs,
                edgeIds).json();
        return GSON.fromJson(encoded, Map.class);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> captureRootOutputPlan() {
        Map<String, Object> result = outputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        java.util.List<Map<String, Object>> actions =
                new java.util.ArrayList<>((java.util.List<Map<String, Object>>)
                        goal.get("symbolize"));
        actions.add(object("symbol", "CAPTURE_ROOT.1",
                "cell", "<T: example.Key currentKey>",
                "location", "RECEIVER_FIELD", "javaType", "example.Key",
                "observed", true, "captureRootOnly", true,
                "dependencyRole", "CONCRETE_STRUCTURE_CARRIER",
                "fieldPath", java.util.Arrays.asList("state", "currentKey")));
        goal.put("symbolize", actions);
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        slice.put("inputPorts", java.util.Arrays.asList(
                "REGION.1.in.demanded", "CAPTURE_ROOT.1"));
        return result;
    }

    private static Map<String, Object> protocolOutputPlan() {
        String method = "<T: java.lang.String fetch()>";
        String symbol = "REGION.1.in.demanded";
        Map<String, Object> action = object(
                "symbol", symbol, "cell", method + "::$r0",
                "location", "PROTOCOL_RETURN",
                "javaType", "java.lang.String", "observed", true,
                "dependencyRole", "VALUE_FRONTIER");
        Map<String, Object> slice = object(
                "outputPort", "REGION.1.out.value",
                "outputCell", "result",
                "inputPorts", Collections.singletonList(symbol),
                "sites", Collections.emptyList(),
                "staticSites", Collections.singletonList(method + "#u3"),
                "methods", Collections.singletonList(method),
                "causalEdgeIds", Collections.emptyList(),
                "captureBindings", Collections.emptyList(),
                "captureBindingIssues", Collections.emptyList());
        Map<String, Object> closure = object(
                "schemaVersion", 2, "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("regionId", "REGION.1",
                        "regionInstanceId", "REGION.1@test#call1",
                        "rootCallId", 1),
                "causalEdges", Collections.emptyList(),
                "members", Collections.singletonList(object(
                        "output", object("portId", "REGION.1.out.value",
                                "cell", "result", "kind", "REGION_OUTPUT",
                                "javaTypeDescriptor", "I"),
                        "slice", slice)));
        Map<String, Object> goal = object(
                "goalId", "GOAL.PROTOCOL",
                "kind", "OUTPUT_RELATION_CLOSURE",
                "runtimeDefinitionMethods", Collections.singletonList(method),
                "admission", object("state", "READY", "blockers",
                        Collections.emptyList()),
                "symbolize", Collections.singletonList(action),
                "branches", Collections.emptyList(),
                "edgeBindings", Collections.emptyList(),
                "outputClosure", closure);
        return object("schemaVersion", 3,
                "kind", "CONCOLIC_REGION_PLAN",
                "regionId", "REGION.1",
                "regionInstanceId", "REGION.1@test#call1",
                "rootCallId", 1,
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", method, "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> boundedArrayOutputPlan(
            boolean boundedDemand) {
        Map<String, Object> result = protocolOutputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        Map<String, Object> action = ((java.util.List<Map<String, Object>>)
                goal.get("symbolize")).get(0);
        String method = "<T: example.Key[] fetch()>";
        action.put("cell", method + "::$r0");
        action.put("javaType", "example.Key[]");
        if (boundedDemand) {
            action.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        }
        goal.put("runtimeDefinitionMethods",
                Collections.singletonList(method));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        slice.put("staticSites", Collections.singletonList(method + "#u3"));
        slice.put("methods", Collections.singletonList(method));
        result.put("rootSelector", object("kind", "GLOBAL_INVOCATION",
                "method", method, "ordinal", 1));
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> boundedMapFieldOutputPlan() {
        Map<String, Object> result = protocolOutputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        Map<String, Object> action = ((java.util.List<Map<String, Object>>)
                goal.get("symbolize")).get(0);
        String method = "<T: void f()>";
        String field = "<example.Keys: java.util.Map allKeys>";
        action.put("cell", field);
        action.put("location", "HEAP_OBJECT_FIELD");
        action.put("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        action.put("javaType", "java.util.Map");
        action.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        action.put("containerCapacity", LoopBoundPolicy
                .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        action.put("fieldPath", Collections.singletonList("allKeys"));
        action.put("fieldPaths", Collections.singletonList(
                Collections.singletonList("allKeys")));
        action.put("accessFieldSignature", field);
        action.put("leafFieldSignature", field);
        action.put("accessSites", Collections.singletonList(method + "#u1"));
        action.put("preStateSelectionAuthority",
                "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1");
        goal.put("runtimeDefinitionMethods",
                Collections.singletonList(method));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        slice.put("staticSites", Collections.singletonList(method + "#u1"));
        slice.put("methods", Collections.singletonList(method));
        result.put("rootSelector", object("kind", "GLOBAL_INVOCATION",
                "method", method, "ordinal", 1));
        return result;
    }

    private static Map<String, Object> port(String id, String cell) {
        return object("portId", id, "symbol", id, "cell", cell);
    }

    private static Map<String, Object> heapLeaf(
            String symbol, String owner, String type, String field) {
        String declaration = "<" + owner + ": " + type + " "
                + field + ">";
        return object(
                "symbol", symbol,
                "cell", declaration,
                "location", "HEAP_OBJECT_FIELD",
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "javaType", type,
                "observed", true,
                "dependencyRole", "VALUE_FRONTIER",
                "fieldPath", Collections.singletonList(field),
                "fieldPaths", Collections.singletonList(
                        Collections.singletonList(field)),
                "leafFieldSignature", declaration,
                "accessFieldSignature", declaration);
    }

    private static String mode(JsonArray actions, String symbol) {
        return inputAction(actions, symbol).get("mode").getAsString();
    }

    private static JsonObject inputAction(JsonArray actions,
                                          String symbol) {
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject();
            if (symbol.equals(action.get("symbol").getAsString())) {
                return action;
            }
        }
        fail("missing input action " + symbol);
        return new JsonObject();
    }

    private static Map<String, Object> refinedEdge() {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.1", "kind", "exception_guard",
                "transferKind", "GUARD", "method", "<T: void f()>",
                "fromCell", "guard", "toCell", "exception");
    }

    private static Map<String, Object> transferEdge(
            String id, String fromCell, String toCell) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", "field_read",
                "transferKind", "HEAP_READ", "method", "<T: void f()>",
                "fromCell", fromCell, "toCell", toCell);
    }

    private static Map<String, Object> protocolRefinedEdge() {
        String method = "<T: java.lang.String fetch()>";
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.protocol", "kind", "call_return",
                "transferKind", "FUNCTION_RETURN", "method", method,
                "fromCell", "<Rpc: java.lang.String call()>.return",
                "toCell", method + "::$r0", "siteId", method + "#u3",
                "unitIndex", 3, "unit", "$r0 = virtualinvoke r1.call()");
    }

    private static Map<String, Object> boundedArrayRefinedEdge() {
        String method = "<T: example.Key[] fetch()>";
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.bounded-array", "kind", "call_return",
                "transferKind", "FUNCTION_RETURN", "method", method,
                "fromCell", "<Rpc: example.Key[] call()>.return",
                "toCell", method + "::$r0", "siteId", method + "#u3",
                "unitIndex", 3, "unit", "$r0 = virtualinvoke r1.call()");
    }

    private static Map<String, Object> boundedMapRefinedEdge() {
        String method = "<T: void f()>";
        String field = "<example.Keys: java.util.Map allKeys>";
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", "DF.bounded-map", "kind", "field_read",
                "transferKind", "HEAP_READ", "method", method,
                "fromCell", field, "toCell", method + "::$r0",
                "siteId", method + "#u1", "unitIndex", 1,
                "unit", "$r0 = r1.<example.Keys: java.util.Map allKeys>");
    }

    private File write(String name, Map<String, Object> row)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.singletonList(GSON.toJson(row)),
                StandardCharsets.UTF_8);
        return file;
    }

    @SafeVarargs
    private final File writeRows(String name, Map<String, Object>... rows)
            throws Exception {
        File file = new File(folder.getRoot(), name);
        java.util.List<String> encoded = new java.util.ArrayList<>();
        for (Map<String, Object> row : rows) encoded.add(GSON.toJson(row));
        Files.write(file.toPath(), encoded, StandardCharsets.UTF_8);
        return file;
    }

    private File writeEmpty(String name) throws Exception {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), Collections.emptyList(),
                StandardCharsets.UTF_8);
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
