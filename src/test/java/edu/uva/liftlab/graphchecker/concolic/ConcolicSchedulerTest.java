package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
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
    public void targetFirstModeRejectsPerGoalFilters() {
        try {
            ConcolicScheduler.Arguments.parse(new String[]{
                    "--region-plan", "plan.jsonl",
                    "--refined-graph", "refined.jsonl",
                    "--target-first",
                    "--goal-id", "GOAL.1"
            });
            fail("target-first and per-goal filters must be exclusive");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("--target-first"));
        }
    }

    @Test
    public void targetStructureCarrierIsNotAnInputAction() throws Exception {
        File regions = write("carrier-regions.jsonl", region());
        File plans = write("carrier-plans.jsonl", carrierTargetPlan());
        File edges = writeEmpty("carrier-edges.jsonl");
        File refined = write("carrier-refined.jsonl", refinedEdge());
        File output = folder.newFolder("carrier-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertFalse(hasInputAction(actions, "REGION.1.in.registry"));
    }

    @Test
    @SuppressWarnings("unchecked")
    public void exactAtomicReadFromProjectsPrimitiveTargetState()
            throws Exception {
        String symbol = "REGION.1.in.snapshotCount";
        String root = "<example.Manager: "
                + "java.util.concurrent.atomic.AtomicInteger count>";
        Map<String, Object> action = object(
                "symbol", symbol,
                "cell", "<example.Manager: int count()>#u1.fieldReceiver",
                "location", "HEAP_OBJECT_FIELD",
                "sourceKind", "ACTIVATION_FIELD_RECEIVER",
                "javaType", "java.util.concurrent.atomic.AtomicInteger",
                "observed", true,
                "dependencyRole", "CONCRETE_STRUCTURE_CARRIER",
                "fieldPath", Collections.singletonList("count"),
                "fieldPaths", Collections.singletonList(
                        Collections.singletonList("count")),
                "fieldPathDeclarations", Collections.singletonList(root),
                "runtimeAccesses", Collections.singletonList(object(
                        "eventSeq", 20,
                        "activationLocalStaticSiteOccurrence", 2)),
                "accessFieldSignature", root,
                "leafFieldSignature", root,
                "accessSites", Collections.singletonList(
                        "<example.Manager: int count()>#u1"));
        Map<String, Object> targetPlan = targetPlanWithActions(action);
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                targetPlan.get("closureGoals")).get(0);
        Map<String, Object> selectedEdge = object(
                "schemaVersion", 3,
                "edgeId", "EDGE.ATOMIC",
                "evidenceKind", "CONTAINER_MUTATION_READ_FROM_V1",
                "correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                "fromOccurrenceId", "REGION.P@test#call9",
                "toOccurrenceId", "REGION.1@test#call1",
                "fromOutputPort", "REGION.P.out.snapshotCount",
                "toInputPort", symbol,
                "receiverObjectId", 70,
                "valueObjectId", 71,
                "readerValueObjectId", 71,
                "writerFieldReadSeq", 10,
                "mutatorEnterSeq", 11,
                "mutationCompletionSeq", 12,
                "mutationInvocationId", 11,
                "mutatorDeclaredCallee",
                "<java.util.concurrent.atomic.AtomicInteger: "
                        + "int getAndDecrement()>",
                "writerEventSeq", 12,
                "readerEventSeq", 20,
                "writerLaneId", "lane.writer",
                "readerLaneId", "lane.reader",
                "programOrderRequired", false,
                "fieldPathDeclarations", Collections.singletonList(root));
        Map<String, Object> unrelatedEdge = GSON.fromJson(
                GSON.toJson(selectedEdge), Map.class);
        unrelatedEdge.put("edgeId", "EDGE.UNRELATED");
        goal.put("edgeBindings", java.util.Arrays.asList(
                selectedEdge, unrelatedEdge));

        File regions = write("atomic-target-regions.jsonl", region());
        File plans = write("atomic-target-plans.jsonl", targetPlan);
        File edges = writeEmpty("atomic-target-edges.jsonl");
        File refined = write("atomic-target-refined.jsonl", refinedEdge());
        File output = folder.newFolder("atomic-target-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                ConcolicScheduler.Arguments.parse(new String[]{
                        "--region-plan", runtimePlan(plans, edges,
                                regions).getPath(),
                        "--refined-graph", refined.getPath(),
                        "--output-dir", output.getPath(),
                        "--target-edge-ids", "EDGE.ATOMIC",
                        "--max-jobs", "16",
                        "--max-loop-iterations", "8"}));

        JsonObject projected = inputAction(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"), symbol);
        assertEquals("SYMBOLIC", projected.get("mode").getAsString());
        assertEquals("FIELD_ACCESS",
                projected.get("bindingMode").getAsString());
        assertEquals("int", projected.get("javaType").getAsString());
        assertEquals("EXACT_INCOMING_COMPOSITION",
                projected.get("symbolicDemand").getAsString());
        assertEquals("<java.util.concurrent.atomic.AtomicInteger: int value>",
                projected.get("leafFieldSignature").getAsString());
        assertEquals(2, projected.get("replayOccurrence").getAsInt());
        assertEquals("EDGE.ATOMIC",
                projected.get("selectedIncomingEdgeId").getAsString());
        assertEquals(java.util.Arrays.asList("count", "value"),
                GSON.fromJson(projected.get("fieldPath"), java.util.List.class));
        assertFalse(projected.has("fieldPaths"));
        assertFalse(projected.has("runtimeAccesses"));
        assertEquals(1, result.executionTasks.get(0)
                .getAsJsonArray("edgeBindings").size());
        assertEquals("REGION.1@test#call1", result.executionTasks.get(0)
                .get("occurrenceId").getAsString());
    }

    @Test
    public void loopControlOnlyInputIsNotAnInputAction() throws Exception {
        File regions = write("loop-input-regions.jsonl", region());
        File plans = write("loop-input-plans.jsonl", loopInputTargetPlan());
        File edges = writeEmpty("loop-input-edges.jsonl");
        File refined = write("loop-input-refined.jsonl", refinedEdge());
        File output = folder.newFolder("loop-input-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertFalse(hasInputAction(actions, "REGION.1.in.running"));
    }

    @Test
    public void unclosedReferenceBoundaryLeafIsNotAnInputAction()
            throws Exception {
        Map<String, Object> action = heapLeaf(
                "REGION.1.in.value", "example.Payload", "int", "value");
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

        assertFalse(hasInputAction(result.executionTasks.get(0)
                .getAsJsonArray("inputActions"), "REGION.1.in.value"));
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
        assertFalse(hasInputAction(actions, "REGION.1.in.payload"));
    }

    @Test
    public void protocolArgumentBecomesAnExactMethodArgument() throws Exception {
        Map<String, Object> plan = protocolArgumentTargetPlan();
        @SuppressWarnings("unchecked")
        Map<String, Object> action = ((java.util.List<Map<String, Object>>)
                ((java.util.List<Map<String, Object>>) plan.get(
                        "closureGoals")).get(0).get("symbolize")).get(0);
        action.put("replayOccurrence", 25);
        File regions = write("protocol-argument-regions.jsonl", region());
        File plans = write("protocol-argument-plans.jsonl", plan);
        File edges = writeEmpty("protocol-argument-edges.jsonl");
        File refined = write("protocol-argument-refined.jsonl",
                refinedEdge());
        File output = folder.newFolder("protocol-argument-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonObject scheduled = result.executionTasks.get(0)
                .getAsJsonArray("inputActions").get(0).getAsJsonObject();
        assertEquals("SYMBOLIC", scheduled.get("mode").getAsString());
        assertEquals("METHOD_ARGUMENT",
                scheduled.get("bindingMode").getAsString());
        assertEquals("<T: void decode(java.lang.String)>",
                scheduled.get("method").getAsString());
        assertEquals(0, scheduled.get("index").getAsInt());
        assertEquals("java.lang.String",
                scheduled.get("javaType").getAsString());
        assertEquals(25, scheduled.get("replayOccurrence").getAsInt());
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

        assertFalse(hasInputAction(result.executionTasks.get(0)
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
        assertFalse(hasInputAction(actions, "REGION.1.in.manager"));
        assertFalse(hasInputAction(actions,
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

        Map<String, Object> unrelatedMutationCount = heapLeaf(
                "REGION.1.in.count", "java.io.ByteArrayOutputStream",
                "int", "count");
        unrelatedMutationCount.put("symbolicDemand",
                "BOUNDED_STATE_FRONTIER");

        Map<String, Object> expiry = heapLeaf(
                "REGION.1.in.expiry", "example.Key", "long",
                "expiryDate");
        Map<String, Object> keyId = heapLeaf(
                "REGION.1.in.keyId", "example.Key", "int", "keyId");

        File regions = write("structure-regions.jsonl", region());
        File plans = write("structure-plans.jsonl", targetPlanWithActions(
                switchTable, ordinal, size, unrelatedMutationCount,
                expiry, keyId));
        File edges = writeEmpty("structure-edges.jsonl");
        File refined = write("structure-refined.jsonl", refinedEdge());
        File output = folder.newFolder("structure-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));
        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");

        assertFalse(hasInputAction(actions,
                "REGION.1.in.switchTable"));
        assertFalse(hasInputAction(actions, "REGION.1.in.ordinal"));
        assertFalse(hasInputAction(actions, "REGION.1.in.size"));
        assertFalse(hasInputAction(actions, "REGION.1.in.count"));
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
    public void schedulerComposesOnlySchemaThreeRuntimeFieldFlow() {
        Map<String, Object> binding = object(
                "schemaVersion", 3,
                "evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1",
                "fromOccurrenceId", "REGION.2@test#call2",
                "toOccurrenceId", "REGION.1@test#call1",
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
        Map<String, Object> row = new LinkedHashMap<>(binding);
        row.putAll(object(
                "schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW",
                "edgeId", "RF.1",
                "transportKind", "HEAP",
                "state", "CONFIRMED_RUNTIME_IDENTITY",
                "fromRegion", "REGION.2",
                "toRegion", "REGION.1"));
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
        assertEquals(8, LoopBoundPolicy.decode(
                result.executionTasks.get(0)).maxBackedgeTraversals());
    }

    @Test
    public void outputClosureRequiresPositiveSymbolicDemand() throws Exception {
        String method = "<T: void publish()>";
        File regions = write("positive-demand-regions.jsonl",
                positiveDemandOutputRegion());
        File plans = write("positive-demand-plans.jsonl",
                positiveDemandOutputPlan(method));
        File edges = writeEmpty("positive-demand-edges.jsonl");
        File refined = writeRows("positive-demand-refined.jsonl",
                refinedEdge(), transferEdgeInMethod("DF.enabled", method,
                        "<example.Owner: boolean enabled>",
                        method + "::$z0"));
        File output = folder.newFolder("positive-demand-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.enabled"));
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.keyId"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.count"));
        assertEquals("CONCRETE", mode(actions, "REGION.1.in.algorithm"));
        assertEquals("EXACT_EXPLORED_GUARD_DEPENDENCE", inputAction(
                actions, "REGION.1.in.enabled").get("symbolicDemand")
                .getAsString());
        assertEquals("EXACT_INCOMING_COMPOSITION", inputAction(
                actions, "REGION.1.in.keyId").get("symbolicDemand")
                .getAsString());
    }

    @Test
    public void outputCaptureAnchorIsPositiveSymbolicDemand()
            throws Exception {
        String method = "<T: void publish()>";
        Map<String, Object> plan = positiveDemandOutputPlan(method);
        @SuppressWarnings("unchecked")
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        @SuppressWarnings("unchecked")
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        @SuppressWarnings("unchecked")
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        @SuppressWarnings("unchecked")
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        slice.put("captureAnchorPort", "REGION.1.in.count");

        File regions = write("capture-anchor-regions.jsonl",
                positiveDemandOutputRegion());
        File plans = write("capture-anchor-plans.jsonl", plan);
        File edges = writeEmpty("capture-anchor-edges.jsonl");
        File refined = writeRows("capture-anchor-refined.jsonl",
                refinedEdge(), transferEdgeInMethod("DF.enabled", method,
                        "<example.Owner: boolean enabled>",
                        method + "::$z0"));
        File output = folder.newFolder("capture-anchor-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, output));

        JsonArray actions = result.executionTasks.get(0)
                .getAsJsonArray("inputActions");
        assertEquals("SYMBOLIC", mode(actions, "REGION.1.in.count"));
        assertEquals("EXACT_OUTPUT_CAPTURE_ANCHOR", inputAction(
                actions, "REGION.1.in.count").get("symbolicDemand")
                .getAsString());
        assertEquals("CONCRETE", mode(actions,
                "REGION.1.in.algorithm"));
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
        assertFalse(task.has("producerProjection"));
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
    @SuppressWarnings("unchecked")
    public void producerProjectionSelectsOneSharedRelationOccurrence()
            throws Exception {
        Map<String, Object> selected = projectableMultiOutputPlan();
        Map<String, Object> sibling = new LinkedHashMap<>(selected);
        sibling.put("occurrenceId", "REGION.1@test#call2");

        File regions = write("projected-occurrence-regions.jsonl",
                projectableOutputRegion());
        File plans = writeRows("projected-occurrence-plans.jsonl",
                selected, sibling);
        File edges = writeEmpty("projected-occurrence-edges.jsonl");
        File refined = write("projected-occurrence-refined.jsonl",
                refinedEdge());
        File projection = write("projected-occurrence.jsonl",
                producerProjection(Collections.singleton(
                        "REGION.1.out.keep"), Collections.singleton(
                        "EDGE.KEEP")));

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined,
                        folder.newFolder("projected-occurrence-schedule"),
                        projection));

        assertEquals(1, result.executionTasks.size());
        assertEquals("REGION.1@test#call1", result.executionTasks.get(0)
                .get("occurrenceId").getAsString());
    }

    @Test
    @SuppressWarnings("unchecked")
    public void producerProjectionAllowsExactIncomingDependencyEdge()
            throws Exception {
        Map<String, Object> plan = projectableMultiOutputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        ((Map<String, Object>) member.get("slice")).put("staticSites",
                Collections.singletonList("<T: void f(int,int)>#u9"));
        java.util.List<Map<String, Object>> bindings =
                new java.util.ArrayList<>((java.util.List<
                        Map<String, Object>>) goal.get("edgeBindings"));
        Map<String, Object> incoming = projectedEdge("EDGE.INCOMING",
                "REGION.P.out.value", "REGION.1.in.keep", 1);
        incoming.put("fromRegion", "REGION.P");
        incoming.put("fromOccurrenceId", "REGION.P@test#call7");
        bindings.add(incoming);
        goal.put("edgeBindings", bindings);

        java.util.Set<String> edgeIds = new java.util.LinkedHashSet<>();
        edgeIds.add("EDGE.KEEP");
        edgeIds.add("EDGE.INCOMING");
        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(
                        write("incoming-regions.jsonl",
                                projectableOutputRegion()),
                        write("incoming-plans.jsonl", plan),
                        writeEmpty("incoming-edges.jsonl"),
                        write("incoming-refined.jsonl", refinedEdge()),
                        folder.newFolder("incoming-schedule"),
                        write("incoming-projection.jsonl",
                                producerProjection(Collections.singleton(
                                        "REGION.1.out.keep"), edgeIds))));

        assertEquals(1, result.executionTasks.size());
        assertEquals("REGION.1@test#call1", result.executionTasks.get(0)
                .get("occurrenceId").getAsString());
    }

    @Test
    public void producerProjectionDeduplicatesEquivalentOccurrenceEdge()
            throws Exception {
        File regions = write("projected-duplicate-regions.jsonl",
                projectableOutputRegion());
        File plans = write("projected-duplicate-plans.jsonl",
                duplicateProjectedEdgePlan(false));
        File edges = writeEmpty("projected-duplicate-edges.jsonl");
        File refined = write("projected-duplicate-refined.jsonl",
                refinedEdge());
        File projection = write("projected-duplicate-projection.jsonl",
                producerProjection(Collections.singleton(
                        "REGION.1.out.keep"), Collections.singleton(
                        "EDGE.KEEP")));

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined,
                        folder.newFolder("projected-duplicate-schedule"),
                        projection));

        assertEquals(1, result.executionTasks.get(0)
                .getAsJsonArray("edgeBindings").size());
    }

    @Test
    public void producerProjectionRejectsConflictingDuplicateEdge()
            throws Exception {
        File regions = write("projected-conflict-regions.jsonl",
                projectableOutputRegion());
        File plans = write("projected-conflict-plans.jsonl",
                duplicateProjectedEdgePlan(true));
        File edges = writeEmpty("projected-conflict-edges.jsonl");
        File refined = write("projected-conflict-refined.jsonl",
                refinedEdge());
        File projection = write("projected-conflict-projection.jsonl",
                producerProjection(Collections.singleton(
                        "REGION.1.out.keep"), Collections.singleton(
                        "EDGE.KEEP")));

        try {
            ConcolicScheduler.schedule(arguments(regions, plans, edges,
                    refined, folder.newFolder(
                            "projected-conflict-schedule"), projection));
            fail("different occurrence projections for one edge must fail");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "unique nonempty ids"));
        }
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
    public void explicitFaultReturnKeepsItsExactStaticCallsite() {
        JsonObject action = new JsonObject();
        action.addProperty("sourceKind", "EXPLICIT_SYMBOLIC_FAULT");
        action.addProperty("callerMethod", "<example.Root: void run()>");
        action.addProperty("unitIndex", 8);
        JsonArray sites = new JsonArray();
        for (int unit : new int[]{3, 8}) {
            JsonObject site = new JsonObject();
            site.addProperty("method", "<example.Root: void run()>");
            site.addProperty("unitIndex", unit);
            site.addProperty("local", unit == 3 ? "first" : "second");
            sites.add(site);
        }

        JsonArray exact = ConcolicScheduler.exactExplicitFaultReturnSite(
                action, sites);

        assertEquals(1, exact.size());
        assertEquals(8, exact.get(0).getAsJsonObject()
                .get("unitIndex").getAsInt());
        assertEquals("second", exact.get(0).getAsJsonObject()
                .get("local").getAsString());
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

    @Test
    public void schedulerCarriesExactSingleWriterMemberTimeline()
            throws Exception {
        File regions = write("timeline-regions.jsonl", timelineRegion());
        File plans = write("timeline-plans.jsonl", timelinePlan(2));
        File edges = writeEmpty("timeline-edges.jsonl");
        File refined = write("timeline-refined.jsonl", refinedEdge());
        File scheduled = folder.newFolder("timeline-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, scheduled));

        JsonObject step = result.executionTasks.get(0)
                .getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice")
                .getAsJsonObject("boundedContainerTimelineStep");
        assertTrue(String.valueOf(step), step != null
                && step.has("admission"));
        assertEquals("PROVED", step.get("admission").getAsString());
        assertEquals("ENGINE_STATE_CHAIN_BOUND_V1",
                step.get("boundAuthority").getAsString());
        assertEquals(LoopBoundPolicy.MAX_STATE_TIMELINE_TRANSITIONS,
                step.get("stateChainBound").getAsInt());
        assertEquals("ONE_DEFINITION_INVOCATION",
                step.get("transitionGranularity").getAsString());
        assertEquals("REGION.1.in.demanded",
                step.get("preStatePort").getAsString());
        assertEquals("REGION.1.out.value",
                step.get("postStatePort").getAsString());
        assertEquals("MEMBER.1", step.get("memberToken").getAsString());
        assertEquals(2, step.getAsJsonArray("memberProjections").size());
        assertFalse(step.toString().contains("fieldEventSeq"));
    }

    @Test
    public void schedulerKeepsSingleReaderMutationAsOneShotRelation()
            throws Exception {
        File regions = write("one-shot-regions.jsonl", timelineRegion());
        File plans = write("one-shot-plans.jsonl", timelinePlan(1));
        File edges = writeEmpty("one-shot-edges.jsonl");
        File refined = write("one-shot-refined.jsonl", refinedEdge());
        File scheduled = folder.newFolder("one-shot-schedule");

        ConcolicScheduler.Result result = ConcolicScheduler.schedule(
                arguments(regions, plans, edges, refined, scheduled));

        JsonObject slice = result.executionTasks.get(0)
                .getAsJsonObject("outputClosure")
                .getAsJsonArray("members").get(0).getAsJsonObject()
                .getAsJsonObject("slice");
        assertFalse(slice.has("boundedContainerTimelineStep"));

        File timelinePlans = write("one-shot-id-timeline-plans.jsonl",
                timelinePlan(2));
        File timelineScheduled = folder.newFolder(
                "one-shot-id-timeline-schedule");
        ConcolicScheduler.Result timeline = ConcolicScheduler.schedule(
                arguments(regions, timelinePlans, edges, refined,
                        timelineScheduled));
        assertFalse(result.executionTasks.get(0).get("taskId").getAsString()
                .equals(timeline.executionTasks.get(0)
                        .get("taskId").getAsString()));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> timelineRegion() {
        Map<String, Object> region = outputRegion();
        Map<String, Object> pre = ((java.util.List<Map<String, Object>>)
                region.get("symbolicInputs")).get(0);
        Map<String, Object> post = ((java.util.List<Map<String, Object>>)
                region.get("outputs")).get(0);
        Map<String, Object> preProjection = memberProjection("PRE_STATE");
        Map<String, Object> postProjection = memberProjection("POST_STATE");
        pre.put("boundedContainerMemberProjections",
                Collections.singletonList(preProjection));
        post.put("boundedContainerStateRole", "MUTATION_POST_STATE");
        post.put("boundedContainerMemberProjectionAdmission", "PROVED");
        post.put("containerTimelineWriterPolicy",
                "SINGLE_WRITER_REQUIRED");
        post.put("boundedContainerPreStatePorts",
                Collections.singletonList("REGION.1.in.demanded"));
        post.put("boundedContainerMemberProjections",
                Collections.singletonList(postProjection));
        post.put("runtimeAccesses", Collections.singletonList(object(
                "eventSeq", 20,
                "boundedContainerMemberProjection", postProjection)));
        return region;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> timelinePlan(int readerCount) {
        Map<String, Object> plan = boundedMapFieldOutputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                plan.get("closureGoals")).get(0);
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> output = (Map<String, Object>) member.get(
                "output");
        Map<String, Object> slice = (Map<String, Object>) member.get(
                "slice");
        output.put("kind", "HEAP_STATE");
        output.put("javaTypeDescriptor", "Ljava/util/Map;");
        slice.put("containerPreStatePort", "REGION.1.in.demanded");
        slice.put("selectedRuntimeEventSeq", 20);
        slice.put("outputBoundaryKind",
                "DEFINITION_INVOCATION_NORMAL_EXIT");
        slice.put("containerPreStateAuthority",
                "EARLIEST_READ_IN_EXACT_DEFINITION_INVOCATION_V1");
        slice.put("observedDefinitionCallId", 4);
        slice.put("containerPreStateEventSeq", 10);
        slice.put("definitionCompletionSeq", 21);
        slice.put("foldedMutationCount", 1);
        slice.put("foldedMutationCompletionSeqs",
                Collections.singletonList(20));

        java.util.List<Map<String, Object>> causalEdges =
                new java.util.ArrayList<>();
        java.util.List<String> causalEdgeIds = new java.util.ArrayList<>();
        for (int index = 0; index < readerCount; index++) {
            String edgeId = "EDGE.TIMELINE." + index;
            Map<String, Object> edge = projectedEdge(edgeId,
                    "REGION.1.out.value",
                    "REGION.T.in.reader" + index, 30 + index * 10L);
            edge.put("toOccurrenceId",
                    "REGION.T@test#call" + (index + 1));
            causalEdges.add(edge);
            causalEdgeIds.add(edgeId);
        }
        slice.put("causalEdgeIds", causalEdgeIds);
        goal.put("edgeBindings", causalEdges);
        return plan;
    }

    private static Map<String, Object> memberProjection(String role) {
        return object(
                "memberToken", "MEMBER.1",
                "identityAuthority",
                "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1",
                "containerObjectId", 99,
                "keyObjectId", 100,
                "valueObjectId", 101,
                "mutationInvocationId", 5,
                "writerLaneId", "lane.writer",
                "stateRole", role,
                "leaves", java.util.Arrays.asList(
                        object("kind", "PRESENT", "javaType", "boolean"),
                        object("kind", "VALUE_FIELD", "javaType", "int",
                                "field", "<example.Key: int keyId>",
                                "fieldEventSeq", 6),
                        object("kind", "VALUE_FIELD", "javaType", "long",
                                "field", "<example.Key: long expiry>",
                                "fieldEventSeq", 7)));
    }

    private ConcolicScheduler.Arguments arguments(
            File regions, File plans, File edges, File graph, File output) {
        try {
            return ConcolicScheduler.Arguments.parse(new String[]{
                "--region-plan", runtimePlan(plans, edges,
                        regions).getPath(),
                "--refined-graph", graph.getPath(),
                "--output-dir", output.getPath(),
                "--max-jobs", "16",
                "--max-loop-iterations", "8"
            });
        } catch (Exception failure) {
            throw new IllegalArgumentException(failure.getMessage(), failure);
        }
    }

    private ConcolicScheduler.Arguments arguments(
            File regions, File plans, File edges, File graph, File output,
            File projection) {
        try {
            return ConcolicScheduler.Arguments.parse(new String[]{
                "--region-plan", runtimePlan(plans, edges,
                        regions).getPath(),
                "--refined-graph", graph.getPath(),
                "--producer-projection", projection.getPath(),
                "--output-dir", output.getPath(),
                "--max-jobs", "16",
                "--max-loop-iterations", "8"
            });
        } catch (Exception failure) {
            throw new IllegalArgumentException(failure.getMessage(), failure);
        }
    }

    private File runtimePlan(File plans, File ignoredEdges, File regionsFile)
            throws Exception {
        java.util.List<JsonObject> source = ArtifactIO.readJsonl(
                plans.toPath());
        if (!source.isEmpty() && RuntimePlanArtifact.CATALOG_KIND.equals(
                source.get(0).has("kind")
                        ? source.get(0).get("kind").getAsString() : "")) {
            return plans;
        }
        java.util.Map<String, JsonObject> edges = new LinkedHashMap<>();
        java.util.List<JsonObject> conflictingEdges =
                new java.util.ArrayList<>();
        java.util.List<JsonObject> compact = new java.util.ArrayList<>();
        for (JsonObject plan : source) {
            for (JsonElement goalElement : plan.getAsJsonArray(
                    "closureGoals")) {
                JsonObject goal = goalElement.getAsJsonObject();
                for (JsonElement bindingElement : goal.getAsJsonArray(
                        "edgeBindings")) {
                    JsonObject binding = bindingElement.getAsJsonObject();
                    String edgeId = binding.get("edgeId").getAsString();
                    JsonObject edge = edges.get(edgeId);
                    if (edge == null) {
                        edge = binding.deepCopy();
                        edges.put(edgeId, edge);
                    } else if (!edge.equals(binding)) {
                        conflictingEdges.add(binding.deepCopy());
                    }
                }
            }
            compact.add(plan);
        }
        java.util.List<JsonObject> catalog =
                new java.util.ArrayList<>(edges.values());
        catalog.addAll(conflictingEdges);
        Files.write(plans.toPath(), RuntimePlanArtifact.encode(compact,
                catalog, ArtifactIO.readJsonl(regionsFile.toPath()))
                .getBytes(StandardCharsets.UTF_8));
        return plans;
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

    private static Map<String, Object> positiveDemandOutputRegion() {
        return object("schemaVersion", 3, "kind", "SYMBOLIC_REGION",
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "regionId", "REGION.1",
                "symbolicInputs", java.util.Arrays.asList(
                        port("REGION.1.in.enabled", "enabled"),
                        port("REGION.1.in.keyId", "keyId"),
                        port("REGION.1.in.count", "count"),
                        port("REGION.1.in.algorithm", "algorithm")),
                "outputs", Collections.singletonList(
                        port("REGION.1.out.value", "result")));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> positiveDemandOutputPlan(
            String method) {
        Map<String, Object> result = outputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        goal.put("runtimeDefinitionMethods",
                Collections.singletonList(method));
        goal.put("symbolize", java.util.Arrays.asList(
                heapLeaf("REGION.1.in.enabled", "example.Owner",
                        "boolean", "enabled"),
                heapLeaf("REGION.1.in.keyId", "example.Key", "int",
                        "keyId"),
                heapLeaf("REGION.1.in.count",
                        "java.io.ByteArrayOutputStream", "int", "count"),
                heapLeaf("REGION.1.in.algorithm", "example.Config",
                        "java.lang.String", "algorithm")));
        goal.put("branches", Collections.singletonList(object(
                "siteId", method + "#u2", "policy", "EXPLORE",
                "operandCells", Collections.singletonList(
                        method + "::$z0"))));
        goal.put("edgeBindings", Collections.singletonList(object(
                "schemaVersion", 3,
                "edgeId", "EDGE.KEY",
                "evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1",
                "correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1",
                "fromOccurrenceId", "REGION.2@test#call2",
                "toOccurrenceId", "REGION.1@test#call1",
                "fromOutputPort", "REGION.2.out.keyId",
                "toInputPort", "REGION.1.in.keyId",
                "receiverObjectId", 77,
                "writerLaneId", "lane.writer",
                "readerLaneId", "lane.reader",
                "programOrderRequired", false,
                "writerEventSeq", 5,
                "readerEventSeq", 6)));
        Map<String, Object> closure = (Map<String, Object>) goal.get(
                "outputClosure");
        Map<String, Object> member = ((java.util.List<Map<String, Object>>)
                closure.get("members")).get(0);
        Map<String, Object> slice = (Map<String, Object>) member.get("slice");
        slice.put("inputPorts", java.util.Arrays.asList(
                "REGION.1.in.enabled", "REGION.1.in.keyId",
                "REGION.1.in.count", "REGION.1.in.algorithm"));
        slice.put("methods", Collections.singletonList(method));
        result.put("rootSelector", object("kind", "GLOBAL_INVOCATION",
                "method", method, "ordinal", 1));
        result.put("targetMethod", method);
        return result;
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
                "sourceKey", "TEST_DRIVER/test#epoch0",
                "occurrenceId", "REGION.1@test#call1",
                "relationKey", "REL.REGION.1",
                "relationContractHash", "CONTRACT.TEST",
                "regionId", "REGION.1",
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
                "fromOccurrenceId", "REGION.P@test#call9",
                "toOccurrenceId", "REGION.1@test#call1",
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
                "schemaVersion", 3,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("relationKey", "REL.REGION.1",
                        "regionId", "REGION.1",
                        "contractHash", "CONTRACT.TEST"),
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
                "sourceKey", "TEST_DRIVER/test#epoch0",
                "occurrenceId", "REGION.1@test#call1",
                "relationKey", "REL.REGION.1",
                "relationContractHash", "CONTRACT.TEST",
                "regionId", "REGION.1",
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
                "schemaVersion", 3,
                "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("relationKey", "REL.REGION.1",
                        "regionId", "REGION.1",
                        "contractHash", "CONTRACT.TEST"),
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
                "sourceKey", "TEST_DRIVER/test#epoch0",
                "occurrenceId", "REGION.1@test#call1",
                "relationKey", "REL.REGION.1",
                "relationContractHash", "CONTRACT.TEST",
                "regionId", "REGION.1",
                "rootSelector", object("kind", "GLOBAL_INVOCATION",
                        "method", method, "ordinal", 1),
                "closureGoals", Collections.singletonList(goal));
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> duplicateProjectedEdgePlan(
            boolean conflict) {
        Map<String, Object> result = projectableMultiOutputPlan();
        Map<String, Object> goal = ((java.util.List<Map<String, Object>>)
                result.get("closureGoals")).get(0);
        java.util.List<Map<String, Object>> original =
                (java.util.List<Map<String, Object>>) goal.get(
                        "edgeBindings");
        Map<String, Object> duplicate = new java.util.LinkedHashMap<>(
                original.get(0));
        if (conflict) duplicate.put("mappingId", "rpc.conflict");
        java.util.List<Map<String, Object>> bindings =
                new java.util.ArrayList<>();
        bindings.add(original.get(0));
        bindings.add(duplicate);
        bindings.add(original.get(1));
        goal.put("edgeBindings", bindings);
        return result;
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
                "fromOccurrenceId", "REGION.1@test#call1",
                "toOccurrenceId", "REGION.T@test#call9",
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
                "CAMPAIGN.1", "REGION.1", "REL.REGION.1",
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
                "schemaVersion", 3, "kind", "OUTPUT_CLOSURE_CONTRACT",
                "producer", object("relationKey", "REL.REGION.1",
                        "regionId", "REGION.1",
                        "contractHash", "CONTRACT.TEST"),
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
                "sourceKey", "TEST_DRIVER/test#epoch0",
                "occurrenceId", "REGION.1@test#call1",
                "relationKey", "REL.REGION.1",
                "relationContractHash", "CONTRACT.TEST",
                "regionId", "REGION.1",
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

    private static boolean hasInputAction(JsonArray actions,
                                          String symbol) {
        for (JsonElement element : actions) {
            JsonObject action = element.getAsJsonObject();
            if (symbol.equals(action.get("symbol").getAsString())) {
                return true;
            }
        }
        return false;
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
        return transferEdgeInMethod(id, "<T: void f()>", fromCell,
                toCell);
    }

    private static Map<String, Object> transferEdgeInMethod(
            String id, String method, String fromCell, String toCell) {
        return object("schemaVersion", 3, "refinementSchemaVersion", 1,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "id", id, "kind", "field_read",
                "transferKind", "HEAP_READ", "method", method,
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
