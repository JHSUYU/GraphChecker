package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {
    @Test
    public void outputCaptureFlipsLatestBranchAndDropsOldSuffix() {
        JsonObject summary = summary("ACT.NEW",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject executionTask = executionTask("ACT.NEW",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject targetSummary = summary("ACT.TARGET",
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        JsonObject targetTask = executionTask("ACT.TARGET",
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        targetSummary.remove("outputClosure");
        targetTask.remove("outputClosure");
        int targetIndex = 0;
        for (com.google.gson.JsonElement element
                : targetSummary.getAsJsonArray("branchMappings")) {
            JsonObject site = element.getAsJsonObject()
                    .getAsJsonObject("witness").getAsJsonObject("site");
            site.addProperty("siteId", "SITE#u" + targetIndex++);
            site.addProperty("method", "SITE");
        }

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(executionTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(2, result.tasks.size());
        JsonObject latest = result.tasks.get(0);
        BranchReplayContract replay = replayContract(latest);
        assertEquals("SITE.1", replay.source().siteId());
        assertEquals(1, replay.orderedPrefix().size());
        assertEquals(2, replay.requiredPathPredicates().size());
        assertEquals(">=", replay.requiredSatisfiedPredicate()
                .getAsJsonObject().get("_op").getAsString());
        assertEquals(BranchReplayContract.SCHEMA_VERSION,
                latest.getAsJsonObject("replayContract")
                        .get("schemaVersion").getAsInt());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertFalse(result.manifest.has("observedPathCount"));
        assertTrue(result.relations.isEmpty());

        RegionPathWorklist.Result bounded = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(executionTask),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(2, 32, 256));
        assertEquals(1, bounded.tasks.size());
        assertTrue(bounded.manifest.getAsJsonArray("gaps").isEmpty());

        JsonArray targetBranches = new JsonArray();
        for (String site : Arrays.asList("SITE#u0", "SITE#u1")) {
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", site);
            branch.addProperty("policy", "EXPLORE");
            targetBranches.add(branch);
        }
        JsonObject helperBranch = new JsonObject();
        helperBranch.addProperty("siteId", "HELPER#u0");
        helperBranch.addProperty("policy", "EXPLORE");
        targetBranches.add(helperBranch);
        targetTask.addProperty("targetMethod", "SITE");
        targetTask.add("branches", targetBranches);
        RegionPathWorklist.Result targetResult = RegionPathWorklist.plan(
                Collections.singletonList(targetSummary),
                Collections.singletonList(targetTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, targetResult.tasks.size());
        for (JsonObject task : targetResult.tasks) {
            assertEquals("TARGET_REACH_CLOSURE",
                    task.get("goalKind").getAsString());
            assertFalse(task.has("outputClosure"));
        }
        assertTrue(targetResult.relations.isEmpty());
        assertEquals("TARGET_REACH_CLOSURE",
                targetResult.manifest.get("goalKind").getAsString());
    }

    @Test
    public void completeEmptyOutputSliceDoesNotBecomeWildcard() {
        JsonObject summary = summary("ACT.EMPTY.SLICE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject executionTask = executionTask(
                "ACT.EMPTY.SLICE", ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.EMPTY");
        attachClosure(summary, closure);
        attachClosure(executionTask, closure);
        summary.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", binary("+", 1));
        String[] evidenceFields = new String[]{
                "vmIntrinsicPlaceholderBindings",
                "unforcedEnvironmentValidationRequirements"};
        for (String field : evidenceFields) {
            JsonObject marker = new JsonObject();
            marker.addProperty("evidenceField", field);
            JsonArray evidence = new JsonArray();
            evidence.add(marker);
            summary.add(field, evidence);
        }
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE.TEST");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        summary.add("edgeBindings", bindings);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(executionTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
        assertEquals(1, result.relations.size());
        JsonObject merged = result.relations.get(0);
        assertEquals("CONCOLIC_REGION_SUMMARY",
                merged.get("kind").getAsString());
        assertTrue(merged.get("relationallyComplete").getAsBoolean());
        assertEquals("GUARDED_PATH_MERGE", merged.getAsJsonObject(
                "regionRelation").get("kind").getAsString());
        JsonObject pathCase = merged.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").get(0).getAsJsonObject();
        assertEquals("TASK.ACT.EMPTY.SLICE",
                pathCase.get("sourceTaskId").getAsString());
        for (String field : evidenceFields) {
            assertEquals(summary.getAsJsonArray(field),
                    pathCase.getAsJsonArray(field));
        }
        assertEquals(bindings, merged.getAsJsonArray("edgeBindings"));
        assertEquals(OutputClosureCodec.decode(summary).closureFingerprint(),
                OutputClosureCodec.decode(merged).closureFingerprint());

        JsonObject targetSummary = summary("ACT.CLOSED.TARGET",
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        JsonObject targetTask = executionTask("ACT.CLOSED.TARGET",
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        targetSummary.remove("outputClosure");
        targetTask.remove("outputClosure");
        targetSummary.add("branchMappings", new JsonArray());
        targetTask.add("branches", new JsonArray());
        RegionPathWorklist.Result target = RegionPathWorklist.plan(
                Collections.singletonList(targetSummary),
                Collections.singletonList(targetTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                target.manifest.get("state").getAsString());
        assertTrue(target.relations.isEmpty());
    }

    @Test
    public void closedJointRelationRequiresEveryOutputExpression() {
        JsonObject summary = summary("ACT.JOINT",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.JOINT");
        JsonObject second = closure.getAsJsonArray("members").get(0)
                .getAsJsonObject().deepCopy();
        second.getAsJsonObject("output").addProperty(
                "portId", "REGION.3.out.1");
        second.getAsJsonObject("output").addProperty(
                "cell", "<P: int y>");
        second.getAsJsonObject("slice").addProperty(
                "outputPort", "REGION.3.out.1");
        second.getAsJsonObject("slice").addProperty(
                "outputCell", "<P: int y>");
        closure.getAsJsonArray("members").add(second);
        for (int index = 0; index < 2; index++) {
            JsonObject member = closure.getAsJsonArray("members").get(index)
                    .getAsJsonObject();
            String port = member.getAsJsonObject("output")
                    .get("portId").getAsString();
            String cell = member.getAsJsonObject("output")
                    .get("cell").getAsString();
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId",
                    "CAPTURE.JOINT.EXIT." + index);
            capture.addProperty("outputPort", port);
            capture.addProperty("outputCell", cell);
            capture.addProperty("accessRootInputPort", "REGION.3.in.0");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add(index == 0 ? "x" : "y");
            capture.add("fieldPath", fieldPath);
            capture.addProperty("fieldSignature", cell);
            capture.addProperty("javaType", "int");
            JsonArray captures = new JsonArray();
            captures.add(capture);
            member.getAsJsonObject("slice").add(
                    "captureBindings", captures);
        }
        attachClosure(summary, closure);
        summary.add("branchMappings", new JsonArray());
        summary.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.0", binary("+", 1));

        RegionPathWorklist.Result incomplete = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                incomplete.manifest.get("state").getAsString());
        assertTrue(incomplete.relations.isEmpty());
        assertTrue(incomplete.manifest.getAsJsonArray("gaps").toString()
                .contains("JOINT_OUTPUT_EXPRESSION_SET_MISMATCH"));

        summary.getAsJsonObject("outputExpressions").add(
                "REGION.3.out.1", binary("-", 1));
        RegionPathWorklist.Result complete = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                complete.manifest.get("state").getAsString());
        assertEquals(1, complete.relations.size());
        assertEquals(2, complete.relations.get(0)
                .getAsJsonObject("regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject().getAsJsonObject(
                        "outputExpressions").size());
    }

    @Test
    public void explicitClosureScopesBranchTasksAndManifest() {
        JsonObject summary = summary("ACT.CLOSURE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject executionTask = executionTask("ACT.CLOSURE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(executionTask, closure);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(executionTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject task = result.tasks.get(0);
        assertEquals("SITE.1", sourceSite(task));
        assertTrue(task.has("outputClosure"));
        assertFalse(task.has("requestedOutput"));
        assertEquals("REGION.3@test#call7",
                OutputClosureCodec.decodeEnvelope(task.getAsJsonObject(
                        "outputClosure")).producer()
                        .regionInstanceId());
        assertEquals(7, OutputClosureCodec.decodeEnvelope(
                task.getAsJsonObject("outputClosure")).producer()
                .rootCallId());
        assertEquals(OutputClosureCodec.decodeEnvelope(
                        task.getAsJsonObject("outputClosure")).demandKey(),
                OutputClosureCodec.decode(result.manifest).demandKey());
        assertEquals(OutputClosureCodec.decodeEnvelope(
                        task.getAsJsonObject("outputClosure"))
                        .closureFingerprint(),
                OutputClosureCodec.decode(result.manifest)
                        .closureFingerprint());
        assertFalse(task.has("outputDemandKey"));
        assertFalse(task.has("outputClosureFingerprint"));

        JsonObject boundedLoop = summary("ACT.LOOP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject boundedLoopTask = executionTask("ACT.LOOP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject loopClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.LOOP", "SITE.1");
        attachClosure(boundedLoop, loopClosure);
        attachClosure(boundedLoopTask, loopClosure);
        boundedLoop.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                "SITE.1", "<test.Region: void run()>", 1,
                                4, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());
        RegionPathWorklist.Result loopResult = RegionPathWorklist.plan(
                Collections.singletonList(boundedLoop),
                Collections.singletonList(boundedLoopTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(loopResult.manifest.toString(),
                RegionPathWorklist.State.PENDING.name(),
                loopResult.manifest.get("state").getAsString());
        assertTrue(loopResult.manifest.getAsJsonArray("gaps").isEmpty());
        assertEquals(1, loopResult.manifest.getAsJsonArray(
                "deferredObservations").size());

        JsonObject legacySummary = summary("ACT.CLOSURE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        legacySummary.remove("outputClosure");
        boolean rejected = false;
        try {
            RegionPathWorklist.plan(
                    Collections.singletonList(legacySummary),
                    Collections.singletonList(executionTask),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults());
        } catch (IllegalArgumentException expected) {
            rejected = expected.getMessage().contains(
                    "canonical outputClosure is required");
        }
        assertTrue("legacy summary must not inherit joint task scope",
                rejected);
    }

    @Test
    public void closureDemandAndProofCannotReuseTerminalFlipRecord() {
        JsonObject firstSummary = summary("ACT.CLOSURE.A",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject firstTask = executionTask("ACT.CLOSURE.A",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject firstClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(firstSummary, firstClosure);
        attachClosure(firstTask, firstClosure);
        RegionPathWorklist.Result first = RegionPathWorklist.plan(
                Collections.singletonList(firstSummary),
                Collections.singletonList(firstTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        JsonObject secondSummary = summary("ACT.CLOSURE.B",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject secondTask = executionTask("ACT.CLOSURE.B",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject secondClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.B", "SITE.1");
        attachClosure(secondSummary, secondClosure);
        attachClosure(secondTask, secondClosure);
        RegionPathWorklist.Result second = RegionPathWorklist.plan(
                Collections.singletonList(secondSummary),
                Collections.singletonList(secondTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(OutputClosureCodec.decodeEnvelope(first.tasks.get(0)
                        .getAsJsonObject("outputClosure"))
                        .demandKey(),
                OutputClosureCodec.decodeEnvelope(second.tasks.get(0)
                        .getAsJsonObject("outputClosure"))
                        .demandKey());
        assertNotEquals(first.tasks.get(0).get("queryKey"),
                second.tasks.get(0).get("queryKey"));
        JsonObject record = new JsonObject();
        record.addProperty("queryKey", first.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status", "UNSAT");
        RegionPathWorklist.Result replay = RegionPathWorklist.plan(
                Collections.singletonList(secondSummary),
                Collections.singletonList(secondTask),
                Collections.singletonList(record),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(1, replay.tasks.size());

        JsonObject otherDemandSummary = summary("ACT.CLOSURE.C",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject otherDemandTask = executionTask("ACT.CLOSURE.C",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject otherDemand = outputClosure("REGION.3.out.1",
                "<P: int y>", "PROOF.A", "SITE.1");
        attachClosure(otherDemandSummary, otherDemand);
        attachClosure(otherDemandTask, otherDemand);
        RegionPathWorklist.Result third = RegionPathWorklist.plan(
                Collections.singletonList(otherDemandSummary),
                Collections.singletonList(otherDemandTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertNotEquals(OutputClosureCodec.decodeEnvelope(first.tasks.get(0)
                        .getAsJsonObject("outputClosure"))
                        .demandKey(),
                OutputClosureCodec.decodeEnvelope(third.tasks.get(0)
                        .getAsJsonObject("outputClosure"))
                        .demandKey());
        assertNotEquals(first.tasks.get(0).get("queryKey"),
                third.tasks.get(0).get("queryKey"));
    }

    @Test
    public void concreteBranchWaitsForBridgeAndRequiresExactOccurrence() {
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int result>", "PROOF.DEFERRED",
                "SITE.0", "SITE.1", "SITE.LATE");
        JsonObject concrete = summary("ACT.CONCRETE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject concreteTask = executionTask("ACT.CONCRETE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        attachClosure(concrete, closure);
        attachClosure(concreteTask, closure);
        concrete.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                "SITE.LATE", "<test.Region: void run()>", 9,
                                2, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());

        RegionPathWorklist.Result bridgePending = RegionPathWorklist.plan(
                Collections.singletonList(concrete),
                Collections.singletonList(concreteTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                bridgePending.manifest.get("state").getAsString());
        assertFalse(bridgePending.tasks.isEmpty());
        assertTrue(bridgePending.manifest.getAsJsonArray("gaps").isEmpty());
        assertEquals(1, bridgePending.manifest.getAsJsonArray(
                "deferredObservations").size());

        List<JsonObject> exhaustedRecords = new ArrayList<>();
        for (JsonObject task : bridgePending.tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey",
                    task.get("queryKey").getAsString());
            record.addProperty("status", "UNSAT");
            exhaustedRecords.add(record);
        }
        RegionPathWorklist.Result exhausted = RegionPathWorklist.plan(
                Collections.singletonList(concrete),
                Collections.singletonList(concreteTask),
                exhaustedRecords, RegionPathWorklist.Bounds.defaults());
        assertTrue(exhausted.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                exhausted.manifest.get("state").getAsString());
        assertTrue(exhausted.relations.isEmpty());
        assertTrue(exhausted.manifest.getAsJsonArray("gaps").toString()
                .contains("SITE.LATE"));
        assertFalse(exhausted.manifest.has("deferredObservations"));

        JsonObject wrongOccurrence = summary("ACT.WRONG.OCCURRENCE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject wrongTask = executionTask("ACT.WRONG.OCCURRENCE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        shareGoal(concrete, wrongOccurrence, wrongTask);
        attachClosure(wrongOccurrence, closure);
        attachClosure(wrongTask, closure);
        addWitness(wrongOccurrence, "SITE.LATE", 1,
                nestedFieldPredicate(99));
        RegionPathWorklist.Result stillDeferred = RegionPathWorklist.plan(
                Arrays.asList(concrete, wrongOccurrence),
                Arrays.asList(concreteTask, wrongTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                stillDeferred.manifest.get("state").getAsString());
        assertEquals(1, stillDeferred.manifest.getAsJsonArray(
                "deferredObservations").size());

        JsonObject exactOccurrence = summary("ACT.EXACT.OCCURRENCE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject exactTask = executionTask("ACT.EXACT.OCCURRENCE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        shareGoal(concrete, exactOccurrence, exactTask);
        attachClosure(exactOccurrence, closure);
        attachClosure(exactTask, closure);
        addWitness(exactOccurrence, "SITE.LATE", 2,
                nestedFieldPredicate(100));
        RegionPathWorklist.Result witnessed = RegionPathWorklist.plan(
                Arrays.asList(concrete, wrongOccurrence, exactOccurrence),
                Arrays.asList(concreteTask, wrongTask,
                        exactTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                witnessed.manifest.get("state").getAsString());
        assertTrue(witnessed.manifest.getAsJsonArray("gaps").isEmpty());
        assertFalse(witnessed.manifest.has("deferredObservations"));
    }

    @Test
    public void concreteLoopGuardClosesOnlyWithStaticNoInputProof() {
        JsonObject concreteLoop = summary("ACT.CONCRETE.LOOP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject concreteTask = executionTask("ACT.CONCRETE.LOOP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject concreteClosure = branchDependencyClosure(false,
                "PROOF.CONCRETE.LOOP");
        attachClosure(concreteLoop, concreteClosure);
        attachClosure(concreteTask, concreteClosure);
        addConcreteObservation(concreteLoop, "SITE.LOOP");
        addConcreteObservation(concreteLoop, "SITE.RUNTIME.ONLY");

        RegionPathWorklist.Result pending = RegionPathWorklist.plan(
                Collections.singletonList(concreteLoop),
                Collections.singletonList(concreteTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                pending.manifest.get("state").getAsString());
        assertFalse(pending.manifest.has("deferredObservations"));

        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Collections.singletonList(concreteLoop),
                Collections.singletonList(concreteTask),
                terminalRecords(pending.tasks),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(closed.manifest.toString(),
                RegionPathWorklist.State.CLOSED.name(),
                closed.manifest.get("state").getAsString());
        assertTrue(closed.manifest.getAsJsonArray("gaps").isEmpty());

        JsonObject missingSymbolic = summary("ACT.MISSING.SYMBOLIC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject missingSymbolicTask = executionTask(
                "ACT.MISSING.SYMBOLIC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject symbolicClosure = branchDependencyClosure(true,
                "PROOF.MISSING.SYMBOLIC");
        attachClosure(missingSymbolic, symbolicClosure);
        attachClosure(missingSymbolicTask, symbolicClosure);
        addConcreteObservation(missingSymbolic, "SITE.LOOP");
        RegionPathWorklist.Result symbolicPending =
                RegionPathWorklist.plan(
                        Collections.singletonList(missingSymbolic),
                        Collections.singletonList(missingSymbolicTask),
                        Collections.<JsonObject>emptyList(),
                        RegionPathWorklist.Bounds.defaults());
        RegionPathWorklist.Result gapped = RegionPathWorklist.plan(
                Collections.singletonList(missingSymbolic),
                Collections.singletonList(missingSymbolicTask),
                terminalRecords(symbolicPending.tasks),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                gapped.manifest.get("state").getAsString());
        assertTrue(gapped.manifest.getAsJsonArray("gaps").toString()
                .contains("SITE.LOOP"));
    }

    private static JsonObject branchDependencyClosure(
            boolean symbolicGuard, String proof) {
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int result>", proof,
                "SITE.0", "SITE.1", "SITE.LOOP");
        JsonObject slice = closure.getAsJsonArray("members").get(0)
                .getAsJsonObject().getAsJsonObject("slice");
        slice.addProperty("complete", true);
        JsonArray inputs = new JsonArray();
        inputs.add("REGION.3.in.0");
        slice.add("inputPorts", inputs);
        JsonObject binding = new JsonObject();
        binding.addProperty("inputPort", "REGION.3.in.0");
        binding.addProperty("dependencyCell", "<P: int input>");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        slice.add("inputBindings", bindings);
        slice.getAsJsonArray("sites").add("SITE.RUNTIME.ONLY");

        JsonArray edges = new JsonArray();
        JsonObject value = new JsonObject();
        value.addProperty("edgeId", "DF.INPUT");
        value.addProperty("transferKind", "VALUE_PASS");
        value.addProperty("fromCell", "<P: int input>");
        value.addProperty("toCell", "<P: int result>::symbolic");
        edges.add(value);
        JsonObject guard = new JsonObject();
        guard.addProperty("edgeId", "DF.LOOP.GUARD");
        guard.addProperty("transferKind", "GUARD");
        guard.addProperty("siteId", "SITE.LOOP");
        guard.addProperty("guardSiteId", "SITE.LOOP");
        guard.addProperty("fromCell", symbolicGuard
                ? "<P: int result>::symbolic"
                : "<P: int result>::loopIndex");
        guard.addProperty("toCell", "<P: int result>");
        edges.add(guard);
        closure.add("causalEdges", edges);
        JsonArray edgeIds = new JsonArray();
        edgeIds.add("DF.INPUT");
        edgeIds.add("DF.LOOP.GUARD");
        slice.add("causalEdgeIds", edgeIds);
        return closure;
    }

    private static void addConcreteObservation(
            JsonObject summary, String site) {
        summary.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                site, "<test.Region: void run()>", 9,
                                1, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());
    }

    private static List<JsonObject> terminalRecords(
            List<JsonObject> tasks) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject task : tasks) {
            JsonObject record = new JsonObject();
            record.addProperty("queryKey",
                    task.get("queryKey").getAsString());
            record.addProperty("status", "UNSAT");
            result.add(record);
        }
        return result;
    }

    private static JsonObject outputClosure(
            String port, String cell, String proofTag, String... sites) {
        JsonObject producer = new JsonObject();
        producer.addProperty("regionId", "REGION.3");
        producer.addProperty("regionInstanceId",
                "REGION.3@test#call7");
        producer.addProperty("rootCallId", 7);

        JsonObject output = new JsonObject();
        output.addProperty("portId", port);
        output.addProperty("cell", cell);
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("javaTypeDescriptor", "I");
        output.addProperty("selectionAuthority", "TEST_EXACT_DEMAND");

        JsonArray siteArray = new JsonArray();
        for (String site : sites) siteArray.add(site);
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", siteArray.deepCopy());
        slice.add("staticSites", siteArray.deepCopy());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", new JsonArray());
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("proofTag", proofTag);

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 2);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("causalEdges", new JsonArray());
        closure.add("members", members);
        return closure;
    }

    private static void attachClosure(JsonObject artifact,
                                      JsonObject closure) {
        artifact.remove("requestedOutput");
        artifact.addProperty("regionInstanceId",
                "REGION.3@test#call7");
        artifact.addProperty("rootCallId", 7);
        artifact.add("outputClosure", closure.deepCopy());
    }

    private static void shareGoal(JsonObject source,
                                  JsonObject... executionArtifacts) {
        String goalId = source.get("goalId").getAsString();
        for (JsonObject artifact : executionArtifacts) {
            artifact.addProperty("goalId", goalId);
        }
    }

    private static JsonObject executionTask(String id,
                                            ClosureGoalKind goal) {
        JsonObject task = new JsonObject();
        task.addProperty("goalId", id + ".GOAL");
        task.addProperty("taskId", "TASK." + id);
        task.addProperty("regionId", "REGION.3");
        goal.writeToTask(task);
        attachClosure(task, outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.DEFAULT", "SITE.0", "SITE.1"));
        return task;
    }

    private static JsonObject summary(String id,
                                      ClosureGoalKind goal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + id);
        summary.addProperty("goalId", id + ".GOAL");
        summary.addProperty("taskId", "TASK." + id);
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        goal.writeToTask(summary);
        attachClosure(summary, outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.DEFAULT", "SITE.0", "SITE.1"));

        JsonArray conditions = new JsonArray();
        conditions.add(binary(">", 0));
        conditions.add(binary("<", 5));
        summary.add("pathCondition", conditions);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("SITE.0", 0));
        mappings.add(mapping("SITE.1", 1));
        summary.add("branchMappings", mappings);
        summary.add("outputExpressions", new JsonObject());
        authorizeVmPcMappings(summary);
        return summary;
    }

    private static void authorizeVmPcMappings(JsonObject summary) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        JsonArray canonical = new JsonArray();
        for (com.google.gson.JsonElement element
                : summary.getAsJsonArray("branchMappings")) {
            JsonObject mapping = element.getAsJsonObject();
            int conditionIndex = mapping.get("conditionIndex").getAsInt();
            SummaryBranchMapping.Policy policy =
                    SummaryBranchMapping.Policy.fromWire(
                            mapping.has("policy")
                                    ? mapping.get("policy").getAsString()
                                    : "EXPLORE");
            if (conditionIndex < 0 || conditionIndex >= conditions.size()) {
                canonical.add(SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                mapping.get("siteId").getAsString(),
                                "<test.Region: void run()>", 0,
                                mapping.get("occurrence").getAsInt(),
                                mapping.get("outcome").getAsBoolean()),
                        policy).toJson());
                continue;
            }
            JsonObject event = new JsonObject();
            event.addProperty("eventId", conditionIndex + 1L);
            event.addProperty("contextId", 7L);
            event.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPc(
                    mapping.get("siteId").getAsString(),
                    "<test.Region: void run()>", conditionIndex,
                    mapping.get("occurrence").getAsInt(),
                    mapping.get("outcome").getAsBoolean(),
                    conditions.get(conditionIndex), conditionIndex, event);
            canonical.add(SummaryBranchMapping.witnessed(witness,
                    conditionIndex, policy).toJson());
        }
        summary.add("branchMappings", canonical);
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
    }

    private static String sourceSite(JsonObject task) {
        return replayContract(task).source().siteId();
    }

    private static JsonObject mapping(String site, int condition) {
        return mapping(site, condition, 1);
    }

    private static JsonObject mapping(String site, int condition,
                                      int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("conditionIndex", condition);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", true);
        return mapping;
    }

    private static void addWitness(JsonObject summary, String site,
                                   int occurrence, JsonObject predicate) {
        JsonArray conditions = summary.getAsJsonArray("pathCondition");
        int conditionIndex = conditions.size();
        conditions.add(predicate);
        JsonObject event = new JsonObject();
        event.addProperty("eventId", conditionIndex + 1L);
        event.addProperty("contextId", 7L);
        event.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc(
                site, "<test.Region: void run()>", 9, occurrence, true,
                predicate, conditionIndex, event);
        summary.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.witnessed(witness, conditionIndex,
                        SummaryBranchMapping.Policy.EXPLORE).toJson());
    }

    private static JsonObject nestedFieldPredicate(int constant) {
        JsonObject expression = binary("<=", constant);
        expression.getAsJsonObject("_left").addProperty("_exp",
                "M_I_field_REGION.3.in.1.field.payload.value.occ.2_"
                        + "example/NestedState");
        return expression;
    }

    private static JsonObject binary(String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp",
                "M_I_field_REGION.3.in.0_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }
}
