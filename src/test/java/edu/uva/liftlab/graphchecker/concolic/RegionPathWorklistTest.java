package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
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
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.NEW",
                RegionCaptureGoal.outputClosure());
        JsonObject targetSummary = summary("ACT.TARGET",
                RegionCaptureGoal.targetBranch());
        JsonObject targetActivation = activation("ACT.TARGET",
                RegionCaptureGoal.targetBranch());
        targetSummary.remove("outputClosure");
        targetActivation.remove("outputClosure");
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
                Collections.singletonList(activation),
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
        assertEquals(BranchReplayContract.DROP_SOURCE_SUFFIX,
                latest.getAsJsonObject("replayContract")
                        .get("suffixPolicy").getAsString());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertFalse(result.manifest.has("observedPathCount"));

        RegionPathWorklist.Result bounded = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
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
        targetActivation.addProperty("targetMethod", "SITE");
        targetActivation.add("branches", targetBranches);
        RegionPathWorklist.Result targetResult = RegionPathWorklist.plan(
                Collections.singletonList(targetSummary),
                Collections.singletonList(targetActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(2, targetResult.tasks.size());
        for (JsonObject task : targetResult.tasks) {
            assertEquals("TARGET_BRANCH", task.getAsJsonObject(
                    "captureGoal").get("kind").getAsString());
            assertFalse(task.has("outputClosure"));
        }
        assertEquals("TARGET_BRANCH", targetResult.manifest.get(
                "captureGoal").getAsString());
    }

    @Test
    public void completeEmptyOutputSliceDoesNotBecomeWildcard() {
        JsonObject summary = summary("ACT.EMPTY.SLICE",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation(
                "ACT.EMPTY.SLICE", RegionCaptureGoal.outputClosure());
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.EMPTY");
        attachClosure(summary, closure);
        attachClosure(activation, closure);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
    }

    @Test
    public void explicitClosureScopesBranchTasksAndManifest() {
        JsonObject summary = summary("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        JsonObject activation = activation("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(activation, closure);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(activation),
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
                RegionCaptureGoal.outputClosure());
        JsonObject boundedLoopActivation = activation("ACT.LOOP",
                RegionCaptureGoal.outputClosure());
        JsonObject loopClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.LOOP", "SITE.1");
        attachClosure(boundedLoop, loopClosure);
        attachClosure(boundedLoopActivation, loopClosure);
        boundedLoop.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                "SITE.1", "<test.Region: void run()>", 1,
                                4, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());
        RegionPathWorklist.Result loopResult = RegionPathWorklist.plan(
                Collections.singletonList(boundedLoop),
                Collections.singletonList(boundedLoopActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(loopResult.manifest.toString(),
                RegionPathWorklist.State.PENDING.name(),
                loopResult.manifest.get("state").getAsString());
        assertTrue(loopResult.manifest.getAsJsonArray("gaps").isEmpty());
        assertEquals(1, loopResult.manifest.getAsJsonArray(
                "deferredObservations").size());

        JsonObject legacySummary = summary("ACT.CLOSURE",
                RegionCaptureGoal.outputClosure());
        legacySummary.remove("outputClosure");
        boolean rejected = false;
        try {
            RegionPathWorklist.plan(
                    Collections.singletonList(legacySummary),
                    Collections.singletonList(activation),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults());
        } catch (IllegalArgumentException expected) {
            rejected = expected.getMessage().contains(
                    "canonical outputClosure is required");
        }
        assertTrue("legacy summary must not inherit joint activation scope",
                rejected);
    }

    @Test
    public void closureDemandAndProofCannotReuseTerminalFlipRecord() {
        JsonObject firstSummary = summary("ACT.CLOSURE.A",
                RegionCaptureGoal.outputClosure());
        JsonObject firstActivation = activation("ACT.CLOSURE.A",
                RegionCaptureGoal.outputClosure());
        JsonObject firstClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.A", "SITE.1");
        attachClosure(firstSummary, firstClosure);
        attachClosure(firstActivation, firstClosure);
        RegionPathWorklist.Result first = RegionPathWorklist.plan(
                Collections.singletonList(firstSummary),
                Collections.singletonList(firstActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        JsonObject secondSummary = summary("ACT.CLOSURE.B",
                RegionCaptureGoal.outputClosure());
        JsonObject secondActivation = activation("ACT.CLOSURE.B",
                RegionCaptureGoal.outputClosure());
        JsonObject secondClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.B", "SITE.1");
        attachClosure(secondSummary, secondClosure);
        attachClosure(secondActivation, secondClosure);
        RegionPathWorklist.Result second = RegionPathWorklist.plan(
                Collections.singletonList(secondSummary),
                Collections.singletonList(secondActivation),
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
                Collections.singletonList(secondActivation),
                Collections.singletonList(record),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(1, replay.tasks.size());

        JsonObject otherDemandSummary = summary("ACT.CLOSURE.C",
                RegionCaptureGoal.outputClosure());
        JsonObject otherDemandActivation = activation("ACT.CLOSURE.C",
                RegionCaptureGoal.outputClosure());
        JsonObject otherDemand = outputClosure("REGION.3.out.1",
                "<P: int y>", "PROOF.A", "SITE.1");
        attachClosure(otherDemandSummary, otherDemand);
        attachClosure(otherDemandActivation, otherDemand);
        RegionPathWorklist.Result third = RegionPathWorklist.plan(
                Collections.singletonList(otherDemandSummary),
                Collections.singletonList(otherDemandActivation),
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
                RegionCaptureGoal.outputClosure());
        JsonObject concreteActivation = activation("ACT.CONCRETE",
                RegionCaptureGoal.outputClosure());
        attachClosure(concrete, closure);
        attachClosure(concreteActivation, closure);
        concrete.getAsJsonArray("branchMappings").add(
                SummaryBranchMapping.concrete(
                        ExactConcreteBranchObservation.attested(
                                "SITE.LATE", "<test.Region: void run()>", 9,
                                2, true),
                        SummaryBranchMapping.Policy.EXPLORE).toJson());

        RegionPathWorklist.Result bridgePending = RegionPathWorklist.plan(
                Collections.singletonList(concrete),
                Collections.singletonList(concreteActivation),
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
                Collections.singletonList(concreteActivation),
                exhaustedRecords, RegionPathWorklist.Bounds.defaults());
        assertTrue(exhausted.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                exhausted.manifest.get("state").getAsString());
        assertTrue(exhausted.manifest.getAsJsonArray("gaps").toString()
                .contains("SITE.LATE"));
        assertFalse(exhausted.manifest.has("deferredObservations"));

        JsonObject wrongOccurrence = summary("ACT.WRONG.OCCURRENCE",
                RegionCaptureGoal.outputClosure());
        JsonObject wrongActivation = activation("ACT.WRONG.OCCURRENCE",
                RegionCaptureGoal.outputClosure());
        attachClosure(wrongOccurrence, closure);
        attachClosure(wrongActivation, closure);
        addWitness(wrongOccurrence, "SITE.LATE", 1,
                nestedFieldPredicate(99));
        RegionPathWorklist.Result stillDeferred = RegionPathWorklist.plan(
                Arrays.asList(concrete, wrongOccurrence),
                Arrays.asList(concreteActivation, wrongActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                stillDeferred.manifest.get("state").getAsString());
        assertEquals(1, stillDeferred.manifest.getAsJsonArray(
                "deferredObservations").size());

        JsonObject exactOccurrence = summary("ACT.EXACT.OCCURRENCE",
                RegionCaptureGoal.outputClosure());
        JsonObject exactActivation = activation("ACT.EXACT.OCCURRENCE",
                RegionCaptureGoal.outputClosure());
        attachClosure(exactOccurrence, closure);
        attachClosure(exactActivation, closure);
        addWitness(exactOccurrence, "SITE.LATE", 2,
                nestedFieldPredicate(100));
        RegionPathWorklist.Result witnessed = RegionPathWorklist.plan(
                Arrays.asList(concrete, wrongOccurrence, exactOccurrence),
                Arrays.asList(concreteActivation, wrongActivation,
                        exactActivation),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                witnessed.manifest.get("state").getAsString());
        assertTrue(witnessed.manifest.getAsJsonArray("gaps").isEmpty());
        assertFalse(witnessed.manifest.has("deferredObservations"));
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
        slice.addProperty("captureBindingsRequired", false);
        slice.addProperty("captureBindingsComplete", true);
        slice.addProperty("proofTag", proofTag);

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        JsonArray members = new JsonArray();
        members.add(member);
        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 1);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
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

    private static JsonObject activation(String id, RegionCaptureGoal goal) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", id);
        activation.addProperty("regionId", "REGION.3");
        activation.add("captureGoal", goal.toJson());
        attachClosure(activation, outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.DEFAULT", "SITE.0", "SITE.1"));
        return activation;
    }

    private static JsonObject summary(String activationId,
                                      RegionCaptureGoal goal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + activationId);
        summary.addProperty("activationId", activationId);
        summary.addProperty("regionId", "REGION.3");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal", goal.toJson());
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
        summary.add("heapEffects", new JsonArray());
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
