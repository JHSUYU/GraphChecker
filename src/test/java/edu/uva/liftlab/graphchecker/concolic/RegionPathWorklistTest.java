package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {

    /**
     * A member's task allowance belongs to the campaign, not to one planner
     * process.  The next wave therefore charges the queryKey recorded by the
     * preceding wave before it considers publishing another obligation.
     */
    @Test
    public void priorWaveQueryKeysConsumeTheCampaignTaskBound() {
        JsonObject summary = summary("ACT.CAMPAIGN.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask("ACT.CAMPAIGN.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.CAMPAIGN.BOUND", "SITE.0", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(task, closure);
        RegionPathWorklist.Bounds oneCampaignTask =
                new RegionPathWorklist.Bounds(64, 32, 1);

        RegionPathWorklist.Result firstWave = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), oneCampaignTask);
        assertEquals(1, firstWave.tasks.size());

        JsonObject record = new JsonObject();
        record.addProperty("queryKey", firstWave.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status",
                "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY");
        RegionPathWorklist.Result secondWave = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.singletonList(record), oneCampaignTask);

        assertTrue(secondWave.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                secondWave.manifest.get("state").getAsString());
        assertEquals("PARTIAL", secondWave.manifest.get(
                "coverageState").getAsString());
        assertTrue(secondWave.manifest.getAsJsonArray("coverageGaps")
                .toString().contains("MAX_TASKS"));
    }

    /** The same path cannot regain its flip allowance in a later wave. */
    @Test
    public void priorWaveFlipConsumesThePathCampaignBound() {
        JsonObject summary = summary("ACT.FLIP.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask("ACT.FLIP.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        RegionPathWorklist.Bounds oneFlip =
                new RegionPathWorklist.Bounds(64, 1, 256);
        RegionPathWorklist.Result firstWave = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), oneFlip);
        assertEquals(1, firstWave.tasks.size());

        JsonObject record = new JsonObject();
        record.addProperty("queryKey", firstWave.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status", "UNSAT");
        RegionPathWorklist.Result secondWave = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.singletonList(record), oneFlip);

        assertTrue(secondWave.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                secondWave.manifest.get("state").getAsString());
        assertEquals("PARTIAL", secondWave.manifest.get(
                "coverageState").getAsString());
        assertTrue(secondWave.manifest.getAsJsonArray("coverageGaps")
                .toString().contains("MAX_FLIPS_PER_PATH"));
    }

    /** Retained path cases also consume one member-wide campaign allowance. */
    @Test
    public void retainedCasesConsumeTheRegionCampaignPathBound() {
        JsonObject first = summary("ACT.PATH.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject second = first.deepCopy();
        second.addProperty("summaryId", "SUMMARY.ACT.PATH.BOUND.SECOND");
        second.getAsJsonArray("pathCondition").set(0, binary(">", 1));
        JsonArray secondMappings = new JsonArray();
        secondMappings.add(mapping("SITE.0", 0));
        secondMappings.add(mapping("SITE.1", 1));
        second.add("branchMappings", secondMappings);
        authorizeVmPcMappings(second);
        JsonObject task = executionTask("ACT.PATH.BOUND",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(first, second), Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(1, 32, 256));

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
        assertEquals("PARTIAL", result.manifest.get(
                "coverageState").getAsString());
        assertTrue(result.manifest.getAsJsonArray("coverageGaps")
                .toString().contains("MAX_PATHS_PER_REGION"));
    }

    /**
     * A flip whose replay ended without an admitted case is not proposed a
     * second time, whichever of the three replay verdicts it carries.
     *
     * <p>Unlike the {@code MATERIALIZATION_GAP} sibling below, this is a
     * regression guard rather than the proof of a fix: the planner already
     * accepted all three of these, and the defect was that nothing ever
     * produced them - each string existed only in this file, the one that
     * consumes it.  The repair is in {@code run_engine.sh}, which now records
     * {@code REPLAY_NOT_ADMITTED} instead of treating an importer that ran
     * and admitted nothing as a missing file.  This test exists so that the
     * consuming half cannot quietly stop accepting them once the producing
     * half finally exists.</p>
     */
    @Test
    public void replayVerdictsEndTheFlipRatherThanReproposingIt() {
        for (String status : new String[]{"REPLAY_NOT_ADMITTED",
                "REPLAY_ENGINE_UNAVAILABLE", "REPLAY_PRODUCED_NO_RESULT"}) {
            JsonObject summary = summary("ACT.CLOSURE." + status,
                    ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
            JsonObject task = executionTask("ACT.CLOSURE." + status,
                    ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
            JsonObject closure = outputClosure("REGION.3.out.0",
                    "<P: int x>", "PROOF." + status, "SITE.1");
            attachClosure(summary, closure);
            attachClosure(task, closure);

            RegionPathWorklist.Result pending = RegionPathWorklist.plan(
                    Collections.singletonList(summary),
                    Collections.singletonList(task),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults());
            assertEquals(status, 1, pending.tasks.size());

            JsonObject record = new JsonObject();
            record.addProperty("queryKey", pending.tasks.get(0)
                    .get("queryKey").getAsString());
            record.addProperty("status", status);

            RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                    Collections.singletonList(summary),
                    Collections.singletonList(task),
                    Collections.singletonList(record),
                    RegionPathWorklist.Bounds.defaults());
            assertTrue(status, closed.tasks.isEmpty());
            assertEquals(status, RegionPathWorklist.State.CLOSED.name(),
                    closed.manifest.get("state").getAsString());
        }
    }

    /**
     * A flip the solver answered with {@code MATERIALIZATION_GAP} is not
     * proposed a second time.
     *
     * <p>This is the termination property of the campaign's obligation wave,
     * which is a {@code while true} loop: it ends only because a queryKey
     * carrying a terminal exploration record stops being emitted.  The solver
     * already calls this outcome terminal and exits 0 on it, and the shell
     * now records it rather than killing the worker - so if the planner did
     * not also treat it as terminal, the same flip would return every wave
     * and the loop would spin instead of closing.  The record's
     * {@code queryKey} and {@code status} are read from one place, the
     * solver's own result, which is what keeps the two halves in agreement.
     * </p>
     */
    @Test
    public void materializationGapFlipIsNotReproposed() {
        JsonObject summary = summary("ACT.CLOSURE.MATGAP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask("ACT.CLOSURE.MATGAP",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.MATGAP", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(task, closure);

        RegionPathWorklist.Result pending = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                pending.manifest.get("state").getAsString());
        assertEquals(1, pending.tasks.size());
        String queryKey = pending.tasks.get(0)
                .get("queryKey").getAsString();

        JsonObject record = new JsonObject();
        record.addProperty("queryKey", queryKey);
        record.addProperty("status", "MATERIALIZATION_GAP");

        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.singletonList(record),
                RegionPathWorklist.Bounds.defaults());
        // The wave terminates: nothing is proposed again.
        assertTrue(closed.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                closed.manifest.get("state").getAsString());
        // And the abandoned flip is named rather than silently dropped.
        assertTrue(closed.manifest.toString()
                .contains("PATH_FLIP_MATERIALIZATION_GAP"));
    }

    /**
     * The verdicts the worklist reaches on a proposed flip's realisation: an
     * outcome the solver could not lower, an outcome whose bounded replay was
     * not admitted, and a contract that contradicts its own seed and is
     * therefore refused before it is ever proposed.  Each is named where the
     * flips an execution abandoned are named, and none of them fails the
     * planning wave or promotes the seed-only relation to a covered one.
     */
    @Test
    public void abandonedFlipRealisationsAreNamedRatherThanFailingTheWave() {
        JsonObject summary = summary("ACT.CLOSURE.UNSUPPORTED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask("ACT.CLOSURE.UNSUPPORTED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.UNSUPPORTED", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(task, closure);
        RegionPathWorklist.Result pending = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                pending.manifest.get("state").getAsString());
        assertEquals(1, pending.tasks.size());

        // The flip solver could not lower the query IR.  The proposal is
        // explored-and-abandoned: closure proceeds, and the manifest names
        // the gap instead of failing the planning wave.
        JsonObject record = new JsonObject();
        record.addProperty("queryKey", pending.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status", "UNSUPPORTED");
        record.addProperty("reason", "UNSUPPORTED_EXPRESSION_IR");
        JsonArray unsupported = new JsonArray();
        unsupported.add("q_branch_0:METHOD_SEMANTICS_MISSING:test");
        record.add("unsupported", unsupported);
        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.singletonList(record),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                closed.manifest.get("state").getAsString());
        assertEquals("SEED_ONLY", closed.manifest.get(
                "coverageState").getAsString());
        assertTrue(closed.tasks.isEmpty());
        assertEquals(1, closed.relations.size());
        assertEquals("SEED_ONLY", closed.relations.get(0)
                .get("pathCoverageState").getAsString());
        assertEquals("SEED_ONLY", closed.relations.get(0)
                .getAsJsonObject("pathCoverage")
                .get("coverageState").getAsString());
        assertEquals(1, closed.relations.get(0)
                .getAsJsonObject("regionRelation")
                .getAsJsonArray("cases").size());
        assertTrue(closed.manifest.getAsJsonArray("gaps").isEmpty());
        JsonArray explorationGaps = closed.manifest
                .getAsJsonArray("explorationGaps");
        assertEquals(1, explorationGaps.size());
        JsonObject gap = explorationGaps.get(0).getAsJsonObject();
        assertEquals("UNSUPPORTED_PATH_FLIP",
                gap.get("kind").getAsString());
        assertEquals(record.get("queryKey").getAsString(),
                gap.get("queryKey").getAsString());
        assertEquals("UNSUPPORTED_EXPRESSION_IR",
                gap.get("reason").getAsString());
        assertEquals(unsupported, gap.get("unsupported"));

        JsonObject rejectedSummary = summary("ACT.CLOSURE.REJECTED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject rejectedTask = executionTask("ACT.CLOSURE.REJECTED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject rejectedClosure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.REJECTED", "SITE.1");
        attachClosure(rejectedSummary, rejectedClosure);
        attachClosure(rejectedTask, rejectedClosure);
        RegionPathWorklist.Result rejectedPending = RegionPathWorklist.plan(
                Collections.singletonList(rejectedSummary),
                Collections.singletonList(rejectedTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(1, rejectedPending.tasks.size());

        // The flip ran, but its bounded replay never reached the region's
        // output relation, so the importer refused the summary.  That is an
        // explored-and-abandoned proposal: the planner closes over it and
        // names the gap instead of failing the wave.
        JsonObject rejectedRecord = new JsonObject();
        rejectedRecord.addProperty("queryKey", rejectedPending.tasks.get(0)
                .get("queryKey").getAsString());
        rejectedRecord.addProperty("status", "REPLAY_NOT_ADMITTED");
        rejectedRecord.addProperty("reason",
                "bounded replay produced no output relation");
        RegionPathWorklist.Result rejectedClosed = RegionPathWorklist.plan(
                Collections.singletonList(rejectedSummary),
                Collections.singletonList(rejectedTask),
                Collections.singletonList(rejectedRecord),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                rejectedClosed.manifest.get("state").getAsString());
        assertEquals("SEED_ONLY", rejectedClosed.manifest.get(
                "coverageState").getAsString());
        assertTrue(rejectedClosed.tasks.isEmpty());
        assertEquals(1, rejectedClosed.relations.size());
        assertTrue(rejectedClosed.manifest.getAsJsonArray("gaps").isEmpty());
        JsonArray rejectedExplorationGaps = rejectedClosed.manifest
                .getAsJsonArray("explorationGaps");
        assertEquals(1, rejectedExplorationGaps.size());
        JsonObject rejectedGap = rejectedExplorationGaps.get(0)
                .getAsJsonObject();
        assertEquals("PATH_FLIP_REPLAY_NOT_ADMITTED",
                rejectedGap.get("kind").getAsString());
        assertEquals(rejectedRecord.get("queryKey").getAsString(),
                rejectedGap.get("queryKey").getAsString());
        assertEquals("bounded replay produced no output relation",
                rejectedGap.get("reason").getAsString());

        // A distributed replay may observe another baseline polarity before
        // it applies this path's selected flip.  The source observation owns
        // the replay contract; the older task seed is not a second authority.
        JsonObject seededSummary = summary("ACT.SEEDED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject seededTask = executionTask("ACT.SEEDED",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonArray seededBranches = new JsonArray();
        seededBranches.add(seedBranch("SITE.0", true));
        seededBranches.add(seedBranch("SITE.1", false));
        seededTask.add("branches", seededBranches);

        RegionPathWorklist.Result seededResult = RegionPathWorklist.plan(
                Collections.singletonList(seededSummary),
                Collections.singletonList(seededTask),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(2, seededResult.tasks.size());
        assertEquals("SITE.1",
                replayContract(seededResult.tasks.get(0)).source().siteId());
        assertTrue(seededResult.manifest.getAsJsonArray("gaps").isEmpty());
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                seededResult.manifest.get("state").getAsString());
        assertTrue(seededResult.manifest.getAsJsonArray(
                "explorationGaps").isEmpty());
    }

    /**
     * A published {@code READ_CUT_GATE_GAP} reaches the classifier.
     *
     * <p>Three components already agree about this kind: the runtime raises
     * it, the importer copies it into the summary's {@code alignmentGaps} and
     * publishes it, and {@link CoverageDivergence} classifies it as
     * {@code GATE} - "a read or message cut could not be enforced".  The
     * worklist sits between the producer and the classifier and forwards
     * alignment gaps into {@code coverageGaps}, which is exactly what decides
     * {@code CLOSED} against {@code PARTIAL}.  While this kind was absent from
     * that forward list the evidence was dropped in transit, so a run could
     * report its coverage {@code CLOSED} with an unenforced read cut
     * standing.</p>
     */
    @Test
    public void aPublishedReadCutGateGapReachesTheClassifier() {
        JsonObject summary = summary("ACT.GATE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask("ACT.GATE",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.GATE", "SITE.1");
        attachClosure(summary, closure);
        attachClosure(task, closure);

        JsonObject published = new JsonObject();
        published.addProperty("kind", SparseReadCutGate.GAP_KIND);
        published.addProperty("reason", "READ_CUT_GATE_NOT_INSTALLABLE");
        JsonArray alignmentGaps = new JsonArray();
        alignmentGaps.add(published);
        summary.add("alignmentGaps", alignmentGaps);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        JsonArray coverageGaps = result.manifest.getAsJsonArray(
                "coverageGaps");
        JsonObject forwarded = null;
        for (JsonElement element : coverageGaps) {
            JsonObject row = element.getAsJsonObject();
            if (SparseReadCutGate.GAP_KIND.equals(
                    row.get("kind").getAsString())) {
                forwarded = row;
            }
        }
        assertNotNull(coverageGaps.toString(), forwarded);
        // The forward list exists to feed this classifier, so what it
        // forwards must be something the classifier understands.
        assertEquals(CoverageDivergence.Kind.GATE,
                CoverageDivergence.classify(forwarded));
        // And an unenforced read cut therefore cannot leave a run closed.
        assertFalse(result.manifest.toString(), CoverageDivergence.CLOSED
                .equals(result.manifest.get("coverageState").getAsString()));
    }

    private static JsonObject outputClosure(
            String port, String cell, String proofTag, String... sites) {
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey", "RELATION.REGION.3");
        producer.addProperty("regionId", "REGION.3");

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
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static void attachClosure(JsonObject artifact,
                                      JsonObject closure) {
        artifact.remove("requestedOutput");
        artifact.addProperty("relationKey", closure.getAsJsonObject(
                "producer").get("relationKey").getAsString());
        artifact.add("outputClosure", closure.deepCopy());
    }

    private static JsonObject executionTask(String id,
                                            ClosureGoalKind goal) {
        JsonObject task = new JsonObject();
        task.addProperty("goalId", id + ".GOAL");
        task.addProperty("taskId", "TASK." + id);
        task.addProperty("regionId", "REGION.3");
        task.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        task.addProperty("occurrenceId", "REGION.3/occurrence-1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
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
        summary.addProperty("sourceKey", "NAMENODE/active/epoch-0");
        summary.addProperty("occurrenceId", "REGION.3/occurrence-1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);
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
        JsonObject outputs = new JsonObject();
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_java_type", "I");
        value.addProperty("_exp", "Y_I_0");
        outputs.add("REGION.3.out.0", value);
        summary.add("outputExpressions", outputs);
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

    private static JsonObject seedBranch(String site, boolean outcome) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", site);
        branch.addProperty("policy", "EXPLORE");
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrence", 1);
        occurrence.addProperty("outcome", outcome);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence);
        branch.add("occurrences", occurrences);
        return branch;
    }

    private static BranchReplayContract replayContract(JsonObject task) {
        return BranchReplayContract.fromJson(task.getAsJsonObject(
                "replayContract"));
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
