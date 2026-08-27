package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class RegionPathWorklistTest {
    private static final Gson GSON = new Gson();

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

        RegionPathWorklist.Result firstWave = worklist(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), oneCampaignTask);
        assertEquals(1, firstWave.tasks.size());

        JsonObject record = new JsonObject();
        record.addProperty("queryKey", firstWave.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status",
                "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY");
        RegionPathWorklist.Result secondWave = worklist(
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
        RegionPathWorklist.Result firstWave = worklist(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(), oneFlip);
        assertEquals(1, firstWave.tasks.size());

        JsonObject record = new JsonObject();
        record.addProperty("queryKey", firstWave.tasks.get(0)
                .get("queryKey").getAsString());
        record.addProperty("status", "UNSAT");
        RegionPathWorklist.Result secondWave = worklist(
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

        RegionPathWorklist.Result result = worklist(
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

            RegionPathWorklist.Result pending = worklist(
                    Collections.singletonList(summary),
                    Collections.singletonList(task),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults());
            assertEquals(status, 1, pending.tasks.size());

            JsonObject record = new JsonObject();
            record.addProperty("queryKey", pending.tasks.get(0)
                    .get("queryKey").getAsString());
            record.addProperty("status", status);

            RegionPathWorklist.Result closed = worklist(
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

        RegionPathWorklist.Result pending = worklist(
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

        RegionPathWorklist.Result closed = worklist(
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
        RegionPathWorklist.Result pending = worklist(
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
        RegionPathWorklist.Result closed = worklist(
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
        JsonArray coverageGaps = closed.manifest
                .getAsJsonArray("coverageGaps");
        assertEquals(1, coverageGaps.size());
        JsonObject gap = coverageGaps.get(0).getAsJsonObject();
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
        RegionPathWorklist.Result rejectedPending = worklist(
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
        RegionPathWorklist.Result rejectedClosed = worklist(
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
        JsonArray rejectedCoverageGaps = rejectedClosed.manifest
                .getAsJsonArray("coverageGaps");
        assertEquals(1, rejectedCoverageGaps.size());
        JsonObject rejectedGap = rejectedCoverageGaps.get(0)
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

        RegionPathWorklist.Result seededResult = worklist(
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
                "coverageGaps").isEmpty());
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

        RegionPathWorklist.Result result = worklist(
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

    @Test
    public void targetWorklistFlipsOnlyLocalPrefixBeforeExactFatal() {
        String id = "ACT.TARGET.LOCAL.PREFIX";
        JsonObject summary = summary(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        JsonObject task = executionTask(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        String sourceId = "TARGET.LOCAL";
        String sourceField = "<example.Target: int localValue>";
        String sourcePhaseId = sourcePhaseId(
                task.get("occurrenceId").getAsString(), sourceId);
        String localRaw = "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                sourcePhaseId, sourceId)
                + "_example/Target";
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";

        JsonArray conditions = new JsonArray();
        conditions.add(binarySymbol(remoteRaw, ">", 0));
        conditions.add(binarySymbol(localRaw, ">", 0));
        conditions.add(binarySymbol(remoteRaw, "<", 10));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        JsonObject remotePrefix = mapping("SITE.REMOTE", 0);
        remotePrefix.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(remotePrefix);
        JsonObject localPrefix = mapping("SITE.LOCAL", 1);
        localPrefix.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(localPrefix);
        JsonObject fatal = mapping("SITE.FATAL", 2);
        fatal.addProperty("policy", "EXPLORE");
        mappings.add(fatal);
        summary.add("branchMappings", mappings);
        authorizeVmPcMappings(summary);
        JsonObject reach = new JsonObject();
        reach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        reach.addProperty("siteId", "SITE.FATAL");
        reach.addProperty("occurrence", 1);
        reach.addProperty("outcome", true);
        summary.add(PathObservation.TargetReachEvent.FIELD, reach);

        JsonArray branches = new JsonArray();
        branches.add(taskBranch("SITE.REMOTE", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.LOCAL", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.FATAL", "EXPLORE"));
        task.add("branches", branches);
        JsonObject target = new JsonObject();
        target.addProperty("siteId", "SITE.FATAL");
        target.addProperty("occurrence", 1);
        task.add("targetBranch", target);
        JsonArray actions = new JsonArray();
        JsonObject localAction = new JsonObject();
        localAction.addProperty("symbol", "REGION.3.in.local");
        localAction.addProperty("portId", "REGION.3.in.local");
        localAction.addProperty("mode", "CONCRETE");
        localAction.addProperty("location", "HEAP_OBJECT_FIELD");
        localAction.addProperty("bindingMode", "FIELD_ACCESS");
        localAction.addProperty("accessFieldSignature", sourceField);
        localAction.addProperty("javaType", "int");
        actions.add(localAction);
        JsonObject remoteAction = new JsonObject();
        remoteAction.addProperty("symbol", "REGION.3.in.rpc");
        remoteAction.addProperty("portId", "REGION.3.in.rpc");
        remoteAction.addProperty("mode", "CONCRETE");
        remoteAction.addProperty("location", "CALL_RETURN");
        remoteAction.addProperty("bindingMode", "LOCAL_DEFINITION");
        remoteAction.addProperty("javaType", "int");
        remoteAction.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        remoteAction.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        actions.add(remoteAction);
        task.add("inputActions", actions);
        addMintSite(task, task.get("occurrenceId").getAsString(), sourceId,
                sourceField, 1);
        JsonObject handoff = new JsonObject();
        handoff.addProperty("role", "ATTACH");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("portId", "REGION.3.in.rpc");
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add("communicationHandoffs", handoffs);
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", "EDGE.remote");
        edge.addProperty("toInputPort", "REGION.3.in.rpc");
        JsonArray bindings = new JsonArray();
        bindings.add(edge);
        task.add("edgeBindings", bindings.deepCopy());
        summary.add("edgeBindings", bindings.deepCopy());
        VmHandoffEvidence.writeTo(summary, Collections.singletonList(
                VmHandoffEvidence.event("REGION.3.in.rpc", 41L, 42L,
                        intSymbol(remoteRaw), "TASK.PRODUCER",
                        "REGION.PRODUCER/occurrence-1")));

        RegionPathWorklist.Result result = worklist(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(result.manifest.toString(), 1, result.tasks.size());
        JsonObject query = result.tasks.get(0);
        BranchReplayContract replay = replayContract(query);
        assertEquals("SITE.LOCAL", replay.source().siteId());
        assertEquals(2, replay.requiredPathPredicates().size());
        assertTrue(CanonicalJson.render(replay.requiredPathPredicates())
                .contains(remoteRaw));
        assertFalse(CanonicalJson.render(replay.requiredPathPredicates())
                .contains("Y_I_10"));
        assertEquals(1, VmHandoffEvidence.eventsOf(query).size());
        assertEquals(1, query.getAsJsonArray("edgeBindings").size());

        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.target.local");
        assignment.addProperty("engineSymbol", localRaw);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:"
                + sourcePhaseId);
        assignment.addProperty("configuredSourceId", sourceId);
        assignment.addProperty("configuredSourcePhaseId", sourcePhaseId);
        assignment.addProperty("configuredSourceFieldSignature",
                sourceField);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "1");
        JsonArray assignments = new JsonArray();
        assignments.add(assignment);
        JsonObject replayTask = PathReplayTaskFactory.create(query, task,
                assignments, replay, null);
        assertEquals(1, replayTask.getAsJsonArray(
                "communicationHandoffs").size());
        assertEquals(1, replayTask.getAsJsonArray("edgeBindings").size());
        assertEquals(1, replayTask.getAsJsonArray("modelAssignments").size());
        assertEquals(2, replayContract(replayTask)
                .requiredPathPredicates().size());

        JsonObject opposite = summary.deepCopy();
        opposite.addProperty("summaryId",
                "SUMMARY.ACT.TARGET.LOCAL.PREFIX.OPPOSITE");
        opposite.getAsJsonArray("pathCondition").set(1,
                binarySymbol(localRaw, "<=", 0));
        JsonArray oppositeMappings = new JsonArray();
        JsonObject oppositeRemote = mapping("SITE.REMOTE", 0);
        oppositeRemote.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeRemote);
        JsonObject oppositeLocal = mapping("SITE.LOCAL", 1);
        oppositeLocal.addProperty("outcome", false);
        oppositeLocal.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeLocal);
        JsonObject oppositeFatal = mapping("SITE.FATAL", 2);
        oppositeFatal.addProperty("policy", "EXPLORE");
        oppositeMappings.add(oppositeFatal);
        opposite.add("branchMappings", oppositeMappings);
        authorizeVmPcMappings(opposite);

        RegionPathWorklist.Result bothOutcomes = worklist(
                Arrays.asList(summary, opposite),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertTrue(bothOutcomes.tasks.toString(),
                bothOutcomes.tasks.isEmpty());
    }

    @Test
    public void severalLocalTargetPrefixesAreExploredAndDedupedSeparately() {
        String id = "ACT.TARGET.MULTIPLE.LOCAL.PREFIXES";
        JsonObject summary = summary(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        JsonObject task = executionTask(id,
                ClosureGoalKind.TARGET_REACH_CLOSURE);
        String occurrence = task.get("occurrenceId").getAsString();
        String firstSource = "TARGET.FIRST";
        String secondSource = "TARGET.SECOND";
        String firstField = "<example.Target: int first>";
        String secondField = "<example.Target: int second>";
        String firstPhaseId = sourcePhaseId(occurrence, firstSource);
        String secondPhaseId = sourcePhaseId(occurrence, secondSource);
        String firstRaw = "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                firstPhaseId, firstSource) + "_example/Target";
        String secondRaw = "M_I_field_"
                + SymbolicSourceEvidence.engineLabelForPhase(
                secondPhaseId, secondSource) + "_example/Target";
        String remoteRaw = "M_I_field_REMOTE.RPC.VALUE_example/Reply";

        JsonArray conditions = new JsonArray();
        conditions.add(binarySymbol(remoteRaw, ">", 0));
        conditions.add(binarySymbol(firstRaw, ">", 0));
        conditions.add(binarySymbol(secondRaw, ">", 0));
        conditions.add(binarySymbol(remoteRaw, "<", 10));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        JsonObject remote = mapping("SITE.REMOTE", 0);
        remote.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(remote);
        JsonObject first = mapping("SITE.FIRST", 1);
        first.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(first);
        JsonObject second = mapping("SITE.SECOND", 2);
        second.addProperty("policy", "PATH_ASSUMPTION");
        mappings.add(second);
        JsonObject fatal = mapping("SITE.FATAL", 3);
        fatal.addProperty("policy", "EXPLORE");
        mappings.add(fatal);
        summary.add("branchMappings", mappings);
        authorizeVmPcMappings(summary);
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", PathObservation.TargetReachEvent.KIND);
        reach.addProperty("siteId", "SITE.FATAL");
        reach.addProperty("occurrence", 1);
        reach.addProperty("outcome", true);
        summary.add(PathObservation.TargetReachEvent.FIELD, reach);

        JsonArray branches = new JsonArray();
        branches.add(taskBranch("SITE.REMOTE", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.FIRST", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.SECOND", "PATH_ASSUMPTION"));
        branches.add(taskBranch("SITE.FATAL", "EXPLORE"));
        task.add("branches", branches);
        JsonObject target = new JsonObject();
        target.addProperty("siteId", "SITE.FATAL");
        target.addProperty("occurrence", 1);
        task.add("targetBranch", target);

        JsonArray actions = new JsonArray();
        actions.add(targetLocalAction("TARGET.in.first", firstField));
        JsonObject remoteAction = new JsonObject();
        remoteAction.addProperty("symbol", "XCH.remote.resp");
        remoteAction.addProperty("portId", "XCH.remote.resp");
        remoteAction.addProperty("mode", "CONCRETE");
        remoteAction.addProperty("location", "CALL_RETURN");
        remoteAction.addProperty("bindingMode", "LOCAL_DEFINITION");
        remoteAction.addProperty("javaType", "int");
        remoteAction.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        remoteAction.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        actions.add(remoteAction);
        actions.add(targetLocalAction("TARGET.in.second", secondField));
        task.add("inputActions", actions);

        addMintSite(task, occurrence, firstSource, firstField, 1);
        addMintSite(task, occurrence, secondSource, secondField, 2);

        RegionPathWorklist.Result initial = worklist(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(initial.manifest.toString(), 2, initial.tasks.size());
        Set<String> flippedSites = new java.util.LinkedHashSet<>();
        for (JsonObject planned : initial.tasks) {
            flippedSites.add(replayContract(planned).source().siteId());
        }
        assertTrue(flippedSites.toString(),
                flippedSites.contains("SITE.FIRST"));
        assertTrue(flippedSites.toString(),
                flippedSites.contains("SITE.SECOND"));
        assertFalse(flippedSites.toString(),
                flippedSites.contains("SITE.REMOTE"));
        assertFalse(flippedSites.toString(),
                flippedSites.contains("SITE.FATAL"));

        // A fresh target replay observed SECOND=false under the same prefix.
        // It closes exactly that flip. FIRST=false remains unexplored and
        // must not be accidentally deduped just because both are local
        // target fields in the same activation.
        JsonObject secondOpposite = summary.deepCopy();
        secondOpposite.addProperty("summaryId",
                "SUMMARY.ACT.TARGET.MULTIPLE.LOCAL.PREFIXES.SECOND.FALSE");
        secondOpposite.getAsJsonArray("pathCondition").set(2,
                binarySymbol(secondRaw, "<=", 0));
        JsonArray oppositeMappings = new JsonArray();
        JsonObject oppositeRemote = mapping("SITE.REMOTE", 0);
        oppositeRemote.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeRemote);
        JsonObject oppositeFirst = mapping("SITE.FIRST", 1);
        oppositeFirst.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeFirst);
        JsonObject oppositeSecond = mapping("SITE.SECOND", 2);
        oppositeSecond.addProperty("outcome", false);
        oppositeSecond.addProperty("policy", "PATH_ASSUMPTION");
        oppositeMappings.add(oppositeSecond);
        JsonObject oppositeFatal = mapping("SITE.FATAL", 3);
        oppositeFatal.addProperty("policy", "EXPLORE");
        oppositeMappings.add(oppositeFatal);
        secondOpposite.add("branchMappings", oppositeMappings);
        authorizeVmPcMappings(secondOpposite);

        RegionPathWorklist.Result afterSecond = worklist(
                Arrays.asList(summary, secondOpposite),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(afterSecond.manifest.toString(), 1,
                afterSecond.tasks.size());
        BranchReplayContract remaining = replayContract(
                afterSecond.tasks.get(0));
        assertEquals("SITE.FIRST", remaining.source().siteId());
        assertEquals(false, remaining.requiredTakenOutcome());
    }

    /**
     * OCC-1: a task's address may be entered several times, and every
     * compatible activation is published as its own occurrence instead of one
     * being answered and the rest reported as an ambiguous address (which is
     * what HDFS-11741 run 24 did for four of six tasks).
     *
     * <p>The activations are cases of ONE relation, closed on the planned
     * address, and they are not alternatives: each carries its own occurrence
     * so the composer can give it its own selector, ports and event scope.
     * They are also one obligation -- a second activation of the same address
     * ran the same code path again and buys no new exploration.</p>
     */
    @Test
    public void severalActivationsAreOneRelationOfSeveralOccurrences() {
        String planned = "REGION.3/occurrence-1";
        JsonObject first = activation(planned, 1, true, "Y_I_7");
        JsonObject second = activation(planned, 2, true, "Y_I_9");
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = worklist(
                Arrays.asList(first, second), Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));
        // The same task with only its first activation: the obligations the
        // planner proposes must not grow because the address was entered a
        // second time.
        RegionPathWorklist.Result alone = worklist(
                Collections.singletonList(first),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));

        assertEquals(RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertEquals("a task with several occurrence cases is still one "
                        + "obligation",
                alone.tasks.size(), result.tasks.size());
        assertEquals("the planned address, not one activation of it",
                planned, result.manifest.get("occurrenceId").getAsString());
        assertEquals("two activations are one relation",
                1, result.relations.size());

        JsonObject relation = result.relations.get(0);
        assertEquals(planned, relation.get("occurrenceId").getAsString());
        JsonArray cases = relation.getAsJsonObject("regionRelation")
                .getAsJsonArray("cases");
        assertEquals("one case per activation", 2, cases.size());
        Set<String> occurrences = new LinkedHashSet<>();
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            occurrences.add(item.get("occurrenceId").getAsString());
            assertTrue("every case names its activation",
                    item.has("activationOrdinal"));
        }
        assertEquals("each case is its own occurrence",
                new LinkedHashSet<>(Arrays.asList(planned + "#a1",
                        planned + "#a2")), occurrences);
    }

    /**
     * An activation that satisfied only part of its output boundary becomes a
     * case of exactly what it captured, marked and named -- never dropped --
     * as long as another activation of the task did satisfy it.
     */
    @Test
    public void aPartialActivationIsAMarkedCaseNotADiscardedRelation() {
        String planned = "REGION.3/occurrence-1";
        JsonObject complete = activation(planned, 1, true, "Y_I_7");
        JsonObject partial = activation(planned, 2, false, "Y_I_9");
        partial.add("outputExpressions", new JsonObject());
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = worklist(
                Arrays.asList(complete, partial),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));

        assertEquals("one partial activation does not gap the relation",
                RegionPathWorklist.State.PENDING.name(),
                result.manifest.get("state").getAsString());
        assertTrue("and it is named",
                result.manifest.getAsJsonArray("coverageGaps").toString()
                        .contains("ACTIVATION_BOUNDARY_NOT_COMPLETE"));
        assertEquals(1, result.relations.size());
        JsonArray cases = result.relations.get(0)
                .getAsJsonObject("regionRelation").getAsJsonArray("cases");
        assertEquals("the partial activation is still a case",
                2, cases.size());
        boolean marked = false;
        for (int index = 0; index < cases.size(); index++) {
            JsonObject item = cases.get(index).getAsJsonObject();
            if (!item.get("relationallyComplete").getAsBoolean()) {
                marked = true;
                assertEquals("it carries only what it captured",
                        0, item.getAsJsonObject("outputExpressions").size());
            }
        }
        assertTrue("the partial case is marked", marked);
    }

    /**
     * A task none of whose activations satisfied the boundary is the
     * pre-OCC-1 case and stays the hard gap it always was.
     */
    @Test
    public void aTaskWithNoCompleteActivationStaysGapped() {
        String planned = "REGION.3/occurrence-1";
        JsonObject partial = activation(planned, 1, false, "Y_I_7");
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = worklist(
                Collections.singletonList(partial),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256));

        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertTrue(result.manifest.getAsJsonArray("gaps").toString()
                .contains("RELATIONAL_INPUT_OUTPUT_SUMMARY_NOT_COMPLETE"));
    }

    /** One published activation of a task's planned address. */
    private static JsonObject activation(String planned, int ordinal,
                                         boolean complete, String value) {
        JsonObject summary = summary("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        summary.addProperty("summaryId", "SUMMARY.ACT.OCC.A" + ordinal);
        summary.addProperty("occurrenceId", planned + "#a" + ordinal);
        summary.addProperty("plannedOccurrenceId", planned);
        summary.addProperty("activationOrdinal", ordinal);
        summary.addProperty("relationallyComplete", complete);
        JsonObject outputs = new JsonObject();
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_java_type", "I");
        constant.addProperty("_exp", value);
        outputs.add("REGION.3.out.0", constant);
        summary.add("outputExpressions", outputs);
        return summary;
    }

    /**
     * Once-only-root rule (OutputCaptureSpec#INSTANCE_SCOPED_PRODUCER).  An
     * instance-scoped once-only heap write's recorded version is decided once
     * at instance scope, so an occurrence that never sampled it owes no
     * per-occurrence production of that port.  The planner is the third owner
     * of this completeness check -- after the recorder's exact output
     * boundary and the importer's capture count -- and must not disagree with
     * the other two by reporting the demand it did not owe as an
     * OUTPUT_EXPRESSION_SET_MISMATCH.
     */
    @Test
    public void onceOnlyInstanceScopedPortIsNotOwedByEveryOccurrence() {
        RegionPathWorklist.Result relaxed = twoPortWave(
                "ACT.ONCEONLY.RELAX", true, false);

        assertFalse(relaxed.manifest.toString()
                .contains("OUTPUT_EXPRESSION_SET_MISMATCH"));
        assertEquals(RegionPathWorklist.State.PENDING.name(),
                relaxed.manifest.get("state").getAsString());
        // The occurrence still states the relation it did produce.
        assertEquals(1, relaxed.relations.size());
    }

    /**
     * Fail-closed, both directions.  A demanded port the contract does not
     * name instance-scoped is the hard set mismatch it has always been, and
     * so is a path that produced a port outside the demand -- the relaxation
     * only ever removes an unproduced once-only port from the demand, and
     * never admits a production the closure never asked for.
     */
    @Test
    public void unflaggedOrWidenedOutputSetsStillMismatchTheDemand() {
        // Same shape, but the second port's only writer never states the
        // once-only flag: the occurrence does owe it.
        RegionPathWorklist.Result unflagged = twoPortWave(
                "ACT.ONCEONLY.UNFLAGGED", false, false);
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                unflagged.manifest.get("state").getAsString());
        assertTrue(unflagged.manifest.toString().contains(
                "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND"));
        assertTrue(unflagged.relations.isEmpty());

        // The flag is stated, but the path also produced a port the closure
        // never demanded.  A relaxation of the missing side may not excuse a
        // production outside the demand.
        RegionPathWorklist.Result widened = twoPortWave(
                "ACT.ONCEONLY.WIDENED", true, true);
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                widened.manifest.get("state").getAsString());
        assertTrue(widened.manifest.toString().contains(
                "OUTPUT_EXPRESSION_SET_DOES_NOT_MATCH_DEMAND"));
        assertTrue(widened.relations.isEmpty());
    }

    /** One planning wave over a two-port closure whose second port is a
     *  once-only heap write the observation never sampled. */
    private static RegionPathWorklist.Result twoPortWave(
            String id, boolean instanceScoped, boolean produceUndemanded) {
        JsonObject summary = summary(id,
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject task = executionTask(id,
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);
        JsonObject closure = onceOnlyClosure(instanceScoped);
        attachClosure(summary, closure);
        attachClosure(task, closure);
        if (produceUndemanded) {
            JsonObject extra = new JsonObject();
            extra.addProperty("_type", "ConstExpr");
            extra.addProperty("_java_type", "I");
            extra.addProperty("_exp", "Y_I_9");
            summary.getAsJsonObject("outputExpressions")
                    .add("REGION.3.out.9", extra);
        }
        return worklist(Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
    }

    /** {@code REGION.3.out.0} as the fixtures already publish it, plus a
     *  {@code REGION.3.out.1} written only by one exact heap write. */
    private static JsonObject onceOnlyClosure(boolean instanceScoped) {
        JsonObject closure = outputClosure("REGION.3.out.0",
                "<P: int x>", "PROOF.ONCEONLY", "SITE.0", "SITE.1");

        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.3.out.1");
        output.addProperty("cell", "<P: int keys>");
        output.addProperty("kind", "REGION_OUTPUT");
        output.addProperty("javaTypeDescriptor", "I");
        output.addProperty("selectionAuthority", "TEST_EXACT_DEMAND");

        JsonObject binding = new JsonObject();
        binding.addProperty("captureBindingId", "CAPTURE.ONCEONLY.0");
        binding.addProperty("outputPort", "REGION.3.out.1");
        binding.addProperty("outputCell", "<P: int keys>");
        binding.addProperty("captureKind", "FIELD_WRITE_STATE");
        binding.addProperty("fieldSignature", "<P: int keys>");
        binding.addProperty("javaType", "int");
        binding.addProperty("definitionMethod", "<P: void setKeys()>");
        binding.addProperty("definitionUnitIndex", 3);
        binding.addProperty("outputSiteId", "<P: void setKeys()>#u3");
        binding.addProperty("outputOccurrence", 1);
        binding.addProperty("occurrenceScope", "REGION_ACTIVATION");
        if (instanceScoped) {
            binding.addProperty("instanceScopedProducer", true);
        }
        JsonArray bindings = new JsonArray();
        bindings.add(binding);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.3.out.1");
        slice.addProperty("outputCell", "<P: int keys>");
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        slice.add("methods", new JsonArray());
        slice.add("causalEdgeIds", new JsonArray());
        slice.add("captureBindings", bindings);
        slice.add("captureBindingIssues", new JsonArray());
        slice.addProperty("proofTag", "PROOF.ONCEONLY.1");

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        closure.getAsJsonArray("members").add(member);
        return closure;
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
        // C2: the census is required, never optional - a summary that
        // never stated it is refused, so every fixture states it.
        summary.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
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

    private static JsonObject taskBranch(String site, String policy) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", site);
        branch.addProperty("policy", policy);
        branch.addProperty("selectedOccurrence", 1);
        return branch;
    }

    private static JsonObject targetLocalAction(
            String port, String field) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "CONCRETE");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("javaType", "int");
        return action;
    }


    private static String sourcePhaseId(
            String occurrence, String sourceId) {
        return ConfiguredSourcePhaseContract.phaseId(occurrence,
                "<fixture.Source." + sourceId + ": void publish()>#u0",
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    /** The task's frozen catalog of declared mint SITES -- what a recorded
     * VM source root is resolved against now that nothing predicts it. */
    private static void addMintSite(JsonObject task, String occurrence,
                                    String sourceId, String field,
                                    int ordinal) {
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                sourceId, field,
                "<fixture.Source." + sourceId + ": void publish()>", 0));
        JsonObject row = ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(
                        declarations).get(0),
                occurrence, 1, ordinal, 10L, 100L + ordinal,
                "<example.Hook: boolean symbolize(java.lang.String,"
                        + "java.lang.Object,java.lang.String)>",
                Collections.singletonList(10L));
        JsonArray phases = task.has(
                ConfiguredSourcePhaseContract.PLAN_FIELD)
                ? task.getAsJsonArray(
                        ConfiguredSourcePhaseContract.PLAN_FIELD)
                : new JsonArray();
        phases.add(row);
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
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
        return binarySymbol(
                "M_I_field_REGION.3.in.0_java/lang/Integer",
                operator, constant);
    }

    private static JsonObject binarySymbol(
            String raw, String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = intSymbol(raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }

    private static JsonObject intSymbol(String raw) {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", raw);
        return symbol;
    }

    /**
     * OCC-1: the delta names the planned address of what it classified,
     * because that is the only occurrence identity a frozen plan states; a
     * summary names the activation that ran.  The two are matched on the
     * address here, exactly as the target reach query and the scheduler match
     * them, so a diverged occurrence excludes its activations from the wave
     * even when the divergence was recorded against another task id.
     */
    @Test
    public void aDivergedOccurrenceExcludesItsActivations() {
        String planned = "REGION.3/occurrence-1";
        JsonObject first = activation(planned, 1, true, "Y_I_7");
        JsonObject second = activation(planned, 2, true, "Y_I_9");
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(first, second), Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256),
                Collections.singletonList(divergenceOf(
                        "TASK.SOME.OTHER.MEMBER",
                        "NAMENODE/active/epoch-0", planned)));

        assertTrue("both activations belong to the next iteration",
                result.tasks.isEmpty());
        assertTrue(result.manifest.getAsJsonArray("coverageGaps").toString()
                .contains("OBLIGATION_BELONGS_TO_THE_NEXT_ITERATION"));
    }

    /**
     * The other half of the same rule: an occurrence the delta did not name
     * is planned as usual, so matching on the address widens nothing.
     */
    @Test
    public void anotherOccurrenceIsNotExcludedByThatDivergence() {
        String planned = "REGION.3/occurrence-1";
        JsonObject first = activation(planned, 1, true, "Y_I_7");
        JsonObject task = executionTask("ACT.OCC",
                ClosureGoalKind.OUTPUT_RELATION_CLOSURE);

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(first),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                new RegionPathWorklist.Bounds(64, 32, 256),
                Collections.singletonList(divergenceOf(
                        "TASK.SOME.OTHER.MEMBER",
                        "NAMENODE/active/epoch-0",
                        "REGION.3/occurrence-2")));

        assertFalse("an unrelated occurrence still plans its obligations",
                result.tasks.isEmpty());
    }

    /** One recorded {@code TOPOLOGY_DIVERGENCE} row of the delta. */
    private static JsonObject divergenceOf(String taskId, String sourceKey,
                                           String occurrenceId) {
        JsonObject row = new JsonObject();
        row.addProperty("deltaKind", TopologyDelta.TOPOLOGY_DIVERGENCE);
        row.addProperty("taskId", taskId);
        row.addProperty("sourceKey", sourceKey);
        row.addProperty("occurrenceId", occurrenceId);
        return row;
    }

    private static RegionPathWorklist.Result worklist(
            List<JsonObject> summaries, List<JsonObject> executionTasks,
            List<JsonObject> explorationRecords,
            RegionPathWorklist.Bounds bounds) {
        return RegionPathWorklist.plan(summaries, executionTasks,
                explorationRecords, bounds,
                Collections.<JsonObject>emptyList());
    }
}
