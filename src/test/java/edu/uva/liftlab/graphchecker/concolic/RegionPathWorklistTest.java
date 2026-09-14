package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ComposedManifest;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import java.util.LinkedHashSet;
import java.util.Set;
import org.junit.Assume;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertSame;

/** Core contracts for the linked region-path worklist. */
public class RegionPathWorklistTest {

    /**
     * The laneBK shape: the target task published no summary at all.
     *
     * <p>Its replay ran, but the region's own decisions came back with the
     * symbolic gate closed and the runtime published no target reach, so the
     * importer wrote no summary for it and this planner is handed a task
     * with no observed path.  There is nothing to explore and nothing to
     * seed from, which is exactly what NO_OBSERVED_PATH_SEED says.  The
     * worklist states it and is GAPPED; it is not a campaign failure, and
     * the wave publishes it as that member's closure so the named gap
     * reaches the gap report and withholds the claim there.</p>
     */
    @Test
    public void regionPathWorklistRules() throws Exception {
        aTaskWithNoObservedSummaryIsGappedAndNamesTheMissingSeed();
        observedOppositeOutcomesCloseTheSemanticFlip();
        oneFlipCarriesTheWholeDependencyClosure();
        aBySitePhaseIsAssignedToEveryOwnerIncludingCompanions();
        aDecisionOverAnArrivedValueIsFlippableThroughItsHandoff();
        theTargetsFatalArmIsPlannedWhenTheSeedMissedIt();
        aFatalArmWithNoControlIsNamed();
        RootSliceObligationTest t0 =
                new RootSliceObligationTest();
        t0.rootSliceObligationRules();
        ConcreteDecisionIsNotAPrefixTest t1 =
                new ConcreteDecisionIsNotAPrefixTest();
        t1.concreteDecisionIsNotAPrefixRules();
        TargetReachPathQueryBuilderTest t2 =
                new TargetReachPathQueryBuilderTest();
        t2.parallelTargetOccurrencesAreScopedBeforeDecision();
        LocalCaseIdentityTest t3 =
                new LocalCaseIdentityTest();
        t3.runtimeAndExpressionFieldsDoNotSplitOneLocalCase();
        RuntimeWorkflowHandoffClosureTest t4 =
                new RuntimeWorkflowHandoffClosureTest();
        t4.inboundHandoffReplacesOnlyItsExactSymbolicInput();
        RootValuationSolverTest t5 =
                new RootValuationSolverTest();
        t5.rootValuationSolverRules();
    }

    private void aTaskWithNoObservedSummaryIsGappedAndNamesTheMissingSeed() {
        JsonObject task = task("T", "REGION.T", "REGION.T/occurrence-1");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.GAPPED.name(),
                result.manifest.get("state").getAsString());
        assertEquals("SEED_ONLY",
                result.manifest.get("coverageState").getAsString());
        JsonArray gaps = result.manifest.getAsJsonArray("gaps");
        assertEquals(1, gaps.size());
        assertEquals("NO_OBSERVED_PATH_SEED",
                gaps.get(0).getAsJsonObject().get("kind").getAsString());
        assertEquals("REGION_PATH_SEED_REQUIRED",
                gaps.get(0).getAsJsonObject().get("reason").getAsString());
    }

    private void observedOppositeOutcomesCloseTheSemanticFlip() {
        JsonObject task = task("B", "REGION.B",
                "REGION.B/occurrence-1");
        JsonObject taken = summary(task, 1, true);
        JsonObject notTaken = summary(task, 1, false);
        taken.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                finalLoopProfile("LOOP.B", 2));
        notTaken.add(LoopBoundPolicy.PATH_LOOP_COUNTS,
                finalLoopProfile("LOOP.B", 1));
        refreshLocalCaseId(taken);
        refreshLocalCaseId(notTaken);
        notTaken.addProperty("summaryId", "SUMMARY.B.not-taken");
        notTaken.addProperty("replayGroupId", "REPLAY.GROUP.SECOND");

        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Arrays.asList(taken, notTaken),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertTrue(result.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                result.manifest.get("state").getAsString());
    }

    private void oneFlipCarriesTheWholeDependencyClosure() {
        JsonObject c = task("C", "REGION.C", "REGION.C/occurrence-1");
        JsonObject b = task("B", "REGION.B", "REGION.B/occurrence-1");
        JsonObject a = task("A", "REGION.A", "REGION.A/occurrence-1");
        List<JsonObject> summaries = Arrays.asList(
                summary(c, 1), summary(b, 1), summary(b, 2), summary(a, 1));
        JsonObject bundle = LinkedReplayBundle.create(
                "TASK.B", Arrays.asList(c, b, a), summaries,
                "SUMMARY.B.2", "ITERATION.7");
        JsonObject carrier = new JsonObject();
        carrier.add(LinkedReplayBundle.FIELD, bundle);
        JsonObject decoded = LinkedReplayBundle.decode(carrier);

        assertEquals(3, decoded.getAsJsonArray("members").size());
        assertEquals("ITERATION.7", decoded.get(
                LinkedReplayBundle.TOPOLOGY_EPOCH_FIELD).getAsString());
        int primaries = 0;
        for (JsonElement element : decoded.getAsJsonArray("members")) {
            JsonObject member = element.getAsJsonObject();
            if (LinkedReplayBundle.PRIMARY.equals(
                    member.get("role").getAsString())) {
                primaries++;
            }
        }
        assertEquals(1, primaries);

        BranchReplayContract oldContract = BranchReplayContract.fromSummary(
                summaries.get(0), "SITE.C", 1);
        for (JsonObject oldPrimary : Arrays.asList(c, b, a)) {
            oldPrimary.add("replayContract", oldContract.toJson());
            oldPrimary.addProperty("pathQueryKey", "old-frontier");
        }
        JsonObject currentAction = new JsonObject();
        currentAction.addProperty("mode", "SYMBOLIC");
        currentAction.addProperty("symbol", "M_I_CURRENT");
        currentAction.addProperty("location", "CALL_RETURN");
        currentAction.addProperty("javaType", "int");
        b.getAsJsonArray("inputActions").add(currentAction);
        JsonArray stalePrimaryAssignments = new JsonArray();
        stalePrimaryAssignments.add(modelAssignment("M_I_STALE_SUFFIX", 7));
        b.add("modelAssignments", stalePrimaryAssignments);
        JsonArray companionAssignments = new JsonArray();
        companionAssignments.add(modelAssignment("M_I_COMPANION", 8));
        a.add("modelAssignments", companionAssignments);
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256("B-flip"));
        query.addProperty("goalId", "GOAL.LINKED");
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(query);
        query.add(LinkedReplayBundle.FIELD, bundle.deepCopy());
        Map<String, JsonObject> tasks = new LinkedHashMap<>();
        for (JsonObject task : Arrays.asList(c, b, a)) {
            tasks.put(task.get("taskId").getAsString(), task);
        }
        JsonArray currentAssignments = new JsonArray();
        currentAssignments.add(modelAssignment("M_I_CURRENT", 9));
        JsonArray guardedReads = new JsonArray();
        JsonObject guardedRead = new JsonObject();
        // The linked bundle may replace the task row with a replay clone;
        // the planned activation occurrence remains its stable identity.
        guardedRead.addProperty("readerTaskId", "TASK.PRIOR.A");
        guardedRead.addProperty("readerOccurrenceId",
                "REGION.A/occurrence-1");
        guardedRead.addProperty("readIdentity", "RFC.fixture");
        guardedReads.add(guardedRead);
        List<JsonObject> replay = linkedReplay(query,
                tasks, currentAssignments, guardedReads,
                BranchReplayContract.fromSummary(
                        summaries.get(2), "SITE.B", 1));
        for (JsonObject replayTask : replay) {
            boolean primary = LinkedReplayBundle.PRIMARY.equals(replayTask
                    .get(LinkedReplayBundle.ROLE_FIELD).getAsString());
            assertEquals(primary, replayTask.has("replayContract"));
            assertEquals(primary, replayTask.has("pathQueryKey"));
            JsonObject expanded = SharedExpressionTable.expand(replayTask);
            ExecutionTask decodedTask = ExecutionTask.decode(replayTask);
            assertEquals(optionalString(expanded, "taskId"),
                    decodedTask.taskId());
            if (primary) {
                assertTrue(replayTask.has(SharedExpressionTable.FIELD));
                assertEquals(optionalString(query, "queryKey"),
                        optionalString(replayTask, "pathQueryKey"));
                assertEquals(expanded.get("replayContract"),
                        decodedTask.replayContract());
                assertEquals("SITE.B", decodedTask.replaySchedule()
                        .sourceSiteId());
                assertEquals(1, expanded.getAsJsonArray(
                        "modelAssignments").size());
                assertEquals("M_I_CURRENT", expanded.getAsJsonArray(
                        "modelAssignments").get(0).getAsJsonObject()
                        .get("engineSymbol").getAsString());
            } else if ("REGION.A".equals(optionalString(expanded, "regionId"))) {
                assertEquals("M_I_COMPANION", expanded.getAsJsonArray(
                        "modelAssignments").get(0).getAsJsonObject()
                        .get("engineSymbol").getAsString());
                assertEquals(1, decodedTask.guardedReadAssignments().size());
            } else {
                assertEquals(0, decodedTask.guardedReadAssignments().size());
            }
        }
    }

    /**
     * laneVM11's shape: the flipped occurrence does not mint the root.
     *
     * <p>A by-site phase id is one variable, and it repeats in every
     * member's catalog that names that mint site.  The model assigns the
     * variable; every owner that mints it has to return the assigned value,
     * or the replay reads two values for one variable.  The primary need not
     * be an owner at all -- bug3's target task depends on the NameNode's
     * root through the wire, and the NameNode is a companion -- so counting
     * owners and refusing on more than one read that dependency as an
     * ambiguity and killed the obligation.</p>
     */
    private void aBySitePhaseIsAssignedToEveryOwnerIncludingCompanions() {
        JsonObject c = task("C", "REGION.C", "REGION.C/occurrence-1");
        JsonObject b = task("B", "REGION.B", "REGION.B/occurrence-1");
        JsonObject a = task("A", "REGION.A", "REGION.A/occurrence-1");
        // Two companions mint the one phase; the primary mints nothing.
        phaseCatalog(a, "");
        phaseCatalog(c, "");
        String sharedPhase = ConfiguredSourcePhaseContract.phaseId(
                "EXAMPLE.ROOT", "<com.example.S: boolean f()>#u1",
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        List<JsonObject> tasks = Arrays.asList(c, b, a);
        List<JsonObject> summaries = Arrays.asList(
                summary(c, 1), summary(b, 1), summary(a, 1));
        Map<String, JsonObject> taskById = new LinkedHashMap<>();
        for (JsonObject task : tasks) {
            taskById.put(task.get("taskId").getAsString(), task);
        }
        JsonObject query = linkedQuery(b, tasks, summaries,
                summaries.get(1));
        JsonArray assignments = new JsonArray();
        JsonObject assignment = modelAssignment("M_Z_SHARED", 1);
        assignment.addProperty("configuredSourcePhaseId", sharedPhase);
        assignments.add(assignment);

        List<JsonObject> replay = linkedReplay(query, taskById, assignments,
                new JsonArray(), BranchReplayContract.fromSummary(
                        summaries.get(1), "SITE.B", 1));

        int assigned = 0;
        for (JsonObject replayTask : replay) {
            JsonObject expanded = SharedExpressionTable.expand(replayTask);
            JsonArray models = expanded.getAsJsonArray("modelAssignments");
            if (models != null && models.size() > 0) assigned++;
        }
        assertEquals("both owners of the one phase must be assigned",
                2, assigned);
    }

    /** Gives one task a catalog that mints one configured source phase. */
    private static void phaseCatalog(JsonObject task, String ignored) {
        String phaseId = ConfiguredSourcePhaseContract.phaseId(
                "EXAMPLE.ROOT", "<com.example.S: boolean f()>#u1",
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
        JsonObject phase = new JsonObject();
        phase.addProperty("schemaVersion", 1);
        phase.addProperty("kind", "CONFIGURED_SOURCE_PHASE");
        phase.addProperty("authority",
                "EXACT_RUNTIME_SOURCE_HOOK_EXECUTION_V1");
        phase.addProperty("phaseId", phaseId);
        phase.addProperty("phase", "PUBLISH");
        phase.addProperty("phaseKind", "PUBLISH");
        phase.addProperty("sourceId", "EXAMPLE.ROOT");
        phase.addProperty("fieldSignature", "<com.example.S: boolean f>");
        phase.addProperty("declarationMethod", "<com.example.S: boolean f()>");
        phase.addProperty("declarationUnitIndex", 1);
        phase.addProperty("siteId", "<com.example.S: boolean f()>#u1");
        phase.addProperty("sourceOccurrenceId",
                task.get("occurrenceId").getAsString());
        phase.addProperty("baselineOrdinal", 1);
        phase.addProperty("eventSeq", 10);
        phase.addProperty("ownerCallId", 9);
        phase.addProperty("invocationId", 10);
        phase.addProperty("runtimeDeclaredCallee",
                "<com.example.Src: boolean symbolize(java.lang.String)>");
        JsonArray ancestry = new JsonArray();
        ancestry.add(9);
        phase.add("enclosingCallIds", ancestry);
        JsonArray phases = new JsonArray();
        phases.add(phase);
        task.add("configuredSourcePhases", phases);
    }

    /** The solver decodes the bundle and its closure once and hands both to
     *  the replay factory; these tests take the same route. */
    private static List<JsonObject> linkedReplay(
            JsonObject query, Map<String, JsonObject> taskById,
            JsonArray assignments, JsonArray guardedReads,
            BranchReplayContract contract) {
        JsonObject bundle = LinkedReplayBundle.decode(query);
        return PathReplayTaskFactory.createLinked(query, bundle,
                LinkedReplayBundle.sourceTasks(bundle, taskById),
                assignments, guardedReads, contract);
    }

    /**
     * A decision over a value that arrived on a wire is flippable, and the
     * obligation carries the row that flips it.
     *
     * <p>Nothing about the arrived value is a root, so the walk that looks
     * for root support finds none and the decision reads as closed by the
     * recording.  What makes it varyable is the replay's own handoff row at
     * that attach: it names the variable the VM minted there, and an
     * assignment to that variable is the whole replay control -- no root
     * assignment, no producer replay.  Without it bug3's
     * {@code allKeys.get(keyId)} produced no obligation at all.</p>
     */
    private void aDecisionOverAnArrivedValueIsFlippableThroughItsHandoff() {
        JsonObject task = task("W", "REGION.W", "REGION.W/occurrence-1");
        JsonObject observed = arrivedValueSummary(task, true);

        RegionPathWorklist.Result closed = RegionPathWorklist.plan(
                Collections.singletonList(observed),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(
                        Collections.singletonList(observed),
                        Collections.singletonList(task)));
        assertTrue("with no handoff row the arrival is not varyable",
                closed.tasks.isEmpty());

        JsonObject withHandoff = arrivedValueSummary(task, true);
        JsonObject attach = new JsonObject();
        attach.addProperty("kind", "VM_HANDOFF_EVENT");
        attach.addProperty("attachEventId", 42L);
        attach.addProperty("exportEventId", 41L);
        attach.addProperty(InSessionReadResolver.HANDOFF_SYMBOL,
                "HOFF.abcdef");
        attach.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                "HANDOFF_PHASE.wire");
        attach.addProperty("javaType", "I");
        attach.addProperty("recordedValue", "7");
        JsonArray attaches = new JsonArray();
        attaches.add(attach);
        withHandoff.add("vmHandoffEvents", attaches);
        refreshLocalCaseId(withHandoff);

        RegionPathWorklist.Result planned = RegionPathWorklist.plan(
                Collections.singletonList(withHandoff),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(
                        Collections.singletonList(withHandoff),
                        Collections.singletonList(task)));
        assertEquals("the arrival is the control, so the flip is planned",
                1, planned.tasks.size());
        JsonArray controls = planned.tasks.get(0).getAsJsonArray(
                RegionPathWorklist.HANDOFF_CONTROLS);
        assertEquals("and the obligation carries the row that flips it",
                1, controls.size());
        assertEquals("HOFF.abcdef", controls.get(0).getAsJsonObject()
                .get("rawSymbol").getAsString());
        assertEquals("HANDOFF_PHASE.wire", controls.get(0).getAsJsonObject()
                .get(InSessionReadResolver.HANDOFF_PHASE_ID).getAsString());
    }

    /**
     * The target's fatal arm is planned exactly when the seed missed it.
     *
     * <p>phi at the anchor is {@code predicate == requiredTakenOutcome}, and
     * the obligation the campaign exists for is reaching the target with
     * that arm.  The task states it on the branch row the query builder
     * already reads, so PLAN and COMPOSE name one fatal arm, and EXPLORE
     * plans the flip whenever the seed took the other one -- and nothing
     * when the seed already took it.</p>
     */
    private void theTargetsFatalArmIsPlannedWhenTheSeedMissedIt() {
        JsonObject missed = targetTask(false);
        RegionPathWorklist.Result planned = RegionPathWorklist.plan(
                Collections.singletonList(targetSummary(missed, true, true)),
                Collections.singletonList(missed),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(
                        Collections.singletonList(
                                targetSummary(missed, true, true)),
                        Collections.singletonList(missed)));
        assertEquals("the seed took the healthy arm, so the fatal arm is the"
                + " obligation", 1, planned.tasks.size());
        assertEquals(0, planned.manifest.getAsJsonArray("gaps").size());

        JsonObject taken = targetTask(true);
        RegionPathWorklist.Result none = RegionPathWorklist.plan(
                Collections.singletonList(targetSummary(taken, true, true)),
                Collections.singletonList(taken),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(
                        Collections.singletonList(
                                targetSummary(taken, true, true)),
                        Collections.singletonList(taken)));
        assertTrue("the seed already took the fatal arm",
                none.tasks.isEmpty());
    }

    /**
     * A fatal arm nothing the campaign varies reaches is named, not silent.
     *
     * <p>An obligation owes a control: a decision over a root, or a handoff
     * row at an attach its predicate names.  With neither there is nothing
     * to assign and nothing to replay, and planning it anyway hands the
     * solver a flip it cannot materialise.</p>
     */
    private void aFatalArmWithNoControlIsNamed() {
        JsonObject task = targetTask(false);
        JsonObject summary = targetSummary(task, true, false);
        RegionPathWorklist.Result result = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(Collections.singletonList(summary),
                        Collections.singletonList(task)));
        assertTrue("nothing is planned", result.tasks.isEmpty());
        JsonArray gaps = result.manifest.getAsJsonArray("gaps");
        assertEquals(1, gaps.size());
        assertEquals("TARGET_FATAL_ARM_NOT_CONTROLLED",
                gaps.get(0).getAsJsonObject().get("kind").getAsString());
    }

    /** The seed whose decision is over a root the campaign declares. */
    private static JsonObject rootedSummary(JsonObject task,
                                            boolean outcome) {
        JsonObject summary = summary(task, 1, outcome);
        String suffix = task.get("taskId").getAsString()
                .substring("TASK.".length());
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", "M_I_field_" + suffix + "_in");
        List<JsonObject> events = new ArrayList<>();
        // reused: the root was minted elsewhere and only travelled here, so
        // the row names it without claiming this phase minted it.
        events.add(SymbolicSourceEvidence.event("SOURCE_PHASE." + suffix,
                "EXAMPLE." + suffix, "node0/region/REGION." + suffix
                        + "#1#a1", "<fixture.Linked: int in>", symbol, 1,
                true, "sym__EXAMPLE_" + suffix + "__1", "3"));
        SymbolicSourceEvidence.writeTo(summary, events);
        refreshLocalCaseId(summary);
        return summary;
    }

    /** A target task stating the arm its failure needs. */
    private static JsonObject targetTask(boolean required) {
        JsonObject task = task("T", "REGION.T", "REGION.T/occurrence-1");
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        JsonObject branch = task.getAsJsonArray("branches").get(0)
                .getAsJsonObject();
        branch.addProperty("requiredOutcome", required);
        branch.addProperty("failureTarget", true);
        JsonObject target = new JsonObject();
        target.addProperty("siteId", "SITE.T");
        target.addProperty("occurrence", 1);
        task.add("targetBranch", target);
        return task;
    }

    /** The seed that reached the target, with or without a control. */
    private static JsonObject targetSummary(JsonObject task, boolean outcome,
                                            boolean controlled) {
        JsonObject summary = controlled
                ? rootedSummary(task, outcome)
                : arrivedValueSummary(task, outcome);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(summary);
        JsonObject reach = new JsonObject();
        reach.addProperty("kind", PathObservation.TargetReachEvent.KIND);
        reach.addProperty("siteId", "SITE.T");
        reach.addProperty("occurrence", 1);
        reach.addProperty("outcome", outcome);
        reach.addProperty("vmEventId", 9L);
        summary.add(PathObservation.TargetReachEvent.FIELD, reach);
        refreshLocalCaseId(summary);
        return summary;
    }

    /** One replay whose only decision is over a value that arrived. */
    private static JsonObject arrivedValueSummary(JsonObject task,
                                                  boolean outcome) {
        JsonObject summary = summary(task, 1, outcome);
        JsonObject arrived = new JsonObject();
        arrived.addProperty("_type", "ConsumerBoundaryExpression");
        arrived.addProperty("boundaryKind", "RPC_ATTACH");
        arrived.addProperty("eventId", 42L);
        arrived.addProperty("_java_type", "I");
        JsonObject carried = new JsonObject();
        carried.addProperty("_type", "SymbolExpression");
        carried.addProperty("_java_type", "I");
        carried.addProperty("_exp", "M_I_field_WIRE_in");
        arrived.add("expression", carried);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", arrived);
        condition.addProperty("_op", outcome ? ">" : "<=");
        condition.add("_right", right);
        JsonArray conditions = new JsonArray();
        conditions.add(condition);
        summary.add("pathCondition", conditions);
        JsonObject vmEvent = new JsonObject();
        vmEvent.addProperty("eventId", 1L);
        vmEvent.addProperty("contextId", 1L);
        vmEvent.addProperty("predicateNormalization", "IDENTITY");
        String site = "SITE." + task.get("taskId").getAsString()
                .substring("TASK.".length());
        BranchWitness witness = BranchWitness.vmPcImmutable(site,
                "<fixture.Wire: void run()>", 0, 1, outcome,
                condition, 0, vmEvent);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(witness, 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);
        // One declared root somewhere in the wave, so the inventory is
        // usable and the walk actually judges this decision.  It is not the
        // one this decision rests on.
        List<JsonObject> events = new ArrayList<>();
        JsonObject rootSymbol = new JsonObject();
        rootSymbol.addProperty("_type", "SymbolExpression");
        rootSymbol.addProperty("_java_type", "Z");
        rootSymbol.addProperty("_exp", RAW_WIRE_ROOT);
        events.add(SymbolicSourceEvidence.event("SOURCE_PHASE.wire",
                "EXAMPLE.WIRE", "node0/region/REGION.W#1#a1",
                "<fixture.Wire: boolean enabled>", rootSymbol, 1, false,
                "sym__EXAMPLE_WIRE__1", "true"));
        SymbolicSourceEvidence.writeTo(summary, events);
        refreshLocalCaseId(summary);
        return summary;
    }

    private static final String RAW_WIRE_ROOT = "M_Z_field_"
            + SymbolicSourceEvidence.engineLabelForPhase("SOURCE_PHASE.wire",
            "EXAMPLE.WIRE") + "_fixture/Wire";

    private static JsonObject task(String id, String region,
                                   String occurrence) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK." + id);
        task.addProperty("goalId", "GOAL.LINKED");
        task.addProperty("regionId", region);
        task.addProperty("sourceKey", "SOURCE." + id);
        task.addProperty("occurrenceId", occurrence);
        task.addProperty("relationKey", "RELATION." + id);
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(task);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", "SITE." + id);
        branch.addProperty("policy", "EXPLORE");
        branch.addProperty("selectedOccurrence", 1);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        task.add("branches", branches);
        task.add("inputActions", new JsonArray());
        return task;
    }

    private static JsonObject modelAssignment(String symbol, int value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", symbol);
        assignment.addProperty("inputSymbol", symbol);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", Integer.toString(value));
        return assignment;
    }

    private static JsonObject linkedQuery(JsonObject primary,
                                          List<JsonObject> tasks,
                                          List<JsonObject> summaries,
                                          JsonObject primarySummary) {
        JsonObject query = new JsonObject();
        query.addProperty("schemaVersion", 3);
        query.addProperty("kind", "REGION_PATH_FLIP");
        query.addProperty("queryKey", CanonicalJson.sha256(
                "shared-owner-" + optionalString(primary, "taskId")));
        query.addProperty("goalId", "GOAL.LINKED");
        query.addProperty("sourceTaskId", optionalString(primary, "taskId"));
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(query);
        query.add(LinkedReplayBundle.FIELD, LinkedReplayBundle.create(
                optionalString(primary, "taskId"), tasks, summaries,
                optionalString(primarySummary, "summaryId"),
                "ITERATION.7"));
        return query;
    }

    private static JsonObject summary(JsonObject task, int activation) {
        return summary(task, activation, true);
    }

    private static JsonObject summary(JsonObject task, int activation,
                                      boolean outcome) {
        String taskId = task.get("taskId").getAsString();
        String planned = task.get("occurrenceId").getAsString();
        String suffix = taskId.substring("TASK.".length());
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY." + suffix + "."
                + activation);
        summary.addProperty("taskId", taskId);
        summary.addProperty("goalId", task.get("goalId").getAsString());
        summary.addProperty("regionId", task.get("regionId").getAsString());
        summary.addProperty("sourceKey", task.get("sourceKey").getAsString());
        summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);
        summary.addProperty(PathObservation.ACTIVATION_ORDINAL, activation);
        summary.addProperty("occurrenceId", planned + "#a" + activation);
        summary.addProperty("replayGroupId", "REPLAY.GROUP.SEED");
        summary.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, "ITERATION.7");
        ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);

        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_field_" + suffix + "_in");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_0");
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "BinaryExpression");
        condition.add("_left", left);
        condition.addProperty("_op", outcome ? ">" : "<=");
        condition.add("_right", right);
        JsonArray conditions = new JsonArray();
        conditions.add(condition);
        summary.add("pathCondition", conditions);

        JsonObject vmEvent = new JsonObject();
        vmEvent.addProperty("eventId", 1L);
        vmEvent.addProperty("contextId", 1L);
        vmEvent.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPcImmutable("SITE." + suffix,
                "<fixture.Linked: void run()>", 0, 1, outcome,
                condition, 0, vmEvent);
        JsonArray mappings = new JsonArray();
        mappings.add(SummaryBranchMapping.witnessed(witness, 0,
                SummaryBranchMapping.Policy.EXPLORE).toJson());
        summary.add("branchMappings", mappings);
        refreshLocalCaseId(summary);
        return summary;
    }

    private static void refreshLocalCaseId(JsonObject summary) {
        summary.remove(LocalCaseIdentity.FIELD);
        summary.addProperty(LocalCaseIdentity.FIELD,
                LocalCaseIdentity.compute(summary));
    }

    private static JsonArray finalLoopProfile(String siteId, int bodyCount) {
        JsonObject loop = new JsonObject();
        loop.addProperty(LoopBoundPolicy.LOOP_SITE_ID, siteId);
        loop.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID,
                "runtime-" + siteId);
        loop.addProperty(LoopBoundPolicy.LOOP_CLASSIFICATION,
                "CFG_BACKEDGE");
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_BOUND, 8);
        loop.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, bodyCount);
        loop.addProperty(LoopBoundPolicy.PATH_LOOP_REACHED, true);
        JsonArray rows = new JsonArray();
        rows.add(loop);
        return rows;
    }

    /**
     * The root forward slice decides which branches are still obligations.
     *
     * <p>A campaign varies its declared roots and nothing else. A branch whose
     * condition names no root therefore evaluates to what the recording observed,
     * and proposing its opposite buys a solver call and - when some writer-arm
     * assignment happens to satisfy it - a whole workload replay that cannot be
     * admitted. These tests pin both halves: that such a branch is closed by the
     * recording, and that every way of not knowing keeps it open.</p>
     */
    static final class RootSliceObligationTest {
        private static final String ROOT_SYMBOL = "M_I_field_ROOT_in";
        private static final String ROOT_PORT = "REGION.ROOTED.in.port-1";

        public void rootSliceObligationRules() throws Exception {
            aBranchOnARootStaysAnObligation();
            aBranchOnNoRootIsClosedByTheRecording();
        }

        private void aBranchOnARootStaysAnObligation() {
            JsonObject task = task("ROOTED", "REGION.ROOTED");
            JsonObject summary = summary(task, ROOT_SYMBOL);
            summary.add(SymbolicSourceEvidence.FIELD,
                    evidence(ROOT_PORT, ROOT_SYMBOL));

            RegionPathWorklist.Result result = plan(summary, task,
                    SymbolicRootInventory.of(
                            Collections.singletonList(summary),
                            Collections.singletonList(task)));

            assertEquals(1, result.tasks.size());
            JsonObject telemetry = telemetry(result);
            assertTrue(telemetry.get("rootSliceApplied").getAsBoolean());
            assertEquals(0, telemetry.get("closedByConstant").getAsInt());
            assertEquals(1, telemetry.getAsJsonArray("rootDependentSites").size());
        }

        private void aBranchOnNoRootIsClosedByTheRecording() {
            JsonObject rooted = task("ROOTED", "REGION.ROOTED");
            JsonObject rootedSummary = summary(rooted, ROOT_SYMBOL);
            rootedSummary.add(SymbolicSourceEvidence.FIELD,
                    evidence(ROOT_PORT, ROOT_SYMBOL));
            JsonObject plain = task("PLAIN", "REGION.PLAIN");
            JsonObject plainSummary = summary(plain, "M_I_field_PLAIN_in");

            SymbolicRootInventory roots = SymbolicRootInventory.of(
                    Arrays.asList(rootedSummary, plainSummary),
                    Arrays.asList(rooted, plain));
            RegionPathWorklist.Result result = plan(plainSummary, plain, roots);

            assertTrue(result.tasks.isEmpty());
            assertEquals(RegionPathWorklist.State.CLOSED.name(),
                    result.manifest.get("state").getAsString());
            // Closing an obligation the recording already decided must not open
            // a coverage gap: the wave would keep re-planning proved-dead work.
            assertEquals(0, result.manifest.getAsJsonArray("coverageGaps").size());
            assertEquals("CLOSED",
                    result.manifest.get("coverageState").getAsString());

            JsonObject telemetry = telemetry(result);
            assertTrue(telemetry.get("rootSliceApplied").getAsBoolean());
            assertEquals(1, telemetry.get("closedByConstant").getAsInt());
            JsonObject row = telemetry.getAsJsonArray("closedByConstantRows")
                    .get(0).getAsJsonObject();
            assertEquals(RegionPathWorklist.CLOSED_BY_CONSTANT,
                    optionalString(row, "kind"));
            assertEquals("SITE.PLAIN", optionalString(row, "siteId"));
            assertEquals("REGION.PLAIN", optionalString(row, "regionId"));
            // The constant: the outcome the recording took.
            assertTrue(row.get("recordedOutcome").getAsBoolean());
        }

        private static RegionPathWorklist.Result plan(JsonObject summary,
                                                      JsonObject task,
                                                      SymbolicRootInventory roots) {
            return RegionPathWorklist.plan(
                    Collections.singletonList(summary),
                    Collections.singletonList(task),
                    Collections.<JsonObject>emptyList(),
                    RegionPathWorklist.Bounds.defaults(),
                    roots);
        }

        private static JsonObject telemetry(RegionPathWorklist.Result result) {
            return result.manifest.getAsJsonObject(
                    RegionPathWorklist.ROOT_SLICE_FIELD);
        }

        private static JsonArray evidence(String portId, String rawSymbol) {
            JsonArray rows = new JsonArray();
            rows.add(SymbolicSourceEvidence.manualEvent(portId,
                    "REGION.ROOTED/occurrence-1#a1",
                    "<fixture.Rooted: int declared>", "I", rawSymbol,
                    "SOURCE.IDENTITY." + portId));
            return rows;
        }

        private static JsonObject task(String id, String region) {
            JsonObject task = new JsonObject();
            task.addProperty("taskId", "TASK." + id);
            task.addProperty("goalId", "GOAL.ROOT_SLICE");
            task.addProperty("regionId", region);
            task.addProperty("sourceKey", "SOURCE." + id);
            task.addProperty("occurrenceId", region + "/occurrence-1");
            task.addProperty("relationKey", "RELATION." + id);
            ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(task);
            LoopBoundPolicy.cfgBackedges(8).writeTo(task);
            JsonObject branch = new JsonObject();
            branch.addProperty("siteId", "SITE." + id);
            branch.addProperty("policy", "EXPLORE");
            branch.addProperty("selectedOccurrence", 1);
            JsonArray branches = new JsonArray();
            branches.add(branch);
            task.add("branches", branches);
            task.add("inputActions", new JsonArray());
            return task;
        }

        private static JsonObject summary(JsonObject task, String leafSymbol) {
            String taskId = task.get("taskId").getAsString();
            String planned = task.get("occurrenceId").getAsString();
            String suffix = taskId.substring("TASK.".length());
            JsonObject summary = new JsonObject();
            summary.addProperty("summaryId", "SUMMARY." + suffix + ".1");
            summary.addProperty("taskId", taskId);
            summary.addProperty("goalId", task.get("goalId").getAsString());
            summary.addProperty("regionId", task.get("regionId").getAsString());
            summary.addProperty("sourceKey", task.get("sourceKey").getAsString());
            summary.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, planned);
            summary.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
            summary.addProperty("occurrenceId", planned + "#a1");
            summary.addProperty("replayGroupId", "REPLAY.GROUP.SEED");
            summary.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, "ITERATION.1");
            ClosureGoalKind.REGION_PATH_CLOSURE.writeToTask(summary);
            LoopBoundPolicy.cfgBackedges(8).writeTo(summary);

            JsonObject left = new JsonObject();
            left.addProperty("_type", "SymbolExpression");
            left.addProperty("_java_type", "I");
            left.addProperty("_exp", leafSymbol);
            JsonObject right = new JsonObject();
            right.addProperty("_type", "ConstExpr");
            right.addProperty("_java_type", "I");
            right.addProperty("_exp", "Y_I_0");
            JsonObject condition = new JsonObject();
            condition.addProperty("_type", "BinaryExpression");
            condition.add("_left", left);
            condition.addProperty("_op", ">");
            condition.add("_right", right);
            JsonArray conditions = new JsonArray();
            conditions.add(condition);
            summary.add("pathCondition", conditions);

            JsonObject vmEvent = new JsonObject();
            vmEvent.addProperty("eventId", 1L);
            vmEvent.addProperty("contextId", 1L);
            vmEvent.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPcImmutable("SITE." + suffix,
                    "<fixture.Sliced: void run()>", 0, 1, true,
                    condition, 0, vmEvent);
            JsonArray mappings = new JsonArray();
            mappings.add(SummaryBranchMapping.witnessed(witness, 0,
                    SummaryBranchMapping.Policy.EXPLORE).toJson());
            summary.add("branchMappings", mappings);
            summary.addProperty(LocalCaseIdentity.FIELD,
                    LocalCaseIdentity.compute(summary));
            return summary;
        }
    }


    /**
     * The prefix a replay must reproduce is pi: root-dependent decisions only.
     *
     * <p>Lane B2's shape. {@code REGION.763d087e} is
     * {@code Client$Connection.sendRpcRequest}, and every decision its seed
     * activation published is concrete -- ten rows, each a
     * {@code concreteObservation} with {@code rawPathConditionSize 0}, no
     * witness and no VM event id. One of them, {@code #u16}, came out
     * {@code true} where the recording had {@code false}, and the seed wave was
     * refused with {@code BRANCH_REPLAY_MISMATCH} for it.</p>
     *
     * <p>A decision the VM contributed no path condition for has no predicate at
     * all, so no root occurs in it: it is the IPC client's own state, not a step
     * of this region's path, and it varies between two runs of one recording
     * because the connection does. Recording it is right; refusing a replay for
     * it is not. The plan cannot make this call -- every branch of a region is
     * planned with policy EXPLORE -- so the observation is asked instead.</p>
     */
    static final class ConcreteDecisionIsNotAPrefixTest {
        private static final String SEND =
                "<org.apache.hadoop.ipc.Client$Connection: void sendRpcRequest("
                        + "org.apache.hadoop.ipc.Client$Call)>";
        private static final String U16 = SEND + "#u16";
        private static final String U4 = SEND + "#u4";
        private static final String U18 = SEND + "#u18";

        /** Lane B2: the recorded outcome differs and nothing is refused. */
        public void concreteDecisionIsNotAPrefixRules() throws Exception {
            aConcreteDecisionThatFlippedIsNotAMismatch();
            aRootDependentDecisionThatFlippedIsStillAMismatch();
            aConcreteDecisionThatMatchesIsAdmitted();
            anUnplannedConcreteSiteIsNotUnexpected();
            anUnplannedRootDependentSiteIsUnexpected();
            aSiteAConcreteDivergenceNeverReachedIsNotMissing();
            aMissingSiteStillRefusesWhenThePathHasRoots();
        }

        private void aConcreteDecisionThatFlippedIsNotAMismatch() {
            assertEquals("", mismatch(concrete(U16, 1, true),
                    concrete(U18, 1, true)));
        }

        /** A root-dependent decision that flipped is still a mismatch. */
        private void aRootDependentDecisionThatFlippedIsStillAMismatch() {
            String refusal = mismatch(witnessed(U16, 1, true),
                    concrete(U18, 1, true));
            assertTrue(refusal, refusal.contains("wrong decision at " + U16));
        }

        /** A concrete decision at its recorded outcome is admitted as before. */
        private void aConcreteDecisionThatMatchesIsAdmitted() {
            assertEquals("", mismatch(concrete(U16, 1, false),
                    concrete(U18, 1, true)));
        }

        /** A site the plan never named is evidence when it is concrete. */
        private void anUnplannedConcreteSiteIsNotUnexpected() {
            assertEquals("", mismatch(concrete(U16, 1, false),
                    concrete(U18, 1, true),
                    concrete(SEND + "#u49", 1, true)));
        }

        /** ... and still refused when it carried a path condition. */
        private void anUnplannedRootDependentSiteIsUnexpected() {
            String refusal = mismatch(concrete(U16, 1, false),
                    concrete(U18, 1, true),
                    witnessed(SEND + "#u49", 1, true));
            assertTrue(refusal, refusal.contains("unexpected " + SEND + "#u49"));
        }

        /**
         * A site a concrete divergence never reached is not missing from pi.
         *
         * <p>Lane B2c, after the concrete sites stopped refusing: the plan
         * declares {@code #u18} and the replay published no decision there at
         * all, because {@code #u16} -- the IPC client's own connection state,
         * concrete -- went the other way and the path never reached it. An
         * activation that decided nothing over a root has an empty pi, so no
         * site can be missing from it.</p>
         */
        private void aSiteAConcreteDivergenceNeverReachedIsNotMissing() {
            assertEquals("", mismatch(concrete(U16, 1, true)));
        }

        /** With a root-dependent decision in the activation, missing refuses. */
        private void aMissingSiteStillRefusesWhenThePathHasRoots() {
            String refusal = mismatch(witnessed(U16, 1, false));
            assertTrue(refusal, refusal.contains("missing " + U18));
        }

        /**
         * The refusal, as the importer computes it for one seed activation whose
         * plan declares {@code #u4=true} and {@code #u16=false}.
         */
        private static String mismatch(JsonObject... observed) {
            JsonArray mappings = new JsonArray();
            mappings.add(concrete(U4, 1, true));
            for (JsonObject mapping : observed) mappings.add(mapping);
            return ConcolicSummaryImporter.seedBranchMismatchForTest(
                    task(), mappings);
        }

        /** One published decision the VM contributed no path condition for. */
        private static JsonObject concrete(String site, int occurrence,
                                           boolean outcome) {
            return SummaryBranchMapping.concrete(
                    ExactConcreteBranchObservation.attested(site,
                            method(site), unit(site), occurrence, outcome),
                    SummaryBranchMapping.Policy.EXPLORE).toJson();
        }

        /** One published decision that carried a path condition. */
        private static JsonObject witnessed(String site, int occurrence,
                                            boolean outcome) {
            JsonObject predicate = new JsonObject();
            predicate.addProperty("_type", "SymbolExpression");
            predicate.addProperty("_java_type", "Z");
            predicate.addProperty("_exp", "M_Z_field_SRC.root");
            JsonObject normalization = new JsonObject();
            normalization.addProperty("predicateNormalization",
                    BranchWitness.IDENTITY_NORMALIZATION);
            return SummaryBranchMapping.witnessed(
                    BranchWitness.vmPcImmutable(site, method(site), unit(site),
                            occurrence, outcome, predicate, 0, normalization),
                    0, SummaryBranchMapping.Policy.EXPLORE).toJson();
        }

        private static String method(String siteId) {
            return siteId.substring(0, siteId.lastIndexOf("#u"));
        }

        private static int unit(String siteId) {
            return Integer.parseInt(
                    siteId.substring(siteId.lastIndexOf("#u") + 2));
        }

        /** The seed task, with lane B2's two declared branches. */
        private static ExecutionTask task() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("taskId", "TASK.SEED.5cfc9e86");
            encoded.addProperty("goalId", "GOAL.REGION_PATH.76bb19d1");
            encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
            encoded.addProperty("regionId", "REGION.763d087e");
            encoded.addProperty("relationKey", "REL.1");
            encoded.addProperty("sourceKey", "hdfs-17899/sps#epoch0");
            encoded.addProperty("occurrenceId",
                    "hdfs-17899/sps#epoch0/region/REGION.763d087e#1");
            encoded.addProperty("rootMethod", SEND);
            encoded.addProperty("instrumentationSelector", "sel");
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "EXECUTABLE");
            encoded.add("admission", admission);
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "RECEIVER_CONTEXT");
            selector.addProperty("receiverClass",
                    "org.apache.hadoop.ipc.Client$Connection");
            selector.addProperty("invocationOrdinal", 1);
            selector.addProperty("method", SEND);
            JsonObject anchor = new JsonObject();
            anchor.addProperty("sourceKey", "hdfs-17899/sps#epoch0");
            anchor.addProperty("kind", "INHERITED_CONTEXT");
            selector.add("causalAnchor", anchor);
            encoded.add("rootSelector", selector);
            JsonArray branches = new JsonArray();
            branches.add(branch(U4, 1, true));
            branches.add(branch(U16, 1, false));
            branches.add(branch(U18, 1, true));
            encoded.add("branches", branches);
            encoded.add("inputActions", new JsonArray());
            JsonObject loopBound = new JsonObject();
            loopBound.addProperty("schemaVersion", 1);
            encoded.add("loopBound", loopBound);
            return ExecutionTask.decode(encoded);
        }

        private static JsonObject branch(String site, int occurrence,
                                         boolean outcome) {
            JsonObject row = new JsonObject();
            row.addProperty("siteId", site);
            row.addProperty("policy", "EXPLORE");
            JsonArray occurrences = new JsonArray();
            JsonObject one = new JsonObject();
            one.addProperty("occurrence", occurrence);
            one.addProperty("outcome", outcome);
            occurrences.add(one);
            row.add("occurrences", occurrences);
            return row;
        }
    }


    /** Focused coverage of target worklist-to-activation closure identity. */
    static final class TargetReachPathQueryBuilderTest {

        public void parallelTargetOccurrencesAreScopedBeforeDecision() {
            JsonObject selected = readySeed("source/dn1#epoch0", "target#2",
                    "GOAL.dn1.2");
            List<JsonObject> seeds = Arrays.asList(
                    readySeed("source/dn0#epoch0", "target#1", "GOAL.dn0.1"),
                    readySeed("source/dn0#epoch0", "target#2", "GOAL.dn0.2"),
                    readySeed("source/dn1#epoch0", "target#1", "GOAL.dn1.1"),
                    selected);
            JsonObject manifest = targetIdentity("target#2");
            manifest.addProperty("sourceKey", "source/dn1#epoch0");
            manifest.addProperty("goalId", "GOAL.dn1.2");

            List<JsonObject> scoped =
                    TargetReachPathQueryBuilder.solverReadySeedsForScope(
                            seeds, manifest);

            assertEquals(1, scoped.size());
            assertSame(selected, scoped.get(0));

            JsonObject sameScope = readySeed("source/dn1#epoch0", "target#2",
                    "GOAL.dn1.2");
            scoped = TargetReachPathQueryBuilder.solverReadySeedsForScope(
                    Arrays.asList(selected, sameScope), manifest);
            assertEquals(2, scoped.size());
        }

        private static JsonObject closedManifest(String occurrence) {
            JsonObject row = targetIdentity(occurrence);
            row.addProperty("state", "CLOSED");
            row.addProperty("coverageState", "CLOSED");
            row.add("gaps", new JsonArray());
            row.add("coverageGaps", new JsonArray());
            return row;
        }

        private static JsonObject targetSummary(String occurrence) {
            return targetIdentity(occurrence);
        }

        private static JsonObject readySeed(String source, String occurrence,
                                            String goal) {
            JsonObject row = targetIdentity(occurrence);
            row.addProperty("sourceKey", source);
            row.addProperty("goalId", goal);
            row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
            row.addProperty("readyForSolver", true);
            return row;
        }

        private static JsonObject targetIdentity(String occurrence) {
            JsonObject row = new JsonObject();
            row.addProperty("sourceKey", "source/dn0#epoch0");
            row.addProperty("regionId", "REGION.target");
            row.addProperty("occurrenceId", occurrence);
            row.addProperty("goalId", "GOAL.target");
            return row;
        }
    }


    /** The local control identity is independent of execution observations. */
    static final class LocalCaseIdentityTest {

        public void runtimeAndExpressionFieldsDoNotSplitOneLocalCase() {
            JsonObject first = summary("R/occurrence-1#a1", true,
                    "M_value_1");
            JsonObject second = first.deepCopy();
            second.addProperty("summaryId", "SUMMARY.second");
            second.addProperty("taskId", "TASK.second");
            second.addProperty("replayGroupId", "REPLAY.second");
            second.addProperty("boundarySessionScope", "SESSION.second");
            second.addProperty("topologyEpoch", "EPOCH.second");
            JsonObject nested = second.getAsJsonArray("pathCondition").get(0)
                    .getAsJsonObject().getAsJsonObject("_left");
            nested.addProperty("_exp", "M_value_2");
            nested.addProperty(SharedExpressionTable.ANCHOR, "EXPR.changed");
            nested.addProperty("eventId", 999L);
            nested.addProperty("javaThreadId", 42L);

            assertEquals(LocalCaseIdentity.compute(first),
                    LocalCaseIdentity.compute(second));
            assertFalse(CanonicalJson.render(LocalCaseIdentity.payload(first))
                    .contains("pathConditionIndex"));
        }

        private static JsonObject summary(String occurrence, boolean outcome,
                                          String symbol) {
            JsonObject row = new JsonObject();
            row.addProperty("sourceKey", "SOURCE.R");
            row.addProperty("regionId", "REGION.R");
            row.addProperty("occurrenceId", occurrence);
            row.addProperty("normalExit", true);
            row.addProperty("boundedExit", false);
            row.addProperty("exceptionType", "");

            JsonObject left = new JsonObject();
            left.addProperty("_type", "SymbolExpression");
            left.addProperty("_java_type", "I");
            left.addProperty("_exp", symbol);
            JsonObject right = new JsonObject();
            right.addProperty("_type", "ConstExpr");
            right.addProperty("_java_type", "I");
            right.addProperty("_exp", "Y_I_0");
            JsonObject condition = new JsonObject();
            condition.addProperty("_code_position",
                    "<fixture.R: void run()>:7");
            condition.addProperty("_type", "BinaryExpression");
            condition.addProperty("_java_type", "Z");
            condition.addProperty("_op", outcome ? ">" : "<=");
            condition.add("_left", left);
            condition.add("_right", right);
            JsonArray path = new JsonArray();
            path.add(condition);
            row.add("pathCondition", path);

            JsonArray mappings = new JsonArray();
            mappings.add(SummaryBranchMapping.concrete(
                    ExactConcreteBranchObservation.attested("SITE.R",
                            "<fixture.R: void run()>", 7, 1, outcome),
                    SummaryBranchMapping.Policy.EXPLORE).toJson());
            row.add("branchMappings", mappings);
            return row;
        }
    }


    /** Focused check for retaining observed communication ancestry. */
    static final class RuntimeWorkflowHandoffClosureTest {

        public void inboundHandoffReplacesOnlyItsExactSymbolicInput() {
            String port = "XCH.test.resp.value";
            String receiver = "source/c/region/R.C#1";
            JsonArray actions = new JsonArray();
            actions.add(input(port, "SYMBOLIC"));
            actions.add(input("manual.root", "SYMBOLIC"));
            actions.add(input(port, "CONCRETE"));
            JsonArray edges = new JsonArray();
            edges.add(protocolEdge("source/p/region/R.P#1",
                    receiver + "#a2", port));
            JsonObject declarations = new JsonObject();
            JsonArray handoffs = new JsonArray();
            handoffs.add(inboundHandoff(port));
            declarations.add(CommunicationHandoffSpec.FIELD, handoffs);

            JsonArray retained = ConcolicScheduler
                    .removeInboundProtocolHandoffInputs(actions, edges,
                            receiver, CommunicationHandoffSpec.decode(
                                    declarations));

            assertEquals(2, retained.size());
            assertEquals("manual.root", retained.get(0).getAsJsonObject()
                    .get("symbol").getAsString());
            assertEquals("CONCRETE", retained.get(1).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals(3, ConcolicScheduler
                    .removeInboundProtocolHandoffInputs(actions, edges,
                            "source/other/region/R.X#1",
                            CommunicationHandoffSpec.decode(declarations))
                    .size());
            assertEquals(3, ConcolicScheduler
                    .removeInboundProtocolHandoffInputs(actions, edges,
                            receiver, Collections
                                    .<CommunicationHandoffSpec>emptyList())
                    .size());
        }

        private static Set<String> selectedOccurrences(
                java.util.List<RegionInstancePlan> plans,
                java.util.List<JsonObject> summaries) throws Exception {
            Set<String> selected = new LinkedHashSet<>();
            for (RuntimeWorkflowDiscovery.Selection selection
                    : RuntimeWorkflowDiscovery.rankedWorkflow(plans, summaries)
                    .selections()) {
                selected.add(selection.occurrenceId);
            }
            return selected;
        }

        /**
         * One recorded versions envelope owned by the writer itself: a WRITE
         * version whose activation closure names an enclosing task, and an empty
         * read log, which is what the writer's own summary carries.
         */
        private static JsonObject unreadWriterRecord(
                String scope, String writerOccurrence,
                String enclosingOccurrence, boolean complete) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConSymbolExp");
            expression.addProperty("_java_type", "I");
            expression.addProperty("_exp", "C_I_1");
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", 3L);
            version.addProperty("versionKind", "WRITE");
            version.addProperty("regionEnterEventId", 11L);
            version.addProperty("regionId", "R.T");
            version.addProperty("taskId", "TASK.T");
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    "source/t");
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    writerOccurrence);
            version.add("expression", expression);
            version.add("pathGuard", SharedStateEvidence.emptyConjunction());

            JsonObject location = new JsonObject();
            location.addProperty("locationKind", "INSTANCE_FIELD");
            location.addProperty("ownerSymRid", 21L);
            location.addProperty("slot", 4);
            JsonObject envelope = new JsonObject();
            envelope.addProperty("kind",
                    SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
            envelope.addProperty("schemaVersion",
                    SharedStateEvidence.SCHEMA_VERSION);
            envelope.addProperty("selected", true);
            envelope.add("location", location);
            envelope.addProperty("writerSetComplete", true);
            JsonArray versions = new JsonArray();
            versions.add(version);
            envelope.add("versions", versions);
            envelope.addProperty("serializationTruncated", false);
            // The writer's own envelope logs no read.
            envelope.add("reads", new JsonArray());
            envelope.addProperty("readLogTruncated", false);
            JsonObject record = SharedStateEvidence.versionsRecord(
                    "INSTANCE_FIELD/21#4", envelope,
                    RecordedEvidenceIdentity.of("run", scope, "TASK.T",
                            writerOccurrence, "source/t", 1L));
            JsonArray records = new JsonArray();
            records.add(record);
            JsonObject recorded = new JsonObject();
            recorded.add("versions", records);
            return recorded;
        }

        private static JsonObject summary(String scope, String task,
                                          String occurrence,
                                          String producerTask,
                                          String producerOccurrence,
                                          String consumerOccurrence,
                                          long attachEvent) {
            JsonObject payload = new JsonObject();
            payload.addProperty("_type", "SymbolExpression");
            payload.addProperty("_java_type", "I");
            payload.addProperty("_exp", "x");
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConsumerBoundaryExpression");
            expression.addProperty("boundaryKind", "RPC_ATTACH");
            expression.addProperty("eventId", attachEvent);
            expression.addProperty("_java_type", "I");
            expression.add("expression", payload);
            JsonObject event = VmHandoffEvidence.event("port", attachEvent - 1L,
                    attachEvent, expression, producerTask, producerOccurrence,
                    consumerOccurrence,
                    edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract
                            .phaseId("port", consumerOccurrence, 1, "<a.B: int v>"),
                    "M_I_field_HOFF.1_a/B", "7", "I", "", false);
            event.addProperty("boundarySessionScope", scope);
            event.addProperty("consumerOccurrenceId", consumerOccurrence);
            JsonArray events = new JsonArray();
            events.add(event);

            JsonObject summary = new JsonObject();
            summary.addProperty("boundarySessionScope", scope);
            summary.addProperty("taskId", task);
            summary.addProperty("occurrenceId", occurrence + "#a1");
            summary.add(VmHandoffEvidence.FIELD, events);
            return summary;
        }

        private static JsonObject readEdge(String from, String to,
                                           long receiverObjectId) {
            JsonObject edge = new JsonObject();
            edge.addProperty("schemaVersion", 3);
            edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
            edge.addProperty("correlationAuthority",
                    SharedFieldFlow.LOCATION_MATCH_AUTHORITY);
            edge.addProperty("fromOccurrenceId", from);
            edge.addProperty("toOccurrenceId", to);
            edge.addProperty("fromOutputPort", "value");
            edge.addProperty("toInputPort", "value");
            edge.addProperty(SharedFieldFlow.EDGE_LOCATION,
                    "example.State#value" + receiverObjectId);
            return edge;
        }

        private static JsonObject input(String symbol, String mode) {
            JsonObject action = new JsonObject();
            action.addProperty("symbol", symbol);
            action.addProperty("mode", mode);
            return action;
        }

        private static JsonObject protocolEdge(String from, String to,
                                               String port) {
            JsonObject edge = new JsonObject();
            edge.addProperty("schemaVersion", 3);
            edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
            edge.addProperty("authority",
                    AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
            edge.addProperty("direction", "RESPONSE");
            edge.addProperty("fromOccurrenceId", from);
            edge.addProperty("toOccurrenceId", to);
            edge.addProperty("fromOutputPort", port);
            edge.addProperty("toInputPort", port);
            return edge;
        }

        private static JsonObject inboundHandoff(String port) {
            JsonObject handoff = new JsonObject();
            handoff.addProperty("portId", port);
            handoff.addProperty("handoffLeafPath", port);
            handoff.addProperty("javaType", "int");
            handoff.addProperty("direction", "RESPONSE");
            handoff.addProperty("side", "IN");
            handoff.addProperty("captureKind", "METHOD_RETURN");
            handoff.addProperty("definitionMethod", "example.Consumer.receive");
            return handoff;
        }

        private static JsonObject activation(String task, String occurrence) {
            JsonObject result = new JsonObject();
            result.addProperty("taskId", task);
            result.addProperty("occurrenceId", occurrence);
            return result;
        }

        private static RegionInstancePlan admitted(
                String region, String occurrence, String basis, Integer depth,
                String targetMethod) {
            JsonObject encoded = plan("s", region, occurrence,
                    "GOAL." + region, false, new JsonArray()).json().deepCopy();
            encoded.addProperty("targetMethod", targetMethod);
            if (basis != null) encoded.addProperty("admissionBasis", basis);
            if (depth != null) encoded.addProperty("demandDepth", depth);
            return RegionInstancePlan.decode(encoded);
        }

        private static RegionInstancePlan plan(String source, String region,
                                               String occurrence, String goal,
                                               boolean target, JsonArray edges) {
            return plan(source, region, occurrence, goal, target, edges, null);
        }

        private static RegionInstancePlan plan(String source, String region,
                                               String occurrence, String goal,
                                               boolean target, JsonArray edges,
                                               Long targetEvent) {
            JsonObject branch = new JsonObject();
            branch.addProperty("failureTarget", target);
            branch.addProperty("loopControlGuard", false);
            branch.addProperty("observed", target);
            if (target) {
                branch.addProperty("requiredOutcome", false);
                branch.addProperty("siteId", "example.Target#u1");
                if (targetEvent != null) {
                    branch.addProperty("selectedRuntimeEventSeq", targetEvent);
                }
            }
            JsonArray branches = new JsonArray();
            branches.add(branch);
            JsonObject admission = new JsonObject();
            admission.addProperty("state", "READY");
            JsonObject closure = new JsonObject();
            closure.addProperty("goalId", goal);
            closure.addProperty("kind", target
                    ? "TARGET_REACH_CLOSURE" : "REGION_PATH_CLOSURE");
            closure.add("admission", admission);
            closure.add("branches", branches);
            closure.add("runtimeDefinitionMethods", new JsonArray());
            closure.add("edgeBindings", edges.deepCopy());
            JsonArray closures = new JsonArray();
            closures.add(closure);
            JsonObject encoded = new JsonObject();
            encoded.addProperty("sourceKey", source);
            encoded.addProperty("occurrenceId", occurrence);
            encoded.addProperty("relationKey", source + "/relation/" + region);
            encoded.addProperty("regionId", region);
            encoded.add("closureGoals", closures);
            return RegionInstancePlan.decode(encoded);
        }

        private static JsonObject taskSummary(String scope, String source,
                                              String region, String goal,
                                              String task, String occurrence) {
            JsonObject summary = new JsonObject();
            summary.addProperty("boundarySessionScope", scope);
            summary.addProperty("sourceKey", source);
            summary.addProperty("regionId", region);
            summary.addProperty("goalId", goal);
            summary.addProperty("taskId", task);
            summary.addProperty("occurrenceId", occurrence);
            return summary;
        }

        private static JsonObject guardedWriterRecord(
                String scope, String readerOccurrence,
                String writerOccurrence) {
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConSymbolExp");
            expression.addProperty("_java_type", "I");
            expression.addProperty("_exp", "C_I_1");
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", 2L);
            version.addProperty("versionKind", "WRITE");
            version.addProperty("regionEnterEventId", 10L);
            version.addProperty("regionId", "R.W");
            version.addProperty("taskId", "TASK.W");
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    "source/w");
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    writerOccurrence);
            version.add("expression", expression);
            version.add("pathGuard", SharedStateEvidence.emptyConjunction());

            JsonObject read = new JsonObject();
            read.addProperty("readEventId", 20L);
            read.addProperty("regionEnterEventId", 19L);
            read.addProperty("regionId", "R.B");
            read.addProperty("taskId", "TASK.B");
            read.addProperty(SharedStateEvidence.READER_SOURCE_KEY, "source/b");
            read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                    readerOccurrence);
            read.addProperty("candidateCount", 1);

            JsonObject location = new JsonObject();
            location.addProperty("locationKind", "INSTANCE_FIELD");
            location.addProperty("ownerSymRid", 17L);
            location.addProperty("slot", 8);
            JsonObject envelope = new JsonObject();
            envelope.addProperty("kind",
                    SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
            envelope.addProperty("schemaVersion",
                    SharedStateEvidence.SCHEMA_VERSION);
            envelope.addProperty("selected", true);
            envelope.add("location", location);
            envelope.addProperty("writerSetComplete", true);
            JsonArray versions = new JsonArray();
            versions.add(version);
            envelope.add("versions", versions);
            envelope.addProperty("serializationTruncated", false);
            JsonArray reads = new JsonArray();
            reads.add(read);
            envelope.add("reads", reads);
            envelope.addProperty("readLogTruncated", false);
            JsonObject record = SharedStateEvidence.versionsRecord(
                    "INSTANCE_FIELD/17#8", envelope,
                    RecordedEvidenceIdentity.of("run", scope, "TASK.B",
                            readerOccurrence, "source/b", 1L));
            JsonArray records = new JsonArray();
            records.add(record);
            JsonObject recorded = new JsonObject();
            recorded.add("versions", records);
            return recorded;
        }
    }


    /** Focused authority tests for Boolean reach-condition extraction. */
    static final class RootValuationSolverTest {

        public void rootValuationSolverRules() throws Exception {
            manualTaskRootIsPublishedWithItsWitness();
            aRefusedCompositionRaisesNoGapsOfItsOwn();
            aNecessaryClockInsideItsWindowIsTheFinding();
            windowBoundaryPerturbationIsNotFaultSensitivity();
            necessaryMechanismIsTheOneThePolarityCannotDoWithout();
        }

        private void manualTaskRootIsPublishedWithItsWitness() throws Exception {
            Assume.assumeTrue(z3Available());
            JsonObject manifest = candidateManifest();
            JsonArray manual = new JsonArray();
            manual.add(manualBoolean());
            manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                    manual);

            String smt = "(set-logic ALL)\n"
                    + "(declare-const manual_enabled Bool)\n"
                    + "(assert manual_enabled)\n(check-sat)\n";
            JsonObject report = RootValuationSolver.extract(smt,
                    manifest, new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);

            assertEquals("CANDIDATE_READY", report.get("state").getAsString());
            JsonArray roots = report.getAsJsonObject("roots")
                    .getAsJsonArray("booleanInputs");
            assertEquals(1, roots.size());
            assertEquals("REGION.0.in.enabled", roots.get(0).getAsJsonObject()
                    .get("portId").getAsString());
            assertTrue(report.getAsJsonArray(
                    RootValuationSolver.SYMBOLIC_VARIABLE_MODELS)
                    .get(0).getAsJsonObject().getAsJsonArray("variables")
                    .get(0).getAsJsonObject().get("value").getAsBoolean());
        }

        /**
         * The laneBG shape: a refusal stated once, by the stage that refused.
         *
         * <p>A composition the Composer refused publishes a stub -- no source
         * ledger, no manual-root ledger, and a state that is not
         * CANDIDATE_READY.  This stage used to read each of those absences as a
         * gap of its own and publish three more codes beside the one refusal
         * the composition had already named.  They said nothing the refusal did
         * not: the ledgers were never written because the composition refused.
         * The refusal is read once, as {@code evidenceOnly}, and the report
         * carries no gaps of its own.</p>
         */
        private void aRefusedCompositionRaisesNoGapsOfItsOwn() throws Exception {
            Assume.assumeTrue(z3Available());
            JsonObject refused = new JsonObject();
            refused.addProperty("schemaVersion", 2);
            refused.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
            refused.addProperty("state", "CANDIDATE_WITH_GAPS");
            refused.addProperty(ComposedManifest.FINAL_STATUS, "FINAL_REFUSED");
            JsonArray refusals = new JsonArray();
            JsonObject refusal = new JsonObject();
            refusal.addProperty("kind", PathMergeComposer.TARGET_NOT_REACHED);
            refusal.addProperty("detail", "no exact reach query");
            refusals.add(refusal);
            refused.add("finalStatusRefusals", refusals);
            refused.add("gaps", new JsonArray());

            JsonObject report = RootValuationSolver.extract(
                    "(set-logic ALL)\n(assert false)\n(check-sat)\n",
                    refused, new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);

            assertEquals(0, report.getAsJsonArray("gaps").size());
            assertTrue(report.get(RootValuationSolver.EVIDENCE_ONLY)
                    .getAsBoolean());
            assertEquals("CANDIDATE_WITH_GAPS",
                    report.get("state").getAsString());
        }

        /**
         * A clock the target cannot reach without is the finding it names.
         *
         * <p>Nothing is flipped here -- the marker sits at what it recorded --
         * and the window the recording anchors the clock in is what lets the
         * comparison go the other way. The probe pins the clock back and the
         * formula dies, which is the only evidence that the move carried the
         * witness rather than accompanied it.</p>
         */
        private void aNecessaryClockInsideItsWindowIsTheFinding() throws Exception {
            Assume.assumeTrue(z3Available());
            // A configured source, not a planted marker: nothing was injected,
            // so the run is not asked to show a flip and the clock is the whole
            // of what it claims.
            JsonObject manifest = clockManifest("true");
            manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                    singleton(manualClock()));
            manifest.add(ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                    singleton(configuredBoolean()));
            String smt = "(set-logic ALL)\n"
                    + "(declare-const sym_enabled Bool)\n"
                    + "(declare-const clock_now Int)\n"
                    + "(assert (and sym_enabled (> clock_now 5000)"
                    + " (< clock_now 6000)))\n"
                    + "(check-sat)\n";

            JsonObject report = RootValuationSolver.extract(smt,
                    manifest, new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);

            JsonObject claim = report.getAsJsonObject(ClaimPolicy.CLAIM);
            JsonObject rootSpace = claim.getAsJsonObject("rootSpace");
            assertEquals(claim.getAsJsonArray("blockers").toString(),
                    ClaimPolicy.SAT_CANDIDATE, claim.get("claim").getAsString());
            assertEquals(WitnessLegitimacy.CLOCK_SKEW,
                    rootSpace.get("acceptedFindingKind").getAsString());
        }

        /** One Boolean marker and one wall clock, each with what it recorded. */
        private static JsonObject clockManifest(String recordedMarker) {
            JsonObject manifest = candidateManifest();
            JsonArray manual = new JsonArray();
            manual.add(manualBoolean());
            manual.add(manualClock());
            manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                    manual);
            manifest.add(ComposedManifest.RECORDED_ROOT_VALUES,
                    recordedRoots(recordedMarker));
            JsonObject physics = new JsonObject();
            physics.addProperty("schemaVersion", 1);
            physics.addProperty("kind", "CLOCK_ROOT_PHYSICS");
            physics.addProperty("clockSkewMillis", 300000);
            physics.add("clockReads", new JsonArray());
            manifest.add(ClockRootPhysics.MANIFEST_FIELD, physics);
            return manifest;
        }

        /** The configured Boolean root the necessary-clock fixture reads. */
        private static JsonObject configuredBoolean() {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 3);
            row.addProperty("kind",
                    ComposedManifest.CONFIGURED_SOURCE_MATERIALIZATION_KIND);
            row.addProperty("authority", ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY);
            row.addProperty("sourceKey", "hdfs/nn0#epoch1");
            row.addProperty("sourceId", "TEST.CONFIG.ENABLED");
            row.addProperty("sourcePhaseId", "SOURCE_PHASE.fixture");
            row.addProperty("sourceOccurrenceId",
                    "node/nn0#1/region/REGION.0#1#a1");
            row.addProperty("fieldSignature", "<Test: boolean enabled>");
            row.addProperty("javaTypeDescriptor", "Z");
            row.addProperty("sort", "BOOL");
            row.addProperty("smtSort", "Bool");
            row.addProperty("solverTerm", "sym_enabled");
            row.addProperty(ComposedManifest.RECORDED_SOURCE_VALUE, "true");
            return row;
        }

        private static JsonArray singleton(JsonObject row) {
            JsonArray rows = new JsonArray();
            rows.add(row);
            return rows;
        }

        private static JsonArray recordedRoots(String recordedMarker) {
            JsonObject marker = new JsonObject();
            marker.addProperty("portId", "REGION.0.in.enabled");
            marker.addProperty("siteId", "<Test: boolean enabled>");
            marker.addProperty("recordedValue", recordedMarker);
            marker.addProperty("solverTerm", "manual_enabled");
            marker.addProperty("wallClock", false);
            JsonObject clock = new JsonObject();
            clock.addProperty("portId", "REGION.0.in.now");
            clock.addProperty("siteId", "<Test: long now>");
            clock.addProperty("recordedValue", "1000");
            clock.addProperty("solverTerm", "clock_now");
            clock.addProperty("wallClock", true);
            JsonArray rows = new JsonArray();
            rows.add(marker);
            rows.add(clock);
            return rows;
        }

        private static JsonObject manualClock() {
            JsonObject row = manualBoolean();
            row.addProperty("portId", "REGION.0.in.now");
            row.addProperty("fieldSignature", "<Test: long now>");
            row.addProperty("javaTypeDescriptor", "J");
            row.addProperty("sort", "INT");
            row.addProperty("smtSort", "Int");
            row.addProperty("solverTerm", "clock_now");
            row.addProperty("sourceIdentity", "manual-root-now");
            return row;
        }

        /** The classified witness row at one valuation ordinal. */
        private static JsonObject witnessAt(JsonObject claim, int ordinal) {
            for (com.google.gson.JsonElement element
                    : claim.getAsJsonArray(WitnessLegitimacy.FINDINGS)) {
                JsonObject row = element.getAsJsonObject();
                if (row.get("valuationOrdinal").getAsInt() == ordinal) {
                    return row;
                }
            }
            throw new AssertionError("no witness row at ordinal " + ordinal);
        }

        /** The one freedom code a witness row names, or "". */
        private static String freedomCode(JsonObject witness) {
            JsonArray freedoms = witness.getAsJsonArray("freedoms");
            return freedoms.size() == 0 ? ""
                    : freedoms.get(0).getAsJsonObject().get("code").getAsString();
        }

        private static JsonObject candidateManifest() {
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", 2);
            manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
            manifest.addProperty("state", "CANDIDATE_READY");
            manifest.addProperty("guardedReadModelComplete", true);
            manifest.addProperty(ComposedManifest.FINAL_STATUS,
                    ComposedManifest.FINAL_READY);
            manifest.addProperty("symbolicPropagationComplete", true);
            manifest.add("symbolicPropagationGaps", new JsonArray());
            JsonObject guardedReads = new JsonObject();
            guardedReads.addProperty("schemaVersion", 1);
            guardedReads.addProperty("kind", "DIRECT_GUARDED_READ_MODEL");
            guardedReads.addProperty("authority",
                    "VM_READ_TIME_CANDIDATE_SNAPSHOT_V1");
            guardedReads.addProperty("complete", true);
            guardedReads.add("reads", new JsonArray());
            manifest.add("guardedReadModel", guardedReads);
            manifest.add("casePathConditionDependencies", new JsonArray());
            manifest.add("caseSelectorPartitions", new JsonArray());
            manifest.add("targetReachLedger", new JsonArray());
            manifest.add(ComposedManifest
                    .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, new JsonArray());
            manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                    new JsonArray());
            return manifest;
        }

        private static JsonObject manualBoolean() {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind",
                    ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_KIND);
            row.addProperty("authority",
                    ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
            row.addProperty("portId", "REGION.0.in.enabled");
            row.addProperty("occurrenceId", "node/nn0#1/region/REGION.0#1#a1");
            row.addProperty("fieldSignature", "<Test: boolean enabled>");
            row.addProperty("javaTypeDescriptor", "Z");
            row.addProperty("sort", "BOOL");
            row.addProperty("smtSort", "Bool");
            row.addProperty("solverTerm", "manual_enabled");
            row.addProperty("sourceIdentity", "manual-root-enabled");
            row.addProperty("sourceIdentityAuthority",
                    SymbolicSourceEvidence.MANUAL_AUTHORITY);
            return row;
        }

        private static boolean z3Available() {
            try {
                Process process = new ProcessBuilder("z3", "-version").start();
                return process.waitFor() == 0;
            } catch (Exception unavailable) {
                return false;
            }
        }

        /**
         * HDFS-17897's witness sat on its clock's own window floor: the recorded
         * read 1789234993718 with the window collapsed onto it. The probe then
         * tried 1789234993717, the solver refused it because it leaves the
         * window, and that refusal was credited as proof that the target depends
         * on the clock. It proves only that {@link ClockRootPhysics} works.
         */
        private void windowBoundaryPerturbationIsNotFaultSensitivity()
                throws Exception {
            Assume.assumeTrue(z3Available());
            long recorded = 1789234993718L;
            JsonObject manifest = clockRootManifest(recorded, 0L);
            String smt = "(set-logic ALL)\n"
                    + "(declare-const " + CLOCK_TERM + " Int)\n"
                    + "(assert (and (>= " + CLOCK_TERM + " " + recorded + ")"
                    + " (<= " + CLOCK_TERM + " " + recorded + ")))\n"
                    + "(check-sat)\n";

            JsonObject report = RootValuationSolver.extract(smt,
                    manifest, new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);

            JsonObject probe = report.getAsJsonObject("existentialRootProbe");
            assertFalse("a window-boundary refusal is not fault sensitivity",
                    probe.get("constrainsRootSpace").getAsBoolean());
            JsonArray perturbations = probe.getAsJsonArray("perturbations");
            assertTrue(perturbations.size() > 0);
            boolean sawBoundary = false;
            for (int index = 0; index < perturbations.size(); index++) {
                JsonObject row = perturbations.get(index).getAsJsonObject();
                assertEquals("skipped", row.get("status").getAsString());
                assertEquals(RootValuationSolver.WINDOW_BOUNDARY,
                        row.get("rejectedBy").getAsString());
                sawBoundary |= String.valueOf(recorded - 1L).equals(
                        row.get("perturbedValue").getAsString());
            }
            assertTrue("the 1789234993717 neighbour is named and not solved",
                    sawBoundary);
        }

        private static JsonObject readArm(String valueTerm, String owner,
                                          String carrier, String selector) {
            JsonObject arm = new JsonObject();
            arm.addProperty("selector", selector);
            arm.addProperty("valueTerm", valueTerm);
            arm.addProperty("writerCaseOwner", owner);
            arm.addProperty("sessionLocationKey", carrier);
            arm.addProperty("locationKey", carrier + "/full");
            arm.addProperty("readIdentity", "RFC.a1");
            arm.addProperty("candidateIdentity", "RFC_ARM." + selector);
            return arm;
        }

        private static final String CLOCK_TERM = "manual__clock";

        /** A manifest with one symbolized wall clock and its declared window. */
        private static JsonObject clockRootManifest(long recorded,
                                                    long skewMillis) {
            JsonObject manifest = candidateManifest();
            JsonObject root = new JsonObject();
            root.addProperty("schemaVersion", 1);
            root.addProperty("kind", ComposedManifest
                    .MANUAL_SOURCE_MATERIALIZATION_KIND);
            root.addProperty("authority", ComposedManifest
                    .MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
            root.addProperty("portId", "REGION.clock.in.now");
            root.addProperty("occurrenceId",
                    "hdfs/nn0#epoch0/region/REGION.clock#1");
            root.addProperty("javaTypeDescriptor", "J");
            root.addProperty("sort", "INT");
            root.addProperty("smtSort", "Int");
            root.addProperty("solverTerm", CLOCK_TERM);
            root.addProperty("sourceIdentity", "MANUAL.clock");
            root.addProperty("sourceIdentityAuthority",
                    "PLANNED_MANUAL_SYMBOLIZATION_V1");
            JsonArray roots = new JsonArray();
            roots.add(root);
            manifest.add(ComposedManifest.MANUAL_SOURCE_MATERIALIZATION_FIELD,
                    roots);

            JsonObject clockRead = new JsonObject();
            clockRead.addProperty("sourceKey", "hdfs/nn0#epoch0");
            clockRead.addProperty("portId", "REGION.clock.in.now");
            clockRead.addProperty("recordedValue", recorded);
            clockRead.addProperty("solverTerm", CLOCK_TERM);
            JsonArray clockReads = new JsonArray();
            clockReads.add(clockRead);
            manifest.add(ClockRootPhysics.MANIFEST_FIELD,
                    ClockRootPhysics.manifest(skewMillis,
                            java.util.Collections.singletonList(clockRead)));
            return manifest;
        }

        /**
         * hdfs-17899-bug3's witness named ten CLOCK_SKEW rows for the polarity
         * with no fault, six of them strictly inside the window -- and the target
         * was still reachable with every clock back at its recorded value. The
         * necessity probe asks exactly that, once per named mechanism.
         */
        private void necessaryMechanismIsTheOneThePolarityCannotDoWithout()
                throws Exception {
            Assume.assumeTrue(z3Available());
            long recorded = 1789234993718L;

            // The target needs the fault, or a clock that moved: pinning the clock
            // back to what it read leaves the no-fault polarity unsatisfiable.
            JsonObject necessary = RootValuationSolver.extract(
                    markerAndClockSmt(recorded, "(> " + CLOCK_TERM + " "
                            + recorded + ")"),
                    markerAndClockManifest(recorded),
                    new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);
            assertTrue(mechanismNecessary(necessary));

            // The same shape with the clock free of the target: it moves because
            // nothing holds it, and pinning it changes nothing.
            JsonObject decoration = RootValuationSolver.extract(
                    markerAndClockSmt(recorded, "true"),
                    markerAndClockManifest(recorded),
                    new RootValuationSolver.Z3Solver(
                            "z3", 20_000L, new JsonArray(), 1), 8, 64);
            assertFalse(mechanismNecessary(decoration));
        }

        private static boolean mechanismNecessary(JsonObject report) {
            JsonObject probe = report.getAsJsonObject(
                    RootValuationSolver.MECHANISM_NECESSITY);
            JsonArray rows = probe.getAsJsonArray("mechanisms");
            for (int index = 0; index < rows.size(); index++) {
                JsonObject row = rows.get(index).getAsJsonObject();
                if (!row.get("polarity").getAsBoolean()
                        && row.get("necessary").getAsBoolean()) {
                    return true;
                }
            }
            return false;
        }

        private static final String MARKER_TERM = "manual__fault";

        /** Reach the target with the fault, or with {@code without} instead. */
        private static String markerAndClockSmt(long recorded, String without) {
            return "(set-logic ALL)\n"
                    + "(declare-const " + MARKER_TERM + " Bool)\n"
                    + "(declare-const " + CLOCK_TERM + " Int)\n"
                    + "(assert (and (>= " + CLOCK_TERM + " " + (recorded - 300000L)
                    + ") (<= " + CLOCK_TERM + " " + (recorded + 300000L) + ")))\n"
                    + "(assert (or " + MARKER_TERM + " " + without + "))\n"
                    + "(check-sat)\n";
        }

        private static JsonObject markerAndClockManifest(long recorded) {
            JsonObject manifest = clockRootManifest(recorded, 300000L);
            JsonArray roots = manifest.getAsJsonArray(ComposedManifest
                    .MANUAL_SOURCE_MATERIALIZATION_FIELD);
            JsonObject marker = roots.get(0).getAsJsonObject().deepCopy();
            marker.addProperty("portId", "REGION.rpc.in.fault");
            marker.addProperty("occurrenceId",
                    "hdfs/dn0#epoch0/region/REGION.rpc#1");
            marker.addProperty("javaTypeDescriptor", "Z");
            marker.addProperty("sort", "BOOL");
            marker.addProperty("smtSort", "Bool");
            marker.addProperty("solverTerm", MARKER_TERM);
            marker.addProperty("sourceIdentity", "MANUAL.fault");
            roots.add(marker);

            JsonArray ledger = new JsonArray();
            ledger.add(recordedRoot(CLOCK_TERM, Long.toString(recorded), true));
            ledger.add(recordedRoot(MARKER_TERM, "false", false));
            manifest.add(ComposedManifest.RECORDED_ROOT_VALUES, ledger);
            return manifest;
        }

        private static JsonObject recordedRoot(String term, String value,
                                               boolean wallClock) {
            JsonObject row = new JsonObject();
            row.addProperty("solverTerm", term);
            row.addProperty("recordedValue", value);
            row.addProperty("wallClock", wallClock);
            return row;
        }

    }

}
