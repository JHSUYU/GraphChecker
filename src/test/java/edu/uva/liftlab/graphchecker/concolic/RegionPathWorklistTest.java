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
    public void aTaskWithNoObservedSummaryIsGappedAndNamesTheMissingSeed() {
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

    @Test
    public void observedOppositeOutcomesCloseTheSemanticFlip() {
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

    @Test
    public void oneFlipCarriesTheWholeDependencyClosure() {
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
    @Test
    public void aBySitePhaseIsAssignedToEveryOwnerIncludingCompanions() {
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
    @Test
    public void aDecisionOverAnArrivedValueIsFlippableThroughItsHandoff() {
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
    @Test
    public void theTargetsFatalArmIsPlannedWhenTheSeedMissedIt() {
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
    @Test
    public void aFatalArmWithNoControlIsNamed() {
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
}
