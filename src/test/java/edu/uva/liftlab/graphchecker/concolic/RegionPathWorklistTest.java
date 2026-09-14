package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Core contracts for the linked region-path worklist. */
public class RegionPathWorklistTest {

    /**
     * A target task whose replay published no summary at all.
     *
     * <p>There is nothing to explore and nothing to seed from, which is
     * what NO_OBSERVED_PATH_SEED says: the worklist states it and is
     * GAPPED, not failed, and the wave publishes it as that member's
     * closure so the gap withholds the claim.</p>
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

    /**
     * A decision over a value that arrived on a wire is flippable, and the
     * obligation carries the row that flips it.
     *
     * <p>Nothing about the arrived value is a root; what makes it varyable
     * is an assignment to the variable its handoff row names.</p>
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
    @Test
    public void theRootSliceDecidesWhichBranchesStayObligations() {
        JsonObject rooted = task("ROOTED", "REGION.ROOTED",
                "REGION.ROOTED/occurrence-1");
        JsonObject rootedSummary = summary(rooted, 1, true);
        rootedSummary.add(SymbolicSourceEvidence.FIELD,
                evidence(ROOT_PORT, ROOT_SYMBOL));

        RegionPathWorklist.Result result = planWith(rootedSummary, rooted,
                SymbolicRootInventory.of(
                        Collections.singletonList(rootedSummary),
                        Collections.singletonList(rooted)));

        assertEquals(1, result.tasks.size());
        JsonObject telemetry = telemetry(result);
        assertTrue(telemetry.get("rootSliceApplied").getAsBoolean());
        assertEquals(0, telemetry.get("closedByConstant").getAsInt());
        assertEquals(1, telemetry.getAsJsonArray("rootDependentSites").size());

        JsonObject plain = task("PLAIN", "REGION.PLAIN",
                "REGION.PLAIN/occurrence-1");
        JsonObject plainSummary = summary(plain, 1, true);

        SymbolicRootInventory roots = SymbolicRootInventory.of(
                Arrays.asList(rootedSummary, plainSummary),
                Arrays.asList(rooted, plain));
        RegionPathWorklist.Result closed = planWith(plainSummary, plain, roots);

        assertTrue(closed.tasks.isEmpty());
        assertEquals(RegionPathWorklist.State.CLOSED.name(),
                closed.manifest.get("state").getAsString());
        // Closing an obligation the recording already decided must not open
        // a coverage gap: the wave would keep re-planning proved-dead work.
        assertEquals(0, closed.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals("CLOSED",
                closed.manifest.get("coverageState").getAsString());

        JsonObject closedTelemetry = telemetry(closed);
        assertTrue(closedTelemetry.get("rootSliceApplied").getAsBoolean());
        assertEquals(1, closedTelemetry.get("closedByConstant").getAsInt());
        JsonObject row = closedTelemetry.getAsJsonArray("closedByConstantRows")
                .get(0).getAsJsonObject();
        assertEquals(RegionPathWorklist.CLOSED_BY_CONSTANT,
                optionalString(row, "kind"));
        assertEquals("SITE.PLAIN", optionalString(row, "siteId"));
        assertEquals("REGION.PLAIN", optionalString(row, "regionId"));
        // The constant: the outcome the recording took.
        assertTrue(row.get("recordedOutcome").getAsBoolean());

        // The same closure, now with a handoff gap the replay raised.  A
        // capture of a port some replay of this exploration DID attach ran
        // where no occurrence was selected; the delivery the paths carry is
        // the one that attached, so the row states a re-execution and not a
        // missing step, and the region still closes.
        JsonObject attached = summary(plain, 1, true);
        attached.add("alignmentGaps", handoffGaps("XCH.P.resp.leaf"));
        attached.add("vmHandoffEvents", attachedLeaf("XCH.P.resp.leaf"));
        RegionPathWorklist.Result delivered = planWith(attached, plain,
                SymbolicRootInventory.of(
                        Arrays.asList(rootedSummary, attached),
                        Arrays.asList(rooted, plain)));
        assertEquals(0,
                delivered.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals("CLOSED",
                delivered.manifest.get("coverageState").getAsString());

        // And a port nothing ever attached keeps withholding: fail-closed,
        // because a delivery no replay made is a step of the path that is
        // genuinely missing.  A row naming no port at all does too.
        JsonObject unbacked = summary(plain, 1, true);
        unbacked.add("alignmentGaps", handoffGaps("XCH.Q.resp.leaf"));
        unbacked.add("vmHandoffEvents", attachedLeaf("XCH.P.resp.leaf"));
        RegionPathWorklist.Result withheld = planWith(unbacked, plain,
                SymbolicRootInventory.of(
                        Arrays.asList(rootedSummary, unbacked),
                        Arrays.asList(rooted, plain)));
        assertEquals(1,
                withheld.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals("XCH.Q.resp.leaf", optionalString(
                withheld.manifest.getAsJsonArray("coverageGaps").get(0)
                        .getAsJsonObject(), RpcExpressionHandoff.PORT_FIELD));
        assertTrue(!"CLOSED".equals(
                withheld.manifest.get("coverageState").getAsString()));

        // The member that CONSUMES a port is not the member that delivers
        // it: this member's own summaries attach nothing, and the wave's
        // index is what says the port was delivered.  lane17897j withheld
        // closure on all ten paths of its anchor for exactly this -- 114
        // rows for a port whose 47 attaches were on another member.
        JsonObject elsewhere = summary(plain, 1, true);
        elsewhere.add("alignmentGaps", handoffGaps("XCH.R.resp.leaf"));
        RegionPathWorklist.Result waveDelivered = RegionPathWorklist.plan(
                Collections.singletonList(elsewhere),
                Collections.singletonList(plain),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults(),
                SymbolicRootInventory.of(
                        Arrays.asList(rootedSummary, elsewhere),
                        Arrays.asList(rooted, plain)),
                Collections.singleton("XCH.R.resp.leaf"));
        assertEquals(0,
                waveDelivered.manifest.getAsJsonArray("coverageGaps").size());
        assertEquals("CLOSED",
                waveDelivered.manifest.get("coverageState").getAsString());
        // And the wave index is read from the same place the campaign fold
        // reads it, so a summary that attached the port yields it.
        assertTrue(RegionPathWorklist.attachedHandoffPorts(
                Collections.singletonList(attached))
                .contains("XCH.P.resp.leaf"));
        assertTrue(RegionPathWorklist.attachedHandoffPorts(
                Collections.singletonList(elsewhere)).isEmpty());

        JsonObject anonymous = summary(plain, 1, true);
        JsonArray nameless = handoffGaps("XCH.P.resp.leaf");
        nameless.get(0).getAsJsonObject().remove(
                RpcExpressionHandoff.PORT_FIELD);
        anonymous.add("alignmentGaps", nameless);
        anonymous.add("vmHandoffEvents", attachedLeaf("XCH.P.resp.leaf"));
        RegionPathWorklist.Result unnamed = planWith(anonymous, plain,
                SymbolicRootInventory.of(
                        Arrays.asList(rootedSummary, anonymous),
                        Arrays.asList(rooted, plain)));
        assertEquals(1,
                unnamed.manifest.getAsJsonArray("coverageGaps").size());
    }

    /** One imported handoff gap, as the replay raised it for {@code port}. */
    private static JsonArray handoffGaps(String port) {
        JsonArray rows = new JsonArray();
        rows.add(RpcExpressionHandoff.portGap(
                RpcExpressionHandoff.STAGE_ATTACH,
                RpcExpressionHandoff.NO_ACTIVE_REGION, 0L, port,
                "capture ran outside every selected occurrence: " + port));
        return rows;
    }

    /** One attach of {@code port}, as some replay of this wave published it. */
    private static JsonArray attachedLeaf(String port) {
        JsonObject event = new JsonObject();
        event.addProperty("kind", "VM_RPC_EXPRESSION_HANDOFF");
        event.addProperty(RpcExpressionHandoff.PORT_FIELD, port);
        event.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                "HANDOFF_PHASE.FIXTURE");
        JsonArray rows = new JsonArray();
        rows.add(event);
        return rows;
    }

    /**
     * The prefix a replay must reproduce is pi: root-dependent decisions only.
     *
     * <p>A decision the VM contributed no path condition for has no
     * predicate at all, so no root occurs in it: it is the caller's own
     * state, not a step of this region's path, and it varies between two
     * runs of one recording.  Recording it is right; refusing a replay for
     * it is not, and the plan cannot make that call -- every branch is
     * planned EXPLORE -- so the observation is asked instead.</p>
     */
    @Test
    public void aConcreteDecisionIsNotPartOfTheReplayPrefix() {
        // A concrete decision that flipped is not a mismatch.
        assertEquals("", mismatch(concrete(U16, 1, true),
                concrete(U18, 1, true)));
        // A concrete decision at its recorded outcome is admitted as before.
        assertEquals("", mismatch(concrete(U16, 1, false),
                concrete(U18, 1, true)));
        // A site the plan never named is evidence when it is concrete.
        assertEquals("", mismatch(concrete(U16, 1, false),
                concrete(U18, 1, true),
                concrete(SEND + "#u49", 1, true)));
        // Lane B2c: a site a concrete divergence never reached is not missing
        // from pi.  The plan declares #u18 and the replay published no decision
        // there at all, because #u16 -- the IPC client's own connection state,
        // concrete -- went the other way and the path never reached it.  An
        // activation that decided nothing over a root has an empty pi, so no
        // site can be missing from it.
        assertEquals("", mismatch(concrete(U16, 1, true)));

        // A root-dependent decision that flipped is still a mismatch.
        assertRefusal("wrong decision at " + U16,
                witnessed(U16, 1, true), concrete(U18, 1, true));
        // ... and an unplanned site is still refused when it carried one.
        assertRefusal("unexpected " + SEND + "#u49",
                concrete(U16, 1, false), concrete(U18, 1, true),
                witnessed(SEND + "#u49", 1, true));
        // With a root-dependent decision in the activation, missing refuses.
        assertRefusal("missing " + U18, witnessed(U16, 1, false));
    }

    // --- fixture: the worklist ---------------------------------------------

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

    // --- fixture: the root slice -------------------------------------------

    private static final String ROOT_SYMBOL = "M_I_field_ROOTED_in";
    private static final String ROOT_PORT = "REGION.ROOTED.in.port-1";

    private static RegionPathWorklist.Result planWith(
            JsonObject summary, JsonObject task, SymbolicRootInventory roots) {
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

    /** The one declared root the rooted seed's decision rests on. */
    private static JsonArray evidence(String portId, String rawSymbol) {
        JsonArray rows = new JsonArray();
        rows.add(SymbolicSourceEvidence.manualEvent(portId,
                "REGION.ROOTED/occurrence-1#a1",
                "<fixture.Rooted: int declared>", "I", rawSymbol,
                "SOURCE.IDENTITY." + portId));
        return rows;
    }

    // --- fixture: lane B2's seed activation ---------------------------------

    private static final String SEND =
            "<org.apache.hadoop.ipc.Client$Connection: void sendRpcRequest("
                    + "org.apache.hadoop.ipc.Client$Call)>";
    private static final String U16 = SEND + "#u16";
    private static final String U4 = SEND + "#u4";
    private static final String U18 = SEND + "#u18";

    private static void assertRefusal(String expected,
                                      JsonObject... observed) {
        String refusal = mismatch(observed);
        assertTrue(refusal, refusal.contains(expected));
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
                seedTask(), mappings);
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

    /** The seed task, with lane B2's declared branches. */
    private static ExecutionTask seedTask() {
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
