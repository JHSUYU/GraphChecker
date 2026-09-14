package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

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
public class RootSliceObligationTest {
    private static final String ROOT_SYMBOL = "M_I_field_ROOT_in";
    private static final String ROOT_PORT = "REGION.ROOTED.in.port-1";

    @Test
    public void aBranchOnARootStaysAnObligation() {
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

    @Test
    public void aBranchOnNoRootIsClosedByTheRecording() {
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
