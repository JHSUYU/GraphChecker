package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A capture binding id is occurrence-scoped, but the instrumentation that
 * carries it is not.
 *
 * <p>{@code run_engine.sh campaign_instrument} rewrites the classes once per
 * iteration over the union of the planned task ids, and a capture binding id
 * reaches the VM only as a string literal compiled into that one class set.
 * Two occurrences of one region that declare the same output site therefore
 * put two ids on that one bytecode site, and both fire in whichever
 * activation runs it -- so an activation reports ids of tasks it was not
 * scheduled for.  The frozen plan, not one task, is the scope that decides
 * whether a reported id is declared.</p>
 *
 * <p>What must stay falsifiable is the other half: the VM never mints a
 * capture id, so an id no task of this plan declares can only have come from
 * a class set this plan did not instrument.  That is a stale instrumented
 * tree and it must still diverge.</p>
 */
public class TopologyDeltaSessionCaptureScopeTest {
    private static final String REGION = "REGION.CAPTURE";
    private static final String RELATION = "test/source/REGION.CAPTURE";
    private static final String OCCURRENCE_ONE =
            "test/source#epoch0/region/REGION.CAPTURE#1";
    private static final String OCCURRENCE_NINE =
            "test/source#epoch0/region/REGION.CAPTURE#9";
    private static final String PORT = "REGION.CAPTURE.out.0";
    private static final String CELL = "<Test: int output>";
    private static final String CAPTURE_ONE = "CAPTURE.occurrence-1";
    private static final String CAPTURE_NINE = "CAPTURE.occurrence-9";

    /**
     * The activation of the first occurrence reported the id the sibling
     * occurrence declares at the same output site.  Both ids are in the
     * frozen plan, so this is a local case of the declared topology -- and
     * the sibling id is named on the row, never dropped in silence.
     */
    @Test
    public void aSiblingTaskCaptureBindingIsNotADivergence() {
        ExecutionTask one = ExecutionTask.decode(
                task("TASK.ONE", OCCURRENCE_ONE, CAPTURE_ONE));
        ExecutionTask nine = ExecutionTask.decode(
                task("TASK.NINE", OCCURRENCE_NINE, CAPTURE_NINE));
        TopologyDelta delta = new TopologyDelta("iteration-1",
                Arrays.asList(one, nine));

        List<JsonObject> rows = classify(delta, one,
                CAPTURE_ONE, CAPTURE_NINE);

        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(row.toString(), TopologyDelta.NEW_OCCURRENCE,
                row.get("deltaKind").getAsString());
        assertEquals("the sibling id is named on the row",
                "[\"" + CAPTURE_NINE + "\"]",
                row.getAsJsonArray("siblingDeclaredCaptureBindings")
                        .toString());
    }

    /**
     * Fail-closed, and the reason the widening is sound: an id <em>no</em>
     * task of this frozen plan declares still diverges.  The VM mints no
     * capture id, so such an id names a class set this plan did not
     * instrument -- a stale instrumented tree, which must re-plan.
     */
    @Test
    public void aCaptureBindingNoTaskDeclaresStillDiverges() {
        ExecutionTask one = ExecutionTask.decode(
                task("TASK.ONE", OCCURRENCE_ONE, CAPTURE_ONE));
        ExecutionTask nine = ExecutionTask.decode(
                task("TASK.NINE", OCCURRENCE_NINE, CAPTURE_NINE));
        TopologyDelta delta = new TopologyDelta("iteration-1",
                Arrays.asList(one, nine));

        List<JsonObject> rows = classify(delta, one,
                CAPTURE_ONE, "CAPTURE.from-a-stale-class-tree");

        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(row.toString(), TopologyDelta.TOPOLOGY_DIVERGENCE,
                row.get("deltaKind").getAsString());
        JsonArray divergences = row.getAsJsonArray("divergences");
        assertEquals(divergences.toString(), 1, divergences.size());
        JsonObject reported = divergences.get(0).getAsJsonObject();
        assertEquals("outputSchema", reported.get("field").getAsString());
        assertEquals("CAPTURE.from-a-stale-class-tree",
                reported.get("observed").getAsString());
        assertFalse(row.toString(),
                row.has("siblingDeclaredCaptureBindings"));
    }

    /**
     * The scope is the frozen plan of <em>this</em> iteration.  A plan that
     * schedules the first occurrence alone never declared the sibling id, so
     * the same observation is a divergence there.
     */
    @Test
    public void aSiblingIdIsOnlyDeclaredWhenThatSiblingIsScheduled() {
        ExecutionTask one = ExecutionTask.decode(
                task("TASK.ONE", OCCURRENCE_ONE, CAPTURE_ONE));
        TopologyDelta delta = new TopologyDelta("iteration-1",
                Collections.singletonList(one));

        List<JsonObject> rows = classify(delta, one,
                CAPTURE_ONE, CAPTURE_NINE);

        assertEquals(rows.toString(), 1, rows.size());
        assertEquals(rows.toString(), TopologyDelta.TOPOLOGY_DIVERGENCE,
                rows.get(0).get("deltaKind").getAsString());
        assertTrue(rows.toString(), rows.get(0)
                .getAsJsonArray("divergences").toString()
                .contains(CAPTURE_NINE));
    }

    /** The plan digest is still the digest of the whole frozen plan. */
    @Test
    public void theRowStillCarriesTheWholePlanDigest() {
        ExecutionTask one = ExecutionTask.decode(
                task("TASK.ONE", OCCURRENCE_ONE, CAPTURE_ONE));
        ExecutionTask nine = ExecutionTask.decode(
                task("TASK.NINE", OCCURRENCE_NINE, CAPTURE_NINE));
        TopologyDelta delta = new TopologyDelta("iteration-1",
                Arrays.asList(one, nine));

        List<JsonObject> rows = classify(delta, one, CAPTURE_ONE);

        assertEquals(TopologyDelta.planDigest(Arrays.asList(one, nine)),
                rows.get(0).get("planDigest").getAsString());
    }

    private static List<JsonObject> classify(TopologyDelta delta,
                                             ExecutionTask task,
                                             String... observedBindings) {
        JsonArray captures = new JsonArray();
        for (String binding : observedBindings) {
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", binding);
            captures.add(capture);
        }
        JsonObject raw = new JsonObject();
        raw.addProperty("taskId", task.taskId());
        raw.add("outputCaptures", captures);

        JsonObject summary = new JsonObject();
        JsonObject outputs = new JsonObject();
        outputs.addProperty(PORT, "value");
        summary.add("outputExpressions", outputs);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = summary;

        delta.classify(task, new ConcolicSummaryImporter.ResultRow(raw, 0),
                admitted);
        return delta.rows();
    }

    /** One occurrence of one region, binding one capture at one site. */
    private static JsonObject task(String taskId, String occurrenceId,
                                   String captureBindingId) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL.CAPTURE");
        task.addProperty("regionId", REGION);
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", RELATION);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                RELATION, REGION, Collections.<String>emptyList(), PORT,
                CELL, "REGION_OUTPUT", "int", slice(captureBindingId)));
        return task;
    }

    /** The one output site both occurrences of this region declare. */
    private static JsonObject slice(String captureBindingId) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", PORT);
        slice.addProperty("outputCell", CELL);
        for (String member : new String[]{"inputPorts", "sites",
                "staticSites", "methods", "causalEdgeIds",
                "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", captureBindingId);
        capture.addProperty("captureKind",
                OutputCaptureSpec.REGION_EXIT_FIELD);
        capture.addProperty("outputPort", PORT);
        capture.addProperty("outputCell", CELL);
        capture.addProperty("fieldSignature", CELL);
        JsonArray path = new JsonArray();
        path.add("output");
        capture.add("fieldPath", path);
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", REGION + ".in.0");
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return slice;
    }
}
