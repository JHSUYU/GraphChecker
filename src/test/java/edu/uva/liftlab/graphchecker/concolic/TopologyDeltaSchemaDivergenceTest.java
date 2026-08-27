package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * README {@code GRAPH-1}: "Same topology adds a case; new
 * site/endpoint/source/occurrence/slot/schema starts the next immutable
 * iteration."  Every member set the schema digest is taken over decides that
 * question, so each of them is compared - and each of them may legitimately
 * shrink, which is a missing observation and not a new topology.
 */
public class TopologyDeltaSchemaDivergenceTest {
    private static final String REGION = "REGION.SCHEMA";
    private static final String RELATION = "test/source/REGION.SCHEMA";
    private static final String OCCURRENCE =
            "test/source#epoch0/region/REGION.SCHEMA#1";
    private static final String PORT = "REGION.SCHEMA.out.0";
    private static final String SYMBOL = "SYM.value";

    /**
     * The occurrence produced an output slot the frozen closure never
     * declared, and no new capture binding backs it: the binding set still
     * matches the plan exactly.  A slot is a slot however it was produced, so
     * this relation belongs to the next iteration's plan and publishes no
     * local case at all.
     */
    @Test
    public void newOutputSlotDivergesEvenWithoutANewCaptureBinding() {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta delta = delta(task);

        JsonObject summary = new JsonObject();
        JsonObject outputs = new JsonObject();
        outputs.addProperty(PORT, "value");
        outputs.addProperty(REGION + ".out.1", "unplanned");
        summary.add("outputExpressions", outputs);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = summary;
        delta.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw(), 0), admitted);

        List<JsonObject> rows = delta.rows();
        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                row.get("deltaKind").getAsString());
        JsonArray divergences = row.getAsJsonArray("divergences");
        assertEquals(divergences.toString(), 1, divergences.size());
        assertEquals("outputSchema", divergences.get(0).getAsJsonObject()
                .get("field").getAsString());
        assertEquals(REGION + ".out.1", divergences.get(0).getAsJsonObject()
                .get("observed").getAsString());
        // The class contract: a differing schema digest is an observed
        // contradiction, and here it is exactly the one just named.
        assertFalse(row.get("plannedSchemaDigest").getAsString().equals(
                row.get("observedSchemaDigest").getAsString()));
    }

    /**
     * The mirror image: this run resolved none of its planned inputs and
     * captured none of its demanded output relation.  Nothing outside the
     * frozen schema was observed, so the topology is unchanged and the case
     * is published - with the two partially observed components named rather
     * than silently reported as agreement.  The Importer already owns the
     * incomplete-relation diagnostic for the same run.
     */
    @Test
    public void shrunkenSchemaSetsAreNamedMissingObservationsNotDivergences() {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta delta = delta(task);

        JsonObject raw = raw();
        JsonArray unresolved = new JsonArray();
        unresolved.add(SYMBOL + ": field materialization failed");
        raw.add("unresolvedInputs", unresolved);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = new JsonObject();
        admitted.summary.add("outputExpressions", new JsonObject());
        delta.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw, 0), admitted);

        List<JsonObject> rows = delta.rows();
        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(TopologyDelta.NEW_OCCURRENCE,
                row.get("deltaKind").getAsString());
        assertEquals(row.get("plannedSchemaDigest").getAsString(),
                row.get("observedSchemaDigest").getAsString());
        String unobserved = row.getAsJsonArray("unobservedSchemaFields")
                .toString();
        assertTrue(unobserved, unobserved.contains("inputSymbols"));
        assertTrue(unobserved, unobserved.contains("outputPorts"));
    }

    private static TopologyDelta delta(ExecutionTask task) {
        return new TopologyDelta("iteration-1",
                Collections.singletonList(task));
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.SCHEMA");
        task.addProperty("goalId", "GOAL.SCHEMA");
        task.addProperty("regionId", REGION);
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", RELATION);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("symbol", SYMBOL);
        JsonArray actions = new JsonArray();
        actions.add(action);
        task.add("inputActions", actions);
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                RELATION, REGION, Collections.<String>emptyList(), PORT, "<Test: int output>",
                "REGION_OUTPUT", "int", slice()));
        return task;
    }

    /** One demanded output port whose capture list the plan leaves empty. */
    private static JsonObject slice() {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", PORT);
        slice.addProperty("outputCell", "<Test: int output>");
        for (String member : new String[]{"inputPorts", "sites",
                "staticSites", "methods", "causalEdgeIds", "captureBindings",
                "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        return slice;
    }

    private static JsonObject raw() {
        JsonObject raw = new JsonObject();
        raw.addProperty("taskId", "TASK.SCHEMA");
        return raw;
    }
}
