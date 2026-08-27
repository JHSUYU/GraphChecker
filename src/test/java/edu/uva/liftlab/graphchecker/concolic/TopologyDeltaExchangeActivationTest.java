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
import static org.junit.Assert.assertTrue;

/**
 * README Step 1 judges topology at the RPC exchange event, whose identity is
 * the (sender occurrence, receiver occurrence, port) triple.  OCC-1 names the
 * activation that ran as {@code <plannedAddress>#a<ordinal>}, and a frozen
 * plan can only ever declare the planned address -- the ordinal does not
 * exist until the run happens.
 *
 * <p>These tests pin both halves of that.  A declared exchange observed at
 * any activation is at the fixed point and re-classifying it never reports a
 * divergence, which is what lets a campaign stop; and an endpoint or port
 * outside the frozen catalog still diverges, at its planned address, which is
 * what keeps the loop fail-closed.</p>
 */
public class TopologyDeltaExchangeActivationTest {
    private static final String REGION = "REGION.RECEIVER";
    private static final String RELATION = "test/receiver/REGION.RECEIVER";
    private static final String RECEIVER =
            "test/receiver#epoch0/region/REGION.RECEIVER#1";
    private static final String SENDER =
            "test/sender#epoch0/region/REGION.SENDER#9";
    private static final String OTHER_SENDER =
            "test/sender#epoch0/region/REGION.SENDER#1";
    private static final String EXCHANGE_PORT = "XCH.declared.resp.value";
    private static final String OUTPUT_PORT = "REGION.RECEIVER.out.0";

    /**
     * The frozen plan declared this exchange; the VM reported it out of the
     * sender's third activation.  Nothing outside the catalog was observed,
     * so this is a case of the declared topology and not a re-plan.
     */
    @Test
    public void aDeclaredExchangeObservedAtAnActivationIsNotADivergence() {
        List<JsonObject> rows = classify(SENDER + "#a3", EXCHANGE_PORT);

        assertEquals(rows.toString(), 1, rows.size());
        assertEquals(rows.toString(), TopologyDelta.NEW_OCCURRENCE,
                rows.get(0).get("deltaKind").getAsString());
        assertEquals("the exchange is at the fixed point",
                rows.get(0).get("plannedSchemaDigest").getAsString(),
                rows.get(0).get("observedSchemaDigest").getAsString());
    }

    /**
     * The fixed point is a fixed point: the next iteration re-plans the same
     * frozen exchange, observes it at a further activation, and still reports
     * no divergence.  A comparison that kept the ordinal would report every
     * declared exchange as new on every iteration, so no campaign over an
     * RPC topology could ever stop.
     */
    @Test
    public void theSameDeclaredExchangeStaysConvergedAcrossIterations() {
        for (int ordinal = 1; ordinal <= 12; ordinal++) {
            List<JsonObject> rows = classify(SENDER + "#a" + ordinal,
                    EXCHANGE_PORT);
            assertEquals("activation " + ordinal + ": " + rows,
                    0, divergences(rows));
        }
    }

    /**
     * A pre-OCC-1 handoff states the planned address itself.  It is the same
     * member and stays converged.
     */
    @Test
    public void aHandoffWithNoActivationOrdinalIsTheSameMember() {
        List<JsonObject> rows = classify(SENDER, EXCHANGE_PORT);
        assertEquals(rows.toString(), 0, divergences(rows));
    }

    /**
     * Fail-closed: a sender occurrence the frozen plan never declared is a
     * real topology change and is still reported -- once, at its planned
     * address, however many activations of it the run happened to name.
     */
    @Test
    public void anUndeclaredSenderOccurrenceStillDiverges() {
        List<JsonObject> rows = classify(OTHER_SENDER + "#a4", EXCHANGE_PORT);

        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                row.get("deltaKind").getAsString());
        JsonArray divergences = row.getAsJsonArray("divergences");
        assertEquals(divergences.toString(), 1, divergences.size());
        JsonObject reported = divergences.get(0).getAsJsonObject();
        assertEquals("exchangeSchema", reported.get("field").getAsString());
        assertEquals("the change is named at the planned address",
                OTHER_SENDER + "\n" + RECEIVER + "\n" + EXCHANGE_PORT,
                reported.get("observed").getAsString());
    }

    /**
     * Fail-closed: an undeclared port over a declared pair of endpoints is
     * still a new exchange event.
     */
    @Test
    public void anUndeclaredPortStillDiverges() {
        List<JsonObject> rows = classify(SENDER + "#a2", "XCH.undeclared.req");

        assertEquals(rows.toString(), 1, rows.size());
        JsonObject row = rows.get(0);
        assertEquals(TopologyDelta.TOPOLOGY_DIVERGENCE,
                row.get("deltaKind").getAsString());
        assertTrue(row.toString(), row.getAsJsonArray("divergences")
                .toString().contains("XCH.undeclared.req"));
    }

    private static int divergences(List<JsonObject> rows) {
        int total = 0;
        for (JsonObject row : rows) {
            if (TopologyDelta.TOPOLOGY_DIVERGENCE.equals(
                    row.get("deltaKind").getAsString())) {
                total += row.getAsJsonArray("divergences").size();
            }
        }
        return total;
    }

    /** Classifies one admitted result whose only VM handoff names this
     *  producer occurrence and this receiving port. */
    private static List<JsonObject> classify(String producerOccurrence,
                                             String portId) {
        ExecutionTask task = ExecutionTask.decode(task());
        TopologyDelta delta = new TopologyDelta("iteration-1",
                Collections.singletonList(task));

        JsonObject handoff = new JsonObject();
        handoff.addProperty(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID,
                producerOccurrence);
        handoff.addProperty("portId", portId);
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        JsonObject raw = new JsonObject();
        raw.addProperty("taskId", "TASK.RECEIVER");
        raw.add(VmHandoffEvidence.FIELD, handoffs);

        JsonObject summary = new JsonObject();
        JsonObject outputs = new JsonObject();
        outputs.addProperty(OUTPUT_PORT, "value");
        summary.add("outputExpressions", outputs);
        TopologyDelta.Observation admitted = new TopologyDelta.Observation();
        admitted.summary = summary;

        delta.classify(task,
                new ConcolicSummaryImporter.ResultRow(raw, 0), admitted);
        return delta.rows();
    }

    /** One receiver whose frozen catalog declares exactly one exchange. */
    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.RECEIVER");
        task.addProperty("goalId", "GOAL.RECEIVER");
        task.addProperty("regionId", REGION);
        task.addProperty("sourceKey", "test/receiver#epoch0");
        task.addProperty("occurrenceId", RECEIVER);
        task.addProperty("relationKey", RELATION);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        JsonObject edge = new JsonObject();
        edge.addProperty("fromOccurrenceId", SENDER);
        edge.addProperty("toOccurrenceId", RECEIVER);
        edge.addProperty("toInputPort", EXCHANGE_PORT);
        edge.addProperty("fromOutputPort", EXCHANGE_PORT);
        JsonArray edges = new JsonArray();
        edges.add(edge);
        task.add("edgeBindings", edges);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.singleton(
                RELATION, REGION, Collections.<String>emptyList(),
                OUTPUT_PORT, "<Test: int output>", "REGION_OUTPUT", "int",
                slice()));
        return task;
    }

    private static JsonObject slice() {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", OUTPUT_PORT);
        slice.addProperty("outputCell", "<Test: int output>");
        for (String member : new String[]{"inputPorts", "sites",
                "staticSites", "methods", "causalEdgeIds", "captureBindings",
                "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        return slice;
    }
}
