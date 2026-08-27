package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * The campaign's one feedback edge: an RPC pairing a replay recorded that the
 * frozen plan did not declare.
 *
 * <p>A receiver the plan schedules more than once alternates between the
 * sender occurrences the workload pairs it with, while the plan declares only
 * the pairing the baseline trace saw.  The pairing the replay actually took
 * is then a member no plan ever declares, {@link TopologyDelta} reports it on
 * every iteration, and the campaign has no fixed point to reach.</p>
 *
 * <p>Nothing is minted: the declared member is the sender task's own frozen
 * binding for that port, re-addressed to the receiver occurrence the handoff
 * attached at.  Every axis below is fail-closed -- refusing leaves the member
 * diverging, which is the safe direction.</p>
 */
public class ConcolicSchedulerObservedExchangeTest {
    private static final String SENDER_REGION = "REGION.SENDER";
    private static final String RECEIVER_REGION = "REGION.RECEIVER";
    private static final String SENDER_ONE =
            "test/sender#epoch0/region/REGION.SENDER#1";
    private static final String SENDER_NINE =
            "test/sender#epoch0/region/REGION.SENDER#9";
    private static final String RECEIVER_NINE =
            "test/receiver#epoch1/region/REGION.RECEIVER#9";
    private static final String RECEIVER_ONE =
            "test/receiver#epoch1/region/REGION.RECEIVER#1";
    private static final String PORT = "XCH.declared.req.keyId";
    private static final String SENDER_ONE_EDGE = "RPC.sender-one";
    private static final String SENDER_NINE_EDGE = "RPC.sender-nine";

    /**
     * The receiving occurrence ran twice; its second activation attached a
     * value the <em>first</em> sender occurrence exported.  Both occurrences
     * are scheduled, both endpoints are at their planned address, the send is
     * recorded strictly before the receive, and the receiver already declares
     * the port -- so the pairing is declared, out of the sender's own frozen
     * binding, and stamped with the evidence that produced it.
     */
    @Test
    public void aSiblingSenderPairingIsDeclaredFromTheSendersOwnBinding() {
        List<ExecutionTask> plan = plan();
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(1, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary(handoff())),
                refusals));
        assertEquals(refusals.toString(), 0, refusals.size());

        JsonObject declared = edge(plan.get(1), SENDER_ONE, RECEIVER_NINE);
        assertNotNull("the pairing is declared", declared);
        assertEquals("nothing is minted: the sender's own edge id",
                SENDER_ONE_EDGE, declared.get("edgeId").getAsString());
        assertEquals(PORT, declared.get("toInputPort").getAsString());
        assertEquals(VmHandoffEvidence.ABSORBED_AUTHORITY,
                declared.get(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD)
                        .getAsString());
        assertTrue("the row is stamped well enough to be re-derived",
                VmHandoffEvidence.absorbed(declared));
        assertEquals("TASK.SENDER", declared.get(
                VmHandoffEvidence.ABSORBED_FROM_TASK_ID).getAsString());
        assertEquals(222, declared.get(
                VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID).getAsLong());
        assertEquals(225, declared.get(
                VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID).getAsLong());
    }

    /**
     * An absorbed pairing is a pairing and nothing else.  It never becomes a
     * member of the {@link OutputClosureContract}: that would hand the
     * Composer a capture from another occurrence, the merge across a cut the
     * README forbids.  It also widens no frontier -- the ports this task
     * selects are exactly the ports it already selected.
     */
    @Test
    public void anAbsorbedPairingTouchesNoOutputContractAndNoNewPort() {
        List<ExecutionTask> plan = plan();
        JsonObject before = plan.get(1).json().deepCopy();
        before.remove("edgeBindings");

        assertEquals(1, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary(handoff())),
                new TreeMap<String, Integer>()));

        JsonObject after = plan.get(1).json().deepCopy();
        JsonArray edges = after.getAsJsonArray("edgeBindings");
        after.remove("edgeBindings");
        assertEquals("no member outside edgeBindings changed", before, after);
        assertFalse("no output closure was written",
                after.has(OutputClosureContract.FIELD));
        for (JsonElement element : edges) {
            assertEquals("no port outside the declared frontier", PORT,
                    element.getAsJsonObject().get("toInputPort")
                            .getAsString());
        }
    }

    /** The rule reaches a fixed point: absorbing the same evidence twice
     *  declares nothing further and refuses nothing. */
    @Test
    public void absorbingTheSameEvidenceTwiceIsIdempotent() {
        List<ExecutionTask> plan = plan();
        List<JsonObject> summaries =
                Collections.singletonList(summary(handoff()));

        assertEquals(1, ConcolicScheduler.absorbObservedExchanges(
                plan, summaries, new TreeMap<String, Integer>()));
        String once = plan.get(1).json().toString();

        Map<String, Integer> refusals = new TreeMap<>();
        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, summaries, refusals));
        assertEquals(refusals.toString(), 0, refusals.size());
        assertEquals(once, plan.get(1).json().toString());
    }

    /** A pairing the frozen plan already declares is at the fixed point: it
     *  is neither declared again nor refused. */
    @Test
    public void anAlreadyDeclaredPairingIsNeitherAbsorbedNorRefused() {
        JsonObject sender = task("TASK.SENDER", SENDER_REGION,
                "test/sender#epoch0", SENDER_NINE);
        sender.add("edgeBindings", edges(edge(SENDER_NINE_EDGE, SENDER_NINE,
                RECEIVER_NINE)));
        JsonObject receiver = task("TASK.RECEIVER", RECEIVER_REGION,
                "test/receiver#epoch1", RECEIVER_NINE);
        receiver.add("edgeBindings", edges(edge(SENDER_NINE_EDGE,
                SENDER_NINE, RECEIVER_NINE)));
        List<ExecutionTask> plan = Arrays.asList(
                ExecutionTask.decode(sender), ExecutionTask.decode(receiver));
        String frozen = plan.get(1).json().toString();

        JsonObject handoff = handoff();
        handoff.addProperty(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID,
                SENDER_NINE + "#a2");
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary(handoff)),
                refusals));
        assertEquals(refusals.toString(), 0, refusals.size());
        assertEquals(frozen, plan.get(1).json().toString());
    }

    // ---- the fail-closed axes: every one leaves the member diverging ----

    /** The sender must be a task this same frozen plan schedules. */
    @Test
    public void aSenderTaskOutsideTheFrozenPlanIsRefused() {
        JsonObject handoff = handoff();
        handoff.addProperty(VmHandoffEvidence.PRODUCER_TASK_ID,
                "TASK.NOT-IN-THIS-PLAN");
        assertRefused(handoff, "PRODUCER_TASK_NOT_IN_FROZEN_PLAN");
    }

    /** The sender occurrence must be the one that task was scheduled for. */
    @Test
    public void aSenderOccurrenceThePlanDoesNotScheduleIsRefused() {
        JsonObject handoff = handoff();
        handoff.addProperty(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID,
                "test/sender#epoch0/region/REGION.SENDER#77#a1");
        assertRefused(handoff, "PRODUCER_OCCURRENCE_NOT_PLANNED");
    }

    /** An attach recorded before its own export states no send. */
    @Test
    public void anInvertedSendAndReceiveIsRefused() {
        JsonObject handoff = handoff();
        handoff.addProperty(VmHandoffEvidence.EXPORT_EVENT_ID, 225);
        handoff.addProperty(VmHandoffEvidence.ATTACH_EVENT_ID, 222);
        assertRefused(handoff, "NO_RECORDED_SEND_BEFORE_RECEIVE");
    }

    /** Evidence that does not state both endpoints is not admitted. */
    @Test
    public void aHandoffMissingAnEndpointIsRefused() {
        JsonObject handoff = handoff();
        handoff.remove(VmHandoffEvidence.EXPORT_EVENT_ID);
        assertRefused(handoff, "NO_RECORDED_SEND_BEFORE_RECEIVE");

        JsonObject attachless = handoff();
        attachless.remove(VmHandoffEvidence.ATTACH_EVENT_ID);
        assertRefused(attachless, "NO_RECORDED_SEND_BEFORE_RECEIVE");
    }

    /** A port the frozen plan never gave this receiver is a new port, and
     *  this rule re-addresses pairings; it never widens a frontier. */
    @Test
    public void aPortTheReceiverNeverDeclaredIsRefused() {
        JsonObject handoff = handoff();
        handoff.addProperty("portId", "XCH.never-declared.req.other");
        assertRefused(handoff, "PORT_NOT_DECLARED_ON_RECEIVER");
    }

    /** Evidence with no sender occurrence names no sender. */
    @Test
    public void aHandoffWithoutASenderOccurrenceIsRefused() {
        JsonObject handoff = handoff();
        handoff.remove(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
        assertRefused(handoff, "HANDOFF_WITHOUT_PRODUCER_OCCURRENCE");
    }

    /** The receiving task must be one this plan schedules. */
    @Test
    public void aReceiverTaskOutsideTheFrozenPlanIsRefused() {
        List<ExecutionTask> plan = plan();
        JsonObject summary = summary(handoff());
        summary.addProperty("taskId", "TASK.NOT-IN-THIS-PLAN");
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary), refusals));
        assertEquals(Collections.singletonMap(
                "RECEIVER_TASK_NOT_IN_FROZEN_PLAN", 1), refusals);
    }

    /** And it must have run at the occurrence it was scheduled for. */
    @Test
    public void aReceiverOccurrenceThePlanDoesNotScheduleIsRefused() {
        List<ExecutionTask> plan = plan();
        JsonObject summary = summary(handoff());
        summary.addProperty("occurrenceId",
                "test/receiver#epoch1/region/REGION.RECEIVER#42#a1");
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary), refusals));
        assertEquals(Collections.singletonMap(
                "RECEIVER_OCCURRENCE_NOT_PLANNED", 1), refusals);
    }

    /**
     * The absorbed row keeps the sender's edge id, so one id can denote two
     * pairings across two tasks -- but never inside one task, where
     * {@code mergeEdgeBindings} merges by edge id and would join them into a
     * single row.  A receiver already holding that id is refused.
     */
    @Test
    public void anEdgeIdTheReceiverAlreadyHoldsIsRefused() {
        List<ExecutionTask> plan = plan();
        JsonArray edges = plan.get(1).json().getAsJsonArray("edgeBindings");
        edges.get(0).getAsJsonObject().addProperty("edgeId", SENDER_ONE_EDGE);
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary(handoff())),
                refusals));
        assertEquals(Collections.singletonMap(
                "ABSORBED_EDGE_ID_ALREADY_DECLARED", 1), refusals);
    }

    /** Evidence that names no port names no exchange. */
    @Test
    public void aHandoffWithoutAPortIsRefused() {
        JsonObject handoff = handoff();
        handoff.remove("portId");
        assertRefused(handoff, "HANDOFF_WITHOUT_PORT");
    }

    /** Nothing is minted: with no frozen binding of the sender's to
     *  re-address, there is no member to declare. */
    @Test
    public void aSenderWithNoFrozenBindingForThePortIsRefused() {
        JsonObject sender = task("TASK.SENDER", SENDER_REGION,
                "test/sender#epoch0", SENDER_ONE);
        JsonObject other = edge(SENDER_ONE_EDGE, SENDER_ONE, RECEIVER_ONE);
        other.addProperty("fromOutputPort", "XCH.other.req.keyId");
        other.addProperty("toInputPort", "XCH.other.req.keyId");
        sender.add("edgeBindings", edges(other));
        JsonObject receiver = task("TASK.RECEIVER", RECEIVER_REGION,
                "test/receiver#epoch1", RECEIVER_NINE);
        receiver.add("edgeBindings", edges(edge(SENDER_NINE_EDGE,
                SENDER_NINE, RECEIVER_NINE)));
        List<ExecutionTask> plan = Arrays.asList(
                ExecutionTask.decode(sender), ExecutionTask.decode(receiver));
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals(0, ConcolicScheduler.absorbObservedExchanges(
                plan, Collections.singletonList(summary(handoff())),
                refusals));
        assertEquals(Collections.singletonMap(
                "PRODUCER_DECLARES_NO_EDGE_FOR_PORT", 1), refusals);
    }

    /** Every refusal leaves the plan exactly as the scheduler froze it. */
    private static void assertRefused(JsonObject handoff, String code) {
        List<ExecutionTask> plan = plan();
        String frozen = plan.get(1).json().toString();
        Map<String, Integer> refusals = new TreeMap<>();

        assertEquals("refused evidence declares nothing", 0,
                ConcolicScheduler.absorbObservedExchanges(plan,
                        Collections.singletonList(summary(handoff)),
                        refusals));
        assertEquals("the refusal is named", 
                Collections.singletonMap(code, 1), refusals);
        assertEquals("the frozen plan is unchanged", frozen,
                plan.get(1).json().toString());
        assertTrue("the pairing is still undeclared, so it still diverges",
                edge(plan.get(1), SENDER_ONE, RECEIVER_NINE) == null);
    }

    /** The sender at its first occurrence, and the receiver at its ninth. */
    private static List<ExecutionTask> plan() {
        JsonObject sender = task("TASK.SENDER", SENDER_REGION,
                "test/sender#epoch0", SENDER_ONE);
        sender.add("edgeBindings", edges(edge(SENDER_ONE_EDGE, SENDER_ONE,
                RECEIVER_ONE)));
        JsonObject receiver = task("TASK.RECEIVER", RECEIVER_REGION,
                "test/receiver#epoch1", RECEIVER_NINE);
        receiver.add("edgeBindings", edges(edge(SENDER_NINE_EDGE,
                SENDER_NINE, RECEIVER_NINE)));
        return Arrays.asList(ExecutionTask.decode(sender),
                ExecutionTask.decode(receiver));
    }

    private static JsonObject summary(JsonObject handoff) {
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        JsonObject summary = new JsonObject();
        summary.addProperty("taskId", "TASK.RECEIVER");
        summary.addProperty("occurrenceId", RECEIVER_NINE + "#a2");
        summary.add(VmHandoffEvidence.FIELD, handoffs);
        return summary;
    }

    /** The recorded handoff: sender occurrence one, receiver occurrence
     *  nine, over a port both already declare. */
    private static JsonObject handoff() {
        JsonObject handoff = new JsonObject();
        handoff.addProperty("kind", VmHandoffEvidence.KIND);
        handoff.addProperty("authority", VmHandoffEvidence.AUTHORITY);
        handoff.addProperty("portId", PORT);
        handoff.addProperty(VmHandoffEvidence.EXPORT_EVENT_ID, 222);
        handoff.addProperty(VmHandoffEvidence.ATTACH_EVENT_ID, 225);
        handoff.addProperty(VmHandoffEvidence.PRODUCER_TASK_ID,
                "TASK.SENDER");
        handoff.addProperty(VmHandoffEvidence.PRODUCER_OCCURRENCE_ID,
                SENDER_ONE + "#a1");
        return handoff;
    }

    private static JsonObject edge(ExecutionTask task, String from,
                                   String to) {
        for (JsonElement element : task.edgeBindings()) {
            JsonObject edge = element.getAsJsonObject();
            if (from.equals(edge.get("fromOccurrenceId").getAsString())
                    && to.equals(
                    edge.get("toOccurrenceId").getAsString())) {
                return edge;
            }
        }
        return null;
    }

    private static JsonObject edge(String edgeId, String from, String to) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("fromOccurrenceId", from);
        edge.addProperty("toOccurrenceId", to);
        edge.addProperty("fromOutputPort", PORT);
        edge.addProperty("toInputPort", PORT);
        return edge;
    }

    private static JsonArray edges(JsonObject... rows) {
        JsonArray edges = new JsonArray();
        for (JsonObject row : rows) edges.add(row);
        return edges;
    }

    private static JsonObject task(String taskId, String regionId,
                                   String sourceKey, String occurrenceId) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL." + taskId);
        task.addProperty("regionId", regionId);
        task.addProperty("sourceKey", sourceKey);
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", sourceKey + "/" + regionId);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        return task;
    }
}
