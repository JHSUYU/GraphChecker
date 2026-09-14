package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;

import org.junit.After;
import org.junit.Test;

import static java.util.Collections.singletonList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * An occurrence is its address, and admission asks nothing else.
 *
 * <p>(node, epoch, region, k-th activation) is the whole identity. The
 * message an activation was reached by is provenance: the handoff row
 * states the producer that actually delivered, and a planned attach that
 * did not reproduce is reported at IMPORT. It is not a second identity that
 * may veto the first.</p>
 *
 * <p>It was one. Whenever the plan named an IN producer for a task,
 * admission replaced the address test entirely with "is the envelope on
 * this thread the one the plan named" -- so an activation that agreed on
 * node, epoch, region AND k was refused because a response envelope had
 * not been reproduced. On hdfs-11741 that is the balancer's REGION #3 and
 * #7, each with candidates listed at every other k and one candidate whose
 * stated difference was empty because its address matched; on hdfs-17897 it
 * is dn0's addKeys #1.</p>
 */
public class AddressIsTheOnlyAdmissionTest {
    private static final String REGION = "REGION.r";
    private static final String NODE = "hdfs-11741/balancer#epoch0";
    private static final String PORT = "XCH.1.resp.block-key-array";

    @After
    public void clearMessageState() {
        SymbolicMessageEnvelope.clear();
        RuntimeTraceContext.resetForTests();
    }

    /**
     * A task the plan gave an IN handoff answers its own address with no
     * envelope present at all.
     */
    @Test
    public void anAddressedActivationIsAdmittedWithNoEnvelope()
            throws Exception {
        ConcolicTaskPlan.RuntimeTask task = task(3);
        SymbolicMessageEnvelope.clear();

        assertTrue("the planned occurrence has an IN handoff",
                task.communicationHandoff(PORT, false) != null);
        assertTrue("its own address answers it",
                task.acceptsRootInvocation(address(3), false));
        assertFalse("another activation of it does not",
                task.acceptsRootInvocation(address(2), false));
        assertFalse("nor does an unnamed address",
                task.acceptsRootInvocation(address(0), false));
    }

    /**
     * An envelope naming another producer changes nothing either way.
     *
     * <p>The value that arrived is evidence the handoff row states. It
     * decides which v_H the attach mints, never which activation this is.</p>
     */
    @Test
    public void anUnplannedEnvelopeNeitherAdmitsNorRefuses() throws Exception {
        ConcolicTaskPlan.RuntimeTask task = task(3);
        assertTrue(SymbolicMessageEnvelope.stage(PORT, 41L, "task-x",
                "some-other-producer#9", singletonList("some-consumer#4")));
        SymbolicMessageEnvelope.installInbound(
                SymbolicMessageEnvelope.takeOutbound());

        assertTrue("the address still answers",
                task.acceptsRootInvocation(address(3), false));
        assertFalse("and still refuses every other k",
                task.acceptsRootInvocation(address(4), false));
    }

    /** A refusal always states a difference; a match states none. */
    @Test
    public void everyRefusalNamesWhatDiffered() {
        OccurrenceAddress planned = address(3);
        assertEquals("", planned.describe(address(3)));
        assertFalse("a refusal is never a hole in the sentence",
                planned.difference(address(2)).trim().isEmpty());
        assertTrue(planned.difference(address(2)),
                planned.difference(address(2)).contains("activation 2"));
        // describe() answers "" for a match, and difference() must still
        // say something a reader can act on.
        assertFalse(planned.difference(address(3)).trim().isEmpty());
    }

    /**
     * A k taken on the plan's word says so on the row.
     *
     * <p>Provisional admission is the one path that is not the address: the
     * run attributed the activation to no node, and it is offered the
     * PLANNED node's next k because the plan says the occurrence is there.
     * Whether the close confirms it decides who owns that k. Neither half
     * was on any row, so on lane11741d dn0's bucket ran past the addressed
     * activation 4 with nothing to say which activations had taken 2, 4 and
     * 6 -- the genuine activations on {@code main} were left observing
     * 1, 3, 5, 7.</p>
     */
    @Test
    public void aProvisionalKIsStatedOnTheRow() throws Exception {
        ConcolicTaskPlan.RuntimeTask task = task(4);
        task.noteProvisionalAdmission("read BUCKET as activation 4");
        task.noteUnaddressedCandidate("occurrence is activation 5, not 4");

        String statement = task.unansweredAddress();
        assertTrue(statement, statement.contains("provisional: "));
        assertTrue(statement, statement.contains("read BUCKET as activation 4"));
        assertTrue("every note names its thread",
                statement.contains("[thread=" + Thread.currentThread().getName() + "]"));
    }

    private static OccurrenceAddress address(int ordinal) {
        return OccurrenceAddress.of(NODE, REGION, ordinal);
    }

    /** One planned occurrence with one selected IN communication handoff. */
    private static ConcolicTaskPlan.RuntimeTask task(int ordinal)
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.SEED.address");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", NODE);
        encoded.addProperty("occurrenceId",
                NODE + "/region/" + REGION + "#" + ordinal);
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", ordinal);
        selector.addProperty("method", "<a.B: void run()>");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", NODE);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        JsonArray handoffs = new JsonArray();
        JsonObject handoff = new JsonObject();
        handoff.addProperty("portId", PORT);
        handoff.addProperty("handoffLeafPath", PORT);
        handoff.addProperty("side", "IN");
        handoff.addProperty("direction", "RESPONSE");
        handoff.addProperty("captureKind", "CALL_RETURN");
        handoff.addProperty("javaType", "int");
        handoff.addProperty("declaredCallee", "<a.P: int getKeyId()>");
        handoff.addProperty("definitionMethod", "<a.B: void run()>");
        handoff.addProperty("definitionUnitIndex", 2);
        handoffs.add(handoff);
        encoded.add("communicationHandoffs", handoffs);
        return new ConcolicTaskPlan.RuntimeTask(
                ExecutionTask.decode(encoded));
    }
}
