package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * The handoff mint: one variable at one occurrence, answered like a source.
 *
 * <p>At a wire attach the consumer's element stops denoting the producer's
 * whole expression and starts denoting a fresh variable v_H. The producer's
 * expression travels on the row as one member of H's family, so the two sides
 * can be explored independently and joined offline at H instead of being
 * re-run in combination.</p>
 *
 * <p>Three things have to hold for that to work, and they are what this
 * pins: H is the same string in every replay, the row states v_H and what it
 * delivered, and an obligation assignment for H answers the mint through the
 * configured-source mechanism rather than a second one. The attach itself
 * runs inside the custom JDK -- {@code ConcolicVmBroker} binds to
 * {@code java.lang.System} entry points that exist only there -- so what is
 * exercised here is every seam on this side of that call.</p>
 */
public class HandoffMintTest {
    private static final String PORT =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70.req"
                    + ".data-encryption-key-id";
    private static final String CONSUMER =
            "hdfs-17899/target-dn#epoch0/region/REGION.53092d3e#1";
    private static final String ELEMENT =
            "<org.apache.hadoop.ipc.Client$Call: int id>";

    /** H is (port, consumer address, k, element) -- and no event id. */
    @Test
    public void theHandoffOccurrenceIsTheSameStringInEveryReplay() {
        String first = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        assertEquals("nothing per-replay is in the identity", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT));
        assertTrue(first.startsWith("HANDOFF_PHASE."));
        assertNotEquals("a loop's second turn is a second variable", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 2, ELEMENT));
        assertNotEquals("another element is another handoff", first,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                        "<org.apache.hadoop.ipc.Client$Call: int retry>"));
        assertNotEquals("another consumer occurrence is another handoff",
                first, HandoffPhaseContract.phaseId(PORT,
                        "hdfs-17899/source-dn#epoch0/region/REGION.53092d3e#1",
                        1, ELEMENT));
        assertNotEquals("the handoff label is not a configured source label",
                "SRC.", HandoffPhaseContract.engineLabelForPhase(first,
                        PORT).substring(0, 4));
    }

    /** The row states v_H, what it delivered, and its domain. */
    @Test
    public void theRowStatesTheHandoffVariableAndItsDeliveredValue() {
        JsonObject row = row("");

        assertEquals(6, row.get("schemaVersion").getAsInt());
        assertEquals(HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                row.get(VmHandoffEvidence.HANDOFF_PHASE_ID).getAsString());
        assertEquals("M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                row.get(VmHandoffEvidence.HANDOFF_SYMBOL).getAsString());
        assertEquals("119982",
                row.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertEquals("I", row.get(VmHandoffEvidence.JAVA_TYPE).getAsString());
        assertFalse(row.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertTrue("e_p stays on the row as a family member, not a shadow",
                row.has(VmHandoffEvidence.EXPRESSION));
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));
    }

    /** Every new member is required; none is completed from another. */
    @Test
    public void aRowMissingAnyOfThemIsRefused() {
        for (String member : new String[]{
                VmHandoffEvidence.HANDOFF_PHASE_ID,
                VmHandoffEvidence.HANDOFF_SYMBOL,
                VmHandoffEvidence.RECORDED_VALUE,
                VmHandoffEvidence.JAVA_TYPE}) {
            JsonObject row = row("");
            row.remove(member);
            assertFalse(member + " must be required",
                    VmHandoffEvidence.isEvent(row));
        }
        JsonObject unanswered = row("");
        unanswered.addProperty(VmHandoffEvidence.ANSWERED, true);
        assertFalse("an answered row without its value is refused",
                VmHandoffEvidence.isEvent(unanswered));
    }

    /**
     * An obligation assignment for H answers the mint, through the
     * configured-source mechanism and not a second one.
     */
    @Test
    public void anAssignmentForTheHandoffAnswersTheMint() {
        String phaseId = HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                ELEMENT);
        JsonObject encoded = new JsonObject();
        encoded.addProperty("engineSymbol", "M_I_field_HOFF.9c1d");
        encoded.addProperty("inputSymbol", "SOURCE_PHASE:" + phaseId);
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "119981");
        encoded.addProperty("configuredSourcePhaseId", phaseId);
        encoded.addProperty("configuredSourceId", PORT);
        encoded.addProperty("configuredSourceFieldSignature", ELEMENT);
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);

        assertTrue("the configured-source matcher is the one mechanism",
                assignment.matchesConfiguredSource(phaseId, PORT, ELEMENT));
        assertFalse("and it is keyed on the handoff occurrence",
                assignment.matchesConfiguredSource(
                        HandoffPhaseContract.phaseId(PORT, CONSUMER, 2,
                                ELEMENT), PORT, ELEMENT));

        JsonObject answered = row(assignment.value);
        assertTrue(answered.get(VmHandoffEvidence.ANSWERED).getAsBoolean());
        assertEquals("119981",
                answered.get(VmHandoffEvidence.ANSWERED_VALUE).getAsString());
        assertEquals("what the wire delivered is still stated", "119982",
                answered.get(VmHandoffEvidence.RECORDED_VALUE).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(answered),
                VmHandoffEvidence.isEvent(answered));
    }

    /** One published row, as the runtime writes it after the mint. */
    private static JsonObject row(String answeredValue) {
        JsonObject producerExpression = new JsonObject();
        producerExpression.addProperty("_type", "ConsumerBoundaryExpression");
        producerExpression.addProperty("boundaryKind", "RPC_ATTACH");
        producerExpression.addProperty("eventId", 468);
        producerExpression.addProperty("_java_type", "I");
        JsonObject payload = new JsonObject();
        payload.addProperty("_type", "SymbolExpression");
        payload.addProperty("_java_type", "I");
        payload.addProperty("_exp", "M_I_field_SRC.8c6c_BlockTokenSecretManager");
        producerExpression.add("expression", payload);
        return VmHandoffEvidence.event(PORT, 466L, 468L, producerExpression,
                "TASK.SEED.78bb59b2", "hdfs-17899/source-dn#epoch0/region/"
                        + "REGION.d930c3a2#1#a1",
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1, ELEMENT),
                "M_I_field_HOFF.9c1d_org/apache/hadoop/ipc/Client$Call",
                "119982", "I", answeredValue);
    }
}
