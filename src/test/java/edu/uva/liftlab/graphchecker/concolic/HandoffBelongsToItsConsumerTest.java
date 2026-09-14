package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A handoff belongs to the occurrence whose port it is.
 *
 * <p>Lane B2d's shape. The port is declared IN as a CALL_RETURN on
 * {@code PBHelper.convert(BlockKeyProto)} -- the decode, REGION.16ba41cf --
 * and a CALL_RETURN attach runs in the CALLER's frame, after the callee's
 * activation has closed and published. The row therefore rides on the
 * caller, REGION.b7266d53, and one attach was reported twice: unplanned
 * there, unreproduced here.</p>
 *
 * <p>So H names the consumer the plan declares, the row says which, and the
 * reproduction question is asked of the corpus rather than of the row that
 * happened to carry the evidence.</p>
 */
public class HandoffBelongsToItsConsumerTest {
    private static final String PORT =
            "XCH.1174244c.resp.block-key-id";
    private static final String CONSUMER =
            "hdfs-17899/sps#epoch0/region/REGION.16ba41cf#1";
    private static final String CARRIER =
            "hdfs-17899/sps#epoch0/region/REGION.b7266d53#1#a1";

    /** The row names the consumer, not the activation carrying it. */
    @Test
    public void theRowNamesTheConsumerNotItsCarrier() {
        JsonObject row = handoff(CONSUMER);

        assertEquals(CONSUMER, row.get(
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));
    }

    /** A row that names its consumer is not an unplanned handoff. */
    @Test
    public void aHandoffThatNamesItsConsumerIsPlanned() {
        assertEquals("", unplanned(handoff(CONSUMER)));
    }

    /** One that names none still is, which is what the code is for. */
    @Test
    public void aHandoffThatNamesNoConsumerIsUnplanned() {
        JsonObject row = handoff(CONSUMER);
        row.addProperty(VmHandoffEvidence.CONSUMER_OCCURRENCE_ID, "");
        assertTrue("a row naming no consumer is refused by admission",
                !VmHandoffEvidence.isEvent(row));
    }

    /** Which port the corpus attached, for which consumer occurrence. */
    private static String unplanned(JsonObject row) {
        // The importer's own question, asked the way the fold asks it.
        String consumer = row.get(
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID).getAsString();
        return consumer.isEmpty() ? "UNPLANNED_HANDOFF" : "";
    }

    private static JsonObject handoff(String consumerOccurrenceId) {
        JsonObject payload = new JsonObject();
        payload.addProperty("_type", "SymbolExpression");
        payload.addProperty("_java_type", "I");
        payload.addProperty("_exp", "M_I_field_SRC.root");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConsumerBoundaryExpression");
        expression.addProperty("boundaryKind", "RPC_ATTACH");
        expression.addProperty("eventId", 63);
        expression.addProperty("_java_type", "I");
        expression.add("expression", payload);
        return VmHandoffEvidence.event(PORT, 55L, 63L, expression,
                "TASK.SEED.1d0b713e",
                "hdfs-17899/nn0#epoch0/region/REGION.2392e4b7#1#a1",
                consumerOccurrenceId,
                HandoffPhaseContract.phaseId(PORT,
                        "hdfs-17899/sps#epoch0/region/REGION.16ba41cf#1", 1,
                        "<a.BlockKey: int keyId>"),
                "M_I_field_HOFF.9c1d_a/BlockKey", "119982", "I", "");
    }
}
