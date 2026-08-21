package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Collections;

import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.constant;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.sum;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.symbol;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.twoWriterEnvelope;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.twoWriterLedger;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Projection of the target slice from the recorded session graph.
 *
 * <p>The slice is what the final formula should contain: the expression and
 * event nodes that can reach the target predicate. These tests pin both
 * directions - what a target pulls in, and what it must not.</p>
 */
public class SessionTargetSliceTest {

    @Test
    public void anExactReadPullsInOnlyTheWriterTheVmProved() {
        JsonObject record = versionsRecord(twoWriterEnvelope(
                SharedStateEvidence.RESOLUTION_EXACT, "SYNC_ORDERED", 11L));

        // An exact read leaves no term to scan for: the reader was handed the
        // writer's own expression.  The caller names the read event instead.
        SessionTargetSlice.Slice slice = SessionTargetSlice.project(
                Collections.singletonList(record),
                SharedStateEvidence.ledgerRecord(twoWriterLedger(),
                        RecordedSharedStateFixtures.identity(
                                "REGION.reader", 1L)),
                inlinedWriterTarget(), Collections.singletonList(21L));

        assertTrue(slice.reachesTarget());
        assertTrue(slice.containsRead(21L));
        assertTrue(slice.containsVersion(11L));
        // The competing writer is out of the slice: provenance was proved.
        assertFalse(slice.containsVersion(12L));
        assertTrue(slice.containsSymbol("A"));
        assertFalse(slice.containsSymbol("B"));
        assertEquals(0, slice.gaps().size());
    }

    private static JsonObject versionsRecord(JsonObject envelope) {
        return SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedSharedStateFixtures.identity("REGION.reader", 1L));
    }

    /**
     * The predicate an exact read produces: the writer's own expression,
     * composed into the target condition with no read node left behind.
     */
    private static JsonObject inlinedWriterTarget() {
        JsonObject target = new JsonObject();
        target.addProperty("_type", "BinaryExpression");
        target.addProperty("_op", "==");
        target.add("_left", sum(symbol("A"), constant(1)));
        target.add("_right", constant(0));
        return target;
    }
}
