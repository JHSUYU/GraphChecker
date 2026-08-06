package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class LoopBoundPolicyTest {
    @Test
    public void roundTripsFixedLoopBodyBound() {
        JsonObject task = new JsonObject();
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);

        LoopBoundPolicy decoded = LoopBoundPolicy.decode(task);

        assertEquals(8, decoded.maxBackedgeTraversals());
        assertEquals("CFG_BACKEDGE:8:CUT_PATH", decoded.identity());
        // Raised on evidence: the demanded HDFS-11741 encryption key is a
        // byte[20], and the loop bound is a separate contract.
        assertEquals(32,
                LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
    }

    @Test
    public void missingOrNonFixedBoundIsRejected() {
        assertRejected(new JsonObject());

        JsonObject task = new JsonObject();
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        task.getAsJsonObject(LoopBoundPolicy.FIELD)
                .addProperty("maxBackedgeTraversals", 3);
        assertRejected(task);

        try {
            LoopBoundPolicy.cfgBackedges(4);
            fail("configurable loop bounds must be rejected");
        } catch (IllegalArgumentException expected) {
            // Fixed execution-wide bound is canonical.
        }
    }

    private static void assertRejected(JsonObject task) {
        try {
            LoopBoundPolicy.decode(task);
            fail("invalid loop bound must be rejected");
        } catch (IllegalArgumentException expected) {
            // Expected fail-closed contract boundary.
        }
    }
}
