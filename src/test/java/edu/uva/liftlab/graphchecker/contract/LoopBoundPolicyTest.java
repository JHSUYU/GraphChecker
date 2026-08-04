package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class LoopBoundPolicyTest {
    @Test
    public void roundTripsCfgBackedgeBound() {
        JsonObject task = new JsonObject();
        LoopBoundPolicy.cfgBackedges(5).writeTo(task);

        LoopBoundPolicy decoded = LoopBoundPolicy.decode(task);

        assertEquals(5, decoded.maxBackedgeTraversals());
        assertEquals("CFG_BACKEDGE:5:CUT_PATH", decoded.identity());
    }

    @Test
    public void missingOrNonPositiveBoundIsRejected() {
        assertRejected(new JsonObject());

        JsonObject task = new JsonObject();
        LoopBoundPolicy.cfgBackedges(1).writeTo(task);
        task.getAsJsonObject(LoopBoundPolicy.FIELD)
                .addProperty("maxBackedgeTraversals", 0);
        assertRejected(task);
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
