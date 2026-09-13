package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** What the recording says a wall clock can have returned. */
public class ClockRootPhysicsTest {

    /**
     * The window brackets the recorded value rather than pinning it, and it
     * survives a recorded value below the skew without underflowing.
     */
    @Test
    public void windowBracketsTheRecordedValue() {
        assertEquals("(and (>= now 1699999700000) (<= now 1700000300000))",
                ClockRootPhysics.window("now", 1700000000000L, 300000L));
        assertEquals("(and (>= now (- 299900)) (<= now 300100))",
                ClockRootPhysics.window("now", 100L, 300000L));
        // A zero skew is a legitimate configuration: pin to the recording.
        assertEquals("(and (>= now 42) (<= now 42))",
                ClockRootPhysics.window("now", 42L, 0L));
    }

    @Test
    public void onlyDeclaredClockCalleesAreClocks() {
        assertTrue(ClockRootPhysics.clockCallee(
                "<org.apache.hadoop.util.Timer: long now()>"));
        assertTrue(ClockRootPhysics.clockCallee(
                "<java.lang.System: long currentTimeMillis()>"));
        assertTrue(!ClockRootPhysics.clockCallee(
                "<org.apache.hadoop.hdfs.security.token.block.BlockKey:"
                        + " int getKeyId()>"));
        assertTrue(!ClockRootPhysics.clockCallee(null));
    }

    private static JsonObject planRow(List<JsonObject> symbolize) {
        JsonArray rows = new JsonArray();
        for (JsonObject row : symbolize) rows.add(row);
        JsonObject goal = new JsonObject();
        goal.add("symbolize", rows);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        JsonObject plan = new JsonObject();
        plan.add("closureGoals", goals);
        return plan;
    }

    private static JsonObject symbolize(String node, String port,
                                        long eventSeq, String recorded) {
        JsonObject row = new JsonObject();
        row.addProperty("declaredCallee",
                "<org.apache.hadoop.util.Timer: long now()>");
        row.addProperty("sourceKey", node);
        row.addProperty("portId", port);
        row.addProperty("siteId", "<C: void m()>#u1");
        row.addProperty("occurrenceId", node + "/region/R#1");
        row.addProperty("eventSeq", eventSeq);
        row.addProperty("primitiveValue", recorded);
        return row;
    }

    private static JsonObject other(String node, String port, long eventSeq) {
        JsonObject row = symbolize(node, port, eventSeq, "7");
        row.addProperty("declaredCallee", "<C: int getKeyId()>");
        return row;
    }
}
