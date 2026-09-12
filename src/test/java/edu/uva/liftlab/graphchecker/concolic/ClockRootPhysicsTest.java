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

    @Test
    public void clockReadsGroupByNodeInRecordedOrder() {
        Map<String, List<ClockRootPhysics.ClockRead>> byNode =
                ClockRootPhysics.readsByNode(Collections.singletonList(
                        planRow(Arrays.asList(
                                symbolize("nn0", "p.late", 200, "1700000000200"),
                                symbolize("nn0", "p.early", 100, "1700000000100"),
                                symbolize("dn0", "p.dn", 150, "1700000000150"),
                                // Not a clock: carries no window or order.
                                other("nn0", "p.field", 120)))));

        assertEquals(2, byNode.size());
        List<ClockRootPhysics.ClockRead> nn0 = byNode.get("nn0");
        assertEquals(2, nn0.size());
        assertEquals(100L, nn0.get(0).eventSeq);
        assertEquals(1700000000100L, nn0.get(0).recordedValue);
        assertEquals(200L, nn0.get(1).eventSeq);
        assertEquals(1, byNode.get("dn0").size());
    }

    /** One port mints one root, so two rows for it are one read. */
    @Test
    public void onePortIsOneRead() {
        Map<String, List<ClockRootPhysics.ClockRead>> byNode =
                ClockRootPhysics.readsByNode(Collections.singletonList(
                        planRow(Arrays.asList(
                                symbolize("nn0", "p.one", 300, "1700000000300"),
                                symbolize("nn0", "p.one", 100, "1700000000100")))));
        assertEquals(1, byNode.get("nn0").size());
        assertEquals(100L, byNode.get("nn0").get(0).eventSeq);
    }

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
