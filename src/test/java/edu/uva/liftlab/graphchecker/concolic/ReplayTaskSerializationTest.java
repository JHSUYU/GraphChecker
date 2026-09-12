package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.IdentityHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A replay task row leaves the solver as a portable artifact, never as the
 * tree its propagated values would unfold into.
 *
 * <p>{@link PathReplayTaskFactory#createLinked} publishes each row through
 * {@link SharedExpressionTable#compact}, and {@code toImmutableJsonView}
 * deliberately hands it the live decoder DAG rather than a copy.  Serializing
 * that DAG directly would restate every shared node once per path that
 * reaches it -- Gson's writer is a per-path walk like every other -- so a
 * 20-node value would be written as a million.  These tests pin the size
 * contract that keeps the worker directories bounded.</p>
 */
public class ReplayTaskSerializationTest {

    /** 20 nodes, 2^19 paths: the wire form must follow the nodes. */
    @Test(timeout = 30000)
    public void compactRowSerializesInSizeLinearInNodes() {
        JsonObject row = replayRow(doublingPredicate(19));
        assertEquals(20, nodeCount(row.get("replayContract")));

        JsonObject portable = SharedExpressionTable.compact(row);
        int wire = portable.toString().length();

        // One definition per node plus its anchor, not one subtree per path.
        assertTrue("portable row is " + wire + " bytes", wire < 20000);
        assertEquals(20, portable.getAsJsonObject(
                SharedExpressionTable.FIELD)
                .getAsJsonArray("definitions").size());
    }

    /** Growing the sharing depth must not grow the wire form exponentially. */
    @Test(timeout = 30000)
    public void wireSizeGrowsWithNodesNotWithPaths() {
        int shallow = SharedExpressionTable.compact(
                replayRow(doublingPredicate(10))).toString().length();
        int deep = SharedExpressionTable.compact(
                replayRow(doublingPredicate(20))).toString().length();

        // Ten more nodes, ten more definitions -- not a 1024-fold blowup.
        assertTrue("shallow=" + shallow + " deep=" + deep,
                deep < shallow * 3);
    }

    /** The portable row still decodes back to the graph it came from. */
    @Test(timeout = 30000)
    public void portableRowRoundTripsToTheSameGraph() {
        JsonObject row = replayRow(doublingPredicate(19));

        JsonObject expanded = SharedExpressionTable.expand(
                SharedExpressionTable.compact(row));

        assertEquals(20, nodeCount(expanded.get("replayContract")));
        assertEquals(CanonicalJson.render(
                        doublingPredicate(19).get("_left")),
                CanonicalJson.render(expanded.getAsJsonObject(
                        "replayContract").get("_left")));
    }

    private static JsonObject replayRow(JsonElement predicate) {
        JsonObject row = new JsonObject();
        row.addProperty("taskId", "TASK.REPLAY.test");
        row.addProperty("goalId", "GOAL.TEST");
        row.add("replayContract", predicate);
        return row;
    }

    private static int nodeCount(JsonElement value) {
        return nodeCount(value,
                new IdentityHashMap<JsonElement, Boolean>());
    }

    private static int nodeCount(JsonElement value,
                                 IdentityHashMap<JsonElement, Boolean> seen) {
        if (value == null || !value.isJsonObject()
                || seen.put(value, Boolean.TRUE) != null) {
            return 0;
        }
        int total = 1;
        for (Map.Entry<String, JsonElement> field
                : value.getAsJsonObject().entrySet()) {
            total += nodeCount(field.getValue(), seen);
        }
        return total;
    }

    private static JsonObject doublingPredicate(int depth) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "I");
        expression.addProperty("_exp", "x");
        for (int index = 0; index < depth; index++) {
            JsonObject parent = new JsonObject();
            parent.addProperty("_type", "BinaryExpression");
            parent.addProperty("_java_type", "Z");
            parent.add("_left", expression);
            parent.addProperty("_op", "==");
            parent.add("_right", expression);
            expression = parent;
        }
        return expression;
    }
}
