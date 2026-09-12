package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.IdentityHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertSame;

/** A canonical copy is a copy of the graph, never of every path through it. */
public class CanonicalJsonDagTest {

    /**
     * A node shared k levels deep is reached 2^k ways.  Copying per path
     * exhausted the composer's heap on a real corpus, so the copy has to stay
     * linear in the graph: this predicate is 41 nodes and 2^40 paths, which a
     * per-path copy cannot finish at all.  Rendering is deliberately not
     * asserted here -- a canonical rendering <em>is</em> the tree, so it is
     * exponential in this input by definition and is checked separately.
     */
    @Test(timeout = 30000)
    public void copyIsLinearInTheGraphNotInItsPaths() {
        JsonObject predicate = doublingPredicate(40);

        JsonObject copy = (JsonObject) CanonicalJson.copy(predicate);

        assertNotSame(predicate, copy);
        assertSame(copy.get("_left"), copy.get("_right"));
        assertEquals(nodeCount(predicate), nodeCount(copy));
    }

    /** Sharing in the copy never reaches back into the source. */
    @Test
    public void copyNeverAliasesItsSource() {
        JsonObject leaf = new JsonObject();
        leaf.addProperty("_type", "SymbolExpression");
        leaf.addProperty("_exp", "x");
        JsonArray uses = new JsonArray();
        uses.add(leaf);
        uses.add(leaf);
        JsonObject source = new JsonObject();
        source.add("uses", uses);

        JsonObject copy = (JsonObject) CanonicalJson.copy(source);
        JsonArray copied = copy.getAsJsonArray("uses");
        assertNotSame(leaf, copied.get(0));
        assertSame(copied.get(0), copied.get(1));

        copied.get(0).getAsJsonObject().addProperty("_exp", "y");
        assertEquals("x", JsonFields.optionalString(leaf, "_exp"));
    }

    /** Member order, nulls and primitives render exactly as they did. */
    @Test
    public void copyKeepsCanonicalRendering() {
        JsonObject source = new JsonObject();
        source.addProperty("zeta", 1);
        source.addProperty("alpha", "two");
        source.add("missing", JsonNull.INSTANCE);
        JsonArray items = new JsonArray();
        items.add(3);
        items.add(true);
        source.add("items", items);

        JsonElement copy = CanonicalJson.copy(source);

        assertEquals("{\"alpha\":\"two\",\"items\":[3,true],"
                + "\"missing\":null,\"zeta\":1}", CanonicalJson.render(copy));
        assertEquals(CanonicalJson.sha256(source), CanonicalJson.sha256(copy));
    }

    /** A copied DAG renders exactly as the DAG it copied. */
    @Test
    public void copyRendersLikeItsSource() {
        JsonObject predicate = doublingPredicate(6);

        JsonElement copy = CanonicalJson.copy(predicate);

        assertEquals(CanonicalJson.render(predicate),
                CanonicalJson.render(copy));
    }

    /** The composer compares a complement and drops it; it must not copy. */
    @Test
    public void complementViewKeepsTheDecodedGraph() {
        JsonObject predicate = doublingPredicate(3);
        JsonElement operand = predicate.get("_left");

        JsonElement complement = BranchPredicateAlgebra.complementView(
                predicate);

        assertSame(operand, complement.getAsJsonObject().get("_left"));
        assertEquals(CanonicalJson.render(
                        BranchPredicateAlgebra.complement(predicate)),
                CanonicalJson.render(complement));
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
            parent.add("_left", expression);
            parent.addProperty("_op", "==");
            parent.add("_right", expression);
            expression = parent;
        }
        return expression;
    }
}
