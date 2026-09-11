package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** The portable expression table preserves values and fails closed. */
public class SharedExpressionTableTest {

    @Test
    public void missingDefinitionIsRejected() {
        JsonObject original = new JsonObject();
        original.add("value", binary(symbol("x"), constant(1), "+"));
        JsonObject compact = SharedExpressionTable.compact(original);
        compact.getAsJsonObject(SharedExpressionTable.FIELD)
                .getAsJsonArray("definitions").remove(0);

        try {
            SharedExpressionTable.expand(compact);
            fail("missing expression definition was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("missing shared")
                    || expected.getMessage().contains("hash differs"));
        }
    }

    @Test
    public void artifactReaderRejectsInlineExpressionTrees() {
        JsonObject inline = new JsonObject();
        inline.add("value", symbol("x"));
        try {
            SharedExpressionTable.expand(inline);
            fail("inline expression artifact was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("inline symbolic"));
        }
    }

    @Test
    public void decoderReusesKnownAnchorsWhenRecompacting() {
        JsonObject leaf = symbol("x");
        JsonObject original = new JsonObject();
        original.add("value", binary(leaf, leaf, "+"));

        JsonObject compact = SharedExpressionTable.compact(original);
        SharedExpressionTable.Decoder decoder =
                new SharedExpressionTable.Decoder();
        JsonObject expanded = decoder.expand(compact);
        // A runtime COW wrapper can replace expression object identities while
        // leaving the expression content unchanged. Re-publication should
        // still reuse the already verified definitions.
        JsonObject copied = expanded.deepCopy();
        JsonObject republished = decoder.compact(copied);

        assertEquals(compact, republished);
        JsonObject expression = expanded.getAsJsonObject("value");
        assertSame(expression.get("_left"), expression.get("_right"));
    }

    @Test
    public void compactScansSharedDoublingDagOncePerNode() {
        JsonObject expression = symbol("x");
        for (int depth = 0; depth < 40; depth++) {
            JsonObject parent = new JsonObject();
            parent.addProperty("_type", "BinaryExpression");
            parent.add("_left", expression);
            parent.addProperty("_op", "+");
            parent.add("_right", expression);
            expression = parent;
        }
        JsonObject artifact = new JsonObject();
        artifact.add("value", expression);

        JsonObject first = SharedExpressionTable.compact(artifact);
        assertEquals(41, first.getAsJsonObject(SharedExpressionTable.FIELD)
                .getAsJsonArray("definitions").size());
        SharedExpressionTable.Decoder decoder =
                new SharedExpressionTable.Decoder();
        java.util.List<JsonObject> batch = decoder.expandAll(
                java.util.Arrays.asList(first, first.deepCopy()));
        JsonObject expanded = batch.get(0);
        assertSame(expanded.get("value"), batch.get(1).get("value"));
        JsonObject cursor = expanded.getAsJsonObject("value");
        for (int depth = 0; depth < 40; depth++) {
            assertSame(cursor.get("_left"), cursor.get("_right"));
            cursor = cursor.getAsJsonObject("_left");
        }
        assertEquals(decoder.semanticDigest(expanded),
                decoder.semanticDigest(batch.get(1)));
        JsonObject second = decoder.compact(expanded);
        assertEquals(41, second.getAsJsonObject(SharedExpressionTable.FIELD)
                .getAsJsonArray("definitions").size());
    }

    private static JsonObject binary(JsonObject left, JsonObject right,
                                     String operator) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static JsonObject symbol(String name) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", name);
        return result;
    }

    private static JsonObject constant(int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConstExpr");
        result.addProperty("_java_type", "I");
        result.addProperty("_exp", "Y_I_" + value);
        return result;
    }
}
