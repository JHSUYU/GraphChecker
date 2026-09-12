package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

/** The VM's temporary ids become portable content-addressed expressions. */
public class VmExpressionTableTest {

    @Test
    public void nativeDagBecomesPortableMerkleDag() {
        JsonObject nativeEnvelope = envelope(7, 30);

        JsonObject portable = compacted(nativeEnvelope);
        assertTrue(SharedExpressionTable.isReference(
                portable.get("expression")));
        assertFalse(portable.has(VmExpressionTable.FIELD));

        JsonObject expanded = SharedExpressionTable.expand(portable);
        assertEquals(binary(symbol("x"), constant(1)),
                expanded.getAsJsonObject("expression"));
    }

    @Test
    public void mixedPortableAndNativeTablesUseOneStore() {
        JsonObject artifact = new JsonObject();
        artifact.add("propagated", symbol("upstream"));
        artifact = SharedExpressionTable.compact(artifact);
        artifact.add("runtimeMetadata", envelope(0, 0));

        JsonObject portable = compacted(artifact);
        JsonObject expanded = SharedExpressionTable.expand(portable);

        assertEquals(symbol("upstream"), expanded.get("propagated"));
        assertFalse(VmExpressionTable.usesNativeDag(portable));
    }

    /** One store's view of one artifact, expressions stored once. */
    private static JsonObject compacted(JsonObject artifact) {
        VmExpressionTable.Store store = new VmExpressionTable.Store();
        return store.compact(store.importEnvelope(artifact));
    }

    @Test
    public void storeInternsEqualContentAcrossNativeSessions() {
        VmExpressionTable.Store store = new VmExpressionTable.Store();
        JsonElement first = store.importField(envelope(7, 30).toString(),
                "expression");
        JsonElement second = store.importField(envelope(8, 80).toString(),
                "expression");

        assertSame(first, second);
        JsonObject result = new JsonObject();
        result.add("first", first);
        result.add("second", second);
        JsonObject compact = store.compact(result);
        assertEquals(3, compact.getAsJsonObject(SharedExpressionTable.FIELD)
                .getAsJsonArray("definitions").size());
        JsonObject expanded = SharedExpressionTable.expand(compact);
        assertEquals(expanded.get("first"), expanded.get("second"));
    }

    @Test
    public void unaryNullOperandKeepsItsAnchorAcrossDefaultGsonWire() {
        JsonObject nativeEnvelope = envelope(23, 300);
        JsonObject unary = new JsonObject();
        unary.addProperty("_type", "BinaryExpression");
        unary.add("_left", JsonNull.INSTANCE);
        unary.addProperty("_op", "-");
        unary.add("_right", reference(23, 301));
        nativeEnvelope.getAsJsonObject(VmExpressionTable.FIELD)
                .getAsJsonArray("definitions").get(2).getAsJsonObject()
                .add("expression", unary);

        VmExpressionTable.Store store = new VmExpressionTable.Store();
        JsonObject expanded = store.importEnvelope(nativeEnvelope);
        JsonObject compact = store.compact(expanded);
        JsonObject roundTripped = JsonParser.parseString(
                new Gson().toJson(compact)).getAsJsonObject();

        assertEquals(SharedExpressionTable.expand(compact),
                SharedExpressionTable.expand(roundTripped));
    }

    @Test
    public void inactiveVmMayPublishOneEmptySessionZeroTable() {
        JsonObject envelope = new JsonObject();
        envelope.addProperty("active", false);
        JsonObject table = new JsonObject();
        table.addProperty("schemaVersion", 1);
        table.addProperty("kind", VmExpressionTable.KIND);
        table.addProperty("authority", VmExpressionTable.AUTHORITY);
        table.addProperty("sessionId", 0);
        table.addProperty("definitionCount", 0);
        table.add("definitions", new JsonArray());
        envelope.add(VmExpressionTable.FIELD, table);

        JsonObject decoded = new VmExpressionTable.Store()
                .importEnvelope(envelope);
        assertFalse(decoded.get("active").getAsBoolean());
        assertFalse(decoded.has(VmExpressionTable.FIELD));
    }

    private static JsonObject envelope(long session, long base) {
        if (session == 0L) {
            JsonObject envelope = new JsonObject();
            JsonObject table = new JsonObject();
            table.addProperty("schemaVersion", 1);
            table.addProperty("kind", VmExpressionTable.KIND);
            table.addProperty("authority", VmExpressionTable.AUTHORITY);
            table.addProperty("sessionId", 0);
            table.addProperty("definitionCount", 0);
            table.add("definitions", new JsonArray());
            envelope.add(VmExpressionTable.FIELD, table);
            return envelope;
        }
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind", "CONCOLIC_EXPRESSION");
        envelope.add("expression", reference(session, base + 2));

        JsonArray definitions = new JsonArray();
        definitions.add(definition(session, base, symbol("x")));
        definitions.add(definition(session, base + 1, constant(1)));
        JsonObject sum = new JsonObject();
        sum.addProperty("_type", "BinaryExpression");
        sum.add("_left", reference(session, base));
        sum.addProperty("_op", "+");
        sum.add("_right", reference(session, base + 1));
        definitions.add(definition(session, base + 2, sum));

        JsonObject table = new JsonObject();
        table.addProperty("schemaVersion", 1);
        table.addProperty("kind", VmExpressionTable.KIND);
        table.addProperty("authority", VmExpressionTable.AUTHORITY);
        table.addProperty("sessionId", session);
        table.addProperty("definitionCount", definitions.size());
        table.add("definitions", definitions);
        envelope.add(VmExpressionTable.FIELD, table);
        return envelope;
    }

    private static JsonObject reference(long session, long id) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", VmExpressionTable.REFERENCE_TYPE);
        result.addProperty("sessionId", session);
        result.addProperty("expressionId", id);
        return result;
    }

    private static JsonObject definition(long session, long id,
                                         JsonObject expression) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", VmExpressionTable.DEFINITION_TYPE);
        result.addProperty("sessionId", session);
        result.addProperty("expressionId", id);
        result.add("expression", expression);
        return result;
    }

    private static JsonObject binary(JsonObject left, JsonObject right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", "+");
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
