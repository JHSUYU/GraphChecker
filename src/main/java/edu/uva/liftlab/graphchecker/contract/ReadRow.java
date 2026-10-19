package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

public final class ReadRow extends Value {
    public static final long UNKNOWN_VERSION = -1L;

    private final String sessionId;
    private final long seq;
    private final Endpoint endpoint;
    private final LocationId location;
    private final long observedVersion;
    private final String symbol;
    private final String javaType;
    private final String concreteValue;
    private final long mintVersion;
    private final boolean unnamedWriter;
    private final int tie;

    private ReadRow(String sessionId, long seq, Endpoint endpoint,
                    LocationId location, long observedVersion, String symbol,
                    String javaType, String concreteValue, long mintVersion,
                    boolean unnamedWriter, int tie) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.observedVersion = observedVersion;
        this.symbol = symbol;
        this.javaType = javaType;
        this.concreteValue = concreteValue;
        this.mintVersion = mintVersion;
        this.unnamedWriter = unnamedWriter;
        this.tie = tie;
    }

    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue) {
        return of(sessionId, seq, endpoint, location, observedVersion, symbol,
                javaType, concreteValue, UNKNOWN_VERSION);
    }

    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue, long mintVersion) {
        return of(sessionId, seq, endpoint, location, observedVersion, symbol,
                javaType, concreteValue, mintVersion, false);
    }

    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue, long mintVersion,
                             boolean unnamedWriter) {
        return new ReadRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), observedVersion,
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.optional(concreteValue), mintVersion, unnamedWriter, 0);
    }

    public ReadRow withTie(int tie) {
        if (tie == this.tie) return this;
        return new ReadRow(sessionId, seq, endpoint, location,
                observedVersion, symbol, javaType, concreteValue, mintVersion,
                unnamedWriter, (int) Fields.nonNegative(tie, "tie"));
    }

    public int tie() {
        return tie;
    }

    public boolean unnamedWriter() {
        return unnamedWriter;
    }

    public long mintVersion() {
        return mintVersion;
    }

    public String sessionId() {
        return sessionId;
    }

    public long seq() {
        return seq;
    }

    public Endpoint endpoint() {
        return endpoint;
    }

    public LocationId location() {
        return location;
    }

    public long observedVersion() {
        return observedVersion;
    }

    public String symbol() {
        return symbol;
    }

    public String javaType() {
        return javaType;
    }

    public String concreteValue() {
        return concreteValue;
    }

    public static String returned(JsonObject node) {
        JsonElement value = node == null ? null : node.get("concreteValue");
        if (value == null) value = exactlyObserved(node);
        if (value == null) return null;
        if (value.isJsonNull()) return VmExpressionIr.SYMBOLIC_NULL;
        if (value.isJsonPrimitive()) {
            return value.getAsJsonPrimitive().isString() ? value.toString()
                    : null;
        }
        if (!value.isJsonObject()) return null;
        if (VmExpressionIr.TRUNCATED_VALUE_TYPE.equals(
                VmExpressionIr.typeOf(value))) {
            return null;
        }
        JsonElement constant = value.getAsJsonObject().get("_exp");
        if (constant == null || !constant.isJsonPrimitive()) return null;
        return VmExpressionIr.SYMBOL_TYPE.equals(VmExpressionIr.typeOf(value))
                ? constant.getAsString()
                : VmExpressionIr.constantPayload(constant.getAsString());
    }

    private static JsonElement exactlyObserved(JsonObject node) {
        JsonElement exact = node == null ? null : node.get("observedExact");
        JsonElement version = node == null ? null
                : node.get("observedVersion");
        if (exact == null || !exact.isJsonPrimitive() || !exact.getAsBoolean()
                || version == null || !version.isJsonObject()) {
            return null;
        }
        JsonElement leaf = version.getAsJsonObject().get("expression");
        if (leaf == null || !leaf.isJsonObject()) return null;
        String type = VmExpressionIr.typeOf(leaf);
        JsonElement spelled = leaf.getAsJsonObject().get("_exp");
        String text = spelled != null && spelled.isJsonPrimitive()
                ? spelled.getAsString() : "";
        boolean stated = "ConstExpr".equals(type)
                || VmExpressionIr.SYMBOL_TYPE.equals(type)
                && (VmExpressionIr.SYMBOLIC_NULL.equals(text)
                || VmRows.referencedObjectRid(text) > 0L);
        return !stated ? null : VmExpressionIr.SYMBOLIC_NULL.equals(text)
                ? JsonNull.INSTANCE : leaf;
    }

    public static String stringContent(String spelled) {
        String text = spelled == null ? "" : spelled.trim();
        if (text.isEmpty() || text.charAt(0) != '"') return null;
        return new JsonParser().parse(text).getAsString();
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location,
                observedVersion, symbol, javaType, concreteValue, mintVersion,
                unnamedWriter, tie};
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + observedVersion + " " + symbol + ":"
                + javaType + "}";
    }
}
