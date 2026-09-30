package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

/**
 * CONTRACT-SPEC §2.2: one read, the consumer half of a STATE interaction.  An
 * unknown {@code observedVersion} is -1, never 0: a wrong join is a
 * fabricated causal edge.
 */
public final class ReadRow extends Value {
    /** The version of a read the run could not attribute. */
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

    private ReadRow(String sessionId, long seq, Endpoint endpoint,
                    LocationId location, long observedVersion, String symbol,
                    String javaType, String concreteValue, long mintVersion,
                    boolean unnamedWriter) {
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
    }

    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue) {
        return of(sessionId, seq, endpoint, location, observedVersion, symbol,
                javaType, concreteValue, UNKNOWN_VERSION);
    }

    /** The same row, stating the mint's own version. */
    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue, long mintVersion) {
        return of(sessionId, seq, endpoint, location, observedVersion, symbol,
                javaType, concreteValue, mintVersion, false);
    }

    /** The same row, stating whether a writer the log never named reached
     *  its location. */
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
                Fields.optional(concreteValue), mintVersion, unnamedWriter);
    }

    /**
     * Whether a writer the VM's log never named reached this read's location
     * when it read (the VM's {@code unnamedWriter}: an unhooked write, an
     * uncaptured Unsafe write, an unmodeled container mutation).  The writers
     * the log states are then not all the writers there were, so the read is
     * paired with the one it observed and no other.  The version bound is not
     * such a writer: every retained version is still a real, exact writer, so
     * a hot field past it keeps its alternatives.
     */
    public boolean unnamedWriter() {
        return unnamedWriter;
    }

    /**
     * A placeholder's own shadow-store version, else {@link #UNKNOWN_VERSION}.
     * {@code observedVersion} joins to the last real write; this is the
     * version a {@code ReadFromExpression} names, unique per mint (so it
     * separates ports declared over one cell).
     */
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

    /** The version observed, or {@link #UNKNOWN_VERSION}. */
    public long observedVersion() {
        return observedVersion;
    }

    /** The symbol the read produced in the path condition. */
    public String symbol() {
        return symbol;
    }

    /** The JVM descriptor {@code symbol} is declared with. */
    public String javaType() {
        return javaType;
    }

    /** What the read returned, spelled as {@link #returned} says, or null. */
    public String concreteValue() {
        return concreteValue;
    }

    /**
     * What one read node states it returned, as {@link #concreteValue}
     * spells it: a scalar constant's payload ({@code Y_I_2} is {@code 2}), a
     * String as its JSON string literal -- quoted, so no content reads as a
     * number or an identity -- Java null as {@code N}, and an object as the
     * name of its identity ({@code M_L'<class>'_<rid>}), which a pin states
     * the read equal to.  An exact read ({@code observedExact}) returned the
     * word its version stored, so a version whose value is one of those
     * leaves states it when the node does not (a reference cell's INITIAL
     * null).  Null when neither states anything.
     */
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
        // A String past the VM's bound states only its length: unstated,
        // never a prefix to pin to.
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

    /** The leaf an exact read's version holds: null, a constant, or a
     *  named object; else null. */
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

    /** The content of a String {@link #returned} spelled, else null. */
    public static String stringContent(String spelled) {
        String text = spelled == null ? "" : spelled.trim();
        if (text.isEmpty() || text.charAt(0) != '"') return null;
        return new JsonParser().parse(text).getAsString();
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location,
                observedVersion, symbol, javaType, concreteValue, mintVersion,
                unnamedWriter};
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + observedVersion + " " + symbol + ":"
                + javaType + "}";
    }
}
