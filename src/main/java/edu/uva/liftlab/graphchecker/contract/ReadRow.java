package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

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
    private final boolean writerSetComplete;

    private ReadRow(String sessionId, long seq, Endpoint endpoint,
                    LocationId location, long observedVersion, String symbol,
                    String javaType, String concreteValue, long mintVersion,
                    boolean writerSetComplete) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.observedVersion = observedVersion;
        this.symbol = symbol;
        this.javaType = javaType;
        this.concreteValue = concreteValue;
        this.mintVersion = mintVersion;
        this.writerSetComplete = writerSetComplete;
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
                javaType, concreteValue, mintVersion, true);
    }

    /** The same row, stating whether its location's writer set was whole. */
    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue, long mintVersion,
                             boolean writerSetComplete) {
        return new ReadRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), observedVersion,
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.optional(concreteValue), mintVersion,
                writerSetComplete);
    }

    /**
     * Whether the VM saw every writer of this read's location when it read
     * (the VM's {@code writerSetComplete}).  A read may state its version
     * without it -- its observation is exact ({@code observedExact}) -- but
     * then its version is the only writer anyone may pair it with: an
     * alternative writer is one of a set known to be partial.
     */
    public boolean writerSetComplete() {
        return writerSetComplete;
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
     * number or an identity -- and Java null as {@code N}.  Null when the
     * node states nothing: it returned an identity, which no value pins.
     */
    public static String returned(JsonObject node) {
        JsonElement value = node == null ? null : node.get("concreteValue");
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
        return constant == null || !constant.isJsonPrimitive() ? null
                : VmExpressionIr.constantPayload(constant.getAsString());
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
                writerSetComplete};
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + observedVersion + " " + symbol + ":"
                + javaType + "}";
    }
}
