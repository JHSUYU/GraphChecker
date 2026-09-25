package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one read, the consumer half of a STATE interaction.  An
 * unknown {@code observedVersion} is -1, never 0: a wrong join is a
 * fabricated causal edge.
 */
public final class ReadRow {
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

    private ReadRow(String sessionId, long seq, Endpoint endpoint,
                    LocationId location, long observedVersion, String symbol,
                    String javaType, String concreteValue, long mintVersion) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.observedVersion = observedVersion;
        this.symbol = symbol;
        this.javaType = javaType;
        this.concreteValue = concreteValue;
        this.mintVersion = mintVersion;
    }

    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue) {
        return of(sessionId, seq, endpoint, location, observedVersion, symbol,
                javaType, concreteValue, UNKNOWN_VERSION);
    }

    /** CONTRACT v2.4: the same row, stating the mint's own version. */
    public static ReadRow of(String sessionId, long seq, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String javaType,
                             String concreteValue, long mintVersion) {
        return new ReadRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), observedVersion,
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.optional(concreteValue), mintVersion);
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

    /** What the read actually saw, or {@code null}. */
    public String concreteValue() {
        return concreteValue;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ReadRow)) return false;
        ReadRow other = (ReadRow) value;
        return seq == other.seq
                && observedVersion == other.observedVersion
                && mintVersion == other.mintVersion
                && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && location.equals(other.location)
                && symbol.equals(other.symbol)
                && javaType.equals(other.javaType)
                && Objects.equals(concreteValue, other.concreteValue);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, seq, endpoint, location, observedVersion,
                symbol, javaType, concreteValue, mintVersion);
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + observedVersion + " " + symbol + ":"
                + javaType + "}";
    }
}
