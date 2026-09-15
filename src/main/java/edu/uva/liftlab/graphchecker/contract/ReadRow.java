package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one read, as the consumer half of a STATE interaction.
 *
 * <p>{@code observedVersion} is the version the read saw, or -1 when the run
 * could not state it -- an unknown version is published as unknown, never as
 * version 0, because the composer joins {@code read := write version's
 * expression} and a wrong join is a fabricated causal edge.</p>
 *
 * <p>{@code seq} orders this read against its session's writes, so a read of a
 * location written twice is placed without a clock; {@code javaType} is the JVM
 * descriptor {@code symbol} is declared with.</p>
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
                Fields.sequence(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), observedVersion,
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.optional(concreteValue), mintVersion);
    }

    /**
     * The version the VM published for this mint's shadow store, or
     * {@link #UNKNOWN_VERSION} when this row is not a placeholder.
     *
     * <p>A declared region input is a READ, so the mint's store is no write
     * and no WriteRow states it -- but a term's {@code ReadFromExpression}
     * names exactly that version, because that is what the location held
     * when the read ran.  {@code observedVersion} is the last REAL write
     * before the mint, which is the JOIN to the occurrence that wrote the
     * cell; this is the other half, the version a reader arrives with.  One
     * occurrence may declare one cell under several ports, so keying the
     * bridge on (occurrence, location) cannot choose between them and this
     * can: the mint's version is unique by construction.</p>
     */
    public long mintVersion() {
        return mintVersion;
    }

    public String sessionId() {
        return sessionId;
    }

    /** Where this read falls in its session's event order. */
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
                symbol, javaType, concreteValue);
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + observedVersion + " " + symbol + ":"
                + javaType + "}";
    }
}
