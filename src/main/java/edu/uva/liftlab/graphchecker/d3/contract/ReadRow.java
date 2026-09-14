package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one read, as the consumer half of a STATE interaction.
 *
 * <p>{@code observedVersion} is the version the read saw, or -1 when the run
 * could not state it -- an unknown version is published as unknown, never as
 * version 0, because the composer joins {@code read := write version's
 * expression} and a wrong join is a fabricated causal edge.</p>
 */
public final class ReadRow {
    /** The version of a read the run could not attribute. */
    public static final long UNKNOWN_VERSION = -1L;

    private final String sessionId;
    private final Endpoint endpoint;
    private final LocationId location;
    private final long observedVersion;
    private final String symbol;
    private final String concreteValue;

    private ReadRow(String sessionId, Endpoint endpoint, LocationId location,
                    long observedVersion, String symbol, String concreteValue) {
        this.sessionId = sessionId;
        this.endpoint = endpoint;
        this.location = location;
        this.observedVersion = observedVersion;
        this.symbol = symbol;
        this.concreteValue = concreteValue;
    }

    public static ReadRow of(String sessionId, Endpoint endpoint,
                             LocationId location, long observedVersion,
                             String symbol, String concreteValue) {
        return new ReadRow(Fields.text(sessionId, "sessionId"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), observedVersion,
                Fields.text(symbol, "symbol"), Fields.optional(concreteValue));
    }

    public String sessionId() {
        return sessionId;
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

    /** What the read actually saw, or {@code null}. */
    public String concreteValue() {
        return concreteValue;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ReadRow)) return false;
        ReadRow other = (ReadRow) value;
        return observedVersion == other.observedVersion
                && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && location.equals(other.location)
                && symbol.equals(other.symbol)
                && Objects.equals(concreteValue, other.concreteValue);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, endpoint, location, observedVersion,
                symbol, concreteValue);
    }

    @Override
    public String toString() {
        return "ReadRow{" + sessionId + " " + endpoint + " " + location
                + " v" + observedVersion + " " + symbol + "}";
    }
}
