package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one write, as the producer half of a STATE interaction.
 *
 * <p>The {@code version} it produced is what a read joins on within the run;
 * across runs the arm set is the writer paths whose endpoint equals this one
 * (INTERACTION-ID R-I4), which is why the endpoint and not the version number
 * is the identity.</p>
 */
public final class WriteRow {
    private final String sessionId;
    private final Endpoint endpoint;
    private final LocationId location;
    private final long version;
    private final String expressionRef;

    private WriteRow(String sessionId, Endpoint endpoint, LocationId location,
                     long version, String expressionRef) {
        this.sessionId = sessionId;
        this.endpoint = endpoint;
        this.location = location;
        this.version = version;
        this.expressionRef = expressionRef;
    }

    public static WriteRow of(String sessionId, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef) {
        return new WriteRow(Fields.text(sessionId, "sessionId"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), version,
                Fields.stated(expressionRef, "expressionRef"));
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

    /** The version of the location this write produced. */
    public long version() {
        return version;
    }

    /** The expression the write stored, in the session's table. */
    public String expressionRef() {
        return expressionRef;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof WriteRow)) return false;
        WriteRow other = (WriteRow) value;
        return version == other.version && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && location.equals(other.location)
                && expressionRef.equals(other.expressionRef);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, endpoint, location, version,
                expressionRef);
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + " " + endpoint + " " + location
                + " v" + version + "}";
    }
}
