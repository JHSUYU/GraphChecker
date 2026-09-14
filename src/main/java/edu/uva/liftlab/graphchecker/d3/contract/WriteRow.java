package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: one write, as the producer half of a STATE interaction.
 *
 * <p>The {@code version} it produced is what a read joins on within the run;
 * across runs the arm set is the writer paths whose endpoint equals this one
 * (INTERACTION-ID R-I4), which is why the endpoint and not the version number
 * is the identity.</p>
 *
 * <p>{@code seq} orders this write against the reads and writes of its own
 * session; {@code javaType} is the JVM descriptor of the stored value, so the
 * read that joins to this version is declared at the same sort.</p>
 */
public final class WriteRow {
    private final String sessionId;
    private final long seq;
    private final Endpoint endpoint;
    private final LocationId location;
    private final long version;
    private final String expressionRef;
    private final String javaType;

    private WriteRow(String sessionId, long seq, Endpoint endpoint,
                     LocationId location, long version, String expressionRef,
                     String javaType) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.location = location;
        this.version = version;
        this.expressionRef = expressionRef;
        this.javaType = javaType;
    }

    public static WriteRow of(String sessionId, long seq, Endpoint endpoint,
                              LocationId location, long version,
                              String expressionRef, String javaType) {
        return new WriteRow(Fields.text(sessionId, "sessionId"),
                Fields.sequence(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), version,
                Fields.stated(expressionRef, "expressionRef"),
                Fields.text(javaType, "javaType"));
    }

    public String sessionId() {
        return sessionId;
    }

    /** Where this write falls in its session's event order. */
    public long seq() {
        return seq;
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

    /** The JVM descriptor of the stored value. */
    public String javaType() {
        return javaType;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof WriteRow)) return false;
        WriteRow other = (WriteRow) value;
        return seq == other.seq && version == other.version
                && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && location.equals(other.location)
                && expressionRef.equals(other.expressionRef)
                && javaType.equals(other.javaType);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, seq, endpoint, location, version,
                expressionRef, javaType);
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + version + ":" + javaType + "}";
    }
}
