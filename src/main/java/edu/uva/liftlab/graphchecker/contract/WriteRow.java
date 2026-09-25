package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 2: one write, the producer half of a STATE interaction.
 * {@code version} joins reads within a run; across runs the endpoint is the
 * identity (INTERACTION-ID R-I4).
 */
public final class WriteRow extends Value {
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
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(location, "location"), version,
                Fields.required(expressionRef, "expressionRef"),
                Fields.text(javaType, "javaType"));
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
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, location, version,
                expressionRef, javaType};
    }

    @Override
    public String toString() {
        return "WriteRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + location + " v" + version + ":" + javaType + "}";
    }
}
