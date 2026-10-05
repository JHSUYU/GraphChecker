package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: a value a producer endpoint put on the wire, {@code e_p}
 * in the {@link ExpressionTable}.  {@code seq} is where the producer's path
 * condition is cut; the sort comes from {@code javaType}, never from the
 * recorded characters.
 */
public final class ExportRow extends Value {
    private final String sessionId;
    private final long seq;
    private final Endpoint endpoint;
    private final String expressionRef;
    private final String javaType;
    private final long handle;
    private final String recordedValue;

    private ExportRow(String sessionId, long seq, Endpoint endpoint,
                      String expressionRef, String javaType, long handle,
                      String recordedValue) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.expressionRef = expressionRef;
        this.javaType = javaType;
        this.handle = handle;
        this.recordedValue = recordedValue;
    }

    public static ExportRow of(String sessionId, long seq, Endpoint endpoint,
                               String expressionRef, String javaType,
                               long handle, String recordedValue) {
        return new ExportRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.required(expressionRef, "expressionRef"),
                Fields.text(javaType, "javaType"), handle,
                Fields.required(recordedValue, "recordedValue"));
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

    /** The reference to {@code e_p} in this session's expression table. */
    public String expressionRef() {
        return expressionRef;
    }

    /** The JVM descriptor of the exported value. */
    public String javaType() {
        return javaType;
    }

    /** The VM handle of the exported value: half of the wire pairing. */
    public long handle() {
        return handle;
    }

    public String recordedValue() {
        return recordedValue;
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, expressionRef, javaType,
                handle, recordedValue};
    }

    @Override
    public String toString() {
        return "ExportRow{" + sessionId + "#" + seq + " " + endpoint
                + " -> " + expressionRef + ":" + javaType + "}";
    }
}
