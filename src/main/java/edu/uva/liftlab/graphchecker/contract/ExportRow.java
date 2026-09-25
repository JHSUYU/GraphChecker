package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: a value a producer endpoint put on the wire, {@code e_p}
 * in the {@link ExpressionTable}.  {@code seq} is where the producer's path
 * condition is cut; the sort comes from {@code javaType}, never from the
 * recorded characters.
 */
public final class ExportRow {
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
                Fields.sequence(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.stated(expressionRef, "expressionRef"),
                Fields.text(javaType, "javaType"), handle,
                Fields.stated(recordedValue, "recordedValue"));
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
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof ExportRow)) return false;
        ExportRow other = (ExportRow) value;
        return seq == other.seq && handle == other.handle
                && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && expressionRef.equals(other.expressionRef)
                && javaType.equals(other.javaType)
                && recordedValue.equals(other.recordedValue);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, seq, endpoint, expressionRef, javaType,
                handle, recordedValue);
    }

    @Override
    public String toString() {
        return "ExportRow{" + sessionId + "#" + seq + " " + endpoint + " -> "
                + expressionRef + ":" + javaType + "}";
    }
}
