package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: a value a producer endpoint put on the wire.
 *
 * <p>{@code expressionRef} names the propagated expression {@code e_p} in the
 * session's {@link ExpressionTable}; {@code handle} and the exchange
 * correlation id are the within-run pairing evidence an attach joins on.</p>
 *
 * <p>{@code seq} places the export in its session's event order, which is where
 * the producer's path condition is cut; {@code javaType} is the JVM descriptor
 * of the exported value ({@code I}, {@code J}, {@code Z},
 * {@code Ljava/lang/String;}), so a solver takes the sort from the declaration
 * instead of inferring it from the recorded characters.</p>
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

    /** Where this export falls in its session's event order. */
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
