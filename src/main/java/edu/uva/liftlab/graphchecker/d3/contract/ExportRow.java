package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: a value a producer endpoint put on the wire.
 *
 * <p>{@code expressionRef} names the propagated expression {@code e_p} in the
 * session's {@link ExpressionTable}; {@code handle} and the exchange
 * correlation id are the within-run pairing evidence an attach joins on.</p>
 */
public final class ExportRow {
    private final String sessionId;
    private final Endpoint endpoint;
    private final String expressionRef;
    private final long handle;
    private final String recordedValue;

    private ExportRow(String sessionId, Endpoint endpoint,
                      String expressionRef, long handle, String recordedValue) {
        this.sessionId = sessionId;
        this.endpoint = endpoint;
        this.expressionRef = expressionRef;
        this.handle = handle;
        this.recordedValue = recordedValue;
    }

    public static ExportRow of(String sessionId, Endpoint endpoint,
                               String expressionRef, long handle,
                               String recordedValue) {
        return new ExportRow(Fields.text(sessionId, "sessionId"),
                Fields.required(endpoint, "endpoint"),
                Fields.stated(expressionRef, "expressionRef"), handle,
                Fields.stated(recordedValue, "recordedValue"));
    }

    public String sessionId() {
        return sessionId;
    }

    public Endpoint endpoint() {
        return endpoint;
    }

    /** The reference to {@code e_p} in this session's expression table. */
    public String expressionRef() {
        return expressionRef;
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
        return handle == other.handle && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && expressionRef.equals(other.expressionRef)
                && recordedValue.equals(other.recordedValue);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, endpoint, expressionRef, handle,
                recordedValue);
    }

    @Override
    public String toString() {
        return "ExportRow{" + sessionId + " " + endpoint + " -> "
                + expressionRef + "}";
    }
}
