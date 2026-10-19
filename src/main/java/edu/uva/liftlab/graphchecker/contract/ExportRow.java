package edu.uva.liftlab.graphchecker.contract;

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

    public String expressionRef() {
        return expressionRef;
    }

    public String javaType() {
        return javaType;
    }

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
