package edu.uva.liftlab.graphchecker.contract;

public final class AttachRow extends Value {
    public static final String HANDLE = "HANDLE";
    public static final String CORRELATION_PORT = "CORRELATION_PORT";

    private final String sessionId;
    private final long seq;
    private final Endpoint endpoint;
    private final String symbol;
    private final String javaType;
    private final String arrival;
    private final boolean answered;
    private final String answeredValue;
    private final Endpoint producer;
    private final String correlationId;
    private final String pairedBy;

    private AttachRow(String sessionId, long seq, Endpoint endpoint,
                      String symbol, String javaType, String arrival,
                      boolean answered, String answeredValue, Endpoint producer,
                      String correlationId, String pairedBy) {
        this.sessionId = sessionId;
        this.seq = seq;
        this.endpoint = endpoint;
        this.symbol = symbol;
        this.javaType = javaType;
        this.arrival = arrival;
        this.answered = answered;
        this.answeredValue = answeredValue;
        this.producer = producer;
        this.correlationId = correlationId;
        this.pairedBy = pairedBy;
    }

    public static AttachRow of(String sessionId, long seq, Endpoint endpoint,
                               String symbol, String javaType, String arrival,
                               boolean answered, String answeredValue,
                               Endpoint producer, String correlationId,
                               String pairedBy) {
        return new AttachRow(Fields.text(sessionId, "sessionId"),
                Fields.nonNegative(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.required(arrival, "arrival"), answered,
                Fields.optional(answeredValue), producer,
                Fields.required(correlationId, "correlationId"),
                Fields.optional(pairedBy));
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

    public String symbol() {
        return symbol;
    }

    public String javaType() {
        return javaType;
    }

    public String arrival() {
        return arrival;
    }

    public boolean answered() {
        return answered;
    }

    public String answeredValue() {
        return answeredValue;
    }

    public Endpoint producer() {
        return producer;
    }

    public String correlationId() {
        return correlationId;
    }

    public String pairedBy() {
        return pairedBy;
    }

    public Interaction interaction() {
        return producer == null ? null
                : Interaction.of(InteractionKind.WIRE, producer, endpoint);
    }

    @Override
    Object[] parts() {
        return new Object[] {sessionId, seq, endpoint, symbol, javaType,
                arrival, answered, answeredValue, producer, correlationId,
                pairedBy};
    }

    @Override
    public String toString() {
        return "AttachRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + symbol + ":" + javaType
                + (producer == null ? " unpaired}" : " <- " + producer + "}");
    }
}
