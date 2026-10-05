package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: a value a consumer endpoint took off the wire.
 * {@code symbol} is the handoff control {@code v_H}, minted at every declared
 * port; {@code arrival} is what arrived; {@code producer} is null only when
 * unpaired (IDENTITY §4).  {@code javaType} must equal every arm's
 * {@code e_q} descriptor in the family.  {@code pairedBy} names which key
 * paired it (not equal evidence, IDENTITY §4); null means unstated,
 * not unpaired.
 */
public final class AttachRow extends Value {
    /** Paired by the VM handle the export staged. */
    public static final String HANDLE = "HANDLE";
    /** Paired by the message's correlation id and the port. */
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

    /** The handoff control {@code v_H} minted at this attach. */
    public String symbol() {
        return symbol;
    }

    /** The JVM descriptor {@code v_H} is declared with. */
    public String javaType() {
        return javaType;
    }

    /** What arrived in this session. */
    public String arrival() {
        return arrival;
    }

    /** Whether an obligation answered this attach instead of the arrival. */
    public boolean answered() {
        return answered;
    }

    /** The answered value, or {@code null}. */
    public String answeredValue() {
        return answeredValue;
    }

    /** The paired producer endpoint, or {@code null} when unpaired. */
    public Endpoint producer() {
        return producer;
    }

    /** The exchange correlation id: the within-run pairing evidence. */
    public String correlationId() {
        return correlationId;
    }

    /** {@link #HANDLE}, {@link #CORRELATION_PORT}, or {@code null}
     *  (unstated). */
    public String pairedBy() {
        return pairedBy;
    }

    /** The WIRE interaction this attach is the consumer half of, or null. */
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
