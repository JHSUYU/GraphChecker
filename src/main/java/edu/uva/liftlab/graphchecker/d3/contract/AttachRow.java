package edu.uva.liftlab.graphchecker.d3.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 2: a value a consumer endpoint took off the wire.
 *
 * <p>{@code symbol} is the handoff control {@code v_H} minted at this attach --
 * at EVERY declared port, whether or not the region was selected -- and
 * {@code arrival} what actually arrived.  {@code producer} is the endpoint the
 * run paired this attach with, by correlation id and handle; it is null only
 * when the arrival could not be paired at all, and carries
 * {@code lineageLost} when the exporter had no scope to name (INTERACTION-ID
 * R-I1).</p>
 *
 * <p>{@code seq} places the attach in its session's event order;{@code
 * javaType} is the JVM descriptor {@code v_H} is declared with, which must be
 * the descriptor of every arm's {@code e_q} in this interaction's family.</p>
 */
public final class AttachRow {
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

    private AttachRow(String sessionId, long seq, Endpoint endpoint,
                      String symbol, String javaType, String arrival,
                      boolean answered, String answeredValue, Endpoint producer,
                      String correlationId) {
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
    }

    public static AttachRow of(String sessionId, long seq, Endpoint endpoint,
                               String symbol, String javaType, String arrival,
                               boolean answered, String answeredValue,
                               Endpoint producer, String correlationId) {
        return new AttachRow(Fields.text(sessionId, "sessionId"),
                Fields.sequence(seq, "seq"),
                Fields.required(endpoint, "endpoint"),
                Fields.text(symbol, "symbol"),
                Fields.text(javaType, "javaType"),
                Fields.stated(arrival, "arrival"), answered,
                Fields.optional(answeredValue), producer,
                Fields.stated(correlationId, "correlationId"));
    }

    public String sessionId() {
        return sessionId;
    }

    /** Where this attach falls in its session's event order. */
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

    /** The WIRE interaction this attach is the consumer half of, or null. */
    public Interaction interaction() {
        return producer == null ? null
                : Interaction.of(InteractionKind.WIRE, producer, endpoint);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof AttachRow)) return false;
        AttachRow other = (AttachRow) value;
        return seq == other.seq && answered == other.answered
                && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && symbol.equals(other.symbol)
                && javaType.equals(other.javaType)
                && arrival.equals(other.arrival)
                && Objects.equals(answeredValue, other.answeredValue)
                && Objects.equals(producer, other.producer)
                && correlationId.equals(other.correlationId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, seq, endpoint, symbol, javaType, arrival,
                answered, answeredValue, producer, correlationId);
    }

    @Override
    public String toString() {
        return "AttachRow{" + sessionId + "#" + seq + " " + endpoint + " "
                + symbol + ":" + javaType
                + (producer == null ? " unpaired}" : " <- " + producer + "}");
    }
}
