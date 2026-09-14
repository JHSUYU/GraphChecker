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
 */
public final class AttachRow {
    private final String sessionId;
    private final Endpoint endpoint;
    private final String symbol;
    private final String arrival;
    private final boolean answered;
    private final String answeredValue;
    private final Endpoint producer;
    private final String correlationId;

    private AttachRow(String sessionId, Endpoint endpoint, String symbol,
                      String arrival, boolean answered, String answeredValue,
                      Endpoint producer, String correlationId) {
        this.sessionId = sessionId;
        this.endpoint = endpoint;
        this.symbol = symbol;
        this.arrival = arrival;
        this.answered = answered;
        this.answeredValue = answeredValue;
        this.producer = producer;
        this.correlationId = correlationId;
    }

    public static AttachRow of(String sessionId, Endpoint endpoint,
                               String symbol, String arrival, boolean answered,
                               String answeredValue, Endpoint producer,
                               String correlationId) {
        return new AttachRow(Fields.text(sessionId, "sessionId"),
                Fields.required(endpoint, "endpoint"),
                Fields.text(symbol, "symbol"),
                Fields.stated(arrival, "arrival"), answered,
                Fields.optional(answeredValue), producer,
                Fields.stated(correlationId, "correlationId"));
    }

    public String sessionId() {
        return sessionId;
    }

    public Endpoint endpoint() {
        return endpoint;
    }

    /** The handoff control {@code v_H} minted at this attach. */
    public String symbol() {
        return symbol;
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
        return answered == other.answered && sessionId.equals(other.sessionId)
                && endpoint.equals(other.endpoint)
                && symbol.equals(other.symbol) && arrival.equals(other.arrival)
                && Objects.equals(answeredValue, other.answeredValue)
                && Objects.equals(producer, other.producer)
                && correlationId.equals(other.correlationId);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sessionId, endpoint, symbol, arrival, answered,
                answeredValue, producer, correlationId);
    }

    @Override
    public String toString() {
        return "AttachRow{" + sessionId + " " + endpoint + " " + symbol
                + (producer == null ? " unpaired}" : " <- " + producer + "}");
    }
}
