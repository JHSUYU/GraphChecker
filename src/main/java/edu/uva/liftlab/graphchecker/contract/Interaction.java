package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.util.Objects;

/**
 * CONTRACT-SPEC 1: one causal-graph edge, named by both endpoints.  A family
 * is keyed by the interaction (INTERACTION-ID R-I2): same port, other
 * endpoint contributes nothing.
 */
public final class Interaction {
    private final InteractionKind kind;
    private final Endpoint producer;
    private final Endpoint consumer;

    private Interaction(InteractionKind kind, Endpoint producer,
                        Endpoint consumer) {
        this.kind = kind;
        this.producer = producer;
        this.consumer = consumer;
    }

    public static Interaction of(InteractionKind kind, Endpoint producer,
                                 Endpoint consumer) {
        return new Interaction(Fields.required(kind, "kind"),
                Fields.required(producer, "producer"),
                Fields.required(consumer, "consumer"));
    }

    public InteractionKind kind() {
        return kind;
    }

    public Endpoint producer() {
        return producer;
    }

    public Endpoint consumer() {
        return consumer;
    }

    public String id() {
        return ArtifactIO.digest(kind.name() + producer.id() + consumer.id(), 16);
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof Interaction)) return false;
        Interaction other = (Interaction) value;
        return kind == other.kind && producer.equals(other.producer)
                && consumer.equals(other.consumer);
    }

    @Override
    public int hashCode() {
        return Objects.hash(kind, producer, consumer);
    }

    @Override
    public String toString() {
        return kind + " " + producer + " -> " + consumer;
    }
}
