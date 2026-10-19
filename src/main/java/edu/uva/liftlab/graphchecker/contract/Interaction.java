package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

public final class Interaction extends Value {
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
    Object[] parts() {
        return new Object[] {kind, producer, consumer};
    }

    @Override
    public String toString() {
        return kind + " " + producer + " -> " + consumer;
    }
}
