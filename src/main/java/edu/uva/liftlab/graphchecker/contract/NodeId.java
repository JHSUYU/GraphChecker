package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1: a component instance and its declared topology epoch,
 * rendered {@code <node>#epoch<N>} (the node name may carry slashes).
 */
public final class NodeId extends Value {
    /** The one spelling of the epoch separator. */
    public static final String EPOCH_MARKER = "#epoch";

    private final String node;
    private final int epoch;

    private NodeId(String node, int epoch) {
        this.node = node;
        this.epoch = epoch;
    }

    public static NodeId of(String node, int epoch) {
        return new NodeId(Fields.text(node, "node"),
                Fields.nonNegative(epoch, "epoch"));
    }

    /** Reads {@code <node>#epoch<N>}; refuses, never half-parses, the rest. */
    public static NodeId parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int marker = value.lastIndexOf(EPOCH_MARKER);
        int epoch = Fields.trailingNumber(value, marker, EPOCH_MARKER.length());
        if (epoch < 0) {
            throw new IllegalArgumentException(
                    "not a node#epoch<N>: " + rendered);
        }
        return of(value.substring(0, marker), epoch);
    }

    /** The component instance, without its epoch. */
    public String node() {
        return node;
    }

    public String render() {
        return node + EPOCH_MARKER + epoch;
    }

    @Override
    Object[] parts() {
        return new Object[] {node, epoch};
    }

    @Override
    public String toString() {
        return render();
    }
}
