package edu.uva.liftlab.graphchecker.contract;

import java.util.Objects;

/**
 * CONTRACT-SPEC 1: a component instance and its topology epoch.
 *
 * <p>Rendered {@code <node>#epoch<N>}, e.g. {@code hdfs-17897/dn0#epoch0}.  The
 * node name itself carries slashes (the workload names a case and a role); the
 * epoch is the lifecycle the workload declared, so the same label means the
 * same lifecycle in a recording and in every replay of it.</p>
 */
public final class NodeId {
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
                Fields.count(epoch, "epoch"));
    }

    /**
     * Reads {@code <node>#epoch<N>}.
     *
     * <p>A string that does not spell a node and an epoch is refused naming
     * itself: an address nobody can read must not half-parse into one that
     * matches something.</p>
     */
    public static NodeId parse(String rendered) {
        String value = rendered == null ? "" : rendered.trim();
        int marker = value.lastIndexOf(EPOCH_MARKER);
        if (marker <= 0 || marker + EPOCH_MARKER.length() >= value.length()) {
            throw new IllegalArgumentException(
                    "not a node#epoch<N>: " + rendered);
        }
        String epoch = value.substring(marker + EPOCH_MARKER.length());
        for (int index = 0; index < epoch.length(); index++) {
            if (!Character.isDigit(epoch.charAt(index))) {
                throw new IllegalArgumentException(
                        "not a node#epoch<N>: " + rendered);
            }
        }
        return of(value.substring(0, marker), Integer.parseInt(epoch));
    }

    /** The component instance, without its epoch. */
    public String node() {
        return node;
    }

    public String render() {
        return node + EPOCH_MARKER + epoch;
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof NodeId)) return false;
        NodeId other = (NodeId) value;
        return epoch == other.epoch && node.equals(other.node);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, epoch);
    }

    @Override
    public String toString() {
        return render();
    }
}
