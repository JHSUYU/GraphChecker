package edu.uva.liftlab.graphchecker.runtime.d3;

import edu.uva.liftlab.graphchecker.d3.contract.Role;
import java.util.Objects;

/**
 * Why an occurrence ran (IDENTITY-V3 §1), one of three:
 *
 * <ul>
 *   <li>{@code Anchor(producerEndpointId, rpcSite)} — a message started it,
 *       and the producer's endpoint id carries the producer's own occurrence
 *       (with its own causal context, recursively) and where in the producer
 *       the export was;</li>
 *   <li>{@code Root(role, windowIndex)} — a workload action or a daemon tick
 *       that no message started; the index is the k-th such root inside the
 *       recording window, which is inherent to the role;</li>
 *   <li>{@code Lost(role)} — this run could not attribute the scope.</li>
 * </ul>
 *
 * <p>The random span id of distributed tracing is replaced by a structural
 * anchor, which is what makes two replays' occurrences comparable at all.</p>
 */
public final class CausalContext {
    /** Which of the three this is. */
    public enum Kind { ANCHOR, ROOT, LOST }

    private final Kind kind;
    private final String producerEndpointId;
    private final String rpcSite;
    private final Role role;
    private final int windowIndex;

    private CausalContext(Kind kind, String producerEndpointId,
                          String rpcSite, Role role, int windowIndex) {
        this.kind = kind;
        this.producerEndpointId = producerEndpointId;
        this.rpcSite = rpcSite;
        this.role = role;
        this.windowIndex = windowIndex;
    }

    public static CausalContext anchor(String producerEndpointId,
                                       String rpcSite) {
        return new CausalContext(Kind.ANCHOR, Text.safe(producerEndpointId),
                Text.safe(rpcSite), Role.UNKNOWN, 0);
    }

    public static CausalContext root(Role role, int windowIndex) {
        return new CausalContext(Kind.ROOT, "", "",
                role == null ? Role.UNKNOWN : role, Math.max(1, windowIndex));
    }

    public static CausalContext lost(Role role) {
        return new CausalContext(Kind.LOST, "", "",
                role == null ? Role.UNKNOWN : role, 0);
    }

    public Kind kind() {
        return kind;
    }

    public String producerEndpointId() {
        return producerEndpointId;
    }

    public String rpcSite() {
        return rpcSite;
    }

    public Role role() {
        return role;
    }

    public int windowIndex() {
        return windowIndex;
    }

    public boolean lost() {
        return kind == Kind.LOST;
    }

    public String render() {
        switch (kind) {
            case ANCHOR:
                return "Anchor:" + producerEndpointId
                        + (rpcSite.isEmpty() ? "" : "@" + rpcSite);
            case ROOT:
                return "Root:" + role.name() + "#" + windowIndex;
            default:
                return "Lost:" + role.name();
        }
    }

    @Override
    public boolean equals(Object value) {
        if (this == value) return true;
        if (!(value instanceof CausalContext)) return false;
        CausalContext other = (CausalContext) value;
        return kind == other.kind && role == other.role
                && windowIndex == other.windowIndex
                && producerEndpointId.equals(other.producerEndpointId)
                && rpcSite.equals(other.rpcSite);
    }

    @Override
    public int hashCode() {
        return Objects.hash(kind, producerEndpointId, rpcSite, role,
                windowIndex);
    }

    @Override
    public String toString() {
        return render();
    }
}
