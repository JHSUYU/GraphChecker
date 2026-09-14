package edu.uva.liftlab.graphchecker.runtime.d3;

import edu.uva.liftlab.graphchecker.d3.contract.LineageHop;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.Role;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Mints identity v2: {@code node#epochN / lineage hops / region#k}.
 *
 * <p>{@code k} is the k-th activation of that region under the same parent
 * hop, so two activations of one region reached through two different
 * callers are two addresses and neither can take the other's.  An
 * activation whose lineage this run could not attribute is still minted --
 * with {@code lineageLost} set and the role it ran as in place of the
 * chain -- because an unnamed interaction is still an interaction
 * (INTERACTION-ID R-I1) and dropping it is the one thing that makes it
 * unreachable for every reader downstream.</p>
 */
public final class OccurrenceMinterV2 {
    private static final Map<String, AtomicInteger> ACTIVATIONS =
            new ConcurrentHashMap<String, AtomicInteger>();

    private OccurrenceMinterV2() {
    }

    /**
     * The address of the next activation of {@code regionId} here, or
     * {@code null} when this run can name no node to put it on.
     *
     * <p>Fail-closed: a guessed node is a wrong causal chain, so an
     * activation with no node publishes no address and the caller files the
     * loss instead (REPORT-ENTRY §4).</p>
     */
    public static OccurrenceAddress mint(String nodeKey, String regionId) {
        return mint(nodeKey, regionId, Lineage.hops(), Lineage.lost());
    }

    /** The same, over a lineage the caller already read. */
    public static OccurrenceAddress mint(String nodeKey, String regionId,
                                         List<LineageHop> lineage,
                                         boolean lineageLost) {
        String region = Text.safe(regionId);
        if (Text.safe(nodeKey).isEmpty() || region.isEmpty()) return null;
        NodeId node = NodeId.parse(nodeKey);
        int k = next(node.render() + "\n" + render(lineage) + "\n" + region);
        return OccurrenceAddress.of(node, lineage, region, k,
                lineageLost || lineage.isEmpty());
    }

    /**
     * The address of an activation that ran under no lineage this run can
     * name: its role and a window-local k, stated as lost.
     *
     * <p>REPORT-ENTRY §4: the region slot carries a role id rather than a
     * plan region, so every reader that distinguishes a planned occurrence
     * from an ambient one does it by the visible {@code ROLE.} prefix.</p>
     */
    public static OccurrenceAddress degraded(String nodeKey, Role role,
                                             String site) {
        if (Text.safe(nodeKey).isEmpty()) return null;
        NodeId node = NodeId.parse(nodeKey);
        Role kind = role == null ? Role.UNKNOWN : role;
        int k = Lineage.windowOrdinal(node.render() + "\n" + kind.name()
                + "\n" + Text.safe(site));
        List<LineageHop> lineage = new ArrayList<LineageHop>(1);
        lineage.add(LineageHop.of(kind, "", k));
        return OccurrenceAddress.of(node, lineage,
                "ROLE." + kind.name(), k, true);
    }

    private static int next(String scope) {
        AtomicInteger counter = ACTIVATIONS.get(scope);
        if (counter == null) {
            AtomicInteger fresh = new AtomicInteger();
            AtomicInteger raced = ACTIVATIONS.putIfAbsent(scope, fresh);
            counter = raced == null ? fresh : raced;
        }
        return counter.incrementAndGet();
    }

    private static String render(List<LineageHop> lineage) {
        if (lineage == null || lineage.isEmpty()) return "";
        StringBuilder rendered = new StringBuilder();
        for (LineageHop hop : lineage) {
            if (rendered.length() > 0) rendered.append('/');
            rendered.append(hop.render());
        }
        return rendered.toString();
    }

    /** Test hook: one window per fixture. */
    public static void resetForTests() {
        ACTIVATIONS.clear();
    }

    /** The empty lineage, for callers that state one explicitly. */
    public static List<LineageHop> noLineage() {
        return Collections.emptyList();
    }
}
