package edu.uva.liftlab.graphchecker.runtime.d3;

import edu.uva.liftlab.graphchecker.d3.contract.CausalContext;
import edu.uva.liftlab.graphchecker.d3.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.d3.contract.NodeId;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.Role;

/**
 * Mints identity v3: {@code node / region / why it ran / where it is}.
 *
 * <p>An activation whose causal context this run cannot attribute is minted
 * all the same, as {@code Lost(role)}: an unnamed interaction is still an
 * interaction (INTERACTION-ID R-I1), and dropping it is the one thing that
 * makes it unreachable for every reader downstream.  A node this run cannot
 * name at all mints nothing -- a guessed node is a wrong causal chain.</p>
 */
public final class OccurrenceMinterV2 {
    private OccurrenceMinterV2() {
    }

    /**
     * The address of the activation entering here, or {@code null} when this
     * run can name no node to put it on.
     *
     * <p>Identity v3: node, region, the causal context it entered under and
     * the execution index of the entry.  No ordinal: "the k-th activation"
     * moves whenever an unrelated invocation is inserted earlier in the run,
     * which is what a branch flip does.</p>
     */
    public static OccurrenceAddress mint(String nodeKey, String regionId,
                                         CausalContext context,
                                         ExecutionIndex index) {
        if (Text.safe(nodeKey).isEmpty() || Text.safe(regionId).isEmpty()) {
            return null;
        }
        return OccurrenceAddress.of(NodeId.parse(nodeKey),
                Text.safe(regionId),
                context == null ? CausalContext.of(Role.UNKNOWN) : context,
                index == null ? ExecutionIndex.empty() : index);
    }

    /**
     * The address of an activation that ran under no lineage this run can
     * name: its role, and where the thread was.
     *
     * <p>REPORT-ENTRY §4: the region slot carries a role id rather than a
     * plan region, so a reader tells an ambient occurrence from a planned
     * one by the visible {@code ROLE.} prefix.</p>
     */
    public static OccurrenceAddress degraded(String nodeKey, Role role,
                                             String site) {
        if (Text.safe(nodeKey).isEmpty()) return null;
        Role kind = role == null ? Role.UNKNOWN : role;
        return OccurrenceAddress.of(NodeId.parse(nodeKey),
                "ROLE." + kind.name(), CausalContext.of(kind),
                Identity.here());
    }

    public static void resetForTests() {
    }
}
