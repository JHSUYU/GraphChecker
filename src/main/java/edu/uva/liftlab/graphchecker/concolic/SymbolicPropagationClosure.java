package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.TreeMap;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Closes receiver-owned symbolic values before SMT lowering.
 *
 * <p>The VM has already propagated each value through ordinary Java
 * operations. It leaves a transparent {@code ConsumerBoundaryExpression} at
 * every RPC attach and shared-state read. This pass gives those dynamic
 * observations a replay-independent family identity and merges the payloads
 * observed for that family. It never recovers a value from a graph edge,
 * output port, or producer capture.</p>
 *
 * <p>A written arm is selected by the exact producer case named by runtime
 * evidence, so its selector implies that case's PC through normal relation
 * lowering. An INITIAL arm names the pre-write source value and therefore
 * uses a content-addressed source case with the empty PC. Nested boundary
 * references are resolved recursively, so an A<-B<-C chain contains two
 * shared merge nodes instead of a product of B and C cases.</p>
 */
public final class SymbolicPropagationClosure {
    public static final int SCHEMA_VERSION = 2;

    /** An INITIAL version is an observed source value, not a region write. */
    /**
     * A whole-state carrier whose INITIAL version stayed opaque, so its
     * initial membership is a free container const rather than content.
     */
    public static final String INITIAL_CONTAINER_SNAPSHOT_TRUNCATED =
            "INITIAL_CONTAINER_SNAPSHOT_TRUNCATED";
    /**
     * One RPC attach whose sender-side expression did not reach the join.
     *
     * <p>Raised where a referenced attach family carries no usable payload
     * arm at all, and where its only payload observation was truncated.
     * Named apart from the field-read cases because the two have different
     * causes and different fixes: a field read with no writer case is an
     * incomplete read-from snapshot, while an attach with no payload means
     * the value the wire carried never reached the join, so the receiver's
     * leaf is left equal to nothing.</p>
     */
    public static final String RPC_ATTACH_SENDER_EXPRESSION_MISSING =
            "RPC_ATTACH_SENDER_EXPRESSION_MISSING";

    private SymbolicPropagationClosure() {
    }


    /**
     * The stable family key one consumer boundary carries.
     *
     * <p>A boundary is addressed by the planned occurrence that consumed it,
     * within its topology epoch, by kind, by the slot the kind names -- a
     * port for an RPC attach, a replay-stable location for a field read --
     * and by which occurrence of that slot this is.  Both the importer, which
     * stamps RPC boundaries as it admits a result, and this closure, which
     * addresses field reads, key on the same five parts in the same order.
     * </p>
     *
     * <p>The topology epoch is the campaign's refinement iteration
     * ({@code iteration-NNNN}), and it stays in the key on purpose.  It is
     * not a per-run counter: the refinement loop is deterministic, so two
     * campaigns over one obligation walk the same iterations and mint the
     * same epochs.  It is also load-bearing, because the epoch is what the
     * family is addressed <em>within</em>: the same planned occurrence
     * consuming the same slot is a different obligation once refinement has
     * changed the topology around it, and dropping the epoch would join two
     * families that were never the same one.  Every other component here is
     * already content-addressed, and this key reaches no published plan row;
     * it names boundary families inside the importer and the closure.</p>
     */
    public static String boundaryFamilyKey(String topologyEpoch,
                                           String plannedOccurrenceId,
                                           String boundaryKind, String slot,
                                           int ordinal) {
        return "CBF." + CanonicalJson.sha256(topologyEpoch + "\n"
                + plannedOccurrenceId + "\n" + boundaryKind + "\n" + slot
                + "\n" + ordinal);
    }

}
