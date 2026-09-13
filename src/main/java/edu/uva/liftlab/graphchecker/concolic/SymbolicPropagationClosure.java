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
    public static final String ITE_TYPE = "CaseMergeExpression";
    /** A physical replay refines a local case only when its propagated
     *  evidence cannot be folded into the case's replay-independent value. */
    public static final String OBSERVATION_SELECTOR =
            "replayObservationSelector";
    public static final String OBSERVATION_SCOPE =
            "replayObservationScope";
    public static final String DEPENDENCY_KIND =
            "CONSUMER_BOUNDARY_CASE_DEPENDENCY";
    /** Stable producer-case join carried by a ReadFrom candidate. */
    public static final String WRITER_CASE_FAMILY =
            "writerCaseFamilyKey";
    public static final String WRITER_CASE_OWNER = "writerCaseOwner";
    public static final String WRITER_CASE_SELECTOR = "writerCaseSelector";
    public static final String WRITER_CASE_REGION_ID = "writerCaseRegionId";
    public static final String WRITER_CASE_OCCURRENCE_ID =
            "writerCaseOccurrenceId";
    /**
     * The physical occurrence whose region entry published an INITIAL
     * candidate's snapshot.  An INITIAL arm is owned by no region case, so
     * this is the only tie between the snapshot and the activation that took
     * it -- which is what decides whether the snapshot still names a value
     * once a fault marker idles that activation.
     *
     * <p>It is published once per INITIAL owner in {@link
     * Result#initialSnapshotHosts()} rather than stamped on every candidate:
     * a candidate travels inside the propagated expressions, whose canonical
     * rendering is content-addressed, so a field added there renames every
     * witness minted from a node that contains one.</p>
     */
    public static final String INITIAL_HOST_KIND = "INITIAL_SNAPSHOT_HOST";
    public static final String INITIAL_HOST_OWNER = "initialSourceCaseOwner";
    public static final String INITIAL_HOST_REGION_ID =
            "initialHostRegionId";
    public static final String INITIAL_HOST_OCCURRENCE_ID =
            "initialHostOccurrenceId";
    /**
     * Whether this row states the host activation or only records that it
     * could not be stated.
     *
     * <p>An INITIAL arm is owned by no region case, so the host row is the
     * only tie between the snapshot and the activation that took it.  When
     * the writer version carries no region or occurrence, the tie does not
     * exist -- and an absent row and an unknown host used to look alike, both
     * being nothing at all.  A row with this field {@code false} is the
     * difference: it says the question was asked and has no answer, which is
     * a fact the composer can refuse on, rather than a silence it reads as
     * "hosted".</p>
     */
    public static final String INITIAL_HOST_STATED = "initialHostStated";
    /** One INITIAL arm whose host activation could not be stated. */
    public static final String INITIAL_HOST_UNKNOWN =
            "INITIAL_SNAPSHOT_HOST_UNKNOWN";
    /**
     * Exact selected-region stack captured when a physical writer region was
     * entered. Runtime entries carry task/region/occurrence addresses; this
     * pass resolves them to replay-independent local cases.
     */
    public static final String WRITER_ACTIVATION_CLOSURE =
            "writerActivationClosure";
    public static final String WRITER_ACTIVATION_CLOSURE_AUTHORITY =
            "ACTIVE_REGION_STACK_AT_WRITER_ENTRY_V1";
    /** Stable local cases which physically enclosed one writer event. */
    public static final String WRITER_CASE_CLOSURE = "writerCaseClosure";
    /** Replay-independent identity of one arm in a guarded read. */
    public static final String READ_CANDIDATE_IDENTITY =
            "readCandidateIdentity";
    /**
     * Stable identity of one recorded read choice.  VM event ids are local to
     * a replay, so path queries must never join a guarded expression to a cut
     * by the bare numeric id.
     */
    /**
     * Cases one shared read may be consumed by before the closure stops
     * naming it.  A read every case in a wave consumes is a sign the
     * boundary address is wrong, not a value worth a family.
     */
    private static final int MAX_BOUNDARY_CONSUMERS = 32;

    public static final String READ_CHOICE_IDENTITY = "readChoiceIdentity";
    public static final String READ_CHOICE_OWNER = "readChoiceOwner";
    public static final String READ_CHOICE_OCCURRENCE_ID =
            "readChoiceOccurrenceId";
    /** Dependency rows with this policy are enabled by an RF arm. */
    public static final String READ_FROM_DEPENDENCY_POLICY =
            "READ_FROM_ARM_IMPLIES_CASE";
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
    /**
     * How many wires a resolved boundary sits behind the fatal cone.
     *
     * <p>Zero is a boundary the target reads directly. One is a boundary that
     * arrived inside another boundary's payload -- the client's cached key
     * inside what the client then sent on -- and so on, because NN to client
     * to DN is one chain and the walk follows it.</p>
     */
    public static final String BOUNDARY_DEPTH = "boundaryDepth";

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
