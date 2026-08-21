package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;

/**
 * Evidence gate shared by graph discovery and SMT preparation.
 *
 * <p>A port map may be useful for locating another region without proving a
 * value relation. Protocol equality is admitted only where the VM itself
 * handed the sender's expression to the receiver; a correlated exchange
 * locates the boundary and never proves what crossed it. Shared state
 * requires a confirmed concrete write/read pair as evidence that the channel
 * exists; its observed event sequence is not an SMT schedule.</p>
 */
public final class AutomaticRegionEdge {
    static final int RUNTIME_EDGE_SCHEMA_VERSION = 3;
    static final String RUNTIME_EDGE_KIND =
            "RUNTIME_FIELD_FLOW";
    static final String RUNTIME_PROTOCOL_EDGE_KIND =
            "RUNTIME_PROTOCOL_FLOW";
    /**
     * What application tracing proves about an RPC boundary on its own: the
     * two endpoints named one exchange and one delivery of it was observed.
     * That is scope and identity, never a value relation, so it admits
     * nothing here - it only marks an edge as a candidate whose expression
     * the session may still attest.
     */
    public static final String TRACED_EXCHANGE_AUTHORITY =
            "TRACED_RPC_EXCHANGE_CORRELATION_V1";
    /**
     * Scheduling-only proof that a concrete reference field carried a
     * configured VM-handoff component into a later occurrence.
     *
     * <p>The reference itself remains concrete.  The exact runtime field
     * write/read pair only keeps the two occurrences in the causal closure;
     * the VM {@code VALUE_HANDOFF} edge remains the sole authority for the
     * component value.</p>
     */
    public static final String TRANSPORTED_VALUE_FRONTIER_FIELD =
            "transportedValueFrontierAuthority";
    public static final String TRANSPORTED_VALUE_FRONTIER_AUTHORITY =
            "EXACT_RUNTIME_REFERENCE_CARRIER_OF_VM_COMPONENT_V1";
    /**
     * A read-from relation the session itself recorded.  The version store
     * says which write the read resolved to, and the event ledger carries the
     * matching {@code FIELD_READ_FROM} edge in the one order domain.  That is
     * strictly more than a confirmed concrete write/read pair proves - which
     * only shows that a channel exists - so it is admitted as its own state
     * rather than by relaxing the existing one.
     */
    static final String CONFIRMED_VM_RECORDED_READ_FROM =
            "CONFIRMED_VM_RECORDED_READ_FROM";
    static final String FIELD_ASSIGNMENT_READ_FROM =
            "FIELD_ASSIGNMENT_READ_FROM_V1";
    static final String CONTAINER_MUTATION_READ_FROM =
            "CONTAINER_MUTATION_READ_FROM_V1";

    private AutomaticRegionEdge() {
    }

    public static boolean composable(JsonObject edge) {
        return !relation(edge).isEmpty();
    }

    static String relation(JsonObject edge) {
        if (edge == null
                || integer(edge, "schemaVersion", -1)
                != RUNTIME_EDGE_SCHEMA_VERSION
                || string(edge, "edgeId").isEmpty()
                || string(edge, "fromRegion").isEmpty()
                || string(edge, "toRegion").isEmpty()
                || string(edge, "transportKind").isEmpty()
                || string(edge, "fromOutputPort").isEmpty()
                || string(edge, "toInputPort").isEmpty()
                || edge.has("bindings")) {
            return "";
        }
        String edgeKind = string(edge, "kind");
        String state = string(edge, "state");
        if (RUNTIME_EDGE_KIND.equals(edgeKind)
                && "CONFIRMED_RUNTIME_IDENTITY".equals(state)) {
            return trustedReadFromEvidence(edge) ? "READ_FROM" : "";
        }
        if (RUNTIME_EDGE_KIND.equals(edgeKind)
                && CONFIRMED_VM_RECORDED_READ_FROM.equals(state)) {
            return trustedVmRecordedReadFromEvidence(edge)
                    ? "READ_FROM" : "";
        }
        return "";
    }

    /**
     * Validates one VM-recorded read-from relation.
     *
     * <p>Admission needs both halves of the session's own answer and they
     * must agree. The version store half is an <em>exact</em> resolution: it
     * names the field version the read took, with the rule it was decided by.
     * The ledger half is the order domain's own {@code FIELD_READ_FROM} edge
     * from that version to that read - which the VM draws only when the
     * provenance was proved, and never for a guarded read, because an
     * undecided choice has no causal edge. The plan half is the endpoint
     * attribution the VM cannot know.</p>
     *
     * <p>A location whose writer set is already incomplete is refused here.
     * Losing writers is what turns "this read took that write" into "this
     * read took that write, unless an untracked one wrote it too", and an
     * equality is not the shape in which to state that doubt; such a read
     * stays a guarded choice.</p>
     */
    public static boolean trustedVmRecordedReadFromEvidence(
            JsonObject evidence) {
        return evidence != null
                && integer(evidence, "schemaVersion", -1) == 3
                && RecordedReadFrom.AUTHORITY.equals(string(evidence,
                "evidenceKind"))
                && RecordedReadFrom.AUTHORITY.equals(firstNonBlank(
                string(evidence, "correlationAuthority"),
                string(evidence, "authority")))
                && !string(evidence, "fromOccurrenceId").isEmpty()
                && !string(evidence, "toOccurrenceId").isEmpty()
                && !string(evidence, "fromOutputPort").isEmpty()
                && !string(evidence, "toInputPort").isEmpty()
                && !string(evidence, "locationKey").isEmpty()
                && !string(evidence, "readFromField").isEmpty()
                && !string(evidence, "writerRegionId").isEmpty()
                && !string(evidence, "resolutionReason").isEmpty()
                && longInteger(evidence, "fieldVersionId", 0L) > 0L
                && longInteger(evidence, "readEventId", 0L) > 0L
                && longInteger(evidence, "fieldVersionId", 0L)
                != longInteger(evidence, "readEventId", 0L)
                && "FIELD_READ_FROM".equals(string(evidence,
                "orderEdgeKind"))
                && bool(evidence, "ledgerJustified", false)
                && bool(evidence, "writerSetComplete", false)
                && RecordedReadFrom.PROVENANCE_EXACT.equals(string(evidence,
                "readFromProvenance"));
    }

    /**
     * Validates one runtime summary binding before it is admitted downstream.
     * Direct field assignments require exact channel endpoints. Container
     * mutations additionally require a completed mutator call and concrete
     * container endpoints. A recorded writer must precede the read it claims
     * to supply even across lanes: event sequence is the trace's global
     * observation order, while a later replay is free to publish a different
     * ordered edge into the growing causal supergraph.
     */
    public static boolean trustedRuntimeReadFromBinding(JsonObject binding) {
        return trustedReadFromEvidence(binding);
    }

    /**
     * Whether one edge is a candidate delivery the trace correlated.
     *
     * <p>It says a message crossed this declared boundary between these two
     * activations. Dynamic exchange identity and event order are trace
     * provenance, not admission constraints: requiring them would reject a
     * valid best-effort replay merely because the transport minted different
     * ids or interleaved differently. The row stays scheduling evidence; only
     * a case-local VM {@code VALUE_HANDOFF} edge supplies the value.</p>
     */
    public static boolean tracedExchangeCandidate(JsonObject edge) {
        if (edge == null
                || integer(edge, "schemaVersion", -1) != 3
                || !RUNTIME_PROTOCOL_EDGE_KIND.equals(string(edge, "kind"))
                || string(edge, "fromOccurrenceId").isEmpty()
                || string(edge, "toOccurrenceId").isEmpty()
                || string(edge, "fromOutputPort").isEmpty()
                || string(edge, "toInputPort").isEmpty()
                || !TRACED_EXCHANGE_AUTHORITY.equals(firstNonBlank(
                string(edge, "correlationAuthority"),
                string(edge, "authority")))) {
            return false;
        }
        return true;
    }

    /** Runtime evidence admitted for recursive summary composition. */
    public static boolean trustedRuntimeCompositionBinding(
            JsonObject binding) {
        return trustedRuntimeReadFromBinding(binding);
    }

    /**
     * Runtime evidence a producer may be <em>scheduled</em> on.
     *
     * <p>Deliberately a wider door than {@link
     * #trustedRuntimeCompositionBinding}, and deliberately a different one.
     * Composition asks what the model may state; scheduling asks what has to
     * run for the session to be able to answer that at all.  A recorded
     * delivery answers the second question and not the first: it names the
     * declared boundary and the two region occurrences, so it says which
     * fragment has to execute before the receiving one can be given anything
     * - but it says nothing about the value, so it is still
     * refused by {@link #relation} and by {@link #composable}.</p>
     *
     * <p>The chicken-and-egg this opens is real: the VM handoff edge that
     * makes the crossing a value relation is produced by running the slice,
     * and the slice cannot be scheduled without a producer.  Admitting the
     * candidate here breaks that cycle in the only direction that stays
     * honest - more execution, not more claim.  A consumer that needs a value
     * relation must keep asking {@link #trustedRuntimeCompositionBinding}.</p>
     */
    public static boolean schedulableProducerBinding(JsonObject binding) {
        return summaryTraversalBinding(binding);
    }

    /**
     * Evidence that may select the two recorded interaction summaries.
     *
     * <p>This is deliberately not value authority.  Exact shared-container
     * identity and a recorded RPC delivery both locate the producer and
     * consumer occurrences; the selected container expression or the VM
     * {@code VALUE_HANDOFF} edge supplies the value.  Java topology never
     * manufactures an equality.</p>
     */
    public static boolean summaryTraversalBinding(JsonObject binding) {
        return trustedRuntimeCompositionBinding(binding)
                || tracedExchangeCandidate(binding);
    }

    /**
     * Evidence that may recursively enter the composed SMT summary graph.
     *
     * <p>Scheduling deliberately keeps the wider {@link
     * #summaryTraversalBinding} gate: a concrete/candidate shared-state edge
     * can still identify work worth replaying.  Composition is narrower.  A
     * shared-state edge may demand/select a producer only after the VM has
     * classified it as exact or guarded; a traced RPC delivery may still
     * locate the two summaries whose case-local VM handoff supplies the
     * value.</p>
     */
    static boolean composerTraversalBinding(JsonObject binding) {
        return selectedReadFromCompositionBinding(binding)
                || tracedExchangeCandidate(binding);
    }

    /** One exact/guarded VM-selected shared-state edge. */
    static boolean selectedReadFromCompositionBinding(
            JsonObject binding) {
        if (!trustedRuntimeCompositionBinding(binding)) return false;
        String provenance = string(binding,
                RecordedReadFrom.EDGE_PROVENANCE);
        return RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                || RecordedReadFrom.PROVENANCE_GUARDED.equals(provenance);
    }

    /**
     * A concrete/candidate/excluded read-from row retained for replay or
     * audit, but not selected by the VM for SMT composition.
     */
    static boolean unselectedReadFromBinding(JsonObject binding) {
        String kind = string(binding, "evidenceKind");
        if (!FIELD_ASSIGNMENT_READ_FROM.equals(kind)
                && !CONTAINER_MUTATION_READ_FROM.equals(kind)) {
            return false;
        }
        String provenance = string(binding,
                RecordedReadFrom.EDGE_PROVENANCE);
        return !RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                && !RecordedReadFrom.PROVENANCE_GUARDED.equals(provenance);
    }

    public static boolean trustedReadFromEvidence(JsonObject evidence) {
        if (evidence == null) return false;
        String kind = string(evidence, "evidenceKind");
        if (FIELD_ASSIGNMENT_READ_FROM.equals(kind)) {
            return integer(evidence, "schemaVersion", -1) == 3
                    && "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1".equals(
                    string(evidence, "correlationAuthority"))
                    && !string(evidence, "fromOccurrenceId").isEmpty()
                    && !string(evidence, "toOccurrenceId").isEmpty()
                    && !string(evidence, "fromOutputPort").isEmpty()
                    && !string(evidence, "toInputPort").isEmpty()
                    && longInteger(evidence, "receiverObjectId", 0L) != 0L
                    && observedChannelOrder(evidence,
                            longInteger(evidence, "writerEventSeq", -1L));
        }
        if (!CONTAINER_MUTATION_READ_FROM.equals(kind)
                || string(evidence, "mutatorDeclaredCallee").isEmpty()) {
            return false;
        }
        long fieldRead = longInteger(evidence, "writerFieldReadSeq", -1L);
        long enter = longInteger(evidence, "mutatorEnterSeq", -1L);
        long completion = longInteger(evidence,
                "mutationCompletionSeq", -1L);
        long writer = longInteger(evidence, "writerEventSeq", -1L);
        long fieldReceiver = longInteger(evidence,
                "receiverObjectId", 0L);
        long writerContainer = longInteger(evidence, "valueObjectId", 0L);
        long readerContainer = longInteger(evidence,
                "readerValueObjectId", 0L);
        return fieldRead >= 0L && enter > fieldRead
                && completion > enter && writer == completion
                && fieldReceiver != 0L
                && longInteger(evidence, "mutationInvocationId", 0L) > 0L
                && writerContainer != 0L
                && readerContainer != 0L
                && observedChannelOrder(evidence, completion);
    }

    private static boolean observedChannelOrder(JsonObject evidence,
                                                long writer) {
        long reader = longInteger(evidence, "readerEventSeq", -1L);
        if (writer < 0L || reader < 0L
                || !trustedProgramOrderMetadata(evidence)) {
            return false;
        }
        return writer < reader;
    }

    private static boolean trustedProgramOrderMetadata(JsonObject evidence) {
        if (!evidence.has("programOrderRequired")) return false;
        String writerLane = string(evidence, "writerLaneId");
        String readerLane = string(evidence, "readerLaneId");
        if (writerLane.isEmpty() || readerLane.isEmpty()) return false;
        boolean required = bool(evidence, "programOrderRequired", false);
        return required == writerLane.equals(readerLane);
    }

}
