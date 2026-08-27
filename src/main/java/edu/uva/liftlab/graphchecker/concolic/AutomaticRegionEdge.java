package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;

/** Evidence gate shared by graph discovery and SMT preparation. */
public final class AutomaticRegionEdge {
    static final int RUNTIME_EDGE_SCHEMA_VERSION = 3;
    static final String RUNTIME_EDGE_KIND =
            "RUNTIME_FIELD_FLOW";
    static final String RUNTIME_PROTOCOL_EDGE_KIND =
            "RUNTIME_PROTOCOL_FLOW";
    /**
     * What application tracing proves about an RPC boundary on its own: the
     * two endpoints named one exchange and one delivery of it was observed.
     */
    public static final String TRACED_EXCHANGE_AUTHORITY =
            "TRACED_RPC_EXCHANGE_CORRELATION_V1";
    /**
     * Scheduling-only proof that a concrete reference field carried a
     * configured VM-handoff component into a later occurrence.
     */
    public static final String TRANSPORTED_VALUE_FRONTIER_FIELD =
            "transportedValueFrontierAuthority";
    public static final String TRANSPORTED_VALUE_FRONTIER_AUTHORITY =
            "EXACT_RUNTIME_REFERENCE_CARRIER_OF_VM_COMPONENT_V1";
    /** A read-from relation the session itself recorded. */
    static final String CONFIRMED_VM_RECORDED_READ_FROM =
            "CONFIRMED_VM_RECORDED_READ_FROM";
    static final String FIELD_ASSIGNMENT_READ_FROM =
            "FIELD_ASSIGNMENT_READ_FROM_V1";
    static final String CONTAINER_MUTATION_READ_FROM =
            "CONTAINER_MUTATION_READ_FROM_V1";

    private AutomaticRegionEdge() {
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

    /** Validates one VM-recorded read-from relation. */
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
     */
    public static boolean trustedRuntimeReadFromBinding(JsonObject binding) {
        return trustedReadFromEvidence(binding);
    }

    /** Whether one edge is a candidate delivery the trace correlated. */
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

    /** Runtime evidence a producer may be <em>scheduled</em> on. */
    public static boolean schedulableProducerBinding(JsonObject binding) {
        return summaryTraversalBinding(binding);
    }

    /** Evidence that may select the two recorded interaction summaries. */
    public static boolean summaryTraversalBinding(JsonObject binding) {
        return trustedRuntimeCompositionBinding(binding)
                || tracedExchangeCandidate(binding);
    }

    /** Evidence that may recursively enter the composed SMT summary graph. */
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
