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
 * value relation. Protocol equality is admitted only for the exact dynamic
 * endpoint occurrences named by a trusted configured RPC mapping and an
 * observed caller/send/receive lineage. Shared state requires a confirmed
 * concrete write/read pair as evidence that the channel exists; its observed
 * event sequence is not an SMT schedule.</p>
 */
public final class AutomaticRegionEdge {
    static final int RUNTIME_EDGE_SCHEMA_VERSION = 3;
    static final String RUNTIME_EDGE_KIND =
            "RUNTIME_FIELD_FLOW";
    static final String RUNTIME_PROTOCOL_EDGE_KIND =
            "RUNTIME_PROTOCOL_FLOW";
    static final String CONFIGURED_PROTOCOL_AUTHORITY =
            "TRUSTED_CONFIGURED_RPC_MAPPING_V1";
    static final String CONFIGURED_PROTOCOL_EQUALITY =
            CONFIGURED_PROTOCOL_AUTHORITY;
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
        String relation = RUNTIME_EDGE_KIND.equals(edgeKind)
                && "CONFIRMED_RUNTIME_IDENTITY".equals(state)
                ? "READ_FROM"
                : RUNTIME_PROTOCOL_EDGE_KIND.equals(edgeKind)
                && "CONFIRMED_TRUSTED_CONFIGURED_RPC".equals(state)
                ? "EQUALITY" : "";
        if (relation.isEmpty()) return "";
        return ("READ_FROM".equals(relation)
                ? trustedReadFromEvidence(edge)
                : trustedRuntimeValueEqualityEvidence(edge))
                ? relation : "";
    }

    /**
     * Validates one runtime summary binding before it is admitted downstream.
     * Direct field assignments require exact channel endpoints. Container
     * mutations additionally require a completed mutator call and concrete
     * container endpoints. Cross-lane trace order and value equality are not
     * admission constraints; the bounded merge chooses the version.
     */
    public static boolean trustedRuntimeReadFromBinding(JsonObject binding) {
        return trustedReadFromEvidence(binding);
    }

    /**
     * Validates a value-equality summary edge independently of READ_FROM.
     *
     * <p>RPC and other serialization transports normally allocate a new
     * receiver-side object. The configured port mapping is the value-equality
     * authority.</p>
     */
    public static boolean trustedRuntimeValueEqualityBinding(
            JsonObject binding) {
        return trustedRuntimeValueEqualityEvidence(binding)
                && !string(binding, "fromOutputPort").isEmpty()
                && !string(binding, "toInputPort").isEmpty();
    }

    /**
     * Validates a planner-produced equality witness before the scheduler
     * enriches it with relation and canonical-port metadata.
     */
    public static boolean trustedRuntimeValueEqualityEvidence(
            JsonObject evidence) {
        if (evidence == null
                || integer(evidence, "schemaVersion", -1) != 3
                || !CONFIGURED_PROTOCOL_EQUALITY.equals(string(evidence,
                "evidenceKind"))
                || string(evidence, "fromRegionInstance").isEmpty()
                || string(evidence, "toRegionInstance").isEmpty()
                || string(evidence, "fromOutputPort").isEmpty()
                || string(evidence, "toInputPort").isEmpty()
                || string(evidence, "mappingId").isEmpty()
                || !CONFIGURED_PROTOCOL_AUTHORITY.equals(firstNonBlank(
                string(evidence, "correlationAuthority"),
                string(evidence, "authority")))) {
            return false;
        }
        long caller = longInteger(evidence, "callerSiteEventSeq", -1L);
        long send = longInteger(evidence, "sendEventSeq", -1L);
        long receive = longInteger(evidence, "receiveEventSeq", -1L);
        return caller >= 0L && caller < send && send < receive;
    }

    /** Runtime evidence admitted for recursive summary composition. */
    public static boolean trustedRuntimeCompositionBinding(
            JsonObject binding) {
        return trustedRuntimeReadFromBinding(binding)
                || trustedRuntimeValueEqualityBinding(binding);
    }

    public static boolean trustedReadFromEvidence(JsonObject evidence) {
        if (evidence == null) return false;
        String kind = string(evidence, "evidenceKind");
        if (FIELD_ASSIGNMENT_READ_FROM.equals(kind)) {
            return integer(evidence, "schemaVersion", -1) == 3
                    && "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1".equals(
                    string(evidence, "correlationAuthority"))
                    && !string(evidence, "fromRegionInstance").isEmpty()
                    && !string(evidence, "toRegionInstance").isEmpty()
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
        return !bool(evidence, "programOrderRequired", false)
                || writer < reader;
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
