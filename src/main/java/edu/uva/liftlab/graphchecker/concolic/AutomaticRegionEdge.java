package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Evidence gate shared by graph discovery and SMT preparation.
 *
 * <p>A port map may be useful for locating another region without proving a
 * value relation.  Automatic composition is deliberately stricter: equality
 * requires an observed complete runtime value fingerprint, and shared state
 * requires a confirmed concrete write/read pair.  Static protocol contracts,
 * endpoint order, and domain-specific mapping names never satisfy this gate.</p>
 */
public final class AutomaticRegionEdge {
    static final int RUNTIME_EDGE_SCHEMA_VERSION = 2;
    static final String RUNTIME_EDGE_KIND =
            "RUNTIME_REGION_EDGE_EVIDENCE";
    static final String COMPLETE_VALUE_EQUALITY =
            "COMPLETE_VALUE_EQUALITY_V1";
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
                || !RUNTIME_EDGE_KIND.equals(string(edge, "kind"))
                || string(edge, "edgeId").isEmpty()
                || string(edge, "fromRegion").isEmpty()
                || string(edge, "toRegion").isEmpty()
                || string(edge, "transportKind").isEmpty()
                || string(edge, "fromPort").isEmpty()
                || string(edge, "toPort").isEmpty()) {
            return "";
        }
        String relation = "CONFIRMED_READ_FROM".equals(string(edge, "state"))
                ? "READ_FROM"
                : "CONFIRMED_RUNTIME_VALUE_EQUALITY".equals(
                string(edge, "state")) ? "EQUALITY" : "";
        JsonElement bindings = edge.get("bindings");
        if (relation.isEmpty() || bindings == null || !bindings.isJsonArray()
                || bindings.getAsJsonArray().size() == 0) {
            return "";
        }
        for (JsonElement element : bindings.getAsJsonArray()) {
            if (!element.isJsonObject()
                    || ("READ_FROM".equals(relation)
                    ? !trustedReadFromEvidence(element.getAsJsonObject())
                    : !trustedRuntimeValueEqualityEvidence(
                    element.getAsJsonObject()))) {
                return "";
            }
        }
        return relation;
    }

    /**
     * Validates one runtime summary binding before it is admitted downstream.
     * Direct field assignments retain their original exact event contract;
     * container mutations additionally require a completed mutator call and
     * the same process-local container identity on both field reads.
     */
    public static boolean trustedRuntimeReadFromBinding(JsonObject binding) {
        return trustedReadFromEvidence(binding);
    }

    /**
     * Validates a value-equality summary edge independently of READ_FROM.
     *
     * <p>RPC and other serialization transports normally allocate a new
     * receiver-side object, so process-local object identity is neither
     * available nor required. Automatic composition instead requires the two
     * exact region instances and canonical ports, a complete runtime
     * fingerprint on both endpoints, and their concrete trace order.</p>
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
                || !COMPLETE_VALUE_EQUALITY.equals(string(evidence,
                "evidenceKind"))
                || string(evidence, "fromRegionInstance").isEmpty()
                || string(evidence, "toRegionInstance").isEmpty()
                || string(evidence, "valueFingerprint").isEmpty()) {
            return false;
        }
        return ordered(evidence);
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
            return longInteger(evidence, "receiverObjectId", 0L) != 0L
                    && ordered(evidence);
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
                && longInteger(evidence, "readerEventSeq", -1L) > completion
                && fieldReceiver != 0L
                && longInteger(evidence, "mutationInvocationId", 0L) > 0L
                && writerContainer != 0L
                && writerContainer == readerContainer;
    }

    private static boolean ordered(JsonObject evidence) {
        long writer = longInteger(evidence, "writerEventSeq", -1L);
        return writer >= 0L
                && longInteger(evidence, "readerEventSeq", -1L) > writer;
    }
}
