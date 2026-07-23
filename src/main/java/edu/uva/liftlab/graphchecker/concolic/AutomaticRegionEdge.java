package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

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
    static final String CONTAINER_MUTATION_READ_FROM_AUTHORITY =
            "RUNTIME_EXACT_FIELD_OWNER_AND_CONTAINER_RECEIVER_IDENTITY_"
                    + "COMPLETED_MUTATION_BEFORE_READ_V1";
    static final String CONTAINER_MUTATOR_CONTRACT_AUTHORITY =
            "DECLARED_CALLEE_MUTATOR_METHOD_NAME_ALLOWLIST_V1";
    static final String TRACE_ORDER_AUTHORITY =
            "GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1";
    static final String VALUE_EQUALITY_ORDER_AUTHORITY =
            "GLOBAL_TRACE_ENDPOINT_SEQUENCE";

    private AutomaticRegionEdge() {
    }

    public static boolean composable(JsonObject edge) {
        if (edge == null || !bool(edge, "composable", false)
                || !bool(edge, "eligibleForAutomaticDerivation", false)
                || !bool(edge, "eligibleForAutomaticSmt", false)) {
            return false;
        }
        String relation = string(edge, "validatedRelation");
        if ("READ_FROM".equals(relation)) {
            if (!"CONFIRMED_READ_FROM".equals(string(edge, "status"))
                    || integer(edge, "confirmedReadFromPairCount", 0) <= 0) {
                return false;
            }
            JsonElement bindings = edge.get("validatedBindings");
            if (bindings == null || !bindings.isJsonArray()
                    || bindings.getAsJsonArray().size() == 0) {
                return false;
            }
            for (JsonElement element : bindings.getAsJsonArray()) {
                if (!element.isJsonObject()
                        || !trustedReadFromEvidence(
                        element.getAsJsonObject())) {
                    return false;
                }
            }
            return true;
        }
        if ("EQUALITY".equals(relation)) {
            String authority = string(edge, "valueEqualityAuthority");
            JsonElement bindings = edge.get("validatedBindings");
            if (bindings == null || !bindings.isJsonArray()
                    || bindings.getAsJsonArray().size() == 0) {
                return false;
            }
            for (JsonElement element : bindings.getAsJsonArray()) {
                if (!element.isJsonObject()
                        || !trustedRuntimeValueEqualityEvidence(
                        element.getAsJsonObject())) {
                    return false;
                }
            }
            return bool(edge, "valueEqualityObserved", false)
                    && integer(edge, "confirmedValueEqualityPairCount", 0) > 0
                    && "RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(authority);
        }
        return false;
    }

    /**
     * Validates one runtime summary binding before it is admitted downstream.
     * Direct field assignments retain their original exact event contract;
     * container mutations additionally require a completed mutator call and
     * the same process-local container identity on both field reads.
     */
    public static boolean trustedRuntimeReadFromBinding(JsonObject binding) {
        return binding != null
                && "RUNTIME_CONFIRMED_READ_FROM".equals(string(binding,
                "selectionAuthority"))
                && trustedReadFromEvidence(binding);
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
        if (binding == null
                || !"RUNTIME_CONFIRMED_VALUE_EQUALITY".equals(string(
                binding, "selectionAuthority"))
                || !"EQUALITY".equals(string(binding, "relationKind"))
                || string(binding, "fromRegionInstance").isEmpty()
                || string(binding, "toRegionInstance").isEmpty()
                || string(binding, "fromOutputPort").isEmpty()
                || string(binding, "toInputPort").isEmpty()
                || !bool(binding, "valueEqualityObserved", false)
                || !"RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(string(
                binding, "valueEqualityAuthority"))
                || string(binding, "valueFingerprint").isEmpty()
                || !VALUE_EQUALITY_ORDER_AUTHORITY.equals(string(binding,
                "endpointOrderAuthority"))
                || !bool(binding, "orderConfirmed", false)) {
            return false;
        }
        long writer = firstLong(binding, "writerEventSeq", "writeSeq",
                "fromEndpointSeq", "fromEventSeq");
        long reader = firstLong(binding, "readerEventSeq", "readSeq",
                "toEndpointSeq", "toEventSeq");
        return writer >= 0L && reader > writer;
    }

    /**
     * Validates a planner-produced equality witness before the scheduler
     * enriches it with relation and canonical-port metadata.
     */
    public static boolean trustedRuntimeValueEqualityEvidence(
            JsonObject evidence) {
        if (evidence == null
                || string(evidence, "fromRegionInstance").isEmpty()
                || string(evidence, "toRegionInstance").isEmpty()
                || !bool(evidence, "valueEqualityObserved", false)
                || !"RUNTIME_COMPLETE_VALUE_FINGERPRINT".equals(string(
                evidence, "valueEqualityAuthority"))
                || string(evidence, "valueFingerprint").isEmpty()
                || !VALUE_EQUALITY_ORDER_AUTHORITY.equals(string(evidence,
                "endpointOrderAuthority"))
                || !bool(evidence, "orderConfirmed", false)) {
            return false;
        }
        long writer = firstLong(evidence, "fromEndpointSeq",
                "writerEventSeq", "writeSeq", "fromEventSeq");
        long reader = firstLong(evidence, "toEndpointSeq",
                "readerEventSeq", "readSeq", "toEventSeq");
        return writer >= 0L && reader > writer;
    }

    /** Runtime evidence admitted for recursive summary composition. */
    public static boolean trustedRuntimeCompositionBinding(
            JsonObject binding) {
        return trustedRuntimeReadFromBinding(binding)
                || trustedRuntimeValueEqualityBinding(binding);
    }

    public static boolean trustedReadFromEvidence(JsonObject evidence) {
        if (evidence == null) return false;
        String kind = string(evidence, "writeEvidenceKind");
        if ("FIELD_ASSIGNMENT".equals(kind)) {
            long writer = firstLong(evidence, "writerEventSeq", "writeSeq");
            long reader = firstLong(evidence, "readerEventSeq", "readSeq");
            return "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1".equals(string(
                    evidence, "writeEvidenceAuthority"))
                    && TRACE_ORDER_AUTHORITY.equals(string(evidence,
                    "orderAuthority"))
                    && bool(evidence, "orderConfirmed", false)
                    && bool(evidence, "fieldReceiverIdentityConfirmed", false)
                    && longInteger(evidence, "receiverObjectId", 0L) != 0L
                    && writer >= 0L && reader > writer;
        }
        if (!"FIELD_CONTAINER_MUTATION".equals(kind)
                || !CONTAINER_MUTATION_READ_FROM_AUTHORITY.equals(string(
                evidence, "writeEvidenceAuthority"))
                || !CONTAINER_MUTATOR_CONTRACT_AUTHORITY.equals(string(
                evidence, "mutationContractAuthority"))
                || !TRACE_ORDER_AUTHORITY.equals(string(evidence,
                "orderAuthority"))
                || !bool(evidence, "orderConfirmed", false)
                || !bool(evidence, "containerIdentityConfirmed", false)
                || !bool(evidence, "fieldReceiverIdentityConfirmed", false)
                || string(evidence, "mutatorDeclaredCallee").isEmpty()) {
            return false;
        }
        long fieldRead = longInteger(evidence, "writerFieldReadSeq", -1L);
        long enter = longInteger(evidence, "mutatorEnterSeq", -1L);
        long completion = longInteger(evidence,
                "mutationCompletionSeq", -1L);
        long writer = firstLong(evidence, "writerEventSeq", "writeSeq");
        long reader = firstLong(evidence, "readerEventSeq", "readSeq");
        long fieldReceiver = longInteger(evidence,
                "receiverObjectId", 0L);
        long writerContainer = longInteger(evidence, "valueObjectId", 0L);
        long readerContainer = longInteger(evidence,
                "readerValueObjectId", 0L);
        return fieldRead >= 0L && enter > fieldRead
                && completion > enter && writer == completion
                && reader > completion && fieldReceiver != 0L
                && longInteger(evidence, "mutationInvocationId", 0L) > 0L
                && writerContainer != 0L
                && writerContainer == readerContainer;
    }

    private static String string(JsonObject object, String name) {
        if (object == null) return "";
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String name,
                                boolean fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String name, int fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String name,
                                    long fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long firstLong(JsonObject object, String... names) {
        for (String name : names) {
            if (object != null && object.has(name)) {
                return longInteger(object, name, -1L);
            }
        }
        return -1L;
    }

}
