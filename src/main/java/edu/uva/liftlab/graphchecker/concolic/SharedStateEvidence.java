package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.textString;

/**
 * Named vocabulary for the VM's recorded shared-state evidence.
 */
public final class SharedStateEvidence {

    /** Schema of the VM envelopes and gap rows this vocabulary reads. */
    public static final int SCHEMA_VERSION = 1;

    /**
     * Schema of the admitted record wrappers this vocabulary produces.
     */
    public static final int RECORD_SCHEMA_VERSION = 2;


    /**
     * Envelope kind of one selected location's version store.
     */
    public static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    /** Expression node type of one guarded read-from choice. */
    public static final String GUARDED_READ_TYPE = "ReadFromExpression";
    /** Authority the VM stamps on a guarded read-from node. */
    public static final String GUARDED_READ_AUTHORITY =
            "VM_GUARDED_READ_FROM_V1";
    /**
     * Explicit form of the empty conjunction.
     */
    public static final String EMPTY_CONJUNCTION_KIND = "EMPTY_CONJUNCTION";
    public static final String EMPTY_CONJUNCTION_AUTHORITY =
            "VM_UNGUARDED_WRITE_V1";
    /** Node type emitted where the VM serializer bounded one expression. */
    public static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    /** Authority proving that a truncated node came from the VM serializer. */
    public static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";


    /** Kind of one admitted version-store record. */
    public static final String VERSIONS_RECORD_KIND =
            "VM_SHARED_FIELD_VERSIONS_V1";
    /** Authority stamped on admitted version records. */
    public static final String RECORD_AUTHORITY =
            "VM_SHARED_STATE_EVIDENCE_V1";
    /** Summary member carrying one execution's recorded shared state. */
    public static final String RECORDED_FIELD = "recordedSharedState";
    /** Kind of that member. */
    public static final String RECORDED_KIND = "RECORDED_SHARED_STATE";
    /** Gap family recorded for every refusal. */
    public static final String GAP_KIND = "SHARED_STATE_GAP";
    /** Authority stamped on a gap row. */
    public static final String GAP_AUTHORITY =
            "VM_SHARED_STATE_EVIDENCE_GAP_V1";


    public static final String STAGE_SELECT = "SELECT";
    public static final String STAGE_VERSIONS = "VERSIONS";
    public static final String STAGE_IDENTITY = "IDENTITY";


    public static final int OK = 0;

    // Declared VM carrier-selection refusals (sharedFieldVersions.hpp).
    // Their numeric values are mirrored here so Java reports the same reason.
    public static final int SELECT_NO_ACTIVE_CONTEXT = -1;
    public static final int SELECT_MISSING_METADATA = -2;
    public static final int SELECT_FIELD_NOT_FOUND = -3;
    public static final int SELECT_UNSUPPORTED_TARGET = -4;
    public static final int INVOCATION_FAILED = -1001;
    public static final int MALFORMED_ENVELOPE = -1002;
    /** The location was never selected, so it has no recorded evidence. */
    public static final int NOT_SELECTED = -1003;
    /** Addressing that names no single location. */
    public static final int MISSING_METADATA = -1004;
    /** The VM retained only a bounded suffix of the recorded reads. */
    public static final int READ_LOG_TRUNCATED = -1006;
    /** One expression root was serialized only up to the VM's safety bound. */
    public static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /** A map-state receiver has no complete runtime carrier identity. */
    public static final int MAP_STATE_IDENTITY_MISSING = -1010;
    /** One session-local map owner claims conflicting carrier identities. */
    public static final int MAP_STATE_IDENTITY_AMBIGUOUS = -1011;

    /** Exact coverage reason for a VM-bounded expression tree. */
    public static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    public static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";


    /** Stable bytecode site attached to one runtime-owned field read. */
    public static final String CONSUMER_SITE_ID = "consumerSiteId";
    /** Activation-local execution number of {@link #CONSUMER_SITE_ID}. */
    public static final String CONSUMER_SITE_OCCURRENCE =
            "consumerSiteOccurrence";
    /** Location kind of one selected map's whole immutable state. */
    public static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    /**
     * The reserved slot of a whole-state location.
     */
    public static final int MAP_STATE_SLOT = -3;

    private static final Set<String> LOCATION_KINDS = names("INSTANCE_FIELD",
            "STATIC_FIELD", "ARRAY_ELEMENT", LOCATION_KIND_MAP_STATE);
    /**
     * Kinds of published version a location may carry.
     *
     * <p>This is the VM's vocabulary, not ours: a whole-state version reads
     * as {@code STATE_<operation>} (SharedFieldVersions::version_label), and
     * the operations are the ones the container support publishes -
     * {@code PUT}, {@code REMOVE}, {@code REMOVE_IF}, {@code CLEAR},
     * {@code REMOVE_AT} and {@code CLEAR_VIEW} for a map, {@code ADD},
     * {@code REMOVE} and {@code CLEAR} for a set.  An operation missing here
     * is not a tolerated unknown: one unadmitted version fails the whole
     * envelope, so the location loses every version it published and each
     * read of it reaches the formula with no read-from arm.
     * {@code REMOVE_IF} represents an iterator removal controlled by a
     * recorded branch predicate.</p>
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "STATE", "STATE_PUT", "STATE_REMOVE", "STATE_REMOVE_IF",
            "STATE_CLEAR", "STATE_REMOVE_AT", "STATE_CLEAR_VIEW",
            "STATE_ADD");
    /** The version kind every location may publish, whatever its shape. */
    private static final String INITIAL_VERSION_KIND = "INITIAL";
    private SharedStateEvidence() {
    }



    public static String reason(int status) {
        switch (status) {
            case OK:
                return "";
            case SELECT_NO_ACTIVE_CONTEXT:
                return REASON_PREFIX + "NO_ACTIVE_CONTEXT";
            case SELECT_MISSING_METADATA:
                return REASON_PREFIX + "SELECT_MISSING_METADATA";
            case SELECT_FIELD_NOT_FOUND:
                return REASON_PREFIX + "FIELD_NOT_FOUND";
            case SELECT_UNSUPPORTED_TARGET:
                return REASON_PREFIX + "UNSUPPORTED_TARGET";
            case INVOCATION_FAILED:
                return REASON_PREFIX + "INVOCATION_FAILED";
            case MALFORMED_ENVELOPE:
                return REASON_PREFIX + "MALFORMED_ENVELOPE";
            case NOT_SELECTED:
                return REASON_PREFIX + "NOT_SELECTED";
            case MISSING_METADATA:
                return REASON_PREFIX + "MISSING_METADATA";
            case READ_LOG_TRUNCATED:
                return REASON_PREFIX + "READ_LOG_TRUNCATED";
            case EXPRESSION_SERIALIZATION_TRUNCATED:
                return VM_EXPRESSION_SERIALIZATION_TRUNCATED;
            case MAP_STATE_IDENTITY_MISSING:
                return REASON_PREFIX + "MAP_STATE_IDENTITY_MISSING";
            case MAP_STATE_IDENTITY_AMBIGUOUS:
                return REASON_PREFIX + "MAP_STATE_IDENTITY_AMBIGUOUS";
            default:
                return UNDECLARED_REASON;
        }
    }

    /** The explicit empty conjunction: a write that took no branch. */
    public static JsonObject emptyConjunction() {
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", EMPTY_CONJUNCTION_KIND);
        guard.addProperty("authority", EMPTY_CONJUNCTION_AUTHORITY);
        return guard;
    }

    /** Whether {@code guard} states that its writer took no branch. */
    public static boolean unguarded(JsonElement guard) {
        if (guard == null) return false;
        if (guard.isJsonNull()) return true;
        return guard.isJsonObject() && EMPTY_CONJUNCTION_KIND.equals(
                optionalString(guard.getAsJsonObject(), "kind"))
                && EMPTY_CONJUNCTION_AUTHORITY.equals(
                optionalString(guard.getAsJsonObject(), "authority"));
    }

    /**
     * Whether an expression tree recursively contains the VM's explicit
     */
    public static boolean containsVmSerializationTruncation(
            JsonElement expression) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(expression);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
            if (current != null && !current.isJsonNull()
                    && !current.isJsonPrimitive()
                    && !visited.add(current)) continue;
            if (current.isJsonArray()) {
                for (JsonElement child : current.getAsJsonArray()) {
                    if (child != null) pending.push(child);
                }
                continue;
            }
            if (!current.isJsonObject()) continue;
            JsonObject term = current.getAsJsonObject();
            if (TRUNCATED_EXPRESSION_TYPE.equals(textString(term, "_type"))
                    && VM_SERIALIZATION_TRUNCATION_AUTHORITY.equals(
                    optionalString(term, "expressionAuthority"))) {
                return true;
            }
            for (String field : term.keySet()) {
                JsonElement child = term.get(field);
                if (child != null) pending.push(child);
            }
        }
        return false;
    }

    /** Whether {@code fault} names exactly this serializer-bound refusal. */
    public static boolean expressionSerializationTruncationFault(
            String fault) {
        return fault != null
                && (VM_EXPRESSION_SERIALIZATION_TRUNCATED.equals(fault)
                || fault.startsWith(
                VM_EXPRESSION_SERIALIZATION_TRUNCATED + ":"));
    }

    /** Builds one named coverage gap. */
    public static JsonObject gap(String stage, int status, String locationKey,
                                 String detail) {
        if (status == OK) {
            throw new IllegalArgumentException(
                    "admitted shared-state evidence is not a gap");
        }
        JsonObject gap = new JsonObject();
        gap.addProperty("kind", GAP_KIND);
        gap.addProperty("schemaVersion", SCHEMA_VERSION);
        gap.addProperty("reason", reason(status));
        gap.addProperty("authority", GAP_AUTHORITY);
        gap.addProperty("stage", text(stage));
        gap.addProperty("statusCode", status);
        gap.addProperty("locationKey", text(locationKey));
        gap.addProperty("detail", text(detail));
        return gap;
    }

    /** Whether {@code row} is a gap this vocabulary produced. */
    public static boolean isGap(JsonObject row) {
        return JsonFields.isGapRow(row, GAP_KIND, GAP_AUTHORITY, OK);
    }


    /**
     * Names the location one version-store envelope describes, as the VM's
     */
    public static String locationKey(JsonObject envelope) {
        JsonObject location = object(envelope, "location");
        if (location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        if (!LOCATION_KINDS.contains(kind)) return "";
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (owner == 0L || !location.has("slot")) return "";
        int slot = optionalInteger(location, "slot", 0);
        if (LOCATION_KIND_MAP_STATE.equals(kind) && slot != MAP_STATE_SLOT) {
            return "";
        }
        return kind + "/" + owner + "#" + slot;
    }

    /** The declared kind of one location key, or "". */
    public static String locationKindOf(String locationKey) {
        if (locationKey == null) return "";
        int separator = locationKey.indexOf('/');
        if (separator <= 0) return "";
        String kind = locationKey.substring(0, separator);
        return LOCATION_KINDS.contains(kind) ? kind : "";
    }

    /** The VM session's symbolic owner encoded in a location key. */
    public static long locationOwnerOf(String locationKey) {
        if (locationKindOf(locationKey).isEmpty()) return 0L;
        int slash = locationKey.indexOf('/');
        int slot = locationKey.indexOf('#', slash + 1);
        if (slash < 0 || slot <= slash + 1) return 0L;
        try {
            long owner = Long.parseLong(locationKey.substring(slash + 1,
                    slot));
            return owner > 0L ? owner : 0L;
        } catch (NumberFormatException invalid) {
            return 0L;
        }
    }

    /** Whether {@code locationKey} names one selected map's whole state. */
    public static boolean isMapState(String locationKey) {
        return LOCATION_KIND_MAP_STATE.equals(locationKindOf(locationKey));
    }

    public static final String SESSION_LOCATION_FIELD = "sessionLocationKey";

    /**
     * A cross-session name for one location, built from the planned region
     */
    public static String canonicalLocationKey(String locationKey,
                                              String declaredField,
                                              String occurrenceId,
                                              long receiverObjectId) {
        String kind = locationKindOf(locationKey);
        if (kind.isEmpty()
                || occurrenceId == null || occurrenceId.trim().isEmpty()
                || declaredField == null || declaredField.trim().isEmpty()
                || receiverObjectId <= 0L) {
            return "";
        }
        int slot = locationKey.indexOf('#');
        if (slot < 0) return "";
        return kind + "/" + occurrenceId.trim() + "@receiver:"
                + receiverObjectId + "@"
                + declaredField.trim()
                + locationKey.substring(slot);
    }

    public static String sessionLocationKey(JsonObject row) {
        String session = optionalString(row, SESSION_LOCATION_FIELD);
        return session.isEmpty() ? optionalString(row, "locationKey") : session;
    }

    /**
     * Renames one summary's locations from the VM's session-local rid to a
     */
    public static Collection<String> canonicalizeLocations(
            JsonObject summary) {
        Set<String> unresolved = new LinkedHashSet<>();
        String occurrenceId = optionalString(summary, "occurrenceId");
        JsonObject recorded = object(summary, RECORDED_FIELD);
        if (recorded.size() > 0) {
            for (JsonElement element : array(recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String key = optionalString(row, "locationKey");
                if (isMapState(sessionLocationKey(row))) continue;
                String named = carrierLocationKey(row, occurrenceId);
                if (named.isEmpty()) {
                    if (!key.isEmpty()) unresolved.add(key);
                    continue;
                }
                rename(row, key, named);
            }
        }
        return unresolved;
    }

    /** Prefix of a content-addressed runtime map-state witness. */
    static final String MAP_STATE_SYMBOL_PREFIX = "MAP_STATE.v1.";

    /**
     * Rebuilds the content address used by a runtime MAP_STATE carrier from
     * its replay action.  This is the inverse lookup needed by sparse map
     * projection: the expression keeps only the stable hash, while the
     * action keeps the exact field and receiver which can be updated.
     */
    static String mapStateSymbolForAction(JsonObject action) {
        if (action == null) return "";
        String sourceKey = optionalString(action, "sourceKey");
        long receiverObjectId = optionalLongInteger(action,
                "fieldReceiverObjectId", 0L);
        JsonArray declarations = array(action, "fieldPathDeclarations");
        String declaration = declarations.size() == 0
                ? optionalString(action, "leafFieldSignature")
                : declarations.get(declarations.size() - 1).isJsonPrimitive()
                ? declarations.get(declarations.size() - 1).getAsString()
                : "";
        FieldPathSpec.DeclaredField field =
                FieldPathSpec.declaredField(declaration);
        if (sourceKey.isEmpty() || receiverObjectId <= 0L || field == null) {
            return "";
        }
        String descriptor = JavaPrimitiveSmtSemantics
                .javaTypeDescriptor(field.type());
        return descriptor.isEmpty() ? "" : mapStateSymbol(sourceKey,
                field.owner(), field.name(), descriptor, receiverObjectId);
    }

    private static String mapStateSymbol(
            String sourceKey, String declaringClass, String fieldName,
            String descriptor, long receiverObjectId) {
        JsonObject material = new JsonObject();
        material.addProperty("schemaVersion", 1);
        material.addProperty("kind", "RUNTIME_MAP_STATE_IDENTITY");
        material.addProperty("sourceKey", sourceKey);
        material.addProperty("carrierKind", LOCATION_KIND_MAP_STATE);
        material.addProperty("declaringClass", declaringClass);
        material.addProperty("fieldName", fieldName);
        material.addProperty("descriptor", descriptor);
        material.addProperty("plannedReceiverObjectId", receiverObjectId);
        return MAP_STATE_SYMBOL_PREFIX + CanonicalJson.sha256(material);
    }

    /** One fail-closed result of scope-wide map-state canonicalization. */
    static final class ContainerStateIssue {
        final JsonObject summary;
        final JsonObject gap;

        private ContainerStateIssue(JsonObject summary, JsonObject gap) {
            this.summary = summary;
            this.gap = gap;
        }
    }

    /**
     * Gives every occurrence of one runtime map owner the same stable value
     * identity within a linked replay/session scope.
     *
     * <p>The VM propagates an associative state as a session-local
     * {@code M_L..._<owner>} expression. A downstream summary can mention an
     * upstream owner without carrying that owner's carrier. This pass first
     * indexes all recorded MAP_STATE carriers in the scope, then rewrites all
     * summaries. It never reads an edge port: graph edges select and schedule
     * occurrences, while runtime carrier evidence proves value identity.</p>
     *
     * <p>Each returned issue is also attached to its summary's
     * {@code alignmentGaps}; downstream worklists consequently stay open
     * instead of solving with a guessed map.</p>
     */
    static List<ContainerStateIssue> canonicalizeContainerStateSymbols(
            Collection<JsonObject> summaries) {
        List<JsonObject> rows = new ArrayList<>();
        if (summaries != null) {
            for (JsonObject summary : summaries) {
                if (summary != null) rows.add(summary);
            }
        }

        Map<RuntimeMapOwner, RuntimeMapIdentitySet> identities =
                new LinkedHashMap<>();
        IdentityHashMap<JsonObject, Set<RuntimeMapOwner>> subjects =
                new IdentityHashMap<>();
        List<MapRecordBinding> records = new ArrayList<>();
        List<MapReceiverBinding> receivers = new ArrayList<>();
        List<ContainerStateIssue> issues = new ArrayList<>();

        for (JsonObject summary : rows) {
            String scope = optionalString(summary, "boundarySessionScope");
            String sourceKey = optionalString(summary, "sourceKey");
            JsonObject recorded = object(summary, RECORDED_FIELD);
            for (JsonElement element : array(recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject record = element.getAsJsonObject();
                String session = sessionLocationKey(record);
                if (!isMapState(session)) continue;
                long owner = locationOwnerOf(session);
                if (scope.isEmpty() || owner <= 0L) {
                    addContainerStateIssue(issues, summary,
                            MAP_STATE_IDENTITY_MISSING, session,
                            "MAP_STATE record has no replay scope or "
                                    + "positive runtime owner");
                    continue;
                }
                RuntimeMapOwner key = new RuntimeMapOwner(scope, session,
                        owner);
                subjects.computeIfAbsent(summary,
                        ignored -> new LinkedHashSet<>()).add(key);
                RuntimeMapIdentitySet set = identities.computeIfAbsent(key,
                        ignored -> new RuntimeMapIdentitySet());
                RuntimeMapIdentity identity = RuntimeMapIdentity.of(record,
                        sourceKey);
                if (identity.fault.isEmpty()) {
                    set.admit(identity);
                } else {
                    set.faults.add(identity.fault);
                }
                records.add(new MapRecordBinding(record, key));
            }
            collectMapStateReceivers(summary, scope, subjects, receivers,
                    issues);
        }

        for (MapRecordBinding binding : records) {
            RuntimeMapIdentity identity = uniqueIdentity(
                    identities.get(binding.owner));
            if (identity != null) {
                String held = sessionLocationKey(binding.record);
                if (optionalString(binding.record, SESSION_LOCATION_FIELD).isEmpty()) {
                    binding.record.addProperty(SESSION_LOCATION_FIELD, held);
                }
                binding.record.addProperty("locationKey",
                        identity.locationKey);
            }
        }
        for (MapReceiverBinding binding : receivers) {
            RuntimeMapIdentity identity = uniqueIdentity(
                    identities.get(binding.owner));
            if (identity != null) {
                binding.receiver.addProperty("_exp", identity.symbol);
            }
        }

        for (JsonObject summary : rows) {
            Set<RuntimeMapOwner> referenced = subjects.get(summary);
            if (referenced == null) continue;
            for (RuntimeMapOwner owner : referenced) {
                RuntimeMapIdentitySet set = identities.get(owner);
                if (uniqueIdentity(set) != null) continue;
                boolean ambiguous = set != null
                        && (set.identities.size() > 1
                        || !set.identities.isEmpty()
                        && !set.faults.isEmpty());
                String detail = "scope=" + owner.scope + ", runtimeOwner="
                        + owner.owner;
                if (set != null && !set.faults.isEmpty()) {
                    detail += ", evidence="
                            + String.join(" | ", set.faults);
                }
                addContainerStateIssue(issues, summary, ambiguous
                                ? MAP_STATE_IDENTITY_AMBIGUOUS
                                : MAP_STATE_IDENTITY_MISSING,
                        owner.sessionLocationKey, detail);
            }
        }
        return issues;
    }

    private static RuntimeMapIdentity uniqueIdentity(
            RuntimeMapIdentitySet set) {
        return set != null && set.faults.isEmpty()
                && set.identities.size() == 1
                ? set.identities.values().iterator().next() : null;
    }

    private static void collectMapStateReceivers(
            JsonObject summary, String scope,
            IdentityHashMap<JsonObject, Set<RuntimeMapOwner>> subjects,
            List<MapReceiverBinding> receivers,
            List<ContainerStateIssue> issues) {
        Deque<JsonElement> pending = new ArrayDeque<>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(summary);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
            if (current == null || current.isJsonNull()
                    || current.isJsonPrimitive() || !visited.add(current)) {
                continue;
            }
            if (current.isJsonArray()) {
                for (JsonElement child : current.getAsJsonArray()) {
                    pending.push(child);
                }
                continue;
            }
            JsonObject node = current.getAsJsonObject();
            if ("ContainerRelation".equals(optionalString(node, "_type"))
                    && "ASSOCIATIVE".equals(optionalString(node, "shape"))
                    && "STATE".equals(optionalString(node, "operation"))) {
                JsonObject receiver = object(node, "receiver");
                if ("SymbolExpression".equals(
                        optionalString(receiver, "_type"))) {
                    String raw = optionalString(receiver, "_exp");
                    long owner = associativeStateOwner(raw);
                    if (owner > 0L && !scope.isEmpty()) {
                        RuntimeMapOwner key = new RuntimeMapOwner(scope,
                                LOCATION_KIND_MAP_STATE + "/" + owner + "#"
                                        + MAP_STATE_SLOT, owner);
                        subjects.computeIfAbsent(summary,
                                ignored -> new LinkedHashSet<>()).add(key);
                        receivers.add(new MapReceiverBinding(receiver, key));
                    } else if (raw.startsWith("M_L")) {
                        addContainerStateIssue(issues, summary,
                                MAP_STATE_IDENTITY_MISSING, "",
                                "associative STATE receiver has no "
                                        + "resolvable runtime owner in scope "
                                        + scope + ": " + raw);
                    }
                }
            }
            for (Map.Entry<String, JsonElement> field : node.entrySet()) {
                pending.push(field.getValue());
            }
        }
    }

    private static void addContainerStateIssue(
            List<ContainerStateIssue> issues, JsonObject summary, int status,
            String locationKey, String detail) {
        JsonObject failure = gap(STAGE_IDENTITY, status, locationKey, detail);
        JsonArray gaps;
        JsonElement existing = summary.get("alignmentGaps");
        if (existing != null && existing.isJsonArray()) {
            gaps = existing.getAsJsonArray();
        } else {
            gaps = new JsonArray();
            summary.add("alignmentGaps", gaps);
        }
        String rendered = CanonicalJson.render(failure);
        for (JsonElement element : gaps) {
            if (element.isJsonObject()
                    && rendered.equals(CanonicalJson.render(element))) {
                return;
            }
        }
        gaps.add(failure);
        issues.add(new ContainerStateIssue(summary, failure));
    }

    private static final class RuntimeMapOwner {
        private final String scope;
        private final String sessionLocationKey;
        private final long owner;

        private RuntimeMapOwner(String scope, String sessionLocationKey,
                                long owner) {
            this.scope = scope;
            this.sessionLocationKey = sessionLocationKey;
            this.owner = owner;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof RuntimeMapOwner)) return false;
            RuntimeMapOwner that = (RuntimeMapOwner) other;
            return owner == that.owner && scope.equals(that.scope)
                    && sessionLocationKey.equals(that.sessionLocationKey);
        }

        @Override
        public int hashCode() {
            int result = scope.hashCode();
            result = 31 * result + sessionLocationKey.hashCode();
            return 31 * result + (int) (owner ^ owner >>> 32);
        }
    }

    private static final class RuntimeMapIdentitySet {
        private final Map<String, RuntimeMapIdentity> identities =
                new LinkedHashMap<>();
        private final Set<String> faults = new LinkedHashSet<>();

        private void admit(RuntimeMapIdentity identity) {
            identities.putIfAbsent(identity.symbol, identity);
        }
    }

    private static final class RuntimeMapIdentity {
        private final String symbol;
        private final String locationKey;
        private final String fault;

        private RuntimeMapIdentity(String symbol, String locationKey,
                                   String fault) {
            this.symbol = symbol;
            this.locationKey = locationKey;
            this.fault = fault;
        }

        private static RuntimeMapIdentity of(
                JsonObject record, String sourceKey) {
            JsonObject carrier = object(record, "carrier");
            String kind = optionalString(carrier, "kind");
            String declaringClass = optionalString(carrier, "declaringClass");
            String fieldName = optionalString(carrier, "fieldName");
            String descriptor = optionalString(carrier, "descriptor");
            long receiverObjectId = optionalLongInteger(carrier,
                    "receiverObjectId", 0L);
            String evidenceSource = optionalString(object(record,
                    RecordedEvidenceIdentity.FIELD), "sourceKey");
            String expectedField = declaringClass + "#" + fieldName + ":"
                    + descriptor;
            String statedField = optionalString(carrier, "fieldKey");
            List<String> missing = new ArrayList<>();
            if (sourceKey.isEmpty()) missing.add("sourceKey");
            if (!sourceKey.equals(evidenceSource)) {
                missing.add("evidence sourceKey agreement");
            }
            if (!LOCATION_KIND_MAP_STATE.equals(kind)) {
                missing.add("MAP_STATE carrier kind");
            }
            if (declaringClass.isEmpty()) missing.add("declaringClass");
            if (fieldName.isEmpty()) missing.add("fieldName");
            if (descriptor.isEmpty()) missing.add("descriptor");
            if (receiverObjectId <= 0L) {
                missing.add("planned receiverObjectId");
            }
            if (!statedField.isEmpty() && !expectedField.equals(statedField)) {
                missing.add("fieldKey agreement");
            }
            if (!missing.isEmpty()) {
                return new RuntimeMapIdentity("", "",
                        "missing or conflicting " + String.join(", ", missing));
            }
            // Scope and VM owner locate this evidence inside one imported
            // execution only. They restart across replays and therefore must
            // never enter the stable value identity.
            String symbol = mapStateSymbol(sourceKey, declaringClass,
                    fieldName, descriptor, receiverObjectId);
            String digest = symbol.substring(MAP_STATE_SYMBOL_PREFIX.length());
            return new RuntimeMapIdentity(symbol,
                    LOCATION_KIND_MAP_STATE + "/" + digest + "#"
                            + MAP_STATE_SLOT, "");
        }
    }

    private static final class MapRecordBinding {
        private final JsonObject record;
        private final RuntimeMapOwner owner;

        private MapRecordBinding(JsonObject record, RuntimeMapOwner owner) {
            this.record = record;
            this.owner = owner;
        }
    }

    private static final class MapReceiverBinding {
        private final JsonObject receiver;
        private final RuntimeMapOwner owner;

        private MapReceiverBinding(JsonObject receiver,
                                   RuntimeMapOwner owner) {
            this.receiver = receiver;
            this.owner = owner;
        }
    }

    static long associativeStateOwner(String symbol) {
        if (symbol == null || !symbol.startsWith("M_L")) return 0L;
        int separator = symbol.lastIndexOf('_');
        if (separator < 0 || separator + 1 >= symbol.length()) return 0L;
        try {
            long owner = Long.parseLong(symbol.substring(separator + 1));
            return owner > 0L ? owner : 0L;
        } catch (NumberFormatException invalid) {
            return 0L;
        }
    }

    /**
     * The canonical name a version row builds from its own carrier, or "" if
     */
    private static String carrierLocationKey(
            JsonObject row, String occurrenceId) {
        JsonObject carrier = object(row, "carrier");
        if (carrier.size() == 0) return "";
        String declaringClass = optionalString(carrier, "declaringClass");
        String fieldName = optionalString(carrier, "fieldName");
        if (declaringClass.isEmpty() || fieldName.isEmpty()) return "";
        return canonicalLocationKey(optionalString(row, "locationKey"),
                declaringClass + "#" + fieldName,
                occurrenceId,
                optionalLongInteger(carrier, "receiverObjectId", 0L));
    }

    private static void rename(JsonObject row, String session,
                               String canonical) {
        String heldSession = optionalString(row, SESSION_LOCATION_FIELD);
        if (!heldSession.isEmpty()
                && !heldSession.equals(optionalString(row, "locationKey"))) return;
        if (heldSession.isEmpty()) {
            row.addProperty(SESSION_LOCATION_FIELD, session);
        }
        row.addProperty("locationKey", canonical);
    }

    /** Whether {@code versionKind} publishes one immutable whole state. */
    public static boolean stateVersionKind(String versionKind) {
        return versionKind != null && (versionKind.equals("STATE")
                || versionKind.startsWith("STATE_"));
    }

    /**
     * Admits one version-store envelope, answering "" or the exact reason it
     */
    public static String versionsFault(JsonObject envelope) {
        if (envelope == null || envelope.size() == 0) {
            return "no version envelope";
        }
        if (!VERSIONS_ENVELOPE_KIND.equals(optionalString(envelope, "kind"))
                || optionalInteger(envelope, "schemaVersion", -1) != SCHEMA_VERSION) {
            return "envelope is not an authoritative version store";
        }
        if (!booleanMember(envelope, "selected")
                || !optionalBool(envelope, "selected", false)) {
            return "location was never selected as a carrier";
        }
        if (locationKey(envelope).isEmpty()) {
            return "envelope names no addressable location";
        }
        if (!booleanMember(envelope, "writerSetComplete")) {
            return "envelope omits writer-set completeness";
        }
        JsonElement versionsMember = envelope.get("versions");
        if (versionsMember == null || !versionsMember.isJsonArray()) {
            return "envelope carries no version array";
        }
        JsonArray versions = array(envelope, "versions");
        if (versions.size() == 0) {
            // Selecting publishes an INITIAL version, so an empty list means
            // the envelope was not produced by a real selection.
            return "selected location published no version";
        }
        if (!booleanMember(envelope, "serializationTruncated")) {
            return "envelope omits version serialization completeness";
        }
        if (optionalBool(envelope, "serializationTruncated", false)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version envelope";
        }
        boolean mapState = isMapState(locationKey(envelope));
        Set<Long> versionIds = new LinkedHashSet<>();
        for (JsonElement element : versions) {
            if (!element.isJsonObject()) return "version is not an object";
            String fault = versionFault(element.getAsJsonObject(), mapState);
            if (!fault.isEmpty()) return fault;
            long id = optionalLongInteger(element.getAsJsonObject(),
                    "fieldVersionId", 0L);
            if (!versionIds.add(id)) {
                return "duplicate fieldVersionId " + id;
            }
        }
        JsonElement readsMember = envelope.get("reads");
        if (readsMember == null || !readsMember.isJsonArray()) {
            return "envelope carries no read array";
        }
        JsonArray reads = readsMember.getAsJsonArray();
        if (!booleanMember(envelope, "readLogTruncated")) {
            return "envelope omits read-log completeness";
        }
        for (JsonElement element : reads) {
            if (!element.isJsonObject()) return "read is not an object";
            String fault = readFault(element.getAsJsonObject());
            if (!fault.isEmpty()) return fault;
        }
        return "";
    }

    /**
     * Admits one published version.
     */
    private static String versionFault(JsonObject version, boolean mapState) {
        long id = optionalLongInteger(version, "fieldVersionId", 0L);
        if (id <= 0L) return "version has no fieldVersionId";
        String versionKind = optionalString(version, "versionKind");
        if (!VERSION_KINDS.contains(versionKind)) {
            return "version " + id + " has no declared kind";
        }
        if (!INITIAL_VERSION_KIND.equals(versionKind)
                && stateVersionKind(versionKind) != mapState) {
            return "version " + id + " has kind " + versionKind
                    + " that its location kind does not publish";
        }
        if (optionalLongInteger(version, "regionEnterEventId", 0L) <= 0L
                || optionalString(version, "regionId").isEmpty()
                || optionalString(version, "taskId").isEmpty()) {
            return "version " + id + " names no writer case";
        }
        if (!version.has("pathGuard")) {
            // Explicitly null means the empty conjunction.  An absent key
            // means the guard was never captured, which is a different and
            return "version " + id + " omits its writer path guard";
        }
        JsonElement expression = version.get("expression");
        if (expression == null || expression.isJsonNull()) {
            return "version " + id + " carries no value expression";
        }
        if (containsVmSerializationTruncation(expression)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " value expression";
        }
        if (containsVmSerializationTruncation(version.get("pathGuard"))) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " path guard";
        }
        return "";
    }

    private static String readFault(JsonObject read) {
        long readEvent = optionalLongInteger(read, "readEventId", 0L);
        if (readEvent <= 0L) return "read has no readEventId";
        if (optionalLongInteger(read, "regionEnterEventId", 0L) <= 0L
                || optionalString(read, "regionId").isEmpty()
                || optionalString(read, "taskId").isEmpty()) {
            return "read " + readEvent + " names no reader case";
        }
        return "";
    }

    /** Whether the envelope's writer set is still complete. */
    public static boolean writerSetComplete(JsonObject envelope) {
        return optionalBool(envelope, "writerSetComplete", false);
    }

    /**
     * Whether the VM dropped read-log entries for this location.
     */
    public static boolean readLogTruncated(JsonObject envelope) {
        return optionalBool(envelope, "readLogTruncated", false);
    }


    /**
     * Members the runtime adds to a version and a read row so each names the
     */
    public static final String WRITER_SOURCE_KEY = "writerSourceKey";
    public static final String WRITER_OCCURRENCE_ID = "writerOccurrenceId";
    public static final String READER_SOURCE_KEY = "readerSourceKey";
    public static final String READER_OCCURRENCE_ID = "readerOccurrenceId";

    public static JsonObject versionsRecord(String locationKey,
                                            JsonObject envelope,
                                            RecordedEvidenceIdentity identity) {
        JsonObject record = new JsonObject();
        record.addProperty("kind", VERSIONS_RECORD_KIND);
        record.addProperty("schemaVersion", RECORD_SCHEMA_VERSION);
        record.addProperty("authority", RECORD_AUTHORITY);
        record.addProperty("locationKey", text(locationKey));
        record.add("envelope", envelope);
        if (identity != null) identity.stamp(record);
        return record;
    }

    /** Whether {@code row} is an admitted version-store record. */
    public static boolean isVersionsRecord(JsonObject row) {
        return row != null
                && VERSIONS_RECORD_KIND.equals(optionalString(row, "kind"))
                && RECORD_AUTHORITY.equals(optionalString(row, "authority"))
                && optionalInteger(row, "schemaVersion", -1) == RECORD_SCHEMA_VERSION
                && RecordedEvidenceIdentity.stamped(row)
                && !optionalString(row, "locationKey").isEmpty()
                && versionsFault(object(row, "envelope")).isEmpty();
    }


    public static JsonObject recorded(Collection<JsonObject> versionRecords) {
        JsonArray versions = new JsonArray();
        if (versionRecords != null) {
            for (JsonObject record : versionRecords) {
                if (isVersionsRecord(record)) versions.add(record);
            }
        }
        if (versions.size() == 0) return new JsonObject();
        JsonObject recorded = new JsonObject();
        recorded.addProperty("schemaVersion", SCHEMA_VERSION);
        recorded.addProperty("kind", RECORDED_KIND);
        recorded.addProperty("authority", RECORD_AUTHORITY);
        recorded.add("versions", versions);
        return recorded;
    }

    /** Whether {@code node} claims to be a guarded read-from choice. */
    public static boolean claimsGuardedRead(JsonObject node) {
        return node != null
                && GUARDED_READ_TYPE.equals(textString(node, "_type"));
    }

    /**
     * Admits one guarded read-from node.
     */
    public static String guardedReadFault(JsonObject node) {
        if (!claimsGuardedRead(node)) {
            return "node is not a guarded read-from choice";
        }
        if (!GUARDED_READ_AUTHORITY.equals(
                optionalString(node, "expressionAuthority"))) {
            return "guarded read carries no VM authority";
        }
        if (optionalString(node, "_java_type").isEmpty()) {
            return "guarded read names no Java value sort";
        }
        long readEvent = optionalLongInteger(node, "readEventId", 0L);
        if (readEvent <= 0L) return "guarded read has no readEventId";
        if (locationKey(node).isEmpty()) {
            return "guarded read names no addressable location";
        }
        if (!booleanMember(node, "writerSetComplete")) {
            return "guarded read omits writer-set completeness";
        }
        JsonArray candidates = array(node, "candidates");
        if (candidates.size() < 1) {
            return "guarded read offers no candidate";
        }
        JsonArray selectors = array(node, "exactlyOne");
        if (selectors.size() != candidates.size()) {
            return "exactlyOne does not cover the candidate set";
        }
        Set<String> seen = new LinkedHashSet<>();
        for (int index = 0; index < candidates.size(); index++) {
            JsonElement element = candidates.get(index);
            if (!element.isJsonObject()) return "candidate is not an object";
            JsonObject candidate = element.getAsJsonObject();
            String selector = optionalString(candidate, "selector");
            if (selector.isEmpty()) return "candidate has no selector";
            if (!seen.add(selector)) {
                return "duplicate candidate selector " + selector;
            }
            if (!selector.equals(selectorName(selectors, index))) {
                return "exactlyOne selector " + index
                        + " does not name its candidate";
            }
            String fault = candidateFault(candidate,
                    isMapState(locationKey(node)));
            if (!fault.isEmpty()) return fault;
        }
        return "";
    }

    private static String selectorName(JsonArray selectors, int index) {
        JsonElement element = selectors.get(index);
        return element != null && element.isJsonPrimitive()
                && element.getAsJsonPrimitive().isString()
                ? element.getAsString() : "";
    }

    private static String candidateFault(JsonObject candidate,
                                         boolean mapState) {
        String selector = optionalString(candidate, "selector");
        long version = optionalLongInteger(candidate, "fieldVersionId", 0L);
        if (version <= 0L) {
            return "candidate " + selector + " names no recorded write";
        }
        String versionKind = optionalString(candidate, "versionKind");
        if (!VERSION_KINDS.contains(versionKind)
                || !INITIAL_VERSION_KIND.equals(versionKind)
                && stateVersionKind(versionKind) != mapState) {
            return "candidate " + selector + " has incompatible version kind";
        }
        JsonElement value = candidate.get("expression");
        if (value == null || value.isJsonNull()) {
            return "candidate " + selector + " carries no value expression";
        }
        if (containsVmSerializationTruncation(value)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": candidate " + selector + " value expression";
        }
        if (!candidate.has("pathGuard")) {
            return "candidate " + selector + " omits its writer path guard";
        }
        if (containsVmSerializationTruncation(candidate.get("pathGuard"))) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": candidate " + selector + " path guard";
        }
        return "";
    }

    private static boolean booleanMember(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }
}
