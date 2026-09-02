package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
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
    /** Envelope kind of the session-wide event ledger. */
    public static final String LEDGER_ENVELOPE_KIND = "SESSION_EVENT_LEDGER";
    /** Expression node type of one guarded read-from choice. */
    public static final String GUARDED_READ_TYPE = "ReadFromExpression";
    /** Authority the VM stamps on a guarded read-from node. */
    public static final String GUARDED_READ_AUTHORITY =
            "VM_GUARDED_READ_FROM_V1";
    /** Selector of the unknown-writer arm, which is always present. */
    public static final String UNKNOWN_WRITER_SELECTOR = "rf_unknown";
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
    /** Kind of one admitted ledger record. */
    public static final String LEDGER_RECORD_KIND =
            "VM_SESSION_EVENT_LEDGER_V1";
    /** Authority stamped on both admitted records. */
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
    public static final String STAGE_LEDGER = "LEDGER";


    public static final int OK = 0;

    // Declared VM carrier-selection refusals (sharedFieldVersions.hpp).
    // Their numeric values are the VM's; they are mirrored so a Java caller
    public static final int SELECT_NO_ACTIVE_CONTEXT = -1;
    public static final int SELECT_MISSING_METADATA = -2;
    public static final int SELECT_FIELD_NOT_FOUND = -3;
    public static final int SELECT_UNSUPPORTED_TARGET = -4;
    /** The requested producer-state version is not retained in this session. */
    public static final int SELECT_VERSION_NOT_FOUND = -5;
    /** More than one retained location claims the requested version id. */
    public static final int SELECT_VERSION_AMBIGUOUS = -6;
    /** The frozen producer edge id is absent or malformed. */
    public static final int SELECT_INVALID_EDGE = -7;

    public static final int INVOCATION_FAILED = -1001;
    public static final int MALFORMED_ENVELOPE = -1002;
    /** The location was never selected, so it has no recorded evidence. */
    public static final int NOT_SELECTED = -1003;
    /** Addressing that names no single location. */
    public static final int MISSING_METADATA = -1004;
    public static final int UNKNOWN_WRITER = -1005;
    /**
     * drowned the log.  README's claim boundary makes a gap-bearing result
     */
    public static final int READ_LOG_TRUNCATED = -1006;
    /** One expression root was serialized only up to the VM's safety bound. */
    public static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /**
     * set (README {@code EVENT-1}): both fail closed, but a malformed
     */
    public static final int LEDGER_LOG_TRUNCATED = -1008;
    public static final int LEDGER_DOMAIN_SATURATED = -1009;

    /** Exact coverage reason for a VM-bounded expression tree. */
    public static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    public static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";


    public static final String RESOLUTION_EXACT = "EXACT";
    public static final String RESOLUTION_GUARDED = "GUARDED";
    public static final String RESOLUTION_NONE = "NONE";
    private static final Set<String> RESOLUTIONS = names(
            RESOLUTION_EXACT, RESOLUTION_GUARDED, RESOLUTION_NONE);
    private static final Set<String> READ_REASONS = names("UNIQUE_VERSION",
            "VALUE_DISTINGUISHED", "SYNC_ORDERED", "AMBIGUOUS_WRITERS",
            "UNTRACKED_WRITER", "INCOMPLETE_WRITER_SET", "NOT_SELECTED");
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
     * {@code REMOVE_IF} is the conditional removal an iterator's
     * {@code remove()} installs, i.e. exactly what HDFS-11741's
     * {@code removeExpiredKeys()} does to the DataNode's key map.</p>
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "STATE", "STATE_PUT", "STATE_REMOVE", "STATE_REMOVE_IF",
            "STATE_CLEAR", "STATE_REMOVE_AT", "STATE_CLEAR_VIEW",
            "STATE_ADD");
    /** The version kind every location may publish, whatever its shape. */
    private static final String INITIAL_VERSION_KIND = "INITIAL";
    private static final Set<String> FINGERPRINT_KINDS = names("NONE",
            "PRIMITIVE", "NULL", "IDENTITY");
    private static final Set<String> EVENT_KINDS = names("VOLATILE_READ",
            "VOLATILE_WRITE", "THREAD_START",
            "THREAD_JOIN", "ATOMIC_RMW", "ATOMIC_CAS", "FIELD_WRITE",
            "FIELD_READ", "REGION_ENTER", "REGION_EXIT", "HANDOFF_EXPORT",
            "HANDOFF_ATTACH");
    private static final Set<String> EDGE_KINDS = names("PROGRAM_ORDER",
            "SYNCHRONIZATION", "FIELD_READ_FROM", "VALUE_HANDOFF", "REGION",
            "CANDIDATE");
    private static final Set<String> ORDER_CONSTRAINT_KINDS = names(
            "WRITE_BEFORE_READ", "OTHER_WRITE_OUTSIDE_CUT",
            "UNKNOWN_WRITE_BEFORE_READ");

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
            case SELECT_VERSION_NOT_FOUND:
                return REASON_PREFIX + "VERSION_NOT_FOUND";
            case SELECT_VERSION_AMBIGUOUS:
                return REASON_PREFIX + "VERSION_AMBIGUOUS";
            case SELECT_INVALID_EDGE:
                return REASON_PREFIX + "INVALID_EDGE";
            case INVOCATION_FAILED:
                return REASON_PREFIX + "INVOCATION_FAILED";
            case MALFORMED_ENVELOPE:
                return REASON_PREFIX + "MALFORMED_ENVELOPE";
            case NOT_SELECTED:
                return REASON_PREFIX + "NOT_SELECTED";
            case MISSING_METADATA:
                return REASON_PREFIX + "MISSING_METADATA";
            case UNKNOWN_WRITER:
                return REASON_PREFIX + "UNKNOWN_WRITER";
            case READ_LOG_TRUNCATED:
                return REASON_PREFIX + "READ_LOG_TRUNCATED";
            case EXPRESSION_SERIALIZATION_TRUNCATED:
                return VM_EXPRESSION_SERIALIZATION_TRUNCATED;
            case LEDGER_LOG_TRUNCATED:
                return REASON_PREFIX + "LEDGER_LOG_TRUNCATED";
            case LEDGER_DOMAIN_SATURATED:
                return REASON_PREFIX + "LEDGER_DOMAIN_SATURATED";
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
                string(guard.getAsJsonObject(), "kind"))
                && EMPTY_CONJUNCTION_AUTHORITY.equals(
                string(guard.getAsJsonObject(), "authority"));
    }

    /**
     * Replaces every JSON-null path guard in one envelope or expression term
     */
    public static JsonElement normalizeGuards(JsonElement node) {
        if (node == null) return null;
        Deque<JsonElement> pending = new ArrayDeque<>();
        pending.push(node);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
            if (current.isJsonArray()) {
                for (JsonElement element : current.getAsJsonArray()) {
                    if (element != null) pending.push(element);
                }
                continue;
            }
            if (!current.isJsonObject()) continue;
            JsonObject term = current.getAsJsonObject();
            JsonElement guard = term.get("pathGuard");
            if (guard != null && guard.isJsonNull()) {
                term.add("pathGuard", emptyConjunction());
            }
            for (String field : new LinkedHashSet<>(term.keySet())) {
                JsonElement child = term.get(field);
                if (!"pathGuard".equals(field) && child != null) {
                    pending.push(child);
                }
            }
        }
        return node;
    }

    /**
     * Whether an expression tree recursively contains the VM's explicit
     */
    public static boolean containsVmSerializationTruncation(
            JsonElement expression) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<>();
        pending.push(expression);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
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
                    string(term, "expressionAuthority"))) {
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
        return row != null
                && GAP_KIND.equals(string(row, "kind"))
                && GAP_AUTHORITY.equals(string(row, "authority"))
                && !string(row, "reason").isEmpty()
                && integer(row, "statusCode", OK) != OK;
    }


    /**
     * Names the location one version-store envelope describes, as the VM's
     */
    public static String locationKey(JsonObject envelope) {
        JsonObject location = object(envelope, "location");
        if (location.size() == 0) return "";
        String kind = string(location, "locationKind");
        if (!LOCATION_KINDS.contains(kind)) return "";
        long owner = longInteger(location, "ownerSymRid", 0L);
        if (owner == 0L || !location.has("slot")) return "";
        int slot = integer(location, "slot", 0);
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
        String session = string(row, SESSION_LOCATION_FIELD);
        return session.isEmpty() ? string(row, "locationKey") : session;
    }

    /**
     * Renames one summary's locations from the VM's session-local rid to a
     */
    public static Collection<String> canonicalizeLocations(
            JsonObject summary) {
        Set<String> unresolved = new LinkedHashSet<>();
        Map<String, Set<String>> candidates = new LinkedHashMap<>();
        String occurrenceId = string(summary, "occurrenceId");
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String key = string(binding, "locationKey");
            if (key.isEmpty()) continue;
            String named = canonicalLocationKey(key,
                    string(binding, RecordedReadFrom.EDGE_FIELD),
                    occurrenceId,
                    longInteger(binding, "receiverObjectId", 0L));
            if (named.isEmpty()) {
                unresolved.add(key);
                continue;
            }
            candidates.computeIfAbsent(key,
                    ignored -> new LinkedHashSet<>()).add(named);
        }
        Map<String, String> canonical = new LinkedHashMap<>();
        for (Map.Entry<String, Set<String>> entry : candidates.entrySet()) {
            if (entry.getValue().size() != 1) {
                unresolved.add(entry.getKey());
                continue;
            }
            canonical.put(entry.getKey(), entry.getValue().iterator().next());
        }
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String key = string(binding, "locationKey");
            String named = canonical.getOrDefault(key, "");
            if (!named.isEmpty()) rename(binding, key, named);
        }
        for (JsonObject recorded : recordedMembers(summary)) {
            for (JsonElement element : array(recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String key = string(row, "locationKey");
                String carried = carrierLocationKey(row, occurrenceId);
                String borrowed = canonical.getOrDefault(key, "");
                if (!carried.isEmpty() && !borrowed.isEmpty()
                        && !carried.equals(borrowed)) {
                    if (!key.isEmpty()) unresolved.add(key);
                    continue;
                }
                String named = carried.isEmpty() ? borrowed : carried;
                if (named.isEmpty()) {
                    if (!key.isEmpty()) unresolved.add(key);
                    continue;
                }
                rename(row, key, named);
            }
        }
        return unresolved;
    }

    /**
     * Replaces a VM session-local associative-state symbol with the exact
     */
    public static Collection<String> canonicalizeContainerStateSymbols(
            JsonObject summary) {
        Map<Long, Set<String>> portsByOwner = new LinkedHashMap<>();
        String occurrenceId = string(summary, "occurrenceId");
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String session = sessionLocationKey(binding);
            long owner = isMapState(session)
                    ? locationOwnerOf(session) : 0L;
            String port = string(binding, "toInputPort");
            if (owner <= 0L || port.isEmpty()
                    || !occurrenceId.equals(string(binding,
                    "toOccurrenceId"))) {
                continue;
            }
            portsByOwner.computeIfAbsent(owner,
                    ignored -> new LinkedHashSet<>()).add(port);
        }
        Set<String> ambiguous = new LinkedHashSet<>();
        canonicalizeContainerStateSymbols(summary, portsByOwner, ambiguous);
        return ambiguous;
    }

    private static void canonicalizeContainerStateSymbols(
            JsonElement element, Map<Long, Set<String>> portsByOwner,
            Set<String> ambiguous) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                canonicalizeContainerStateSymbols(child, portsByOwner,
                        ambiguous);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        if ("ContainerRelation".equals(string(object, "_type"))
                && "ASSOCIATIVE".equals(string(object, "shape"))
                && "STATE".equals(string(object, "operation"))) {
            JsonObject receiver = object(object, "receiver");
            if ("SymbolExpression".equals(string(receiver, "_type"))) {
                long owner = associativeStateOwner(
                        string(receiver, "_exp"));
                Set<String> ports = portsByOwner.get(owner);
                if (ports != null && ports.size() == 1) {
                    receiver.addProperty("_exp", ports.iterator().next());
                } else if (ports != null && ports.size() > 1) {
                    ambiguous.add(LOCATION_KIND_MAP_STATE + "/" + owner
                            + "#" + MAP_STATE_SLOT);
                }
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            canonicalizeContainerStateSymbols(entry.getValue(),
                    portsByOwner, ambiguous);
        }
    }

    private static long associativeStateOwner(String symbol) {
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
        String declaringClass = string(carrier, "declaringClass");
        String fieldName = string(carrier, "fieldName");
        if (declaringClass.isEmpty() || fieldName.isEmpty()) return "";
        return canonicalLocationKey(string(row, "locationKey"),
                declaringClass + "#" + fieldName,
                occurrenceId,
                longInteger(carrier, "receiverObjectId", 0L));
    }

    private static void rename(JsonObject row, String session,
                               String canonical) {
        if (row.has(SESSION_LOCATION_FIELD)) return;
        row.addProperty(SESSION_LOCATION_FIELD, session);
        row.addProperty("locationKey", canonical);
    }

    /** One summary's own recorded state and that of each of its cases. */
    private static Collection<JsonObject> recordedMembers(
            JsonObject summary) {
        Collection<JsonObject> members = new java.util.ArrayList<>();
        JsonObject own = object(summary, RECORDED_FIELD);
        if (own.size() > 0) members.add(own);
        for (JsonElement element
                : array(object(summary, "regionRelation"), "cases")) {
            if (!element.isJsonObject()) continue;
            JsonObject recorded = object(element.getAsJsonObject(),
                    RECORDED_FIELD);
            if (recorded.size() > 0) members.add(recorded);
        }
        return members;
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
        if (!VERSIONS_ENVELOPE_KIND.equals(string(envelope, "kind"))
                || integer(envelope, "schemaVersion", -1) != SCHEMA_VERSION) {
            return "envelope is not an authoritative version store";
        }
        if (!envelope.has("selected") || !bool(envelope, "selected", false)) {
            return "location was never selected as a carrier";
        }
        if (locationKey(envelope).isEmpty()) {
            return "envelope names no addressable location";
        }
        if (!envelope.has("writerSetComplete")) {
            return "envelope omits writer-set completeness";
        }
        JsonArray versions = array(envelope, "versions");
        if (versions.size() == 0) {
            // Selecting publishes an INITIAL version, so an empty list means
            // the envelope was not produced by a real selection.
            return "selected location published no version";
        }
        boolean mapState = isMapState(locationKey(envelope));
        Set<Long> versionIds = new LinkedHashSet<>();
        for (JsonElement element : versions) {
            if (!element.isJsonObject()) return "version is not an object";
            String fault = versionFault(element.getAsJsonObject(), mapState);
            if (!fault.isEmpty()) return fault;
            long id = longInteger(element.getAsJsonObject(),
                    "fieldVersionId", 0L);
            if (!versionIds.add(id)) {
                return "duplicate fieldVersionId " + id;
            }
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) return "read is not an object";
            String fault = readFault(element.getAsJsonObject(), versionIds);
            if (!fault.isEmpty()) return fault;
        }
        return "";
    }

    /**
     * Admits one published version.
     */
    private static String versionFault(JsonObject version, boolean mapState) {
        long id = longInteger(version, "fieldVersionId", 0L);
        if (id <= 0L) return "version has no fieldVersionId";
        String versionKind = string(version, "versionKind");
        if (!VERSION_KINDS.contains(versionKind)) {
            return "version " + id + " has no declared kind";
        }
        if (!INITIAL_VERSION_KIND.equals(versionKind)
                && stateVersionKind(versionKind) != mapState) {
            return "version " + id + " has kind " + versionKind
                    + " that its location kind does not publish";
        }
        if (longInteger(version, "writerContextId", 0L) == 0L) {
            return "version " + id + " names no writer context";
        }
        if (!FINGERPRINT_KINDS.contains(
                string(version, "fingerprintKind"))) {
            return "version " + id + " has no declared fingerprint kind";
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

    private static String readFault(JsonObject read, Set<Long> versionIds) {
        long readEvent = longInteger(read, "readEventId", 0L);
        if (readEvent <= 0L) return "read has no readEventId";
        String resolution = string(read, "resolution");
        if (!RESOLUTIONS.contains(resolution)) {
            return "read " + readEvent + " has no declared resolution";
        }
        if (!READ_REASONS.contains(string(read, "reason"))) {
            return "read " + readEvent + " has no declared reason";
        }
        long chosen = longInteger(read, "chosenFieldVersionId", 0L);
        if (RESOLUTION_EXACT.equals(resolution)) {
            if (chosen <= 0L) {
                return "exact read " + readEvent + " names no writer";
            }
            if (!versionIds.contains(chosen)) {
                return "exact read " + readEvent + " names version " + chosen
                        + " that this store does not hold";
            }
        } else if (chosen != 0L) {
            return "unresolved read " + readEvent + " still names a writer";
        }
        if (integer(read, "candidateCount", -1) < 0) {
            return "read " + readEvent + " reports no candidate count";
        }
        // Wave 3 B: a read chooses among every recorded version of its
        // location.  Nothing preselects an edge for it, so a read that still
        // names one is stating a narrowing this model no longer has.
        if (!string(read, "selectedEdgeId").isEmpty()) {
            return "read " + readEvent + " names a preselected writer edge";
        }
        return "";
    }

    /** Whether the envelope's writer set is still complete. */
    public static boolean writerSetComplete(JsonObject envelope) {
        return bool(envelope, "writerSetComplete", false);
    }

    /**
     * Whether the VM dropped read-log entries for this location.
     */
    public static boolean readLogTruncated(JsonObject envelope) {
        return bool(envelope, "readLogTruncated", false);
    }


    /**
     * Members the runtime adds to a version and a read row so each names the
     */
    public static final String WRITER_SOURCE_KEY = "writerSourceKey";
    public static final String WRITER_OCCURRENCE_ID = "writerOccurrenceId";
    public static final String READER_SOURCE_KEY = "readerSourceKey";
    public static final String READER_OCCURRENCE_ID = "readerOccurrenceId";

    /** The activation that published one version, or "". */
    public static String writerSite(JsonObject version) {
        return RecordedEvidenceIdentity.siteKey(
                string(version, WRITER_OCCURRENCE_ID));
    }

    /** The activation that performed one read, or "". */
    public static String readerSite(JsonObject read) {
        return RecordedEvidenceIdentity.siteKey(
                string(read, READER_OCCURRENCE_ID));
    }

    public static JsonObject versionsRecord(String locationKey,
                                            JsonObject envelope,
                                            RecordedEvidenceIdentity identity) {
        JsonObject record = new JsonObject();
        record.addProperty("kind", VERSIONS_RECORD_KIND);
        record.addProperty("schemaVersion", RECORD_SCHEMA_VERSION);
        record.addProperty("authority", RECORD_AUTHORITY);
        record.addProperty("locationKey", text(locationKey));
        record.add("envelope", envelope.deepCopy());
        if (identity != null) identity.stamp(record);
        return record;
    }

    /** Whether {@code row} is an admitted version-store record. */
    public static boolean isVersionsRecord(JsonObject row) {
        return row != null
                && VERSIONS_RECORD_KIND.equals(string(row, "kind"))
                && RECORD_AUTHORITY.equals(string(row, "authority"))
                && integer(row, "schemaVersion", -1) == RECORD_SCHEMA_VERSION
                && RecordedEvidenceIdentity.stamped(row)
                && !string(row, "locationKey").isEmpty()
                && versionsFault(object(row, "envelope")).isEmpty();
    }


    /**
     * Admits one event-ledger envelope.
     */
    public static String ledgerFault(JsonObject envelope) {
        if (envelope == null || envelope.size() == 0) {
            return "no ledger envelope";
        }
        if (!LEDGER_ENVELOPE_KIND.equals(string(envelope, "kind"))
                || integer(envelope, "schemaVersion", -1) != SCHEMA_VERSION) {
            return "envelope is not an authoritative event ledger";
        }
        if (!bool(envelope, "open", false)) {
            return "ledger belongs to no open session";
        }
        if (!bool(envelope, "partialOrder", false)) {
            return "ledger does not declare a partial order";
        }
        if (!bool(envelope, "acyclic", false)) {
            return "ledger order domain is cyclic";
        }
        if (bool(envelope, "domainSaturated", false)) {
            // A saturated domain refused edges it could not cycle-check, so
            // the relation it reports is not the relation the run had.
            return "ledger order domain is saturated";
        }
        Set<Long> eventIds = new LinkedHashSet<>();
        for (JsonElement element : array(envelope, "events")) {
            if (!element.isJsonObject()) return "event is not an object";
            JsonObject event = element.getAsJsonObject();
            long id = longInteger(event, "eventId", 0L);
            if (id <= 0L) return "event has no eventId";
            if (!EVENT_KINDS.contains(string(event, "eventKind"))) {
                return "event " + id + " has no declared kind";
            }
            if (!eventIds.add(id)) return "duplicate eventId " + id;
        }
        for (JsonElement element : array(envelope, "order")) {
            if (!element.isJsonObject()) return "order edge is not an object";
            JsonObject edge = element.getAsJsonObject();
            long before = longInteger(edge, "beforeEventId", 0L);
            long after = longInteger(edge, "afterEventId", 0L);
            if (!EDGE_KINDS.contains(string(edge, "edgeKind"))) {
                return "order edge " + before + "->" + after
                        + " has no declared kind";
            }
            if (before <= 0L || after <= 0L || before == after) {
                return "order edge " + before + "->" + after
                        + " is not between two distinct events";
            }
            if (!eventIds.contains(before) || !eventIds.contains(after)) {
                return "order edge " + before + "->" + after
                        + " names an event the ledger does not hold";
            }
        }
        if (bool(envelope, "truncated", false)) {
            // The event log dropped its oldest entries, so an edge endpoint
            // may be missing and the relation is not the run's whole one.
            return "ledger event log is truncated";
        }
        return "";
    }

    /**
     * <p>README {@code EVENT-1}: selected ledger truncation and saturation
     */
    public static int ledgerFaultStatus(JsonObject envelope, String fault) {
        if (fault == null || fault.isEmpty()) return OK;
        if (envelope != null) {
            if (bool(envelope, "domainSaturated", false)) {
                return LEDGER_DOMAIN_SATURATED;
            }
            if (bool(envelope, "truncated", false)) {
                return LEDGER_LOG_TRUNCATED;
            }
        }
        return MALFORMED_ENVELOPE;
    }

    /** Wraps one admitted ledger envelope as a recorded evidence row. */
    public static JsonObject ledgerRecord(JsonObject envelope,
                                          RecordedEvidenceIdentity identity) {
        JsonObject record = new JsonObject();
        record.addProperty("kind", LEDGER_RECORD_KIND);
        record.addProperty("schemaVersion", RECORD_SCHEMA_VERSION);
        record.addProperty("authority", RECORD_AUTHORITY);
        record.addProperty("eventCount", array(envelope, "events").size());
        record.addProperty("edgeCount", array(envelope, "order").size());
        record.add("envelope", envelope.deepCopy());
        if (identity != null) identity.stamp(record);
        return record;
    }

    /** Whether {@code row} is an admitted ledger record. */
    public static boolean isLedgerRecord(JsonObject row) {
        return row != null
                && LEDGER_RECORD_KIND.equals(string(row, "kind"))
                && RECORD_AUTHORITY.equals(string(row, "authority"))
                && integer(row, "schemaVersion", -1) == RECORD_SCHEMA_VERSION
                && RecordedEvidenceIdentity.stamped(row)
                && ledgerFault(object(row, "envelope")).isEmpty();
    }


    public static JsonObject recorded(Collection<JsonObject> versionRecords,
                                      JsonObject ledgerRecord) {
        JsonArray versions = new JsonArray();
        if (versionRecords != null) {
            for (JsonObject record : versionRecords) {
                if (isVersionsRecord(record)) versions.add(record.deepCopy());
            }
        }
        boolean admittedLedger = isLedgerRecord(ledgerRecord);
        if (versions.size() == 0 && !admittedLedger) {
            return new JsonObject();
        }
        JsonObject recorded = new JsonObject();
        recorded.addProperty("schemaVersion", SCHEMA_VERSION);
        recorded.addProperty("kind", RECORDED_KIND);
        recorded.addProperty("authority", RECORD_AUTHORITY);
        recorded.add("versions", versions);
        if (admittedLedger) {
            recorded.add("eventLedger", ledgerRecord.deepCopy());
        }
        return recorded;
    }

    // README EVENT-1 forbids a cross-session event-id or snapshot merge, and

    /** Whether {@code candidate} is the later snapshot of the two. */
    public static boolean later(JsonObject candidate, JsonObject held) {
        return held == null
                || RecordedEvidenceIdentity.snapshotOrdinalOf(candidate)
                > RecordedEvidenceIdentity.snapshotOrdinalOf(held);
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
                string(node, "expressionAuthority"))) {
            return "guarded read carries no VM authority";
        }
        if (!RESOLUTION_GUARDED.equals(string(node, "resolution"))) {
            return "guarded read does not declare a guarded resolution";
        }
        if (!READ_REASONS.contains(string(node, "reason"))) {
            return "guarded read has no declared reason";
        }
        long readEvent = longInteger(node, "readEventId", 0L);
        if (readEvent <= 0L) return "guarded read has no readEventId";
        if (locationKey(node).isEmpty()) {
            return "guarded read names no addressable location";
        }
        if (!node.has("writerSetComplete")) {
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
        int unknownArms = 0;
        for (int index = 0; index < candidates.size(); index++) {
            JsonElement element = candidates.get(index);
            if (!element.isJsonObject()) return "candidate is not an object";
            JsonObject candidate = element.getAsJsonObject();
            String selector = string(candidate, "selector");
            if (selector.isEmpty()) return "candidate has no selector";
            if (!seen.add(selector)) {
                return "duplicate candidate selector " + selector;
            }
            if (!selector.equals(selectorName(selectors, index))) {
                return "exactlyOne selector " + index
                        + " does not name its candidate";
            }
            String fault = candidateFault(candidate, readEvent, index,
                    candidates.size());
            if (!fault.isEmpty()) return fault;
            if (bool(candidate, "unknown", false)) unknownArms++;
        }
        if (unknownArms != 1) {
            return "guarded read must carry exactly one unknown-writer arm";
        }
        if (!bool(candidates.get(candidates.size() - 1).getAsJsonObject(),
                "unknown", false)) {
            return "unknown-writer arm is not the final ite arm";
        }
        if (node.get("ite") == null || node.get("ite").isJsonNull()) {
            return "guarded read carries no selection term";
        }
        if (containsVmSerializationTruncation(node.get("ite"))) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": guarded read selection term";
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
                                         long readEvent, int index,
                                         int total) {
        String selector = string(candidate, "selector");
        boolean unknown = bool(candidate, "unknown", false);
        long version = longInteger(candidate, "fieldVersionId", 0L);
        if (unknown) {
            if (!UNKNOWN_WRITER_SELECTOR.equals(selector)) {
                return "unknown arm is not named " + UNKNOWN_WRITER_SELECTOR;
            }
            if (version != 0L) {
                return "unknown arm names a recorded write";
            }
            if (index + 1 != total) {
                return "unknown arm is not the last candidate";
            }
        } else if (version <= 0L) {
            return "candidate " + selector + " names no recorded write";
        }
        JsonElement value = candidate.get("expression");
        if (value == null || value.isJsonNull()) {
            return "candidate " + selector + " carries no value expression";
        }
        if (containsVmSerializationTruncation(value)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": candidate " + selector + " value expression";
        }
        if (containsVmSerializationTruncation(candidate.get("pathGuard"))) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": candidate " + selector + " path guard";
        }
        JsonArray constraints = array(candidate, "orderConstraints");
        if (constraints.size() == 0) {
            return "candidate " + selector + " carries no read cut";
        }
        boolean sawCut = false;
        for (JsonElement element : constraints) {
            if (!element.isJsonObject()) {
                return "order constraint is not an object";
            }
            JsonObject constraint = element.getAsJsonObject();
            String kind = string(constraint, "kind");
            if (!ORDER_CONSTRAINT_KINDS.contains(kind)) {
                return "candidate " + selector
                        + " carries an undeclared order constraint " + kind;
            }
            if ("WRITE_BEFORE_READ".equals(kind)) {
                if (longInteger(constraint, "beforeEventId", 0L) != version
                        || longInteger(constraint, "afterEventId", 0L)
                        != readEvent) {
                    return "candidate " + selector
                            + " does not place its own write before the read";
                }
                sawCut = true;
            } else if ("UNKNOWN_WRITE_BEFORE_READ".equals(kind)) {
                if (!unknown || longInteger(constraint, "readEventId", 0L)
                        != readEvent) {
                    return "unknown cut does not name this read";
                }
                sawCut = true;
            } else if (longInteger(constraint, "selectedEventId", 0L)
                    != version
                    || longInteger(constraint, "readEventId", 0L)
                    != readEvent
                    || longInteger(constraint, "otherEventId", 0L) <= 0L) {
                return "candidate " + selector
                        + " carries a competitor cut for another read";
            }
        }
        return sawCut ? ""
                : "candidate " + selector + " never orders its own write";
    }

    /** Whether {@code node} is a guarded read-from node this layer admits. */
    public static boolean isGuardedRead(JsonObject node) {
        return guardedReadFault(node).isEmpty();
    }

    private static Set<String> names(String... values) {
        return Collections.unmodifiableSet(
                new LinkedHashSet<>(Arrays.asList(values)));
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }
}
