package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.d3.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.FieldPathSpec;

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

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.textString;

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
    public static final int SELECT_FIELD_NOT_FOUND = -3;
    public static final int SELECT_UNSUPPORTED_TARGET = -4;
    public static final int INVOCATION_FAILED = -1001;
    public static final int MALFORMED_ENVELOPE = -1002;
    /** One expression root was serialized only up to the VM's safety bound. */
    public static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /**
     * A container's INITIAL version does not state the contents tracking
     * began from.
     *
     * <p>A container relation resolves as its base plus the mutation chain,
     * so a base the VM could not state leaves every read of that container
     * standing on nothing.  The VM walks a container at the first symbolic
     * access to it; when it has no walker for the class it says so, and the
     * class name travels in the gap because that is the fix.</p>
     */
    public static final int CONTAINER_BASE_UNSTATED = -1012;

    /** Exact coverage reason for a VM-bounded expression tree. */
    public static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    public static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";


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
     * {@code REMOVE} and {@code CLEAR} for a set, and {@code APPEND},
     * {@code INSERT}, {@code WRITE}, {@code REMOVE} and {@code CLEAR} for an
     * indexed container.  An operation missing here is not a tolerated
     * unknown: one unadmitted version fails the whole envelope, so the
     * location loses every version it published and each read of it reaches
     * the formula with no read-from arm.
     * {@code REMOVE_IF} represents an iterator removal controlled by a
     * recorded branch predicate.</p>
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "STATE", "STATE_PUT", "STATE_REMOVE", "STATE_REMOVE_IF",
            "STATE_CLEAR", "STATE_REMOVE_AT", "STATE_CLEAR_VIEW",
            "STATE_ADD", "STATE_APPEND", "STATE_INSERT", "STATE_WRITE");
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
            case SELECT_FIELD_NOT_FOUND:
                return REASON_PREFIX + "FIELD_NOT_FOUND";
            case SELECT_UNSUPPORTED_TARGET:
                return REASON_PREFIX + "UNSUPPORTED_TARGET";
            case INVOCATION_FAILED:
                return REASON_PREFIX + "INVOCATION_FAILED";
            case MALFORMED_ENVELOPE:
                return REASON_PREFIX + "MALFORMED_ENVELOPE";
            case EXPRESSION_SERIALIZATION_TRUNCATED:
                return VM_EXPRESSION_SERIALIZATION_TRUNCATED;
            case CONTAINER_BASE_UNSTATED:
                return REASON_PREFIX + "CONTAINER_BASE_UNSTATED";
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

    /**
     * Whether one expression node is the STATE root of a container whose
     * whole state a carrier versions.
     *
     * <p>Both whole-state shapes answer yes.  An indexed root that answered
     * no would keep its session-local symbol instead of the content address
     * runtime carrier evidence gives it, and one logical container would
     * then be a different witness in every replay session.</p>
     */
    public static boolean isWholeStateRoot(JsonObject node) {
        if (node == null) return false;
        String shape = optionalString(node, "shape");
        return "ContainerRelation".equals(optionalString(node, "_type"))
                && "STATE".equals(optionalString(node, "operation"))
                && ("ASSOCIATIVE".equals(shape) || "INDEXED".equals(shape));
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

    /**
     * Why a container's INITIAL version states no base, or {@code ""}.
     *
     * <p>Only a container has one: a scalar's INITIAL is the value the field
     * held, which the expression already carries.  A container's is the
     * contents tracking began from, which the VM walks at the first symbolic
     * access, and every relation over that container stands on it.  An
     * INITIAL that carries no snapshot member at all is an older image; one
     * that says {@code stated:false} is this image telling us it has no
     * walker for the class, and the class name is in the gap because naming
     * it is what gets it walked.</p>
     */
    private static String containerBaseFault(JsonObject version,
                                             String versionKind,
                                             boolean mapState) {
        if (!mapState || !INITIAL_VERSION_KIND.equals(versionKind)) return "";
        JsonElement encoded = version.get("initialSnapshot");
        if (encoded == null || !encoded.isJsonObject()) {
            return CONTAINER_BASE_UNSTATED_FAULT
                    + ": INITIAL states no container base";
        }
        JsonObject snapshot = encoded.getAsJsonObject();
        if (!snapshot.has("stated")
                || optionalBool(snapshot, "stated", false)) {
            return "";
        }
        String unsupported = optionalString(snapshot, "unsupportedClass");
        return CONTAINER_BASE_UNSTATED_FAULT + ": the VM walks no container "
                + "of class " + (unsupported.isEmpty() ? "<unnamed>"
                : unsupported);
    }

    /** Fault prefix that maps to {@link #CONTAINER_BASE_UNSTATED}. */
    public static final String CONTAINER_BASE_UNSTATED_FAULT =
            "CONTAINER_BASE_UNSTATED";

    /** Whether {@code fault} is an unstated container base. */
    public static boolean containerBaseUnstatedFault(String fault) {
        return fault != null && fault.startsWith(CONTAINER_BASE_UNSTATED_FAULT);
    }

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
        String base = containerBaseFault(version, versionKind, mapState);
        if (!base.isEmpty()) return base;
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

    /** Whether {@code row} is an admitted write log. */
    public static boolean isVersionsRecord(JsonObject row) {
        return writeLogFault(row).isEmpty();
    }

    /**
     * Why one published write log cannot be read, or {@code ""}.
     *
     * <p>{@link #versionsFault} is the recording side's contract: it runs on
     * the VM envelope, which states the selection, the writer case behind
     * every version, the read log and the truncation flags.  A replay
     * publishes none of that -- it publishes the write log, {@code
     * location#version -> expression} -- because a read inside one replay is
     * determined and needs only the version it observed and the expression
     * written at it.  So this side admits on exactly that: an addressable
     * location, and per version an id, a declared kind and an untruncated
     * value.  Requiring the recording's members here refuses every write log
     * the runtime publishes and leaves every read unresolved.</p>
     */
    public static String writeLogFault(JsonObject row) {
        if (row == null) return "no write log";
        if (!VERSIONS_RECORD_KIND.equals(optionalString(row, "kind"))
                || !RECORD_AUTHORITY.equals(
                optionalString(row, "authority"))) {
            return "row is not an authoritative write log";
        }
        if (optionalString(row, "locationKey").isEmpty()) {
            return "write log names no location";
        }
        JsonObject envelope = object(row, "envelope");
        if (!VERSIONS_ENVELOPE_KIND.equals(optionalString(envelope, "kind"))
                || optionalInteger(envelope, "schemaVersion", -1)
                != SCHEMA_VERSION) {
            return "envelope is not an authoritative version store";
        }
        if (locationKey(envelope).isEmpty()) {
            return "envelope names no addressable location";
        }
        JsonElement versionsMember = envelope.get("versions");
        if (versionsMember == null || !versionsMember.isJsonArray()) {
            return "envelope carries no version array";
        }
        JsonArray versions = versionsMember.getAsJsonArray();
        if (versions.size() == 0) {
            return "selected location published no version";
        }
        boolean mapState = isMapState(locationKey(envelope));
        Set<Long> versionIds = new LinkedHashSet<>();
        for (JsonElement element : versions) {
            if (!element.isJsonObject()) return "version is not an object";
            JsonObject version = element.getAsJsonObject();
            String fault = writtenVersionFault(version, mapState);
            if (!fault.isEmpty()) return fault;
            if (!versionIds.add(optionalLongInteger(version,
                    "fieldVersionId", 0L))) {
                return "duplicate fieldVersionId "
                        + optionalLongInteger(version, "fieldVersionId", 0L);
            }
        }
        return "";
    }

    /** Admits one version of a published write log. */
    private static String writtenVersionFault(
            JsonObject version, boolean mapState) {
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
        JsonElement expression = version.get("expression");
        if (expression == null || expression.isJsonNull()) {
            return "version " + id + " carries no value expression";
        }
        if (containsVmSerializationTruncation(expression)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " value expression";
        }
        return "";
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
