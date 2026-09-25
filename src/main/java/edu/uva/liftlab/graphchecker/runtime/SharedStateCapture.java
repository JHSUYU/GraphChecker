package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.textString;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.decodeVmEnvelope;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.parseJson;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

/**
 * The write log of one activation, read out by object.
 *
 * <p>The runtime names no locations: it asks the VM for every location the
 * session tracked at or after this activation's entry event and publishes
 * {@code location#version -> expression}, keyed by
 * {@code (kind, ownerSymRid, slot)} -- the same key the read nodes carry.</p>
 */
final class SharedStateCapture {
    /** Outcome of one recorded shared-state evidence call. */
    static final class SharedStateResult {
        private final String stage;
        private final int status;
        private final String locationKey;
        private final JsonObject record;

        private SharedStateResult(String stage, int status,
                                  String locationKey, JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.locationKey = safe(locationKey);
            this.record = record;
        }

        boolean ok() {
            return status == OK;
        }

        @Override
        public String toString() {
            return stage + "/" + status
                    + (locationKey.isEmpty() ? "" : " " + locationKey);
        }
    }

    private SharedStateCapture() {
    }

    /**
     * Reads out every location this activation touched, paging until the VM
     * says the answer is complete.  Called while the owner thread holds the VM
     * context; decoding is {@link #assembleRecordedSharedState}.  A short page
     * that names no resume point is a gap: a short write log reads as "never
     * written".
     */
    static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, ConcolicVmBroker api) {
        java.util.List<String> pages = new java.util.ArrayList<>();
        String fault = "";
        long after = active == null ? 0L : active.vmRegionEnterEventId;
        for (int page = 0; page < MAX_READ_OUT_PAGES; page++) {
            final String serialized;
            try {
                serialized = api.trackedLocationVersions(after,
                        READ_OUT_PAGE_BYTES);
            } catch (Throwable throwable) {
                fault = "tracked-location read-out failed: "
                        + rootCause(throwable);
                break;
            }
            pages.add(serialized);
            JsonElement parsed = parseJson(serialized);
            if (!parsed.isJsonObject()) {
                fault = "tracked-location read-out returned no JSON object";
                break;
            }
            JsonObject document = parsed.getAsJsonObject();
            if (optionalBool(document, "complete", false)) {
                return new RawSharedStateReadOut(pages, "");
            }
            long next = optionalLongInteger(document, "nextAfterEventId", 0L);
            if (next <= after) {
                fault = "a partial tracked-location read-out states no event "
                        + "to resume from after " + after;
                break;
            }
            after = next;
        }
        if (fault.isEmpty()) {
            fault = "tracked-location read-out did not complete in "
                    + MAX_READ_OUT_PAGES + " pages";
        }
        return new RawSharedStateReadOut(pages, fault);
    }

    /**
     * The most pages one read-out may take; hitting it is a stated gap, not a
     * truncation.  It stops a VM that never advances from hanging the run.
     */
    private static final int MAX_READ_OUT_PAGES = 4096;

    /** The byte budget of one page; the VM stops at a location boundary. */
    private static final int READ_OUT_PAGE_BYTES = 64 * 1024 * 1024;

    /** Decodes and files the read-out after the VM context is closed. */
    static void assembleRecordedSharedState(
            ActiveRegion active, RawSharedStateReadOut raw) {
        if (raw == null) return;
        if (!raw.fault.isEmpty()) {
            fileShared(failedShared(STAGE_VERSIONS,
                    MALFORMED_ENVELOPE, "", raw.fault),
                    active);
        }
        for (String serialized : raw.pages) {
            try {
                decodeTrackedLocations(serialized, active);
            } catch (Throwable throwable) {
                fileShared(failedShared(STAGE_VERSIONS,
                        MALFORMED_ENVELOPE, "",
                        rootCause(throwable)), active);
            }
        }
    }

    /**
     * One page of the read-out: envelopes over one per-document expression
     * table, imported once so every envelope resolves against it.
     */
    private static void decodeTrackedLocations(String serialized,
                                               ActiveRegion active) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            fileShared(failedShared(STAGE_VERSIONS,
                    MALFORMED_ENVELOPE, "",
                    "tracked-location read-out returned no JSON object"),
                    active);
            return;
        }
        JsonObject document = decodeVmEnvelope(parsed.getAsJsonObject(),
                active);
        if (!TRACKED_LOCATIONS_KIND.equals(optionalString(document, "kind"))) {
            fileShared(failedShared(STAGE_VERSIONS,
                    MALFORMED_ENVELOPE, "",
                    "unsupported tracked-location read-out schema"), active);
            return;
        }
        JsonArray locations = array(document, "locations");
        int stated = optionalInteger(document, "locationCount", -1);
        if (stated >= 0 && stated != locations.size()) {
            fileShared(failedShared(STAGE_VERSIONS,
                    MALFORMED_ENVELOPE, "",
                    "tracked-location read-out states " + stated
                            + " locations and carries " + locations.size()),
                    active);
            return;
        }
        for (JsonElement element : locations) {
            if (!element.isJsonObject()) {
                fileShared(failedShared(STAGE_VERSIONS,
                        MALFORMED_ENVELOPE, "",
                        "tracked location is not an object"), active);
                continue;
            }
            fileShared(decodeVersionsEnvelope(element.getAsJsonObject()),
                    active);
        }
    }

    static final String TRACKED_LOCATIONS_KIND = "SHARED_TRACKED_LOCATIONS";

    /** One tracked location's write log, or the fault that replaced it. */
    static SharedStateResult decodeVersionsEnvelope(JsonObject envelope) {
        String fault = versionsFault(envelope);
        if (!fault.isEmpty()) {
            return failedShared(STAGE_VERSIONS,
                    expressionSerializationTruncationFault(
                            fault)
                            ? EXPRESSION_SERIALIZATION_TRUNCATED
                            : containerBaseUnstatedFault(
                            fault)
                            ? CONTAINER_BASE_UNSTATED
                            : MALFORMED_ENVELOPE,
                    locationKey(envelope), fault);
        }
        String locationKey = locationKey(envelope);
        return new SharedStateResult(STAGE_VERSIONS,
                OK, locationKey,
                writeLogRecord(versionsRecord(
                        locationKey, envelope)));
    }

    /**
     * One location's write log: {@code location#version -> expression}, the
     * whole of what a replay says about shared state.
     *
     * <p>{@code fieldVersionId} is on the same session-global counter as the
     * decisions' {@code vmEventId}, so "latest write before this access" is a
     * comparison within one {@code sessionId} (the counter restarts per
     * session).  An INITIAL version stays, tagged, to keep "the program
     * computed this" apart from "the recording started after it".</p>
     */
    static JsonObject writeLogRecord(JsonObject record) {
        JsonObject envelope = edu.uva.liftlab.graphchecker.smt.JsonFields
                .object(record, "envelope");
        JsonObject published = new JsonObject();
        copyIfPresent(record, published, "kind");
        copyIfPresent(record, published, "authority");
        copyIfPresent(record, published, "locationKey");
        JsonObject publishedEnvelope = new JsonObject();
        copyIfPresent(envelope, publishedEnvelope, "kind");
        copyIfPresent(envelope, publishedEnvelope, "schemaVersion");
        copyIfPresent(envelope, publishedEnvelope, "sessionId");
        copyIfPresent(envelope, publishedEnvelope, "location");
        JsonArray versions = new JsonArray();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(version, entry, "fieldVersionId");
            copyIfPresent(version, entry, "versionKind");
            // Site and activation: the two halves of the WriteRow's
            // endpoint identity (IDENTITY-V3 sec 1); dropping them merges
            // distinct writes into one endpoint.
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            // A container INITIAL's base contents; every relation over the
            // container stands on it, and containerBaseFault re-reads it.
            copyIfPresent(version, entry, "initialSnapshot");
            copyIfPresent(version, entry, "expression");
            versions.add(entry);
        }
        publishedEnvelope.add("versions", versions);
        // The read log, by event id: it supplies the activation a
        // ReadFromExpression node does not name.  No value -- the node
        // already carries the version it observed.
        JsonArray reads = new JsonArray();
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(read, entry, "readEventId");
            copyIfPresent(read, entry, "regionEnterEventId");
            copyIfPresent(read, entry, "site");
            reads.add(entry);
        }
        publishedEnvelope.add("reads", reads);
        copyIfPresent(envelope, publishedEnvelope, "readLogTruncated");
        published.add("envelope", publishedEnvelope);
        return published;
    }

    private static void copyIfPresent(JsonObject from, JsonObject to,
                                      String field) {
        JsonElement value = from.get(field);
        if (value != null && !value.isJsonNull()) to.add(field, value);
    }

    /**
     * One refused location: no write version, stated as an UNSTATED_VALUE
     * diagnostic gap, since every read of it reaches the formula with no
     * read-from arm.
     */
    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .UNSTATED_VALUE,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                // A blank subject would refuse inside Fields.text.
                edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank(
                        safe(locationKey), safe(stage),
                        RowRuntime.sessionId()),
                reason(status) + ": " + safe(detail));
        return new SharedStateResult(stage, status, safe(locationKey), null);
    }

    /**
     * Files one admitted write log with the active region; a refusal already
     * filed its gap and publishes no record.
     */
    private static void fileShared(SharedStateResult result,
                                   ActiveRegion active) {
        if (active == null || !result.ok()) return;
        if (!result.locationKey.isEmpty()) {
            active.sharedStateRecords.put(result.locationKey, result.record);
        }
    }

    /** Raw read-out pages frozen before one VM region is finished. */
    static final class RawSharedStateReadOut {
        private final java.util.List<String> pages;
        private final String fault;

        private RawSharedStateReadOut(java.util.List<String> pages,
                                      String fault) {
            this.pages = pages;
            this.fault = fault;
        }
    }

    // ---- the VM's shared-state vocabulary (this decoder is its one reader)

    /** Schema of the VM envelopes and gap rows this vocabulary reads. */
    static final int SCHEMA_VERSION = 1;

    /** Schema of the admitted record wrappers this vocabulary produces. */
    private static final int RECORD_SCHEMA_VERSION = 2;

    /** Envelope kind of one selected location's version store. */
    private static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    /** Node type emitted where the VM serializer bounded one expression. */
    static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    /** Authority proving that a truncated node came from the VM serializer. */
    private static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    /** Kind of one admitted version-store record. */
    private static final String VERSIONS_RECORD_KIND =
            "VM_SHARED_FIELD_VERSIONS_V1";
    /** Authority stamped on admitted version records. */
    private static final String RECORD_AUTHORITY =
            "VM_SHARED_STATE_EVIDENCE_V1";

    static final String STAGE_VERSIONS = "VERSIONS";

    static final int OK = 0;

    /**
     * The one refusal this decoder raises on its own: an envelope it will not
     * admit.  Undeclared statuses read as {@link #UNDECLARED_REASON}.
     */
    static final int MALFORMED_ENVELOPE = -1002;
    /** One expression root was serialized only up to the VM's safety bound. */
    static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /**
     * A container's INITIAL version states no base contents, so every read of
     * it (base plus mutation chain) stands on nothing.  The gap names the
     * class the VM has no walker for, because that is the fix.
     */
    static final int CONTAINER_BASE_UNSTATED = -1012;

    /** Exact coverage reason for a VM-bounded expression tree. */
    static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    private static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    /** Location kind of one selected map's whole immutable state. */
    static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    /** The reserved slot of a whole-state location. */
    static final int MAP_STATE_SLOT = -3;

    private static final Set<String> LOCATION_KINDS = names("INSTANCE_FIELD",
            "STATIC_FIELD", "ARRAY_ELEMENT", LOCATION_KIND_MAP_STATE);
    /**
     * Kinds of published version a location may carry: the VM's
     * {@code STATE_<operation>} vocabulary (SharedFieldVersions::version_label).
     * Trap: an operation missing here fails the whole envelope, so the
     * location loses every version.
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "STATE", "STATE_PUT", "STATE_REMOVE", "STATE_REMOVE_IF",
            "STATE_CLEAR", "STATE_REMOVE_AT", "STATE_CLEAR_VIEW",
            "STATE_ADD", "STATE_APPEND", "STATE_INSERT", "STATE_WRITE");
    /** The version kind every location may publish, whatever its shape. */
    private static final String INITIAL_VERSION_KIND = "INITIAL";

    static String reason(int status) {
        switch (status) {
            case OK:
                return "";
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

    /** Whether an expression tree contains the VM's truncation marker. */
    static boolean containsVmSerializationTruncation(
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
    static boolean expressionSerializationTruncationFault(
            String fault) {
        return fault != null
                && (VM_EXPRESSION_SERIALIZATION_TRUNCATED.equals(fault)
                || fault.startsWith(
                VM_EXPRESSION_SERIALIZATION_TRUNCATED + ":"));
    }

    /** The location key one version-store envelope describes. */
    static String locationKey(JsonObject envelope) {
        return locationKeyOf(object(envelope, "location"));
    }

    /**
     * The same key for any VM location node: the one spelling and admission
     * shared by write envelopes and read nodes.  An undeclared kind, a zero
     * owner rid, an absent slot, or a whole-state location off the reserved
     * slot names no location ({@code ""}).
     */
    static String locationKeyOf(JsonObject location) {
        if (location == null || location.size() == 0) return "";
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

    /**
     * The contract location one VM location key names, or {@code null}.  No
     * default kind: defaulting to {@code INSTANCE} makes a read that joins
     * nothing.
     */
    static edu.uva.liftlab.graphchecker.contract.LocationId locationId(
            String locationKey) {
        String key = safe(locationKey);
        int separator = key.indexOf('/');
        int slot = key.lastIndexOf('#');
        if (separator <= 0 || slot <= separator) return null;
        String kind = key.substring(0, separator);
        edu.uva.liftlab.graphchecker.contract.LocationKind declared;
        if ("INSTANCE_FIELD".equals(kind)) {
            declared = edu.uva.liftlab.graphchecker.contract
                    .LocationKind.INSTANCE;
        } else if ("STATIC_FIELD".equals(kind)) {
            declared = edu.uva.liftlab.graphchecker.contract
                    .LocationKind.STATIC;
        } else if ("ARRAY_ELEMENT".equals(kind)) {
            declared = edu.uva.liftlab.graphchecker.contract
                    .LocationKind.ARRAY;
        } else if (LOCATION_KIND_MAP_STATE.equals(kind)) {
            declared = edu.uva.liftlab.graphchecker.contract
                    .LocationKind.MAP;
        } else {
            return null;
        }
        return edu.uva.liftlab.graphchecker.contract.LocationId.of(declared,
                key.substring(separator + 1, slot), key.substring(slot + 1));
    }

    /** The declared kind of one location key, or "". */
    static String locationKindOf(String locationKey) {
        if (locationKey == null) return "";
        int separator = locationKey.indexOf('/');
        if (separator <= 0) return "";
        String kind = locationKey.substring(0, separator);
        return LOCATION_KINDS.contains(kind) ? kind : "";
    }

    /** Whether {@code locationKey} names one selected map's whole state. */
    static boolean isMapState(String locationKey) {
        return LOCATION_KIND_MAP_STATE.equals(locationKindOf(locationKey));
    }

    /** Whether {@code versionKind} publishes one immutable whole state. */
    static boolean stateVersionKind(String versionKind) {
        return versionKind != null && (versionKind.equals("STATE")
                || versionKind.startsWith("STATE_"));
    }

    /** Admits one version-store envelope: {@code ""} or the refusal reason. */
    static String versionsFault(JsonObject envelope) {
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
            // Selection publishes an INITIAL, so empty means no selection.
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
     * Why a container's INITIAL version states no base, or {@code ""}.  A
     * missing snapshot is an older VM image; {@code stated:false} means no
     * walker for the class.
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
    static final String CONTAINER_BASE_UNSTATED_FAULT =
            "CONTAINER_BASE_UNSTATED";

    /** Whether {@code fault} is an unstated container base. */
    static boolean containerBaseUnstatedFault(String fault) {
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
            // Explicit null is the empty conjunction; absent is uncaptured.
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

    static JsonObject versionsRecord(String locationKey,
                                            JsonObject envelope) {
        JsonObject record = new JsonObject();
        record.addProperty("kind", VERSIONS_RECORD_KIND);
        record.addProperty("schemaVersion", RECORD_SCHEMA_VERSION);
        record.addProperty("authority", RECORD_AUTHORITY);
        record.addProperty("locationKey", text(locationKey));
        record.add("envelope", envelope);
        return record;
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
