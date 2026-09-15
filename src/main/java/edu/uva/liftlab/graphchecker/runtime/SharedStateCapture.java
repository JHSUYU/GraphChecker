package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;

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
 * <p>A location is tracked because a symbolic value reached it, and the VM
 * files it under the identity of the object actually written.  So the runtime
 * does not name locations at all: it asks for every location the session
 * tracked at or after this activation's entry event, and publishes what comes
 * back.  {@code location#version -> expression}, keyed by
 * {@code (kind, ownerSymRid, slot)} -- the same key the read nodes carry.</p>
 *
 * <p>What this replaces is a whole layer.  The runtime used to declare which
 * locations were worth versioning, select each one in the VM by its declaring
 * class, field and descriptor, and then invent a receiver identity that would
 * survive into the next session, because the VM's own was session-local and
 * the declaration was the only thing both sides shared.  Every part of that
 * existed to answer "which program location is this a version of", and under
 * by-value retention nothing asks: the object is the answer, the VM states
 * it, and a read resolves inside the session that produced it.</p>
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
     * says the answer is complete.
     *
     * <p>Called while the owner thread still holds the VM context; decoding
     * happens afterwards, in {@link #assembleRecordedSharedState}.  A page
     * that stops short states where to resume, and the loop resumes there; a
     * page that stops short and does not say where is a gap, because a write
     * log short of the truth reads as "the location was never written".</p>
     */
    static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, ConcolicVmBroker api) {
        java.util.List<String> pages = new java.util.ArrayList<>();
        String fault = "";
        // The activation's own entry event scopes the read-out: every
        // location tracked at or after it is one this activation touched.
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
     * The most pages one activation's read-out may take.
     *
     * <p>Not a cap on what is published: every page is published, and a
     * read-out that has not finished by here is a stated gap rather than a
     * silent truncation.  It exists so a VM that answers without advancing
     * ends the loop instead of the run.</p>
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
     * One page of the read-out: a document of envelopes over one expression
     * table.
     *
     * <p>The table is per document, so the whole document is imported once
     * and every envelope's references resolve against it.  Each envelope is
     * then exactly the one the VM emits for a single location, and is
     * admitted by the same contract that admitted it before.</p>
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
     * One location's write log: {@code location#version -> expression}.
     *
     * <p>This is the whole of what a replay says about shared state.  A read
     * inside one replay is determined -- the location had one version when
     * the read ran and one event wrote it -- so the reader needs the version
     * and the expression written at it, and nothing else.</p>
     *
     * <p>The name is the object.  The VM files a version under the identity
     * of the object it was written to, states that identity in the location
     * key, and the read nodes carry the same one, so a read and a write meet
     * without anything in between having to agree about a declaration.  The
     * carrier block that used to travel with every record -- declaring class,
     * field, descriptor, and a receiver identity synthesised to survive into
     * the next session -- named a location for a reader that no longer
     * exists.</p>
     *
     * <p>The version clock is {@code fieldVersionId}, drawn from the
     * session-global event counter at the moment of publish, which is the
     * counter the decisions' {@code vmEventId} is on.  So "the latest write
     * whose event precedes this access" is a comparison between the two,
     * within one {@code sessionId} -- the counter restarts at session
     * teardown, which is why the session is stated.</p>
     *
     * <p>An INITIAL version stays, tagged as one: a value the recording did
     * not watch being produced is still the value, and saying which kind it
     * is keeps "the program computed this" apart from "the recording started
     * after it".  Its content now arrives from the VM, which snapshots a
     * container at the first symbolic write to it; the runtime used to offer
     * that snapshot itself, one declared container at a time.</p>
     */
    private static JsonObject writeLogRecord(JsonObject record) {
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
            // Where the store stood, and which region activation it ran
            // inside: the two halves of the WriteRow's endpoint identity
            // (IDENTITY-V3 sec 1).  The reduction dropped both, so every
            // write endpoint published its location as a site and the empty
            // site index while the VM had stated the bytecode site
            // (REPORT-VM21) and the entry event of the activation -- four
            // reads of one location inside one occurrence were then one
            // endpoint.  Small and bounded: four strings and a long.
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            // A container's INITIAL states the contents tracking began from,
            // and every relation over that container stands on them.  The
            // reduction dropped it, so the corpus could not say whether a
            // base was stated, enumerated or truncated -- and an offline
            // re-drive of the admission that reads it
            // (containerBaseFault) had nothing to read.
            // It is one small object per container INITIAL.
            copyIfPresent(version, entry, "initialSnapshot");
            copyIfPresent(version, entry, "expression");
            versions.add(entry);
        }
        publishedEnvelope.add("versions", versions);
        // The read log, by event id.  A ReadFromExpression node names the
        // read event it is and the site it stood at, but not the activation
        // that ran it; the log record of the same event does, and that is
        // what files the read under a frame journal.  No value travels with
        // it -- the node already carries the version it observed.
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

    /** The reduction, for a test that pins what a version publishes. */
    static JsonObject reduceWriteLogForTest(JsonObject record) {
        return writeLogRecord(record);
    }

    private static void copyIfPresent(JsonObject from, JsonObject to,
                                      String field) {
        JsonElement value = from.get(field);
        if (value != null && !value.isJsonNull()) to.add(field, value);
    }

    /**
     * One refused location: it publishes no write version, and the refusal is
     * stated through the one gap vocabulary rather than onto an artifact.
     *
     * <p>Every read of the location reaches the formula with no read-from
     * arm, which is exactly what UNSTATED_VALUE names.  It is a diagnostic:
     * the rows the run did publish still say what they observed.</p>
     */
    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .UNSTATED_VALUE,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                safe(locationKey).isEmpty() ? safe(stage) : safe(locationKey),
                reason(status) + ": " + safe(detail));
        return new SharedStateResult(stage, status, safe(locationKey), null);
    }

    /**
     * Files one admitted write log with the active region.  A refusal named
     * itself as a gap row when it was built, and publishes no record: a
     * location with no version is a read the formula meets with no arm, not
     * a location with a wrong one.
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

    // ---- the VM's shared-state vocabulary ----------------------------
    //
    // It used to be plan/SharedStateEvidence, a published contract beside a
    // published artifact.  R1 deleted the artifact; what the vocabulary
    // describes is the envelope THIS decoder reads, and nothing outside it
    // asks any of these questions, so it lives here with its one reader.

    /** Schema of the VM envelopes and gap rows this vocabulary reads. */
    static final int SCHEMA_VERSION = 1;

    /**
     * Schema of the admitted record wrappers this vocabulary produces.
     */
    static final int RECORD_SCHEMA_VERSION = 2;

    /**
     * Envelope kind of one selected location's version store.
     */
    static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    /** Node type emitted where the VM serializer bounded one expression. */
    static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    /** Authority proving that a truncated node came from the VM serializer. */
    static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    /** Kind of one admitted version-store record. */
    static final String VERSIONS_RECORD_KIND =
            "VM_SHARED_FIELD_VERSIONS_V1";
    /** Authority stamped on admitted version records. */
    static final String RECORD_AUTHORITY =
            "VM_SHARED_STATE_EVIDENCE_V1";

    static final String STAGE_VERSIONS = "VERSIONS";

    static final int OK = 0;

    // Declared VM carrier-selection refusals (sharedFieldVersions.hpp).
    // Their numeric values are mirrored here so Java reports the same reason.
    static final int SELECT_NO_ACTIVE_CONTEXT = -1;
    static final int SELECT_FIELD_NOT_FOUND = -3;
    static final int SELECT_UNSUPPORTED_TARGET = -4;
    static final int INVOCATION_FAILED = -1001;
    static final int MALFORMED_ENVELOPE = -1002;
    /** One expression root was serialized only up to the VM's safety bound. */
    static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
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
    static final int CONTAINER_BASE_UNSTATED = -1012;

    /** Exact coverage reason for a VM-bounded expression tree. */
    static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    /** Location kind of one selected map's whole immutable state. */
    static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    /**
     * The reserved slot of a whole-state location.
     */
    static final int MAP_STATE_SLOT = -3;

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

    static String reason(int status) {
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

    /**
     * Whether an expression tree recursively contains the VM's explicit
     */
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

    /**
     * Names the location one version-store envelope describes, as the VM's
     */
    static String locationKey(JsonObject envelope) {
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

    /**
     * Admits one version-store envelope, answering "" or the exact reason it
     */
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
