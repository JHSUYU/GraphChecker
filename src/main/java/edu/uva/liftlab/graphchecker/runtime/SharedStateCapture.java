package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.smt.VmRows;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.decodeVmRecords;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.members;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.textString;

/**
 * The write log of one activation, read out by object.
 *
 * <p>The runtime names no locations: it asks the VM for every location the
 * session tracked at or after this activation's entry event and publishes
 * {@code location#version -> expression}, keyed by
 * {@code (kind, ownerSymRid, slot)} -- the same key the read nodes carry.</p>
 */
final class SharedStateCapture {
    private SharedStateCapture() {
    }

    /**
     * Reads out every location this activation touched, paging until the VM
     * says the answer is complete.  Called while the owner thread holds the VM
     * context.  Each page goes to the publication thread as soon as it is
     * read ({@link SharedStateReadOut#decodeLater}), where it is decoded
     * while the next is read and ahead of this activation's publication,
     * which that thread runs later, in order; no page waits for the rest of
     * the read-out, and none outlives its decoding (SB12's obligation
     * replay held 8 pages, 220 MB, a fifth of its live heap at its peak,
     * awaiting decoding once the region closed).  The next page is read
     * once this one is handed on, which waits for room among those still
     * undecoded ({@code ConcolicResultPublisher#decodeBeforePublication}).
     * A short page that names no resume point is a gap: a short write log
     * reads as "never written".
     */
    static SharedStateReadOut captureRecordedSharedState(
            ActiveRegion active, ConcolicVmBroker api) {
        SharedStateReadOut readOut = new SharedStateReadOut();
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
            if (!readOut.decodeLater(serialized, active)) {
                fault = "a tracked-location read-out page could not be"
                        + " handed to the publication thread";
                break;
            }
            JsonObject header = pageHeader(serialized);
            if (header == null) {
                fault = "tracked-location read-out returned no JSON object";
                break;
            }
            if (optionalBool(header, COMPLETE, false)) {
                return readOut;
            }
            long next = optionalLongInteger(header, NEXT_AFTER_EVENT_ID, 0L);
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
        readOut.fault = fault;
        return readOut;
    }

    /** A page's members that say whether it is the last, and where the
     *  next one resumes. */
    private static final String COMPLETE = "complete";
    private static final String NEXT_AFTER_EVENT_ID = "nextAfterEventId";

    /**
     * What one page says of itself ({@link #COMPLETE},
     * {@link #NEXT_AFTER_EVENT_ID}), streamed off its top-level members
     * ({@link ConcolicRegionRuntime#members}): the locations before them
     * are skipped and the expression table after them is not read.  The
     * owner thread holds the VM context meanwhile; parsed whole, a 64 MB
     * page took it eight times as long.  A blank page says nothing; null
     * when it is no JSON object.
     */
    static JsonObject pageHeader(String serialized) {
        return members(serialized, COMPLETE, NEXT_AFTER_EVENT_ID);
    }

    /**
     * The most pages one read-out may take; hitting it is a stated gap, not a
     * truncation.  It stops a VM that never advances from hanging the run.
     */
    private static final int MAX_READ_OUT_PAGES = 4096;

    /**
     * The byte budget of one page; the VM stops at a location boundary, and
     * every page repeats the expression closure its locations share.
     * Measured (solr-18406's V17 seed replay; SB12's obligation
     * 0a1a085e98d056aa, whose read-outs are 50-60 MB): at 64 MB the seed
     * peaked at 328 MB live after a full collection, at 16 and 8 MB at 229
     * and 225; the obligation at 1480, 1290 and 1145 MB, reading 1.6 and 2
     * times 64 MB's text.  Below one location's closure every page repeats
     * it: the seed at 4 MB read 20 times its text in 198 pages and passed
     * 2 GB resident, at 2 MB 4 GB.  16 MB keeps four times that away.
     */
    private static final int READ_OUT_PAGE_BYTES = 16 * 1024 * 1024;

    /**
     * Files what decoding the read-out refused, at the activation's
     * publication, where its pages' decoding used to run: the read-out's
     * fault, then each page's refusals in page order.  A publication that
     * is withheld files none of them, as one that never decoded.
     */
    static void assembleRecordedSharedState(
            ActiveRegion active, SharedStateReadOut readOut) {
        if (readOut == null) return;
        if (!readOut.fault.isEmpty()) {
            refuse(MALFORMED_ENVELOPE, "", readOut.fault);
        }
        for (Runnable refusal : readOut.refusals) refusal.run();
    }

    /**
     * One page of the read-out: location envelopes over the page's one
     * expression table, read one location at a time
     * ({@link ConcolicRegionRuntime#decodeVmRecords}), each filed as its
     * write log record; the page is never parsed or copied whole (a Solr
     * region's 52 MB page was its replay's largest tree).  A page that
     * states another kind or another location count than it carries files
     * nothing.
     */
    private static void decodeTrackedLocations(String serialized,
                                               ActiveRegion active) {
        // One page's versions share their subexpressions (one import): a
        // node scanned clean once is not scanned again.
        Set<JsonElement> clean = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        decodeVmRecords(serialized, LOCATIONS, active, header -> {
            if (!TRACKED_LOCATIONS_KIND.equals(
                    optionalString(header, "kind"))) {
                refuse(MALFORMED_ENVELOPE, "",
                        "unsupported tracked-location read-out schema");
                return false;
            }
            int stated = optionalInteger(header, "locationCount", -1);
            int carried = optionalInteger(header,
                    VmExpressionTable.RECORD_COUNT, -1);
            if (stated >= 0 && stated != carried) {
                refuse(MALFORMED_ENVELOPE, "",
                        "tracked-location read-out states " + stated
                                + " locations and carries " + carried);
                return false;
            }
            return true;
        }, element -> {
            if (!element.isJsonObject()) {
                refuse(MALFORMED_ENVELOPE, "",
                        "tracked location is not an object");
                return;
            }
            fileVersionsEnvelope(element.getAsJsonObject(), active, clean);
        });
    }

    /** The member a read-out page holds its location envelopes in. */
    private static final String LOCATIONS = "locations";

    private static final String TRACKED_LOCATIONS_KIND =
            "SHARED_TRACKED_LOCATIONS";

    /**
     * Files one tracked location's write log with the active region, or
     * names the fault that replaced it (and files nothing).
     */
    private static void fileVersionsEnvelope(JsonObject envelope,
                                             ActiveRegion active,
                                             Set<JsonElement> clean) {
        String fault = versionsFault(envelope, clean);
        String locationKey = locationKey(envelope);
        if (!fault.isEmpty()) {
            if (active != null && !locationKey.isEmpty()) {
                active.sharedStateRefusals.put(locationKey, fault);
            }
            refuse(expressionSerializationTruncationFault(fault)
                            ? EXPRESSION_SERIALIZATION_TRUNCATED
                            : containerBaseUnstatedFault(fault)
                            ? CONTAINER_BASE_UNSTATED
                            : MALFORMED_ENVELOPE,
                    locationKey, fault);
            return;
        }
        if (active != null && !locationKey.isEmpty()) {
            active.sharedStateRecords.put(locationKey,
                    writeLogRecord(locationKey, envelope));
        }
    }

    /**
     * One admitted location's write log, reduced to what the rows read:
     * {@code location#version -> expression} plus where each version and
     * read ran.
     *
     * <p>{@code fieldVersionId} is on the same session-global counter as the
     * decisions' {@code vmEventId}, so "latest write before this access" is a
     * comparison within one {@code sessionId} (the counter restarts per
     * session).</p>
     */
    static JsonObject writeLogRecord(String locationKey, JsonObject envelope) {
        JsonArray versions = new JsonArray();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(version, entry, "fieldVersionId");
            // Its kind: an INITIAL is a write row flagged as one.
            copyIfPresent(version, entry, "versionKind");
            // Site and activation: the two halves of the WriteRow's
            // endpoint identity (IDENTITY §4); dropping them merges
            // distinct writes into one endpoint.
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            copyIfPresent(version, entry, "expression");
            // A reference write's container state, or why none is stated.
            copyIfPresent(version, entry, REFERENT_STATE);
            copyIfPresent(version, entry, REFERENT_STATE_REFUSED);
            versions.add(entry);
        }
        // The read log, by event id: it supplies the activation a
        // ReadFromExpression node does not name, and states each read under
        // the node's names -- the version its plan chose and how far that
        // is the value it read -- so a read no published expression holds
        // is a row too (RowPublication#loggedReads).  No value: an exact
        // read returned its version's.
        JsonArray reads = new JsonArray();
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(read, entry, "readEventId");
            copyIfPresent(read, entry, "regionEnterEventId");
            copyIfPresent(read, entry, "site");
            copyIfPresent(read, entry, VmRows.OBSERVED_VERSION);
            copyIfPresent(read, entry, VmRows.OBSERVED_EXACT);
            copyIfPresent(read, entry, VmRows.WRITER_SET_COMPLETE);
            copyIfPresent(read, entry, VmRows.UNNAMED_WRITER);
            copyIfPresent(read, entry, "_java_type");
            reads.add(entry);
        }
        JsonObject kept = new JsonObject();
        kept.add("versions", versions);
        kept.add("reads", reads);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", locationKey);
        record.add("envelope", kept);
        return record;
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
    private static void refuse(int status, String locationKey,
                               String detail) {
        List<Runnable> deferred = DECODING.get();
        if (deferred != null) {
            deferred.add(() -> refuse(status, locationKey, detail));
            return;
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                // A blank subject would refuse inside Fields.text.
                firstNonBlank(safe(locationKey), STAGE_VERSIONS,
                        RowRuntime.sessionId()),
                reason(status) + ": " + safe(detail));
    }

    /**
     * The refusals of the page the publication thread is decoding, held for
     * its activation's publication ({@link #assembleRecordedSharedState}),
     * or null outside a page's decoding.
     */
    private static final ThreadLocal<List<Runnable>> DECODING =
            new ThreadLocal<List<Runnable>>();

    /**
     * One activation's read-out: its pages are decoded into the activation
     * on the publication thread as they are read; what is left for its
     * publication is what that decoding refused, and the read-out's fault.
     */
    static final class SharedStateReadOut {
        /** Written by the owner thread before the publication is queued. */
        private String fault = "";
        /** Appended to and read on the publication thread only. */
        private final List<Runnable> refusals = new ArrayList<>();

        /**
         * Queues one page's decoding on the publication thread, ahead of
         * this activation's publication, once the pages queued before it
         * leave room ({@code ConcolicResultPublisher
         * #decodeBeforePublication}).
         *
         * @return false when the publication thread refused the work
         */
        private boolean decodeLater(String page, ActiveRegion active) {
            return ConcolicResultPublisher.decodeBeforePublication(
                    page.length(), () -> {
                        DECODING.set(refusals);
                        try {
                            decodeTrackedLocations(page, active);
                        } catch (Throwable throwable) {
                            refuse(MALFORMED_ENVELOPE, "",
                                    rootCause(throwable));
                        } finally {
                            DECODING.remove();
                        }
                    });
        }
    }

    // ---- the VM's shared-state vocabulary (this decoder is its one reader)

    /**
     * Schema of the VM's version-store envelope this vocabulary reads: 2,
     * whose read log states each read's chosen version (VM.md §5.2).  An
     * envelope of another schema -- an image older than its jar -- is
     * refused by name, never read as a log of unversioned reads.
     */
    private static final int SCHEMA_VERSION = 2;

    /** Envelope kind of one selected location's version store. */
    private static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    /** Node type emitted where the VM serializer bounded one expression. */
    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    /** Authority proving that a truncated node came from the VM serializer. */
    private static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    static final String STAGE_VERSIONS = "VERSIONS";

    private static final int OK = 0;

    /**
     * The one refusal this decoder raises on its own: an envelope it will not
     * admit.  Undeclared statuses read as {@link #UNDECLARED_REASON}.
     */
    private static final int MALFORMED_ENVELOPE = -1002;
    /** One expression root was serialized only up to the VM's safety bound. */
    private static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    /**
     * A container's INITIAL version states no base contents, so every read of
     * it (base plus mutation chain) stands on nothing.  The gap names the
     * class the VM has no walker for, because that is the fix.
     */
    private static final int CONTAINER_BASE_UNSTATED = -1012;

    /** Exact coverage reason for a VM-bounded expression tree. */
    private static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    /** Reason used for any status this build does not declare. */
    private static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    /** Location kind of one selected map's whole immutable state. */
    private static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    /** The reserved slot of a whole-state location. */
    private static final int MAP_STATE_SLOT = -3;

    private static final Set<String> LOCATION_KINDS = names("INSTANCE_FIELD",
            "STATIC_FIELD", "ARRAY_ELEMENT", LOCATION_KIND_MAP_STATE);
    /**
     * Kinds of published version a location may carry: the VM's
     * {@code STATE_<operation>} vocabulary (SharedFieldVersions::version_label),
     * and UNOBSERVED: a word the read found that no hooked store left, which
     * names no writer.  Trap: an operation missing here fails the whole
     * envelope, so the location loses every version.
     */
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "UNOBSERVED", "STATE", "STATE_PUT", "STATE_PUT_IF",
            "STATE_PUT_ALL", "STATE_REMOVE", "STATE_REMOVE_IF", "STATE_CLEAR",
            "STATE_REMOVE_AT", "STATE_CLEAR_VIEW", "STATE_ADD",
            "STATE_APPEND", "STATE_INSERT", "STATE_WRITE", "STATE_POLL",
            "STATE_COLLECT", "STATE_ATTACH");
    /**
     * A reference write's container state (R3-REFCONT §1.1): {@code
     * {ownerSymRid, slot, locationKind: MAP_STATE, fieldVersionId}}, the
     * canonical container's location and its version live at the store;
     * or {@link #REFERENT_STATE_REFUSED}, why none is stated.  Only on a
     * WRITE or RMW of a field or an array element.
     */
    static final String REFERENT_STATE = "referentState";
    static final String REFERENT_STATE_REFUSED = "referentStateRefused";
    /** The version kind every location may publish, whatever its shape. */
    private static final String INITIAL_VERSION_KIND = "INITIAL";

    private static String reason(int status) {
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
    private static boolean containsVmSerializationTruncation(
            JsonElement expression, Set<JsonElement> clean) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(expression);
        while (!pending.isEmpty()) {
            JsonElement current = pending.pop();
            if (current != null && !current.isJsonNull()
                    && !current.isJsonPrimitive()
                    && (clean.contains(current)
                    || !visited.add(current))) continue;
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
        // Scanned whole and found clean: no later scan re-enters it.
        clean.addAll(visited);
        return false;
    }

    /** Whether {@code fault} names exactly this serializer-bound refusal. */
    private static boolean expressionSerializationTruncationFault(
            String fault) {
        return fault != null
                && (VM_EXPRESSION_SERIALIZATION_TRUNCATED.equals(fault)
                || fault.startsWith(
                VM_EXPRESSION_SERIALIZATION_TRUNCATED + ":"));
    }

    /** The location key one version-store envelope describes. */
    private static String locationKey(JsonObject envelope) {
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
    static LocationId locationId(
            String locationKey) {
        String key = safe(locationKey);
        int separator = key.indexOf('/');
        int slot = key.lastIndexOf('#');
        if (separator <= 0 || slot <= separator) return null;
        String kind = key.substring(0, separator);
        LocationKind declared;
        if ("INSTANCE_FIELD".equals(kind)) {
            declared = LocationKind.INSTANCE;
        } else if ("STATIC_FIELD".equals(kind)) {
            declared = LocationKind.STATIC;
        } else if ("ARRAY_ELEMENT".equals(kind)) {
            declared = LocationKind.ARRAY;
        } else if (LOCATION_KIND_MAP_STATE.equals(kind)) {
            declared = LocationKind.MAP;
        } else {
            return null;
        }
        return LocationId.of(declared,
                key.substring(separator + 1, slot), key.substring(slot + 1));
    }

    /** Whether {@code versionKind} publishes one immutable whole state. */
    private static boolean stateVersionKind(String versionKind) {
        return versionKind != null && (versionKind.equals("STATE")
                || versionKind.startsWith("STATE_"));
    }

    /** Admits one version-store envelope: {@code ""} or the refusal reason. */
    private static String versionsFault(JsonObject envelope,
                                        Set<JsonElement> clean) {
        if (envelope == null || envelope.size() == 0) {
            return "no version envelope";
        }
        if (!VERSIONS_ENVELOPE_KIND.equals(optionalString(envelope, "kind"))) {
            return "envelope is not an authoritative version store";
        }
        int schema = optionalInteger(envelope, "schemaVersion", -1);
        if (schema != SCHEMA_VERSION) {
            return "version store of schema " + schema + ", and this jar"
                    + " reads schema " + SCHEMA_VERSION + " (a VM image"
                    + " whose read log states no read's version?)";
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
        if (!booleanMember(envelope, "serializationTruncated")) {
            return "envelope omits version serialization completeness";
        }
        // Before the count: an envelope cut before its first version is
        // truncated, not empty.
        if (optionalBool(envelope, "serializationTruncated", false)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version envelope";
        }
        JsonArray versions = array(envelope, "versions");
        if (versions.size() == 0) {
            // Selection publishes an INITIAL, so empty means no selection.
            return "selected location published no version";
        }
        // A selected map's whole state (#locationKeyOf's spelling).
        boolean mapState = locationKey(envelope).startsWith(
                LOCATION_KIND_MAP_STATE + "/");
        Set<Long> versionIds = new LinkedHashSet<>();
        for (JsonElement element : versions) {
            if (!element.isJsonObject()) return "version is not an object";
            String fault = versionFault(element.getAsJsonObject(), mapState,
                    clean);
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
    private static final String CONTAINER_BASE_UNSTATED_FAULT =
            "CONTAINER_BASE_UNSTATED";

    /** Whether {@code fault} is an unstated container base. */
    private static boolean containerBaseUnstatedFault(String fault) {
        return fault != null && fault.startsWith(CONTAINER_BASE_UNSTATED_FAULT);
    }

    /**
     * Whether a version is its location's INITIAL: the value from before
     * every store the log names, which whichever access first observed the
     * location started its log with -- a scalar's word, a container's
     * members (the base its chain of mutations stands on).  No occurrence
     * wrote it (WriteRow#initial).
     */
    static boolean initial(JsonObject version) {
        return INITIAL_VERSION_KIND.equals(
                optionalString(version, "versionKind"));
    }

    /** Whether a version was stored outside every region: it names no
     *  writer context, region, task or activation at all. */
    static boolean unattributed(JsonObject version) {
        return optionalLongInteger(version, "writerContextId", 0L) == 0L
                && optionalLongInteger(version, "regionEnterEventId", 0L) == 0L
                && optionalString(version, "regionId").isEmpty()
                && optionalString(version, "taskId").isEmpty();
    }

    private static String versionFault(JsonObject version, boolean mapState,
                                       Set<JsonElement> clean) {
        long id = optionalLongInteger(version, "fieldVersionId", 0L);
        if (id <= 0L) return "version has no fieldVersionId";
        String versionKind = optionalString(version, "versionKind");
        if (!VERSION_KINDS.contains(versionKind)) {
            return "version " + id + " has kind \"" + versionKind
                    + "\", which this jar does not know (a VM image newer"
                    + " than its jar?)";
        }
        if (!INITIAL_VERSION_KIND.equals(versionKind)
                && stateVersionKind(versionKind) != mapState) {
            return "version " + id + " has kind " + versionKind
                    + " that its location kind does not publish";
        }
        // All three name the region that wrote it; none of them, a store
        // outside every region (a thread with no concolic context), which
        // is a version with no writer row.  Some of them is malformed.
        if (!unattributed(version)
                && (optionalLongInteger(version, "regionEnterEventId", 0L) <= 0L
                || optionalString(version, "regionId").isEmpty()
                || optionalString(version, "taskId").isEmpty())) {
            return "version " + id + " names no writer case";
        }
        if (!version.has("pathGuard")) {
            // Explicit null is the empty conjunction; absent is uncaptured.
            return "version " + id + " omits its writer path guard";
        }
        String base = containerBaseFault(version, versionKind, mapState);
        if (!base.isEmpty()) return base;
        String referent = referentFault(version, id, versionKind, mapState);
        if (!referent.isEmpty()) return referent;
        JsonElement expression = version.get("expression");
        if (expression == null || expression.isJsonNull()) {
            return "version " + id + " carries no value expression";
        }
        if (containsVmSerializationTruncation(expression, clean)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " value expression";
        }
        if (containsVmSerializationTruncation(version.get("pathGuard"),
                clean)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version " + id + " path guard";
        }
        return "";
    }

    /**
     * Why a version's referent members are malformed, or {@code ""}: they
     * belong to a WRITE or RMW of a field or an element, at most one of
     * them, and a state names a MAP_STATE location's version older than
     * this one.
     */
    private static String referentFault(JsonObject version, long id,
                                        String versionKind,
                                        boolean mapState) {
        JsonElement state = version.get(REFERENT_STATE);
        JsonElement refused = version.get(REFERENT_STATE_REFUSED);
        if (state == null && refused == null) return "";
        if (mapState || !("WRITE".equals(versionKind)
                || "RMW".equals(versionKind))) {
            return "version " + id + " of kind " + versionKind
                    + " states a referent";
        }
        if (state != null && refused != null) {
            return "version " + id + " states a referent and refuses it";
        }
        if (refused != null) {
            return refused.isJsonPrimitive()
                    && !refused.getAsString().trim().isEmpty() ? ""
                    : "version " + id + " refuses its referent by no name";
        }
        JsonObject named = state.isJsonObject() ? state.getAsJsonObject()
                : new JsonObject();
        long at = optionalLongInteger(named, "fieldVersionId", 0L);
        if (!locationKeyOf(named).startsWith(LOCATION_KIND_MAP_STATE + "/")
                || at <= 0L || at >= id) {
            return "version " + id + " states a referent that is no older "
                    + "MAP_STATE version";
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
        if (VmRows.recordedVersion(read) <= 0L
                || !booleanMember(read, VmRows.OBSERVED_EXACT)
                || !booleanMember(read, VmRows.WRITER_SET_COMPLETE)) {
            return "read " + readEvent + " states no version it observed";
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
}
