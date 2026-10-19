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
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
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

final class SharedStateCapture {
    private SharedStateCapture() {
    }

    static SharedStateReadOut captureRecordedSharedState(
            ActiveRegion active, ConcolicVmBroker api) {
        SharedStateReadOut readOut = new SharedStateReadOut();
        String fault = "";
        long after = active == null ? 0L : active.vmRegionEnterEventId;
        for (int page = 0; page < MAX_READ_OUT_PAGES; page++) {
            final String serialized;
            synchronized (READ_OUT_ORDER) {
                if (!ConcolicResultPublisher.awaitDecodeRoom(
                        READ_OUT_PAGE_BYTES)) {
                    fault = "the replay ended before this read-out completed";
                    break;
                }
                long asked = System.nanoTime();
                try {
                    serialized = api.readOutTrackedLocations(after,
                            READ_OUT_PAGE_BYTES);
                    READ_OUT_NANOS.addAndGet(System.nanoTime() - asked);
                    READ_OUT_PAGES.incrementAndGet();
                    READ_OUT_CHARS.addAndGet(serialized.length());
                } catch (Throwable throwable) {
                    fault = "tracked-location read-out failed: "
                            + rootCause(throwable);
                    ConcolicRegionRuntime.expressionStore(active)
                            .readOutLost("a page after " + after + ": "
                                    + rootCause(throwable));
                    break;
                }
                if (!readOut.decodeLater(serialized, active)) {
                    fault = "a tracked-location read-out page could not be"
                            + " handed to the decoding thread";
                    break;
                }
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

    private static final Object READ_OUT_ORDER = new Object();

    private static final AtomicLong READ_OUT_PAGES = new AtomicLong();
    private static final AtomicLong READ_OUT_CHARS = new AtomicLong();
    private static final AtomicLong READ_OUT_NANOS = new AtomicLong();
    private static final AtomicLong DECODE_NANOS = new AtomicLong();
    private static final AtomicLong VERSIONS = new AtomicLong();
    private static final AtomicLong FILED = new AtomicLong();
    private static final AtomicLong DECODED = new AtomicLong();

    static boolean readOutsTaken() {
        return READ_OUT_PAGES.get() > 0L;
    }

    static String readOutSummary() {
        return String.format(java.util.Locale.ROOT, "%d page(s), %.1f MB,"
                        + " %.1f s in the VM, %.1f s decoding, %d version(s)"
                        + " listed, %d location envelope(s) filed, %d of"
                        + " them decoded; ",
                READ_OUT_PAGES.get(), READ_OUT_CHARS.get() / 1e6,
                READ_OUT_NANOS.get() / 1e9, DECODE_NANOS.get() / 1e9,
                VERSIONS.get(), FILED.get(), DECODED.get())
                + ConcolicRegionRuntime.workloadExpressionStore
                .repeatedSummary();
    }

    static void resetForTests() {
        for (AtomicLong counter : new AtomicLong[] {READ_OUT_PAGES,
                READ_OUT_CHARS, READ_OUT_NANOS, DECODE_NANOS, VERSIONS,
                FILED, DECODED}) {
            counter.set(0L);
        }
    }

    private static final String COMPLETE = "complete";
    private static final String NEXT_AFTER_EVENT_ID = "nextAfterEventId";

    static JsonObject pageHeader(String serialized) {
        return members(serialized, COMPLETE, NEXT_AFTER_EVENT_ID);
    }

    private static final int MAX_READ_OUT_PAGES = 4096;

    private static final int READ_OUT_PAGE_BYTES = 16 * 1024 * 1024;

    static void assembleRecordedSharedState(
            ActiveRegion active, SharedStateReadOut readOut) {
        if (readOut == null) return;
        if (!readOut.fault.isEmpty()) {
            refuse(MALFORMED_ENVELOPE, "", readOut.fault);
        }
        for (Runnable refusal : readOut.refusals) refusal.run();
    }

    private static void decodeTrackedLocations(String serialized,
                                               ActiveRegion active,
                                               SharedStateReadOut readOut) {
        long started = System.nanoTime();
        try {
            decodePage(serialized, active, readOut);
        } finally {
            DECODE_NANOS.addAndGet(System.nanoTime() - started);
        }
    }

    private static void decodePage(String serialized, ActiveRegion active,
                                   SharedStateReadOut readOut) {
        VmExpressionTable.Store store =
                ConcolicRegionRuntime.expressionStore(active);
        store.importReadOutPage(serialized, LOCATIONS, header -> {
            if (readOut != null
                    && ConcolicResultPublisher.withholds(readOut)) {
                return false;
            }
            if (!TRACKED_LOCATIONS_KIND.equals(
                    optionalString(header, "kind"))
                    || optionalInteger(header, "schemaVersion", -1)
                    != PAGE_SCHEMA_VERSION) {
                refuse(MALFORMED_ENVELOPE, "", "tracked-location read-out"
                        + " page of kind " + optionalString(header, "kind")
                        + " and schema " + optionalInteger(header,
                        "schemaVersion", -1) + ", and this jar reads "
                        + TRACKED_LOCATIONS_KIND + " schema "
                        + PAGE_SCHEMA_VERSION);
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
        }, Filed.class, element -> {
            if (readOut != null && ConcolicResultPublisher.withholds(readOut)) {
                throw Withheld.INSTANCE;
            }
            return decoded(element, store.truncationMarked());
        }, filed -> file(filed, active),
                ConcolicResultPublisher.recordDecoders(),
                ConcolicResultPublisher.RECORD_DECODERS);
    }

    private static final class Withheld extends RuntimeException {
        private static final long serialVersionUID = 1L;
        static final Withheld INSTANCE = new Withheld();

        private Withheld() {
            super("withheld", null, false, false);
        }
    }

    static final class Filed {
        final String locationKey;
        final JsonObject record;
        final String fault;
        final int versions;
        boolean walked;

        Filed(String locationKey, JsonObject record, String fault,
              int versions) {
            this.locationKey = locationKey;
            this.record = record;
            this.fault = fault;
            this.versions = versions;
        }
    }

    private static Filed decoded(JsonElement element, boolean marked) {
        DECODED.incrementAndGet();
        if (!element.isJsonObject()) {
            return new Filed("", null, "tracked location is not an object",
                    0);
        }
        JsonObject envelope = element.getAsJsonObject();
        int versions = array(envelope, "versions").size();
        String fault = versionsFault(envelope, marked
                ? Collections.newSetFromMap(
                        new IdentityHashMap<JsonElement, Boolean>())
                : null);
        String locationKey = locationKey(envelope);
        return fault.isEmpty()
                ? new Filed(locationKey, writeLogRecord(locationKey,
                envelope), "", versions)
                : new Filed(locationKey, null, fault, versions);
    }

    private static void file(Filed filed, ActiveRegion active) {
        FILED.incrementAndGet();
        VERSIONS.addAndGet(filed.versions);
        if (!filed.fault.isEmpty()) {
            if (active != null && !filed.locationKey.isEmpty()) {
                active.sharedStateRefusals.put(filed.locationKey,
                        filed.fault);
            }
            refuse(expressionSerializationTruncationFault(filed.fault)
                            ? EXPRESSION_SERIALIZATION_TRUNCATED
                            : containerBaseUnstatedFault(filed.fault)
                            ? CONTAINER_BASE_UNSTATED
                            : MALFORMED_ENVELOPE,
                    filed.locationKey, filed.fault);
            return;
        }
        if (active != null) {
            active.sharedStateRecords.put(filed.locationKey, filed);
        }
    }

    private static final String LOCATIONS = "locations";

    private static final String TRACKED_LOCATIONS_KIND =
            "SHARED_TRACKED_LOCATIONS";
    private static final int PAGE_SCHEMA_VERSION = 2;

    static JsonObject writeLogRecord(String locationKey, JsonObject envelope) {
        JsonArray versions = new JsonArray();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(version, entry, "fieldVersionId");
            copyIfPresent(version, entry, "versionKind");
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            copyIfPresent(version, entry, "expression");
            copyIfPresent(version, entry, REFERENT_STATE);
            copyIfPresent(version, entry, REFERENT_STATE_REFUSED);
            versions.add(entry);
        }
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

    private static void refuse(int status, String locationKey,
                               String detail) {
        List<Runnable> deferred = DECODING.get();
        if (deferred != null) {
            deferred.add(() -> refuse(status, locationKey, detail));
            return;
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                firstNonBlank(nonNull(locationKey), STAGE_VERSIONS,
                        RowRuntime.sessionId()),
                reason(status) + ": " + nonNull(detail));
    }

    private static void lostTable(String detail) {
        List<Runnable> deferred = DECODING.get();
        if (deferred != null) {
            deferred.add(() -> lostTable(detail));
            return;
        }
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING, READ_OUT,
                detail);
    }

    private static final String READ_OUT = "READ_OUT";

    private static final ThreadLocal<List<Runnable>> DECODING =
            new ThreadLocal<List<Runnable>>();

    static final class SharedStateReadOut {
        private String fault = "";
        private final List<Runnable> refusals = new ArrayList<>();
        private int pending;
        long ordinal;

        private boolean decodeLater(String page, ActiveRegion active) {
            synchronized (this) {
                pending++;
            }
            boolean handed = ConcolicResultPublisher.decodeInOrder(
                    page.length(), () -> {
                        DECODING.set(refusals);
                        try {
                            decodeTrackedLocations(page, active, this);
                        } catch (Withheld withheld) {
                        } catch (Throwable throwable) {
                            String lost = ConcolicRegionRuntime
                                    .expressionStore(active).readOutLosses();
                            if (lost.isEmpty()) {
                                refuse(MALFORMED_ENVELOPE, "",
                                        rootCause(throwable));
                            } else {
                                lostTable(rootCause(throwable) + "; read-out"
                                        + " tables never imported: " + lost);
                            }
                        } finally {
                            DECODING.remove();
                            decoded();
                        }
                    });
            if (!handed) decoded();
            return handed;
        }

        private synchronized void decoded() {
            pending--;
            notifyAll();
        }

        synchronized void awaitDecoded() {
            boolean interrupted = false;
            while (pending > 0) {
                try {
                    wait();
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
            }
            if (interrupted) Thread.currentThread().interrupt();
        }
    }


    private static final int SCHEMA_VERSION = 2;

    private static final String VERSIONS_ENVELOPE_KIND =
            "SHARED_FIELD_VERSIONS";
    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    private static final String VM_SERIALIZATION_TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

    static final String STAGE_VERSIONS = "VERSIONS";

    private static final int OK = 0;

    private static final int MALFORMED_ENVELOPE = -1002;
    private static final int EXPRESSION_SERIALIZATION_TRUNCATED = -1007;
    private static final int CONTAINER_BASE_UNSTATED = -1012;

    private static final String VM_EXPRESSION_SERIALIZATION_TRUNCATED =
            "VM_EXPRESSION_SERIALIZATION_TRUNCATED";

    private static final String REASON_PREFIX = "SHARED_STATE_";
    private static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    private static final String LOCATION_KIND_MAP_STATE = "MAP_STATE";
    private static final int MAP_STATE_SLOT = -3;

    private static final Set<String> LOCATION_KINDS = names("INSTANCE_FIELD",
            "STATIC_FIELD", "ARRAY_ELEMENT", LOCATION_KIND_MAP_STATE);
    private static final Set<String> VERSION_KINDS = names("INITIAL", "WRITE",
            "RMW", "UNOBSERVED", "STATE", "STATE_PUT", "STATE_PUT_IF",
            "STATE_PUT_ALL", "STATE_REMOVE", "STATE_REMOVE_IF", "STATE_CLEAR",
            "STATE_REMOVE_AT", "STATE_CLEAR_VIEW", "STATE_ADD",
            "STATE_APPEND", "STATE_INSERT", "STATE_WRITE", "STATE_POLL",
            "STATE_COLLECT", "STATE_ATTACH");
    static final String REFERENT_STATE = "referentState";
    static final String REFERENT_STATE_REFUSED = "referentStateRefused";
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
        clean.addAll(visited);
        return false;
    }

    private static boolean expressionSerializationTruncationFault(
            String fault) {
        return fault != null
                && (VM_EXPRESSION_SERIALIZATION_TRUNCATED.equals(fault)
                || fault.startsWith(
                VM_EXPRESSION_SERIALIZATION_TRUNCATED + ":"));
    }

    private static String locationKey(JsonObject envelope) {
        return locationKeyOf(object(envelope, "location"));
    }

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

    static LocationId locationId(
            String locationKey) {
        String key = nonNull(locationKey);
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

    private static boolean stateVersionKind(String versionKind) {
        return versionKind != null && (versionKind.equals("STATE")
                || versionKind.startsWith("STATE_"));
    }

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
        if (optionalBool(envelope, "serializationTruncated", false)) {
            return VM_EXPRESSION_SERIALIZATION_TRUNCATED
                    + ": version envelope";
        }
        JsonArray versions = array(envelope, "versions");
        if (versions.size() == 0) {
            return "selected location published no version";
        }
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

    private static final String CONTAINER_BASE_UNSTATED_FAULT =
            "CONTAINER_BASE_UNSTATED";

    private static boolean containerBaseUnstatedFault(String fault) {
        return fault != null && fault.startsWith(CONTAINER_BASE_UNSTATED_FAULT);
    }

    static boolean initial(JsonObject version) {
        return INITIAL_VERSION_KIND.equals(
                optionalString(version, "versionKind"));
    }

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
        if (!unattributed(version)
                && (optionalLongInteger(version, "regionEnterEventId", 0L) <= 0L
                || optionalString(version, "regionId").isEmpty()
                || optionalString(version, "taskId").isEmpty())) {
            return "version " + id + " names no writer case";
        }
        if (!version.has("pathGuard")) {
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
        if (clean == null) return "";
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
