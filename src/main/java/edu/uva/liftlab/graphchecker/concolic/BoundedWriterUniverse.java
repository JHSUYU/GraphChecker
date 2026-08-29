package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.uva.liftlab.graphchecker.contract.PathObservation;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The bounded writer universe of one selected read: materialized local path
 * case x bounded semantic occurrence x compatible field, map owner and
 * symbolic key. A merely static may-write site is not an executable writer
 * until its local relation has been materialized, and this is where that rule
 * is enforced - over the recorded version store of the read's own location and
 * the arms the VM lowered. It enumerates and does not fabricate: a recorded
 * write no arm carries is a named gap, and an arm whose writer cannot be
 * placed is reported rather than deleted. Bounded semantic occurrences are
 * Step 3's input; until they exist the occurrences are the ones this run
 * materialized, which is a gap on every read and why the unconditional
 * {@code rf_unknown} arm stays.
 */
public final class BoundedWriterUniverse {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BOUNDED_WRITER_UNIVERSE";
    public static final String AUTHORITY = "BOUNDED_WRITER_UNIVERSE_V1";

    /** Gap family every refusal of this enumeration joins. */
    public static final String GAP_KIND = "BOUNDED_WRITER_UNIVERSE_GAP";
    public static final String GAP_AUTHORITY =
            "BOUNDED_WRITER_UNIVERSE_GAP_V1";

    /** The read's location has no admitted version store to enumerate. */
    public static final String NO_RECORDED_VERSION_STORE =
            "WRITER_UNIVERSE_NO_RECORDED_VERSION_STORE";
    /** An arm names a write the recorded version store does not hold. */
    public static final String UNRECORDED_WRITER_CASE =
            "WRITER_UNIVERSE_UNRECORDED_WRITER_CASE";
    /** A recorded write carries no materialized local case: no captured
     * writer path guard, or no cross-run address, so it is a static
     * possibility and not an executable writer. */
    public static final String UNMATERIALIZED_WRITER_CASE =
            "WRITER_UNIVERSE_UNMATERIALIZED_WRITER_CASE";
    /** A recorded compatible write that no arm of this read carries. */
    public static final String WRITER_WITHOUT_ARM =
            "WRITER_UNIVERSE_WRITER_WITHOUT_ARM";
    /** Two arms of one read query two different keys. */
    public static final String INCOMPATIBLE_QUERY_KEY =
            "WRITER_UNIVERSE_INCOMPATIBLE_QUERY_KEY";
    /** A map arm reads a state other than the one its own writer published. */
    public static final String ARM_STATE_NOT_ITS_WRITER =
            "WRITER_UNIVERSE_ARM_STATE_NOT_ITS_WRITER";
    /** The VM already reported that this location has lost writers. */
    public static final String RECORDED_WRITER_SET_INCOMPLETE =
            "WRITER_UNIVERSE_RECORDED_WRITER_SET_INCOMPLETE";
    /** The occurrence axis of the product is this run's, not a declared
     * bound: named on every read whose writers cannot be placed on README
     * section 5's loop axis, so the set is never read as closed. */
    public static final String SEMANTIC_OCCURRENCE_COVERAGE_OPEN =
            "WRITER_UNIVERSE_SEMANTIC_OCCURRENCE_COVERAGE_OPEN";
    /** How the occurrence axis of the product was supplied. */
    public static final String OCCURRENCE_SOURCE_MATERIALIZED_RUN =
            "MATERIALIZED_RUN_OCCURRENCE";
    /** The selected LOOP_BODY_ROOT relation enumerated its declared a1..aK. */
    public static final String OCCURRENCE_SOURCE_DECLARED_BOUNDED_LOOP =
            "DECLARED_BOUNDED_LOOP_OCCURRENCES";

    private final long readEventId;
    private final String locationKey;
    private final String locationKind;
    private final boolean mapState;
    private final JsonArray cases = new JsonArray();
    private final List<JsonObject> gaps = new ArrayList<>();
    private final Set<String> gapKeys = new LinkedHashSet<>();
    private boolean closed = true;
    private int materializedCases;
    private String occurrenceSource = OCCURRENCE_SOURCE_MATERIALIZED_RUN;
    private final Set<String> boundedWriterAddresses =
            new LinkedHashSet<>();
    private Set<String> closedOccurrenceAddresses = Collections.emptySet();

    private BoundedWriterUniverse(long readEventId, String locationKey) {
        this.readEventId = readEventId;
        this.locationKey = locationKey;
        this.locationKind = SharedStateEvidence.locationKindOf(locationKey);
        this.mapState = SharedStateEvidence.isMapState(locationKey);
    }

    /**
     * Enumerates the universe of one guarded read.
     *
     * @param guardedRead   the admitted {@code ReadFromExpression}
     * @param versionsRecord the admitted version-store record of that read's
     *                       location, or null when none was recorded
     */
    public static BoundedWriterUniverse of(JsonObject guardedRead,
                                           JsonObject versionsRecord) {
        return of(guardedRead, versionsRecord,
                Collections.<String>emptySet());
    }

    /**
     * Enumerates one read using selected LOOP_BODY_ROOT addresses whose
     * complete relation proved the dense declared {@code a1..aK} prefix.
     */
    public static BoundedWriterUniverse of(JsonObject guardedRead,
                                           JsonObject versionsRecord,
                                           Collection<String>
                                                   closedOccurrences) {
        String locationKey = SharedStateEvidence.locationKey(guardedRead);
        BoundedWriterUniverse universe = new BoundedWriterUniverse(
                longInteger(guardedRead, "readEventId", 0L), locationKey);
        universe.closedOccurrenceAddresses = closedOccurrences == null
                ? Collections.<String>emptySet()
                : new LinkedHashSet<>(closedOccurrences);
        universe.enumerate(guardedRead, versionsRecord);
        return universe;
    }

    private void enumerate(JsonObject guardedRead,
                           JsonObject versionsRecord) {
        Map<Long, JsonObject> published = publishedVersions(versionsRecord);
        if (published.isEmpty()) {
            // Without the store the arms are all this layer can see, so it
            // cannot say whether they are all there is.
            open(NO_RECORDED_VERSION_STORE,
                    "read " + readEventId + " has no admitted version store"
                            + " for its location, so its writer set cannot be"
                            + " enumerated");
        }
        Set<Long> armed = new LinkedHashSet<>();
        String queryKey = "";
        for (JsonElement element : array(guardedRead, "candidates")) {
            if (!element.isJsonObject()) continue;
            JsonObject candidate = element.getAsJsonObject();
            if (bool(candidate, "unknown", false)) {
                cases.add(unknownCase(candidate));
                continue;
            }
            long version = longInteger(candidate, "fieldVersionId", 0L);
            armed.add(version);
            JsonObject recorded = published.get(version);
            queryKey = admit(candidate, recorded, version, queryKey);
        }
        for (Map.Entry<Long, JsonObject> entry : published.entrySet()) {
            if (armed.contains(entry.getKey())) continue;
            // A write the store holds and the read offers no arm for: the
            // set the formula chooses from is smaller than the set the run
            // published, which is precisely a missing writer.
            open(WRITER_WITHOUT_ARM, "recorded write " + entry.getKey()
                    + " of " + locationKey + " is a materialized writer that"
                    + " read " + readEventId + " offers no arm for");
        }
        if (!bool(guardedRead, "writerSetComplete", false)) {
            open(RECORDED_WRITER_SET_INCOMPLETE,
                    "the VM reports that " + locationKey
                            + " has already lost writers");
        }
        if (closesSemanticOccurrenceAxis(guardedRead, versionsRecord,
                published)) {
            for (JsonElement element : cases) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                if (!bool(row, "unknown", false)) {
                    row.addProperty("occurrenceSource", occurrenceSource);
                }
            }
        } else {
            open(SEMANTIC_OCCURRENCE_COVERAGE_OPEN,
                    "read " + readEventId + " enumerates only writer "
                            + "occurrences materialized by recorded evidence");
        }
    }

    /**
     * Closes only the occurrence axis. Every structural enumeration check has
     * already run, so any earlier gap leaves the universe open. The number of
     * writes is deliberately irrelevant: several writes may belong to one
     * bounded activation.
     */
    private boolean closesSemanticOccurrenceAxis(
            JsonObject guardedRead, JsonObject versionsRecord,
            Map<Long, JsonObject> published) {
        if (!mapState || !gaps.isEmpty()
                || !bool(guardedRead, "writerSetComplete", false)
                || !SharedStateEvidence.isVersionsRecord(versionsRecord)) {
            return false;
        }
        JsonObject envelope = object(versionsRecord, "envelope");
        JsonArray versions = array(envelope, "versions");
        if (!SharedStateEvidence.writerSetComplete(envelope)
                || SharedStateEvidence.readLogTruncated(envelope)
                || bool(envelope, "serializationTruncated", false)
                || longInteger(envelope, "versionsDropped", -1L) != 0L
                || longInteger(envelope, "versionsObserved", -1L)
                != versions.size()
                || longInteger(envelope, "serializedVersionCount", -1L)
                != versions.size()
                || published.size() != versions.size()) {
            return false;
        }
        int initial = 0;
        int bounded = 0;
        for (JsonObject version : published.values()) {
            if ("INITIAL".equals(string(version, "versionKind"))) {
                initial++;
                continue;
            }
            String writerOccurrence = string(version,
                    SharedStateEvidence.WRITER_OCCURRENCE_ID);
            String address = PathObservation.plannedOccurrenceOf(
                    writerOccurrence);
            if (address.isEmpty()
                    || !closedOccurrenceAddresses.contains(address)) {
                return false;
            }
            boundedWriterAddresses.add(address);
            bounded++;
        }
        if (initial != 1 || bounded <= 0) return false;
        occurrenceSource = OCCURRENCE_SOURCE_DECLARED_BOUNDED_LOOP;
        return true;
    }

    /**
     * Admits one arm as an executable writer case, or names why it is not.
     *
     * @return the query key every arm of this read must agree on
     */
    private String admit(JsonObject candidate, JsonObject recorded,
                         long version, String queryKey) {
        JsonObject row = new JsonObject();
        row.addProperty("selector", string(candidate, "selector"));
        row.addProperty("fieldVersionId", version);
        row.addProperty("locationKey", locationKey);
        row.addProperty("locationKind", locationKind);
        row.addProperty("writerRegionId", string(candidate, "regionId"));
        row.addProperty("writerTaskId", string(candidate, "taskId"));
        row.addProperty("unknown", false);
        row.addProperty("occurrenceSource",
                OCCURRENCE_SOURCE_MATERIALIZED_RUN);
        if (recorded == null) {
            row.addProperty("materialized", false);
            row.addProperty("writerOccurrenceId", "");
            row.addProperty("versionKind", "");
            row.addProperty("localCaseGuarded", false);
            open(UNRECORDED_WRITER_CASE, "arm "
                    + string(candidate, "selector") + " of read "
                    + readEventId + " names write " + version
                    + " that no admitted version store holds");
            cases.add(row);
            return queryKey;
        }
        String occurrence = string(recorded,
                SharedStateEvidence.WRITER_OCCURRENCE_ID);
        boolean localCase = recorded.has("pathGuard");
        boolean materialized = localCase && !occurrence.isEmpty();
        row.addProperty("writerOccurrenceId", occurrence);
        row.addProperty("writerSourceKey", string(recorded,
                SharedStateEvidence.WRITER_SOURCE_KEY));
        row.addProperty("versionKind", string(recorded, "versionKind"));
        row.addProperty("localCaseGuarded", localCase
                && !SharedStateEvidence.unguarded(recorded.get("pathGuard")));
        row.addProperty("materialized", materialized);
        if (!materialized) {
            open(UNMATERIALIZED_WRITER_CASE, "write " + version + " of "
                    + locationKey + " has "
                    + (localCase ? "no addressable activation"
                    : "no recorded local path case")
                    + ", so it is a static site and not an executable"
                    + " writer of read " + readEventId);
        } else {
            materializedCases++;
        }
        String key = queryKey;
        if (mapState) {
            key = admitMapArm(candidate, recorded, version, row, queryKey);
        }
        cases.add(row);
        return key;
    }

    /**
     * The two structural facts that keep a map arm {@code READ(stateAfter(W),
     * key)} a real alternative: its receiver must be the state its own writer
     * published, and every arm of one read must query the same key, because
     * the choice is over writers and not over what was asked.
     */
    private String admitMapArm(JsonObject candidate, JsonObject recorded,
                               long version, JsonObject row,
                               String queryKey) {
        JsonElement expression = candidate.get("expression");
        JsonObject query = expression != null && expression.isJsonObject()
                && ContainerSmtCodec.EXPRESSION_TYPE.equals(
                string(expression.getAsJsonObject(), "_type"))
                ? expression.getAsJsonObject() : null;
        if (query == null) {
            row.addProperty("queryOperation", "");
            row.addProperty("queryKey", "");
            open(ARM_STATE_NOT_ITS_WRITER, "arm "
                    + string(candidate, "selector") + " of read "
                    + readEventId + " is not a container query over write "
                    + version);
            return queryKey;
        }
        row.addProperty("queryOperation", string(query, "operation"));
        String canonicalQueryKey = CanonicalJson.render(
                array(query, "arguments"));
        row.addProperty("queryKey", canonicalQueryKey);
        JsonElement receiver = query.get("receiver");
        JsonElement published = recorded.get("expression");
        boolean ownState = receiver != null && published != null
                && CanonicalJson.render(writerStateIdentity(receiver)).equals(
                CanonicalJson.render(writerStateIdentity(published)));
        row.addProperty("readsItsOwnWriterState", ownState);
        if (!ownState) {
            open(ARM_STATE_NOT_ITS_WRITER, "arm "
                    + string(candidate, "selector") + " of read "
                    + readEventId + " queries a state other than the one"
                    + " write " + version + " published");
        }
        if (queryKey.isEmpty()) return canonicalQueryKey;
        if (!queryKey.equals(canonicalQueryKey)) {
            open(INCOMPATIBLE_QUERY_KEY, "read " + readEventId
                    + " offers arms over two different symbolic keys, so"
                    + " selecting an arm would change the query and not the"
                    + " writer");
        }
        return queryKey;
    }

    /**
     * Canonical identity of a published map state.
     *
     * <p>A map mutation may contain the value of an earlier guarded read.
     * The VM serializes that nested read together with the candidate set known
     * at the instant of each write, so later snapshots can contain a larger
     * candidate array for the same {@code (readEventId, location)}.  Candidate
     * enumeration is not part of the value inserted into the map: the one
     * selected read value is.  Compare nested reads by that stable identity,
     * while retaining every other member of the state expression.  This keeps
     * a genuinely different writer state different and prevents temporal
     * growth of diagnostic RF metadata from opening the writer universe.</p>
     */
    private static JsonElement writerStateIdentity(JsonElement expression) {
        if (expression == null || expression.isJsonNull()
                || expression.isJsonPrimitive()) {
            return expression == null ? null : expression.deepCopy();
        }
        if (expression.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : expression.getAsJsonArray()) {
                result.add(writerStateIdentity(element));
            }
            return result;
        }
        JsonObject object = expression.getAsJsonObject();
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(
                string(object, "_type"))) {
            JsonObject identity = new JsonObject();
            identity.addProperty("_type",
                    SharedStateEvidence.GUARDED_READ_TYPE);
            identity.addProperty("_java_type", string(object,
                    "_java_type"));
            identity.addProperty("readEventId",
                    longInteger(object, "readEventId", 0L));
            identity.addProperty("locationKey",
                    SharedStateEvidence.locationKey(object));
            return identity;
        }
        JsonObject result = new JsonObject();
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            result.add(entry.getKey(), writerStateIdentity(entry.getValue()));
        }
        return result;
    }

    private JsonObject unknownCase(JsonObject candidate) {
        JsonObject row = new JsonObject();
        row.addProperty("selector", string(candidate, "selector"));
        row.addProperty("fieldVersionId", 0L);
        row.addProperty("locationKey", locationKey);
        row.addProperty("locationKind", locationKind);
        row.addProperty("unknown", true);
        row.addProperty("materialized", false);
        row.addProperty("writerOccurrenceId", "");
        row.addProperty("occurrenceSource", "");
        return row;
    }

    private static Map<Long, JsonObject> publishedVersions(
            JsonObject versionsRecord) {
        Map<Long, JsonObject> published = new LinkedHashMap<>();
        if (!SharedStateEvidence.isVersionsRecord(versionsRecord)) {
            return published;
        }
        for (JsonElement element
                : array(object(versionsRecord, "envelope"), "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            published.put(longInteger(version, "fieldVersionId", 0L),
                    version);
        }
        return published;
    }

    private void open(String reason, String detail) {
        closed = false;
        String key = reason + "\n" + detail;
        if (!gapKeys.add(key)) return;
        JsonObject gap = new JsonObject();
        gap.addProperty("kind", GAP_KIND);
        gap.addProperty("schemaVersion", SCHEMA_VERSION);
        gap.addProperty("reason", reason);
        gap.addProperty("authority", GAP_AUTHORITY);
        gap.addProperty("locationKey", locationKey);
        gap.addProperty("readEventId", readEventId);
        gap.addProperty("detail", detail);
        gaps.add(gap);
    }

    public String locationKey() {
        return locationKey;
    }

    /**
     * Whether the enumerated set is the whole bounded universe. Never true in
     * this build: the occurrence axis is not yet declared. It stays a method
     * because the day that input arrives this is the one place that changes.
     */
    public boolean closed() {
        return closed;
    }

    /** Whether the read must retain its unconditional unknown-writer arm. */
    public boolean retainsUnknownArm() {
        return !closed;
    }

    /** Named coverage findings of this enumeration. */
    public List<JsonObject> gaps() {
        return Collections.unmodifiableList(gaps);
    }

    /** The universe as one manifest member. */
    public JsonObject toJson() {
        JsonObject universe = new JsonObject();
        universe.addProperty("schemaVersion", SCHEMA_VERSION);
        universe.addProperty("kind", KIND);
        universe.addProperty("authority", AUTHORITY);
        universe.addProperty("readEventId", readEventId);
        universe.addProperty("locationKey", locationKey);
        universe.addProperty("locationKind", locationKind);
        universe.addProperty("mapState", mapState);
        universe.addProperty("closed", closed);
        universe.addProperty("retainsUnknownArm", retainsUnknownArm());
        universe.addProperty("materializedCases", materializedCases);
        universe.addProperty("occurrenceSource", occurrenceSource);
        JsonArray addresses = new JsonArray();
        for (String address : boundedWriterAddresses) addresses.add(address);
        universe.add("boundedWriterAddresses", addresses);
        JsonArray declared = new JsonArray();
        for (String address : closedOccurrenceAddresses) {
            declared.add(address);
        }
        universe.add("closedOccurrenceAddresses", declared);
        universe.add("cases", cases.deepCopy());
        JsonArray recorded = new JsonArray();
        for (JsonObject gap : gaps) recorded.add(gap.deepCopy());
        universe.add("gaps", recorded);
        return universe;
    }
}
