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

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Which write a read took, as the session recorded it.
 *
 * <p>Composition used to answer that question after the fact, by pairing a
 * writer to a reader whose observed concrete values matched. For a primitive
 * leaf that test cannot tell two writers of the same value apart, and choosing
 * one anyway manufactures a read-from edge the run never showed. That rule is
 * gone. Trace refinement now retains <em>every</em> observed writer of the
 * field as a candidate and decides nothing; the VM answers the question where
 * it can be answered, and this index applies that answer to the candidates at
 * campaign completion.</p>
 *
 * <p>The join address is the one the rest of the pipeline uses for an
 * activation: {@code sourceKey + occurrenceId}, composed by
 * {@link RecordedEvidenceIdentity#siteKey}. A static {@code regionId} is not an
 * address - two concurrent activations of one thread-entry region share it, so
 * a decision keyed on it would answer for a writer that never ran. Where a
 * recorded row carries no such address the index says so and decides nothing:
 * an unattributable writer widens the unknown arm rather than narrowing the
 * choice.</p>
 *
 * <p>Three outcomes, and they stay distinguishable end to end: an exact read
 * binds one writer, a guarded read keeps the recorded candidate set together
 * with its {@code rf_unknown} arm, and a location the session never watched
 * leaves the trace candidates exactly as they were, under a named gap.</p>
 */
public final class RecordedReadFrom {

    /** Evidence schema shared with the other admitted runtime edge rows. */
    public static final int EDGE_SCHEMA_VERSION = 3;

    /** Authority of one VM-recorded read-from equality. */
    public static final String AUTHORITY = "VM_RECORDED_READ_FROM_V1";

    /** Provenance stamped on an edge the recorded evidence proved. */
    public static final String PROVENANCE_EXACT = "VM_RECORDED_EXACT";
    /** Provenance stamped on an edge the recorded evidence kept guarded. */
    public static final String PROVENANCE_GUARDED = "VM_RECORDED_GUARDED";
    /**
     * Provenance stamped on a writer the trace observed and nothing has yet
     * decided. It is a candidate and never an observed edge: the run showed
     * that this writer could have produced the value, not that it did.
     */
    public static final String PROVENANCE_CANDIDATE =
            "TRACE_CANDIDATE_WRITER";
    /** Provenance stamped on a candidate the recorded evidence ruled out. */
    public static final String PROVENANCE_EXCLUDED = "VM_RECORDED_EXCLUDED";

    /** Edge member naming the declared field a candidate is stated over. */
    public static final String EDGE_FIELD = "readFromField";
    /**
     * Edge member naming the source both endpoints were traced under.
     *
     * <p>It is reporting, not the join key. The occurrence ids on the edge are
     * minted from a <em>semantic</em> source, which for a target activation is
     * the source of the event its failure branch was observed on, while this
     * is the source current at root entry; the two legitimately differ, and
     * composing them would produce an address neither side agrees on.</p>
     */
    public static final String EDGE_SOURCE_KEY = "readFromSourceKey";
    /** Edge member carrying the provenance state above. */
    public static final String EDGE_PROVENANCE = "readFromProvenance";
    /** Edge member naming why a provenance state is not a proof. */
    public static final String EDGE_PROVENANCE_GAP = "readFromProvenanceGap";
    /**
     * Edge member naming the unknown-writer arm this read retains. Present
     * whenever the recorded writer set is incomplete or an observed writer
     * could not be given a cross-run address.
     */
    public static final String EDGE_UNKNOWN_ARM = "readFromUnknownArm";

    /**
     * Watched locations, by declared field and then by VM location identity.
     *
     * <p>The second level is what keeps README {@code STATE-1}'s "NN, Balancer
     * and DN maps never merge by field name" true here. One declared field is
     * a <em>name</em>, and a distributed run holds several distinct objects
     * under it; folding their version stores into one entry would let a read
     * of the DataNode's map be answered by a write to the NameNode's, which
     * is a read-from edge nothing observed. The VM's own location key
     * separates them, and the declared field remains only the cross-run join
     * a later replay can name.</p>
     */
    private final Map<String, Map<String, Location>> byField =
            new LinkedHashMap<>();

    /** What the recorded evidence says about one writer/reader pair. */
    public enum Decision {
        /** Nothing was recorded about this location; decide nothing. */
        NO_RECORDED_EVIDENCE,
        /** The VM proved this writer for this reader. */
        RECORDED_EXACT,
        /** The VM kept this writer among the reader's candidates. */
        RECORDED_GUARDED_CANDIDATE,
        /** The recorded evidence names a different writer. */
        RECORDED_EXCLUDED;

        /** Whether the recorded evidence answers the question at all. */
        public boolean decides() {
            return this != NO_RECORDED_EVIDENCE;
        }

        /** The provenance a resolved candidate carries. */
        public String provenance() {
            switch (this) {
                case RECORDED_EXACT:
                    return PROVENANCE_EXACT;
                case RECORDED_GUARDED_CANDIDATE:
                    return PROVENANCE_GUARDED;
                case RECORDED_EXCLUDED:
                    return PROVENANCE_EXCLUDED;
                default:
                    return PROVENANCE_CANDIDATE;
            }
        }
    }

    private RecordedReadFrom() {
    }

    /**
     * Indexes the recorded shared state of one or more executions.
     *
     * @param recordedMembers {@code recordedSharedState} members
     */
    public static RecordedReadFrom index(
            Collection<JsonObject> recordedMembers) {
        RecordedReadFrom index = new RecordedReadFrom();
        if (recordedMembers == null) return index;
        for (JsonObject member : recordedMembers) {
            if (member == null || !SharedStateEvidence.RECORDED_KIND.equals(
                    string(member, "kind"))) {
                continue;
            }
            for (JsonElement element : array(member, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject record = element.getAsJsonObject();
                if (!SharedStateEvidence.isVersionsRecord(record)) continue;
                String field = fieldKey(object(record, "carrier"));
                if (field.isEmpty()) {
                    // Without the declared field the record cannot be joined
                    // to anything a later run can name.  It is still evidence
                    // for the slice, which addresses locations by the VM's own
                    // identity; it is not evidence for a cross-run pairing.
                    continue;
                }
                index.location(field, string(record, "locationKey"))
                        .absorb(record);
            }
        }
        return index;
    }

    /** The join key of one declared field: its owner and its name. */
    public static String fieldKey(String declaringClass, String fieldName) {
        if (declaringClass == null || fieldName == null
                || declaringClass.trim().isEmpty()
                || fieldName.trim().isEmpty()) {
            return "";
        }
        return declaringClass.trim() + "#" + fieldName.trim();
    }

    private static String fieldKey(JsonObject carrier) {
        return fieldKey(string(carrier, "declaringClass"),
                string(carrier, "fieldName"));
    }

    private Location location(String field, String locationKey) {
        Map<String, Location> locations = byField.get(field);
        if (locations == null) {
            locations = new LinkedHashMap<>();
            byField.put(field, locations);
        }
        Location location = locations.get(locationKey);
        if (location == null) {
            location = new Location();
            locations.put(locationKey, location);
        }
        return location;
    }

    private Collection<Location> locations(String field) {
        Map<String, Location> locations = byField.get(field);
        return locations == null ? Collections.<Location>emptyList()
                : locations.values();
    }

    /**
     * The one location of {@code field} that recorded a read by this reader.
     *
     * <p>A read is performed on one object, so exactly one of the field's
     * location stores can answer for it. Where none did, this run watched
     * nothing that reader read; where several did, the activation read two
     * distinct locations that share a declared field and no single store
     * answers the pair. Both are "decide nothing", which leaves the trace's
     * candidates in place under their gap rather than crediting a write to a
     * read of another object.</p>
     */
    private Location deciding(String field, String readerSite) {
        if (readerSite == null || readerSite.isEmpty()) return null;
        Location answer = null;
        for (Location location : locations(field)) {
            if (!location.reads(readerSite)) continue;
            if (answer != null) return null;
            answer = location;
        }
        return answer;
    }

    public boolean isEmpty() {
        return byField.isEmpty();
    }

    /**
     * Decides one writer/reader pair, both named by activation site.
     *
     * <p>An exact read answers for its own reader and for no other: the VM
     * proved which write <em>that</em> read took. A guarded read admits every
     * writer the location recorded, because that is precisely what being
     * undecided means. A location the session never watched, and a site the
     * recorded rows could not address, decide nothing at all.</p>
     *
     * @param writerSite {@link RecordedEvidenceIdentity#siteKey} of the writer
     * @param readerSite {@link RecordedEvidenceIdentity#siteKey} of the reader
     */
    public Decision decide(String field, String writerSite,
                           String readerSite) {
        return decide(field, writerSite, readerSite, "");
    }

    /** Edge-aware form used only when resolving frozen candidate bindings. */
    private Decision decide(String field, String writerSite,
                            String readerSite, String edgeId) {
        Location location = deciding(field, readerSite);
        if (location == null || writerSite == null || writerSite.isEmpty()) {
            return Decision.NO_RECORDED_EVIDENCE;
        }
        Set<String> plannedEdges = location.plannedEdgesByReader.get(
                readerSite);
        if (plannedEdges != null && !plannedEdges.isEmpty()) {
            // A planned producer-state admission chooses an edge, not merely
            // an occurrence.  Without that edge the caller cannot safely
            // answer: several phase tasks may share the same writer and
            // reader occurrence addresses.
            if (edgeId == null || edgeId.isEmpty()
                    || plannedEdges.size() != 1) {
                return Decision.NO_RECORDED_EVIDENCE;
            }
            String selected = plannedEdges.iterator().next();
            if (!selected.equals(edgeId)) {
                return Decision.RECORDED_EXCLUDED;
            }
            Set<String> exact = location.exactWriters.get(readerSite);
            return exact != null && exact.contains(writerSite)
                    ? Decision.RECORDED_EXACT
                    : Decision.RECORDED_EXCLUDED;
        }
        Set<String> exact = location.exactWriters.get(readerSite);
        if (exact != null) {
            return exact.contains(writerSite)
                    ? Decision.RECORDED_EXACT : Decision.RECORDED_EXCLUDED;
        }
        return location.writers.contains(writerSite)
                ? Decision.RECORDED_GUARDED_CANDIDATE
                : Decision.RECORDED_EXCLUDED;
    }

    /**
     * The one activation of {@code regionId} this index recorded for
     * {@code field}, or "" when it recorded none or several.
     *
     * <p>Callers that only hold a static region - a compiled read-cut gate is
     * the one that does - resolve it here rather than keying a decision on it.
     * Several activations of one region is exactly the case a region-keyed
     * join gets wrong, so it answers "" and the caller reports a gap.</p>
     */
    public String siteOfRegion(String field, String regionId) {
        if (regionId == null || regionId.isEmpty()) return "";
        Set<String> sites = new LinkedHashSet<>();
        for (Location location : locations(field)) {
            Set<String> known = location.sitesByRegion.get(regionId);
            if (known != null) sites.addAll(known);
        }
        return sites.size() != 1 ? "" : sites.iterator().next();
    }

    /** The location this reader's recorded read was performed on, or "". */
    public String locationKey(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        return location == null ? "" : location.locationKey;
    }

    /**
     * Whether every writer of one field is both recorded and addressable.
     *
     * <p>The VM's own completeness claim is only half the question. A write it
     * did record but whose activation cannot be named is, for a cross-run
     * pairing, indistinguishable from one it never saw: no candidate can carry
     * it, so the read keeps its unknown arm either way.</p>
     */
    public boolean writerSetComplete(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        return location != null && location.writerSetComplete
                && location.unaddressableWriters == 0;
    }

    private boolean plannedProducerRead(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        Set<String> edges = location == null ? null
                : location.plannedEdgesByReader.get(readerSite);
        return edges != null && edges.size() == 1;
    }

    /**
     * Whether the VM dropped read-log entries for this field's location.
     *
     * <p>Truncation clears completeness, so this never widens what the model
     * believes: it only says which of the two open-writer-set findings this
     * location has.</p>
     */
    public boolean readLogTruncated(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        return location != null && location.readLogTruncated;
    }

    // ---- Campaign-completion resolution ---------------------------------

    /**
     * Resolves the trace's candidate writers against this run's recorded
     * evidence, in place.
     *
     * <p>Trace refinement runs before any concolic execution exists, so the
     * edges it produces state what the run <em>observed</em>: every writer of
     * the field that could have reached the read. This is where the recorded
     * answer is applied to them, because it is the first point at which both
     * exist. An exact read binds its one proven writer and excludes the
     * others; a guarded read keeps the recorded set and its unknown arm; a
     * location nothing watched leaves every candidate exactly as it was, still
     * carrying the gap that says so.</p>
     *
     * <p>Nothing is removed. An excluded candidate is marked, not deleted: the
     * edge is the trace's own observation, and deleting it would leave a
     * consumer input with no producer at all rather than with a producer this
     * run's evidence rules out.</p>
     *
     * @return how many candidate edges the recorded evidence decided
     */
    public int resolve(Iterable<JsonObject> bindings) {
        int decided = 0;
        if (bindings == null) return 0;
        for (JsonObject binding : bindings) {
            if (binding == null || !PROVENANCE_CANDIDATE.equals(
                    string(binding, EDGE_PROVENANCE))) {
                continue;
            }
            String field = string(binding, EDGE_FIELD);
            String readerSite = RecordedEvidenceIdentity.siteKey(
                    string(binding, "toOccurrenceId"));
            Decision decision = decide(field,
                    RecordedEvidenceIdentity.siteKey(
                            string(binding, "fromOccurrenceId")),
                    readerSite, string(binding, "edgeId"));
            if (!decision.decides()) continue;
            decided++;
            binding.addProperty(EDGE_PROVENANCE, decision.provenance());
            binding.remove(EDGE_PROVENANCE_GAP);
            String location = locationKey(field, readerSite);
            if (!location.isEmpty()) {
                binding.addProperty("locationKey", location);
            }
            if (decision == Decision.RECORDED_EXCLUDED) {
                binding.addProperty(EDGE_PROVENANCE_GAP,
                        SharedStateEvidence.reason(
                                SharedStateEvidence.NOT_SELECTED));
            }
            // The unknown arm is a property of the location, not of the arm
            // that happens to be selected: a writer set that is incomplete or
            // not fully addressable leaves the read able to have taken a write
            // no candidate represents, whatever the recorded answer was.
            if (!plannedProducerRead(field, readerSite)
                    && !writerSetComplete(field, readerSite)) {
                binding.addProperty(EDGE_UNKNOWN_ARM,
                        SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
                // A truncated read log is an open writer set for a different
                // reason, and the difference is what a reader acts on, so it
                // is named apart instead of merged into the generic one.
                binding.addProperty(EDGE_PROVENANCE_GAP,
                        SharedStateEvidence.reason(
                                readLogTruncated(field, readerSite)
                                ? SharedStateEvidence.READ_LOG_TRUNCATED
                                : SharedStateEvidence.UNKNOWN_WRITER));
            }
        }
        return decided;
    }

    /**
     * The named gap for a candidate no recorded evidence decided.
     *
     * <p>The trace's candidates stay in the model - they are what it observed
     * - but nothing upgraded them to an observed read-from edge, and this says
     * so in the same coverage stream as every other refusal.</p>
     */
    public static JsonObject absentEvidenceGap(String field,
                                               String readerSite) {
        return SharedStateEvidence.gap(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.NOT_SELECTED, field,
                "no recorded read-from evidence for " + field + " read by "
                        + readerSite
                        + "; the trace's candidate writers stay unresolved");
    }

    /** The named gap for a read that retains an unknown-writer arm. */
    public static JsonObject unknownWriterGap(String field,
                                              String readerSite) {
        return SharedStateEvidence.gap(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.UNKNOWN_WRITER, field,
                "the recorded writer set of " + field + " read by "
                        + readerSite + " is incomplete or not addressable, so "
                        + "the read keeps its "
                        + SharedStateEvidence.UNKNOWN_WRITER_SELECTOR
                        + " arm");
    }

    /**
     * Turns the provenance stamps of edge bindings into coverage gaps: one per
     * field and reader whose candidates nothing decided, and one per field and
     * reader that retains an unknown-writer arm.
     */
    public static List<JsonObject> provenanceGaps(
            Collection<JsonObject> bindings) {
        List<JsonObject> gaps = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        if (bindings == null) return gaps;
        for (JsonObject binding : bindings) {
            if (binding == null) continue;
            String field = string(binding, EDGE_FIELD);
            String reader = string(binding, "toOccurrenceId");
            if (reader.isEmpty()) reader = string(binding, "toRegion");
            if (PROVENANCE_CANDIDATE.equals(string(binding, EDGE_PROVENANCE))
                    && seen.add("candidate\n" + field + "\n" + reader)) {
                gaps.add(absentEvidenceGap(field, reader));
            }
            if (!string(binding, EDGE_UNKNOWN_ARM).isEmpty()
                    && seen.add("unknown\n" + field + "\n" + reader)) {
                gaps.add(unknownWriterGap(field, reader));
            }
        }
        return gaps;
    }

    /**
     * Completes one recorded exact read-from into an edge evidence row.
     *
     * <p>{@code endpoints} supplies what the VM cannot know - the region
     * occurrences and ports the two sites belong to. The VM half must be an
     * exact read whose read-from edge the ledger itself holds: the version
     * store says which write the read took, and the order domain carries the
     * matching {@code FIELD_READ_FROM} edge. Either half alone is refused, so
     * a guarded read - which draws no ledger edge, deliberately - can never
     * become an equality here.</p>
     */
    public static JsonObject edgeEvidence(JsonObject endpoints,
                                          JsonObject versionsRecord,
                                          long readEventId,
                                          SessionOrderDomain domain) {
        if (endpoints == null || domain == null
                || !SharedStateEvidence.isVersionsRecord(versionsRecord)) {
            return new JsonObject();
        }
        JsonObject envelope = object(versionsRecord, "envelope");
        JsonObject read = readRecord(envelope, readEventId);
        if (read == null || !SharedStateEvidence.RESOLUTION_EXACT.equals(
                string(read, "resolution"))) {
            return new JsonObject();
        }
        String plannedEdge = string(read, "selectedEdgeId");
        String endpointEdge = string(endpoints, "edgeId");
        if (SharedStateEvidence.READ_REASON_PLANNED_PRODUCER_STATE.equals(
                string(read, "reason"))
                && (plannedEdge.isEmpty()
                || !plannedEdge.equals(endpointEdge))) {
            return new JsonObject();
        }
        long version = longInteger(read, "chosenFieldVersionId", 0L);
        if (version <= 0L
                || !"FIELD_READ_FROM".equals(domain.directKind(version,
                readEventId))) {
            return new JsonObject();
        }
        JsonObject writer = versionRecord(envelope, version);
        if (writer == null) return new JsonObject();
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", EDGE_SCHEMA_VERSION);
        evidence.addProperty("kind",
                AutomaticRegionEdge.RUNTIME_EDGE_KIND);
        evidence.addProperty("state",
                AutomaticRegionEdge.CONFIRMED_VM_RECORDED_READ_FROM);
        evidence.addProperty("evidenceKind", AUTHORITY);
        evidence.addProperty("correlationAuthority", AUTHORITY);
        for (String field : new String[]{"transportKind", "fromRegion",
                "toRegion", "fromOccurrenceId", "toOccurrenceId",
                "fromOutputPort", "toInputPort"}) {
            evidence.addProperty(field, string(endpoints, field));
        }
        evidence.addProperty("locationKey",
                string(versionsRecord, "locationKey"));
        evidence.addProperty(EDGE_FIELD,
                fieldKey(object(versionsRecord, "carrier")));
        evidence.addProperty("fieldVersionId", version);
        evidence.addProperty("readEventId", readEventId);
        evidence.addProperty("writerRegionId", string(writer, "regionId"));
        evidence.addProperty("writerSite",
                SharedStateEvidence.writerSite(writer));
        evidence.addProperty("readerSite",
                SharedStateEvidence.readerSite(read));
        evidence.addProperty("resolutionReason", string(read, "reason"));
        evidence.addProperty("orderEdgeKind", "FIELD_READ_FROM");
        evidence.addProperty("ledgerJustified", true);
        evidence.addProperty("writerSetComplete",
                SharedStateEvidence.READ_REASON_PLANNED_PRODUCER_STATE
                        .equals(string(read, "reason"))
                        || SharedStateEvidence.writerSetComplete(envelope));
        evidence.addProperty(EDGE_PROVENANCE, PROVENANCE_EXACT);
        String edgeId = string(endpoints, "edgeId");
        evidence.addProperty("edgeId", edgeId.isEmpty()
                ? "RFV." + ArtifactIO.sha256(version + "\n" + readEventId
                + "\n" + string(endpoints, "fromOutputPort") + "\n"
                + string(endpoints, "toInputPort")).substring(0, 16)
                : edgeId);
        return evidence;
    }

    private static JsonObject readRecord(JsonObject envelope,
                                         long readEventId) {
        for (JsonElement element : array(envelope, "reads")) {
            JsonObject read = element.getAsJsonObject();
            if (longInteger(read, "readEventId", 0L) == readEventId) {
                return read;
            }
        }
        return null;
    }

    private static JsonObject versionRecord(JsonObject envelope,
                                            long fieldVersionId) {
        for (JsonElement element : array(envelope, "versions")) {
            JsonObject version = element.getAsJsonObject();
            if (longInteger(version, "fieldVersionId", 0L)
                    == fieldVersionId) {
                return version;
            }
        }
        return null;
    }

    /** One watched location, reduced to the identities a pairing can use. */
    private static final class Location {
        private String locationKey = "";
        private boolean writerSetComplete = true;
        /** The VM dropped read-log entries for this location. */
        private boolean readLogTruncated;
        private int unaddressableWriters;
        private final Set<String> writers = new LinkedHashSet<>();
        private final Set<String> guardedReaders = new LinkedHashSet<>();
        private final Map<String, Set<String>> exactWriters =
                new LinkedHashMap<>();
        /** Exact selected edge ids of planned producer-state reads. */
        private final Map<String, Set<String>> plannedEdgesByReader =
                new LinkedHashMap<>();
        /** Activations of each static region, for region-only callers. */
        private final Map<String, Set<String>> sitesByRegion =
                new LinkedHashMap<>();

        private void absorb(JsonObject record) {
            JsonObject envelope = object(record, "envelope");
            locationKey = string(record, "locationKey");
            writerSetComplete = writerSetComplete
                    && SharedStateEvidence.writerSetComplete(envelope);
            readLogTruncated = readLogTruncated
                    || SharedStateEvidence.readLogTruncated(envelope);
            Map<Long, String> siteByVersion = new LinkedHashMap<>();
            for (JsonElement element : array(envelope, "versions")) {
                JsonObject version = element.getAsJsonObject();
                String site = SharedStateEvidence.writerSite(version);
                if (site.isEmpty()) {
                    // A write the VM saw but whose activation nothing can
                    // name.  No candidate can carry it, so it is exactly as
                    // undecidable as a write nobody saw.
                    unaddressableWriters++;
                    continue;
                }
                siteByVersion.put(longInteger(version, "fieldVersionId", 0L),
                        site);
                writers.add(site);
                register(string(version, "regionId"), site);
            }
            for (JsonElement element : array(envelope, "reads")) {
                JsonObject read = element.getAsJsonObject();
                String reader = SharedStateEvidence.readerSite(read);
                if (reader.isEmpty()) continue;
                register(string(read, "regionId"), reader);
                if (SharedStateEvidence.RESOLUTION_EXACT.equals(
                        string(read, "resolution"))) {
                    String writer = siteByVersion.get(longInteger(read,
                            "chosenFieldVersionId", 0L));
                    if (writer == null) continue;
                    Set<String> exact = exactWriters.get(reader);
                    if (exact == null) {
                        exact = new LinkedHashSet<>();
                        exactWriters.put(reader, exact);
                    }
                    exact.add(writer);
                    if (SharedStateEvidence
                            .READ_REASON_PLANNED_PRODUCER_STATE.equals(
                            string(read, "reason"))) {
                        String edgeId = string(read, "selectedEdgeId");
                        if (!edgeId.isEmpty()) {
                            Set<String> edges = plannedEdgesByReader.get(
                                    reader);
                            if (edges == null) {
                                edges = new LinkedHashSet<>();
                                plannedEdgesByReader.put(reader, edges);
                            }
                            edges.add(edgeId);
                        }
                    }
                } else {
                    guardedReaders.add(reader);
                }
            }
        }

        /** Whether this store recorded a read performed by {@code site}. */
        private boolean reads(String site) {
            return exactWriters.containsKey(site)
                    || guardedReaders.contains(site);
        }

        private void register(String regionId, String site) {
            if (regionId == null || regionId.isEmpty()) return;
            Set<String> sites = sitesByRegion.get(regionId);
            if (sites == null) {
                sites = new LinkedHashSet<>();
                sitesByRegion.put(regionId, sites);
            }
            sites.add(site);
        }
    }

    /** Fields this index watches, for reporting. */
    public Set<String> fields() {
        return Collections.unmodifiableSet(byField.keySet());
    }

    /** One artifact-ready description of what the index decided from. */
    public JsonObject toJson() {
        JsonObject index = new JsonObject();
        index.addProperty("schemaVersion", 1);
        index.addProperty("kind", "RECORDED_READ_FROM_INDEX");
        index.addProperty("authority", AUTHORITY);
        JsonArray fields = new JsonArray();
        // One row per watched location, never one per declared field: a field
        // several objects share is several stores, and averaging them into
        // one row would report a completeness no single location has.
        for (Map.Entry<String, Map<String, Location>> entry
                : byField.entrySet()) {
            for (Location location : entry.getValue().values()) {
                JsonObject row = new JsonObject();
                row.addProperty("field", entry.getKey());
                row.addProperty("locationKey", location.locationKey);
                row.addProperty("writerSetComplete",
                        location.writerSetComplete
                                && location.unaddressableWriters == 0);
                row.addProperty("readLogTruncated", location.readLogTruncated);
                row.addProperty("writerSites", location.writers.size());
                row.addProperty("unaddressableWriters",
                        location.unaddressableWriters);
                row.addProperty("exactReaders", location.exactWriters.size());
                row.addProperty("guardedReaders",
                        location.guardedReaders.size());
                fields.add(row);
            }
        }
        index.add("fields", fields);
        return index;
    }
}
