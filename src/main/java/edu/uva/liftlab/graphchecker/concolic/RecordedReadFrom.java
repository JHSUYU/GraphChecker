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
 */
public final class RecordedReadFrom {


    /** Authority of one VM-recorded read-from equality. */
    public static final String AUTHORITY = "VM_RECORDED_READ_FROM_V1";

    /** Provenance stamped on an edge the recorded evidence proved. */
    public static final String PROVENANCE_EXACT = "VM_RECORDED_EXACT";
    /** Provenance stamped on an edge the recorded evidence kept guarded. */
    public static final String PROVENANCE_GUARDED = "VM_RECORDED_GUARDED";
    public static final String PROVENANCE_CANDIDATE =
            "TRACE_CANDIDATE_WRITER";
    /** Provenance stamped on a candidate the recorded evidence ruled out. */
    public static final String PROVENANCE_EXCLUDED = "VM_RECORDED_EXCLUDED";

    /** Edge member naming the declared field a candidate is stated over. */
    public static final String EDGE_FIELD = "readFromField";
    /**
     * Edge member naming the source both endpoints were traced under.
     */
    public static final String EDGE_SOURCE_KEY = "readFromSourceKey";
    /** Edge member carrying the provenance state above. */
    public static final String EDGE_PROVENANCE = "readFromProvenance";
    /** Edge member naming why a provenance state is not a proof. */
    public static final String EDGE_PROVENANCE_GAP = "readFromProvenanceGap";
    public static final String EDGE_UNKNOWN_ARM = "readFromUnknownArm";

    /**
     * <p>The second level is what keeps README {@code STATE-1}'s "NN, Balancer
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
     */
    private Location deciding(String field, String readerSite) {
        return deciding(field, readerSite, 0L);
    }

    private Location deciding(String field, String readerSite,
                              long receiverObjectId) {
        if (readerSite == null || readerSite.isEmpty()) return null;
        List<Location> matches = new ArrayList<>();
        for (Location location : locations(field)) {
            if (receiverObjectId > 0L && location.receiverObjectId != 0L
                    && receiverObjectId != location.receiverObjectId) {
                continue;
            }
            if (!location.reads(readerSite)) continue;
            matches.add(location);
        }
        if (matches.size() == 1) return matches.get(0);
        if (matches.isEmpty()) return null;

        // One logical heap location is copied into one case-local snapshot
        // per replay path.  Canonical location keys intentionally include the
        // exact activation, while sessionLocationKey keeps the VM store
        // identity.  Join those snapshots only when every one names the same
        // non-empty VM store; otherwise multiple locations remain ambiguous.
        String session = matches.get(0).sessionLocationKey;
        if (session.isEmpty()) return null;
        for (Location location : matches) {
            if (!session.equals(location.sessionLocationKey)) return null;
        }
        return Location.combine(matches, session);
    }

    public boolean isEmpty() {
        return byField.isEmpty();
    }

    /**
     * Decides one writer/reader pair, both named by activation site.
     */
    public Decision decide(String field, String writerSite,
                           String readerSite) {
        return decide(field, writerSite, readerSite, 0L);
    }

    private Decision decide(String field, String writerSite,
                            String readerSite, long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        if (location == null || writerSite == null || writerSite.isEmpty()) {
            return Decision.NO_RECORDED_EVIDENCE;
        }
        return location.decide(writerSite, readerSite);
    }

    /**
     * The one activation of {@code regionId} this index recorded for
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

    private String locationKey(String field, String readerSite,
                               long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location == null ? "" : location.locationKey;
    }

    /**
     * Whether every writer of one field is both recorded and addressable.
     */
    public boolean writerSetComplete(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        return location != null && location.writerSetComplete
                && location.unaddressableWriters == 0;
    }

    private boolean writerSetComplete(String field, String readerSite,
                                      long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location != null && location.writerSetComplete
                && location.unaddressableWriters == 0;
    }

    /**
     * Whether the VM dropped read-log entries for this field's location.
     */
    public boolean readLogTruncated(String field, String readerSite) {
        Location location = deciding(field, readerSite);
        return location != null && location.readLogTruncated;
    }

    private boolean readLogTruncated(String field, String readerSite,
                                     long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location != null && location.readLogTruncated;
    }

    private String exactWriterSite(String field, String readerSite,
                                   long receiverObjectId,
                                   String requestedWriter) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location == null ? ""
                : location.writerSite(requestedWriter, readerSite);
    }

    private String exactReaderSite(String field, String readerSite,
                                   long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location == null ? "" : location.readerSite(readerSite);
    }

    private String sessionLocationKey(String field, String readerSite,
                                      long receiverObjectId) {
        Location location = deciding(field, readerSite, receiverObjectId);
        return location == null ? "" : location.sessionLocationKey;
    }


    /**
     * Resolves the trace's candidate writers against this run's recorded
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
            String writerOccurrence = string(binding,
                    "fromValueOccurrenceId");
            if (writerOccurrence.isEmpty()) {
                writerOccurrence = string(binding, "fromOccurrenceId");
            }
            long receiverObjectId = longInteger(binding,
                    "receiverObjectId", 0L);
            Decision decision = decide(field,
                    RecordedEvidenceIdentity.siteKey(
                            writerOccurrence),
                    readerSite, receiverObjectId);
            if (!decision.decides()) continue;
            decided++;
            String exactWriter = exactWriterSite(field, readerSite,
                    receiverObjectId, writerOccurrence);
            if (!exactWriter.isEmpty()) {
                binding.addProperty("fromValueOccurrenceId", exactWriter);
            }
            String exactReader = exactReaderSite(field, readerSite,
                    receiverObjectId);
            if (!exactReader.isEmpty()) {
                binding.addProperty("toValueOccurrenceId", exactReader);
            }
            binding.addProperty(EDGE_PROVENANCE, decision.provenance());
            binding.remove(EDGE_PROVENANCE_GAP);
            String location = locationKey(field, readerSite,
                    receiverObjectId);
            if (!location.isEmpty()) {
                binding.addProperty("locationKey", location);
            }
            String sessionLocation = sessionLocationKey(field, readerSite,
                    receiverObjectId);
            if (!sessionLocation.isEmpty()) {
                binding.addProperty(
                        SharedStateEvidence.SESSION_LOCATION_FIELD,
                        sessionLocation);
            }
            if (decision == Decision.RECORDED_EXCLUDED) {
                binding.addProperty(EDGE_PROVENANCE_GAP,
                        SharedStateEvidence.reason(
                                SharedStateEvidence.NOT_SELECTED));
            }
            // The unknown arm is a property of the location, not of the arm
            // that happens to be selected: a writer set that is incomplete or
            if (!writerSetComplete(field, readerSite, receiverObjectId)) {
                binding.addProperty(EDGE_UNKNOWN_ARM,
                        SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
                // A truncated read log is an open writer set for a different
                // reason, and the difference is what a reader acts on, so it
                binding.addProperty(EDGE_PROVENANCE_GAP,
                        SharedStateEvidence.reason(
                                readLogTruncated(field, readerSite,
                                        receiverObjectId)
                                ? SharedStateEvidence.READ_LOG_TRUNCATED
                                : SharedStateEvidence.UNKNOWN_WRITER));
            }
        }
        return decided;
    }

    /**
     * The named gap for a candidate no recorded evidence decided.
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




    /** One watched location, reduced to the identities a pairing can use. */
    private static final class Location {
        private String locationKey = "";
        private String sessionLocationKey = "";
        private boolean writerSetComplete = true;
        /** The VM dropped read-log entries for this location. */
        private boolean readLogTruncated;
        private int unaddressableWriters;
        private long receiverObjectId;
        private final Set<String> writers = new LinkedHashSet<>();
        private final Set<String> guardedReaders = new LinkedHashSet<>();
        private final Map<String, Set<String>> exactWriters =
                new LinkedHashMap<>();
        /** Exact selected edge ids of planned producer-state reads. */
        /** Activations of each static region, for region-only callers. */
        private final Map<String, Set<String>> sitesByRegion =
                new LinkedHashMap<>();
        /** Mutually-exclusive snapshots of one session location. */
        private List<Location> caseMembers = Collections.emptyList();

        /** Case-local snapshots of the same VM store, kept case-local. */
        private static Location combine(Collection<Location> members,
                                        String sessionLocationKey) {
            Location result = new Location();
            result.locationKey = sessionLocationKey;
            result.sessionLocationKey = sessionLocationKey;
            result.writerSetComplete = true;
            result.caseMembers = Collections.unmodifiableList(
                    new ArrayList<>(members));
            for (Location member : members) {
                result.writerSetComplete &= member.writerSetComplete;
                result.readLogTruncated |= member.readLogTruncated;
                result.unaddressableWriters += member.unaddressableWriters;
                if (result.receiverObjectId == 0L) {
                    result.receiverObjectId = member.receiverObjectId;
                } else if (member.receiverObjectId != 0L
                        && result.receiverObjectId
                        != member.receiverObjectId) {
                    result.receiverObjectId = -1L;
                }
            }
            return result;
        }

        private void absorb(JsonObject record) {
            JsonObject envelope = object(record, "envelope");
            locationKey = string(record, "locationKey");
            sessionLocationKey = SharedStateEvidence
                    .sessionLocationKey(record);
            long receiver = longInteger(object(record, "carrier"),
                    "receiverObjectId", 0L);
            if (receiverObjectId == 0L) receiverObjectId = receiver;
            else if (receiver > 0L && receiverObjectId != receiver) {
                receiverObjectId = -1L;
            }
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
                } else {
                    guardedReaders.add(reader);
                }
            }
        }

        /** Whether this store recorded a read performed by {@code site}. */
        private boolean reads(String site) {
            if (exactWriters.containsKey(site)
                    || guardedReaders.contains(site)) {
                return true;
            }
            String address = planned(site);
            for (String reader : exactWriters.keySet()) {
                if (address.equals(planned(reader))) return true;
            }
            for (String reader : guardedReaders) {
                if (address.equals(planned(reader))) return true;
            }
            return false;
        }

        private Decision decide(String writer, String reader) {
            if (!caseMembers.isEmpty()) {
                boolean guarded = false;
                for (Location member : caseMembers) {
                    Decision decision = member.decide(writer, reader);
                    if (decision == Decision.NO_RECORDED_EVIDENCE) {
                        return Decision.NO_RECORDED_EVIDENCE;
                    }
                    if (decision == Decision.RECORDED_EXACT) {
                        // A family of exact case-local reads needs exact
                        // version/order lowering per case.  Do not collapse it
                        // into one unconditional edge.
                        return Decision.NO_RECORDED_EVIDENCE;
                    }
                    guarded |= decision
                            == Decision.RECORDED_GUARDED_CANDIDATE;
                }
                return guarded
                        ? Decision.RECORDED_GUARDED_CANDIDATE
                        : Decision.RECORDED_EXCLUDED;
            }
            Set<String> exact = exactWriters.get(reader);
            if (exact != null) {
                return containsSite(exact, writer)
                        ? Decision.RECORDED_EXACT
                        : Decision.RECORDED_EXCLUDED;
            }
            if (guardedReaders.contains(reader)) {
                return containsSite(writers, writer)
                        ? Decision.RECORDED_GUARDED_CANDIDATE
                        : Decision.RECORDED_EXCLUDED;
            }

            String address = planned(reader);
            Set<String> commonExact = null;
            boolean guarded = false;
            for (Map.Entry<String, Set<String>> entry
                    : exactWriters.entrySet()) {
                if (!address.equals(planned(entry.getKey()))) continue;
                if (commonExact == null) {
                    commonExact = new LinkedHashSet<>(entry.getValue());
                } else if (!commonExact.equals(entry.getValue())) {
                    return Decision.NO_RECORDED_EVIDENCE;
                }
            }
            for (String candidate : guardedReaders) {
                if (address.equals(planned(candidate))) {
                    guarded = true;
                    break;
                }
            }
            if (guarded) {
                return containsSite(writers, writer)
                        ? Decision.RECORDED_GUARDED_CANDIDATE
                        : Decision.RECORDED_EXCLUDED;
            }
            if (commonExact != null) {
                return containsSite(commonExact, writer)
                        ? Decision.RECORDED_EXACT
                        : Decision.RECORDED_EXCLUDED;
            }
            return Decision.NO_RECORDED_EVIDENCE;
        }

        private String writerSite(String requested, String reader) {
            if (!caseMembers.isEmpty()) {
                Set<String> sites = new LinkedHashSet<>();
                for (Location member : caseMembers) {
                    if (member.decide(requested, reader)
                            != Decision.RECORDED_GUARDED_CANDIDATE) {
                        continue;
                    }
                    String site = member.writerSite(requested, reader);
                    if (site.isEmpty()) return "";
                    sites.add(site);
                }
                return sites.size() == 1
                        ? sites.iterator().next() : "";
            }
            if (writers.contains(requested)) return requested;
            String address = planned(requested);
            String answer = "";
            for (String writer : writers) {
                if (!address.equals(planned(writer))) continue;
                if (!answer.isEmpty() && !answer.equals(writer)) return "";
                answer = writer;
            }
            return answer;
        }

        private String readerSite(String requested) {
            if (!caseMembers.isEmpty()) return "";
            if (exactWriters.containsKey(requested)
                    || guardedReaders.contains(requested)) {
                return requested;
            }
            String address = planned(requested);
            String answer = "";
            Set<String> readers = new LinkedHashSet<>(
                    exactWriters.keySet());
            readers.addAll(guardedReaders);
            for (String reader : readers) {
                if (!address.equals(planned(reader))) continue;
                if (!answer.isEmpty() && !answer.equals(reader)) return "";
                answer = reader;
            }
            return answer;
        }

        private static boolean containsSite(Set<String> sites,
                                            String requested) {
            if (sites.contains(requested)) return true;
            String address = planned(requested);
            for (String site : sites) {
                if (address.equals(planned(site))) return true;
            }
            return false;
        }

        private static String planned(String occurrenceId) {
            return edu.uva.liftlab.graphchecker.contract.PathObservation
                    .plannedOccurrenceOf(occurrenceId);
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


    /** One artifact-ready description of what the index decided from. */
    public JsonObject toJson() {
        JsonObject index = new JsonObject();
        index.addProperty("schemaVersion", 1);
        index.addProperty("kind", "RECORDED_READ_FROM_INDEX");
        index.addProperty("authority", AUTHORITY);
        JsonArray fields = new JsonArray();
        // One row per watched location, never one per declared field: a field
        // several objects share is several stores, and averaging them into
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
