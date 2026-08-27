package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.textString;

/**
 * The target slice of the recorded session graph: the expression and event
 * nodes that can reach the target predicate, computed from what the session
 * recorded rather than from an offline reconstruction. The backward walk is
 * conservative in one direction only - a read pulls in every writer it could
 * have taken - because dropping a node costs soundness while keeping one
 * costs formula size. Evidence that cannot answer at all yields a named gap.
 */
public final class SessionTargetSlice {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "SESSION_TARGET_SLICE";
    public static final String AUTHORITY =
            "RECORDED_SESSION_GRAPH_SLICE_V1";

    /** Gap family of every refusal this projection makes. */
    public static final String GAP_KIND = "TARGET_SLICE_GAP";
    public static final String GAP_AUTHORITY =
            "RECORDED_SESSION_GRAPH_SLICE_GAP_V1";

    /** The target predicate mentions no node this session recorded. */
    public static final String NO_RECORDED_TARGET_REFERENCE =
            "TARGET_SLICE_NO_RECORDED_REFERENCE";
    /** A read reached the slice whose location was never a carrier. */
    public static final String UNRECORDED_READ =
            "TARGET_SLICE_UNRECORDED_READ";
    /** A candidate named a version no recorded store holds. */
    public static final String UNRECORDED_VERSION =
            "TARGET_SLICE_UNRECORDED_VERSION";
    /** A guarded read whose candidate set was not recorded as a term. */
    public static final String UNRECORDED_CANDIDATE_SET =
            "TARGET_SLICE_UNRECORDED_CANDIDATE_SET";
    /** A sliced node's event is absent from the order domain. */
    public static final String UNORDERED_EVENT =
            "TARGET_SLICE_UNORDERED_EVENT";
    /** The writer set of a sliced location has already lost writers. */
    public static final String INCOMPLETE_WRITER_SET =
            "TARGET_SLICE_INCOMPLETE_WRITER_SET";

    public static final String NODE_READ = "READ";
    public static final String NODE_VERSION = "VERSION";
    public static final String NODE_SYMBOL = "SYMBOL";

    private SessionTargetSlice() {
    }

    /**
     * Projects the target slice.
     *
     * <p>Roots come from two places. A <em>guarded</em> read is a node of the
     * target term, so scanning the predicate finds it; an <em>exact</em> read
     * is not, because the VM handed the reader its writer's own expression, so
     * {@code targetReadEvents} names those recorded event ids instead.
     * {@code orderedEvents} are events that need a position in the order
     * domain but are not nodes - an RPC export/attach pair is the case -
     * which walking them as reads would report as unrecorded reads.</p>
     */
    public static Slice project(Collection<JsonObject> versionRecords,
                                JsonObject ledgerRecord,
                                JsonElement targetPredicate,
                                Collection<Long> targetReadEvents,
                                Collection<Long> orderedEvents) {
        RecordedGraph graph = new RecordedGraph(versionRecords);
        SessionOrderDomain domain = SessionOrderDomain.of(ledgerRecord);
        Slice slice = new Slice(domain);
        if (orderedEvents != null) {
            for (Long event : orderedEvents) {
                if (event != null && event > 0L) {
                    slice.orderedOnly.add(event);
                }
            }
        }
        References roots = new References();
        graph.collect(targetPredicate, roots);
        if (targetReadEvents != null) {
            for (Long read : targetReadEvents) {
                if (read != null && read > 0L) roots.reads.add(read);
            }
        }
        if (roots.isEmpty()) {
            slice.gap(NO_RECORDED_TARGET_REFERENCE, "",
                    "target predicate mentions no recorded read or symbol");
            slice.close(graph, domain);
            return slice;
        }
        Deque<String> frontier = new ArrayDeque<>();
        for (long read : roots.reads) frontier.push(NODE_READ + ":" + read);
        for (String symbol : roots.symbols) {
            frontier.push(NODE_SYMBOL + ":" + symbol);
        }
        while (!frontier.isEmpty()) {
            String nodeId = frontier.pop();
            if (!slice.add(nodeId)) continue;
            int separator = nodeId.indexOf(':');
            String kind = nodeId.substring(0, separator);
            String identity = nodeId.substring(separator + 1);
            if (NODE_READ.equals(kind)) {
                expandRead(graph, slice, Long.parseLong(identity), frontier);
            } else if (NODE_VERSION.equals(kind)) {
                expandVersion(graph, slice, Long.parseLong(identity),
                        frontier);
            }
        }
        slice.close(graph, domain);
        return slice;
    }

    /**
     * A read pulls in the writers it could have taken: an exact read exactly
     * one, a guarded read every candidate its term names plus the
     * unknown-writer symbol, which is a slice node like any other.
     */
    private static void expandRead(RecordedGraph graph, Slice slice,
                                   long readEventId,
                                   Deque<String> frontier) {
        JsonObject guarded = graph.guardedReads.get(readEventId);
        if (guarded != null) {
            for (JsonElement element : array(guarded, "candidates")) {
                JsonObject candidate = element.getAsJsonObject();
                if (bool(candidate, "unknown", false)) {
                    References unknown = new References();
                    graph.collect(candidate.get("expression"), unknown);
                    for (String symbol : unknown.symbols) {
                        frontier.push(NODE_SYMBOL + ":" + symbol);
                    }
                    continue;
                }
                frontier.push(NODE_VERSION + ":"
                        + longInteger(candidate, "fieldVersionId", 0L));
            }
            if (!bool(guarded, "writerSetComplete", false)) {
                slice.gap(INCOMPLETE_WRITER_SET,
                        SharedStateEvidence.locationKey(guarded),
                        "guarded read " + readEventId
                                + " reads a location that has lost writers");
            }
            return;
        }
        RecordedRead read = graph.reads.get(readEventId);
        if (read == null) {
            slice.gap(UNRECORDED_READ, "",
                    "read event " + readEventId
                            + " has no recorded version store");
            return;
        }
        if (SharedStateEvidence.RESOLUTION_EXACT.equals(read.resolution)) {
            frontier.push(NODE_VERSION + ":" + read.chosenVersionId);
            return;
        }
        // The read record proves the choice was not decided, but only the
        // guarded term names which writers competed.  Without that term every
        // version of the location stays reachable: narrowing the set here
        // would be the read-from guess the design forbids, in the direction
        // that loses writers.
        slice.gap(UNRECORDED_CANDIDATE_SET, read.locationKey,
                "guarded read " + readEventId
                        + " kept every recorded writer of its location");
        for (Long version : graph.versionsAt(read.locationKey)) {
            frontier.push(NODE_VERSION + ":" + version);
        }
    }

    private static void expandVersion(RecordedGraph graph, Slice slice,
                                      long fieldVersionId,
                                      Deque<String> frontier) {
        RecordedVersion version = graph.versions.get(fieldVersionId);
        if (version == null) {
            slice.gap(UNRECORDED_VERSION, "",
                    "field version " + fieldVersionId
                            + " is named by a candidate but not recorded");
            return;
        }
        References referenced = new References();
        graph.collect(version.expression, referenced);
        graph.collect(version.pathGuard, referenced);
        for (long read : referenced.reads) {
            frontier.push(NODE_READ + ":" + read);
        }
        for (String symbol : referenced.symbols) {
            frontier.push(NODE_SYMBOL + ":" + symbol);
        }
    }

    /** One projected slice: its nodes, its events and its order. */
    public static final class Slice {
        private final SessionOrderDomain domain;
        private final Set<String> nodes = new LinkedHashSet<>();
        private final List<JsonObject> gaps = new ArrayList<>();
        private final Set<String> gapKeys = new LinkedHashSet<>();
        private final Set<Long> eventIds = new TreeSet<>();
        /** Events that need a position but are not nodes of the drawing. */
        private final Set<Long> orderedOnly = new TreeSet<>();
        private List<JsonObject> order = Collections.emptyList();
        private final List<JsonObject> nodeRows = new ArrayList<>();
        private final Map<Long, JsonObject> guardedReads =
                new LinkedHashMap<>();

        private Slice(SessionOrderDomain domain) {
            this.domain = domain;
        }

        private boolean add(String nodeId) { return nodes.add(nodeId); }

        private void gap(String reason, String locationKey, String detail) {
            String key = reason + "\n" + locationKey + "\n" + detail;
            if (!gapKeys.add(key)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", GAP_KIND);
            gap.addProperty("schemaVersion", SCHEMA_VERSION);
            gap.addProperty("reason", reason);
            gap.addProperty("authority", GAP_AUTHORITY);
            gap.addProperty("locationKey", locationKey == null
                    ? "" : locationKey);
            gap.addProperty("detail", detail);
            gaps.add(gap);
        }

        private void close(RecordedGraph graph, SessionOrderDomain domain) {
            for (String nodeId : nodes) {
                int separator = nodeId.indexOf(':');
                String kind = nodeId.substring(0, separator);
                String identity = nodeId.substring(separator + 1);
                JsonObject row = new JsonObject();
                row.addProperty("nodeId", nodeId);
                row.addProperty("nodeKind", kind);
                if (NODE_SYMBOL.equals(kind)) {
                    row.addProperty("symbol", identity);
                    nodeRows.add(row);
                    continue;
                }
                long eventId = Long.parseLong(identity);
                row.addProperty("eventId", eventId);
                if (NODE_READ.equals(kind)) {
                    RecordedRead read = graph.reads.get(eventId);
                    JsonObject guarded = graph.guardedReads.get(eventId);
                    if (guarded != null) guardedReads.put(eventId, guarded);
                    row.addProperty("resolution", read != null
                            ? read.resolution
                            : guarded != null
                            ? SharedStateEvidence.RESOLUTION_GUARDED : "");
                    row.addProperty("locationKey", read != null
                            ? read.locationKey
                            : guarded != null
                            ? SharedStateEvidence.locationKey(guarded) : "");
                } else {
                    RecordedVersion version = graph.versions.get(eventId);
                    row.addProperty("locationKey", version == null
                            ? "" : version.locationKey);
                    row.addProperty("regionId", version == null
                            ? "" : version.regionId);
                    row.addProperty("taskId", version == null
                            ? "" : version.taskId);
                }
                nodeRows.add(row);
                if (domain.knows(eventId)) {
                    eventIds.add(eventId);
                } else if (!domain.isEmpty()) {
                    gap(UNORDERED_EVENT, "", "event " + eventId
                            + " is not in the recorded order domain");
                }
            }
            for (Long event : orderedOnly) {
                if (domain.knows(event)) eventIds.add(event);
            }
            eventIds.addAll(adjacentChannelEvents(domain, eventIds));
            order = domain.project(eventIds);
        }

        /**
         * The other-channel events that directly order a sliced event. One
         * hop on purpose: a lifecycle, volatile or handoff event that ordered
         * a sliced write is a fact about this slice, unrelated session
         * traffic is not. Program order adds nothing the field events lack.
         */
        private static Set<Long> adjacentChannelEvents(
                SessionOrderDomain domain, Set<Long> sliced) {
            Set<Long> adjacent = new TreeSet<>();
            for (JsonObject edge : domain.directEdges()) {
                String kind = string(edge, "edgeKind");
                if ("PROGRAM_ORDER".equals(kind)) continue;
                long before = longInteger(edge, "beforeEventId", 0L);
                long after = longInteger(edge, "afterEventId", 0L);
                if (sliced.contains(before) && !sliced.contains(after)) {
                    adjacent.add(after);
                } else if (sliced.contains(after)
                        && !sliced.contains(before)) {
                    adjacent.add(before);
                }
            }
            return adjacent;
        }

        public boolean containsRead(long readEventId) {
            return nodes.contains(NODE_READ + ":" + readEventId);
        }

        public boolean containsVersion(long fieldVersionId) {
            return nodes.contains(NODE_VERSION + ":" + fieldVersionId);
        }

        public boolean containsSymbol(String symbol) {
            return nodes.contains(NODE_SYMBOL + ":" + symbol);
        }

        /** Sliced events, ascending; every one is in the order domain. */
        public Set<Long> eventIds() {
            return Collections.unmodifiableSet(eventIds);
        }

        /** The order domain restricted to this slice. */
        public List<JsonObject> order() {
            return Collections.unmodifiableList(order);
        }

        /**
         * The guarded read-from terms of the sliced reads, by read event.
         * An exact read has none: it took the writer's expression directly.
         */
        public Map<Long, JsonObject> guardedReads() {
            return Collections.unmodifiableMap(guardedReads);
        }

        public List<JsonObject> gaps() {
            return Collections.unmodifiableList(gaps);
        }

        /** Whether the recorded graph reaches the target predicate at all. */
        public boolean reachesTarget() { return !nodes.isEmpty(); }

        public SessionOrderDomain orderDomain() { return domain; }

        /** The slice as one artifact-ready object. */
        public JsonObject toJson() {
            JsonObject slice = new JsonObject();
            slice.addProperty("schemaVersion", SCHEMA_VERSION);
            slice.addProperty("kind", KIND);
            slice.addProperty("authority", AUTHORITY);
            slice.addProperty("reachesTarget", reachesTarget());
            JsonArray rows = new JsonArray();
            for (JsonObject row : nodeRows) rows.add(row.deepCopy());
            slice.add("nodes", rows);
            JsonArray events = new JsonArray();
            for (Long event : eventIds) events.add(event);
            slice.add("eventIds", events);
            JsonArray relation = new JsonArray();
            for (JsonObject edge : order) relation.add(edge.deepCopy());
            slice.add("order", relation);
            JsonArray recorded = new JsonArray();
            for (JsonObject gap : gaps) recorded.add(gap.deepCopy());
            slice.add("gaps", recorded);
            return slice;
        }
    }

    /** Identities one expression tree mentions. */
    private static final class References {
        private final Set<Long> reads = new LinkedHashSet<>();
        private final Set<String> symbols = new LinkedHashSet<>();

        private boolean isEmpty() {
            return reads.isEmpty() && symbols.isEmpty();
        }
    }

    /** One published write version, as the session recorded it. */
    private static final class RecordedVersion {
        private final String locationKey;
        private final String regionId;
        private final String taskId;
        private final JsonElement expression;
        private final JsonElement pathGuard;

        private RecordedVersion(String locationKey, JsonObject version) {
            this.locationKey = locationKey;
            this.regionId = string(version, "regionId");
            this.taskId = string(version, "taskId");
            this.expression = version.get("expression");
            this.pathGuard = version.get("pathGuard");
        }
    }

    /** One resolved read, as the session recorded it. */
    private static final class RecordedRead {
        private final String locationKey;
        private final String resolution;
        private final long chosenVersionId;

        private RecordedRead(String locationKey, JsonObject read) {
            this.locationKey = locationKey;
            this.resolution = string(read, "resolution");
            this.chosenVersionId = longInteger(read,
                    "chosenFieldVersionId", 0L);
        }
    }

    /** The recorded evidence, indexed by the identities the slice walks. */
    private static final class RecordedGraph {
        private final Map<Long, RecordedVersion> versions =
                new LinkedHashMap<>();
        private final Map<Long, RecordedRead> reads = new LinkedHashMap<>();
        private final Map<String, Set<Long>> versionsByLocation =
                new LinkedHashMap<>();
        private final Map<Long, JsonObject> guardedReads =
                new LinkedHashMap<>();

        private RecordedGraph(Collection<JsonObject> versionRecords) {
            if (versionRecords == null) return;
            for (JsonObject record : versionRecords) {
                if (!SharedStateEvidence.isVersionsRecord(record)) continue;
                JsonObject envelope = object(record, "envelope");
                String locationKey = SharedStateEvidence.locationKey(
                        envelope);
                for (JsonElement element : array(envelope, "versions")) {
                    JsonObject version = element.getAsJsonObject();
                    long id = longInteger(version, "fieldVersionId", 0L);
                    versions.put(id,
                            new RecordedVersion(locationKey, version));
                    versionsAt(locationKey).add(id);
                    // A version's own value may itself be a guarded read of
                    // another location, so the index has to see through it.
                    collect(version.get("expression"), new References());
                    collect(version.get("pathGuard"), new References());
                }
                for (JsonElement element : array(envelope, "reads")) {
                    JsonObject read = element.getAsJsonObject();
                    reads.put(longInteger(read, "readEventId", 0L),
                            new RecordedRead(locationKey, read));
                }
            }
        }

        private Set<Long> versionsAt(String locationKey) {
            Set<Long> at = versionsByLocation.get(locationKey);
            if (at == null) {
                at = new LinkedHashSet<>();
                versionsByLocation.put(locationKey, at);
            }
            return at;
        }

        /**
         * Walks one expression term, noting the recorded identities it
         * mentions. A node that claims to be a guarded read but does not pass
         * admission is walked as an ordinary term: it still holds symbols.
         */
        private void collect(JsonElement node, References into) {
            if (node == null || node.isJsonNull()) return;
            if (node.isJsonArray()) {
                for (JsonElement element : node.getAsJsonArray()) {
                    collect(element, into);
                }
                return;
            }
            if (!node.isJsonObject()) return;
            JsonObject term = node.getAsJsonObject();
            String type = textString(term, "_type");
            if ("SymbolExpression".equals(type)) {
                String symbol = textString(term, "_exp");
                if (!symbol.isEmpty()) into.symbols.add(symbol);
            } else if (SharedStateEvidence.claimsGuardedRead(term)
                    && SharedStateEvidence.isGuardedRead(term)) {
                long readEventId = longInteger(term, "readEventId", 0L);
                into.reads.add(readEventId);
                guardedReads.put(readEventId, term);
                // The candidate arms are reached through the read node, not
                // by inlining them here: which of them the slice keeps is the
                // read's own question.
                return;
            }
            for (Map.Entry<String, JsonElement> entry : term.entrySet()) {
                collect(entry.getValue(), into);
            }
        }
    }
}
