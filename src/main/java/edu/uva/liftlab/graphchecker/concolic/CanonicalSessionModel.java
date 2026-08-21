package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The one canonical model the SMT and the causal graph are both projections of.
 *
 * <p>The composition already held every part of it - the local region
 * relations it lowered, the occurrences and ports it bound, the recorded field
 * versions and reads it sliced, the VM handoffs it recorded, the event order
 * it asserted, the target it was built for, and the gaps it could not close.
 * Until now those parts only left the composer as separate manifest members,
 * and the graph rebuilt a second causal reading of them from the runtime plan's
 * edge catalog. Two readings of one run is one reading too many: whichever
 * disagreed, nothing in the artifacts said which.</p>
 *
 * <p>So the composer assembles them once, here, into a node table, a set of
 * value bindings and a set of order relations, each row naming its own two
 * endpoints. The SMT is the formula those rows were lowered into; the graph is
 * a diagnostic drawing of the same rows and owns no acceptance decision.</p>
 *
 * <p>Nothing here observes anything new. Every field is copied from a manifest
 * member or from the selected relations, and a row this class cannot address -
 * an occurrence with no known source, an order edge over an event the node
 * table does not hold - becomes a named gap instead of an invented endpoint.
 * </p>
 */
public final class CanonicalSessionModel {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "CANONICAL_SESSION_MODEL";
    public static final String AUTHORITY = "CANONICAL_SESSION_MODEL_V1";

    /** Manifest member the composed model travels in. */
    public static final String MANIFEST_FIELD = "canonicalModel";

    // ----- evidence states ------------------------------------------------

    /** The VM proved one writer or one delivery; a direct equality. */
    public static final String EXACT = "EXACT";
    /** One arm of a recorded choice, selected by its own Boolean. */
    public static final String GUARDED = "GUARDED";
    /** The unconditional arm that admits a writer nobody recorded. */
    public static final String UNKNOWN_ARM = "UNKNOWN_ARM";
    /** A recorded order relation, carrying no value of its own. */
    public static final String NATURAL_ORDER = "NATURAL_ORDER";
    /** A resolved trace edge that never became a value binding. */
    public static final String CANDIDATE = "CANDIDATE";
    /** Identity and containment, which state no evidence at all. */
    public static final String STRUCTURAL = "STRUCTURAL";

    // ----- node types -----------------------------------------------------

    public static final String NODE_SOURCE = "SOURCE";
    public static final String NODE_REGION = "REGION_OCCURRENCE";
    public static final String NODE_FIELD_VERSION = "FIELD_VERSION";
    public static final String NODE_FIELD_READ = "FIELD_READ";
    public static final String NODE_UNKNOWN_WRITER = "UNKNOWN_WRITER";
    public static final String NODE_SESSION_EVENT = "SESSION_EVENT";
    public static final String NODE_TARGET_BRANCH = "TARGET_BRANCH";
    // ----- structural edge kinds ------------------------------------------

    public static final String SOURCE_CONTAINS_REGION =
            "SOURCE_CONTAINS_REGION";
    public static final String REGION_REACHES_TARGET_BRANCH =
            "REGION_REACHES_TARGET_BRANCH";
    // ----- gaps this assembly can raise -----------------------------------

    /** An occurrence no selected relation attributes to a source. */
    public static final String SOURCE_KEY_UNAVAILABLE =
            "CANONICAL_SOURCE_KEY_UNAVAILABLE";
    /** An order relation over an event the node table does not hold. */
    public static final String ORDER_EVENT_UNAVAILABLE =
            "CANONICAL_ORDER_EVENT_UNAVAILABLE";
    /** A value binding whose two endpoints cannot both be named. */
    public static final String BINDING_ENDPOINT_UNAVAILABLE =
            "CANONICAL_BINDING_ENDPOINT_UNAVAILABLE";

    private CanonicalSessionModel() {
    }

    /**
     * Assembles the canonical model of one composition.
     *
     * @param manifest         the composed manifest, with every member the
     *                         composition has already emitted
     * @param localRelations   one row per selected region relation, as
     *                         {@link #relation} builds it
     * @param resolvedEdges    one row per resolved trace edge, as
     *                         {@link #resolvedEdge} builds it; the manifest
     *                         carries only their ids, and a candidate needs
     *                         its two endpoints to be drawable at all
     * @param targetRegionId   the region the target branch belongs to
     * @param targetOccurrence the activation of that region
     */
    public static JsonObject of(JsonObject manifest, JsonArray localRelations,
                                JsonArray resolvedEdges,
                                String targetRegionId,
                                String targetOccurrence) {
        return new Assembly(manifest, localRelations, resolvedEdges,
                targetRegionId, targetOccurrence).build();
    }

    /** One resolved trace edge's endpoints, as the model records them. */
    public static JsonObject resolvedEdge(String edgeId,
                                          String fromOccurrenceId,
                                          String toOccurrenceId,
                                          String fromOutputPort,
                                          String toInputPort) {
        JsonObject row = new JsonObject();
        row.addProperty("edgeId", edgeId);
        row.addProperty("fromOccurrenceId", fromOccurrenceId);
        row.addProperty("toOccurrenceId", toOccurrenceId);
        row.addProperty("fromOutputPort", fromOutputPort);
        row.addProperty("toInputPort", toInputPort);
        return row;
    }

    /** One selected local region relation, as the model records it. */
    public static JsonObject relation(String summaryId,
                                          String relationKey,
                                          String regionId,
                                          String occurrenceId,
                                          String sourceKey,
                                          int caseCount,
                                          String pathCoverageState) {
        JsonObject row = new JsonObject();
        row.addProperty("summaryId", summaryId);
        row.addProperty("relationKey", relationKey);
        row.addProperty("regionId", regionId);
        row.addProperty("occurrenceId", occurrenceId);
        row.addProperty("sourceKey", sourceKey);
        row.addProperty("caseCount", caseCount);
        // No default: a relation that declared no coverage state is drawn as
        // one that declared none, never as a closed one.
        row.addProperty("pathCoverageState", pathCoverageState);
        return row;
    }

    /** Whether {@code model} is a canonical model this class produced. */
    public static boolean isModel(JsonObject model) {
        return model != null && KIND.equals(string(model, "kind"))
                && AUTHORITY.equals(string(model, "authority"));
    }

    /**
     * The canonical model inside {@code artifact}, which may be the composed
     * manifest carrying it or the model itself.
     */
    public static JsonObject read(JsonObject artifact) {
        if (isModel(artifact)) return artifact;
        JsonObject member = object(artifact, MANIFEST_FIELD);
        return isModel(member) ? member : new JsonObject();
    }

    /**
     * The stable key of one SMT value binding.
     *
     * <p>The audit recomputes it from the raw manifest rows and the graph
     * carries it on every projected edge, so the three artifacts are compared
     * by the binding's own identity rather than by position in a list.</p>
     */
    public static String valueBindingKey(JsonObject row) {
        String kind = string(row, "kind");
        // A VM handoff row carries its own identity - the ledger export
        // event the attach referenced - and that identity is the key.
        if (VmHandoffEvidence.BINDING_KIND.equals(kind)) {
            return string(row, "bindingKey");
        }
        if ("RECORDED_READ_FROM_VALUE_BINDING".equals(kind)) {
            return kind + "\n" + longInteger(row, "readEventId", 0L) + "\n"
                    + string(row, "arm");
        }
        if ("RECORDED_EXACT_VALUE_BINDING".equals(kind)) {
            return kind + "\n" + string(row, "edgeId") + "\n"
                    + string(row, "fromOutputPort") + "\n"
                    + string(row, "toInputPort");
        }
        if ("RECORDED_GUARDED_READ_PORT_BINDING".equals(kind)) {
            return kind + "\n" + string(row, "edgeId") + "\n"
                    + string(row, "toInputPort");
        }
        return kind + "\n" + string(row, "edgeId");
    }

    /** The key of the candidate row one unbound resolved edge becomes. */
    public static String candidateBindingKey(String edgeId) {
        return "RESOLVED_EDGE_CANDIDATE\n" + edgeId;
    }

    /** The stable key of one recorded order relation. */
    public static String orderRelationKey(JsonObject edge) {
        return longInteger(edge, "beforeEventId", 0L) + "\n"
                + longInteger(edge, "afterEventId", 0L) + "\n"
                + string(edge, "edgeKind");
    }

    static String identity(String prefix, String key) {
        return prefix + ":" + ArtifactIO.sha256(key).substring(0, 16);
    }

    // ----- assembly -------------------------------------------------------

    /** One pass over the composed manifest, building the one model. */
    private static final class Assembly {
        private final JsonObject manifest;
        private final JsonArray localRelations;
        private final Map<String, JsonObject> resolvedEdges =
                new LinkedHashMap<>();
        private final String targetRegionId;
        private final String targetOccurrence;

        private final Map<String, JsonObject> nodes = new LinkedHashMap<>();
        private final Map<String, String> sourceByOccurrence =
                new LinkedHashMap<>();
        private final Map<String, String> regionByOccurrence =
                new LinkedHashMap<>();
        private final Map<Long, String> nodeByEvent = new LinkedHashMap<>();
        private final JsonArray sourceOccurrences = new JsonArray();
        private final JsonArray fieldVersions = new JsonArray();
        private final JsonArray fieldReads = new JsonArray();
        private final JsonArray valueBindings = new JsonArray();
        private final JsonArray eventOrder = new JsonArray();
        private final JsonArray structuralEdges = new JsonArray();
        private final JsonArray boundedLoopRows = new JsonArray();
        private final JsonArray gaps = new JsonArray();
        private final Set<String> bindingKeys = new LinkedHashSet<>();
        private final Set<String> symbols = new LinkedHashSet<>();
        private final Set<Long> orderedEvents = new LinkedHashSet<>();
        private int sessionEvents;

        private Assembly(JsonObject manifest, JsonArray localRelations,
                         JsonArray resolvedEdges, String targetRegionId,
                         String targetOccurrence) {
            this.manifest = manifest == null ? new JsonObject() : manifest;
            this.localRelations = localRelations == null
                    ? new JsonArray() : localRelations;
            if (resolvedEdges != null) {
                for (JsonElement element : resolvedEdges) {
                    if (!element.isJsonObject()) continue;
                    JsonObject row = element.getAsJsonObject();
                    this.resolvedEdges.put(string(row, "edgeId"), row);
                }
            }
            this.targetRegionId = firstNonBlank(targetRegionId);
            this.targetOccurrence = firstNonBlank(targetOccurrence);
        }

        private JsonObject build() {
            JsonObject recorded = object(manifest, "recordedSessionModel");
            JsonObject slice = object(recorded, "targetSlice");
            relations();
            boundedLoops();
            sliceNodes(slice);
            bindings();
            candidates();
            order(array(recorded, "order"));
            String branch = targetBranch();
            collectGaps();

            JsonObject model = new JsonObject();
            model.addProperty("schemaVersion", SCHEMA_VERSION);
            model.addProperty("kind", KIND);
            model.addProperty("authority", AUTHORITY);
            model.add("target", target(branch, recorded, slice));
            model.add("localRelations", localRelations.deepCopy());
            model.add("boundedLoops", boundedLoopRows);
            model.add("sourceOccurrences", sourceOccurrences);
            model.add("fieldVersions", fieldVersions);
            model.add("fieldReads", fieldReads);
            model.add("nodes", nodeRows());
            model.add("valueBindings", valueBindings);
            model.add("eventOrder", eventOrder);
            model.add("structuralEdges", structuralEdges);
            model.add("gaps", gaps);
            model.add("counts", counts());
            return model;
        }

        // ----- identity -----------------------------------------------

        private JsonObject node(String nodeId, String nodeType) {
            JsonObject held = nodes.get(nodeId);
            if (held != null) return held;
            JsonObject row = new JsonObject();
            row.addProperty("nodeId", nodeId);
            row.addProperty("nodeType", nodeType);
            nodes.put(nodeId, row);
            return row;
        }

        private JsonArray nodeRows() {
            JsonArray rows = new JsonArray();
            for (JsonObject row : nodes.values()) rows.add(row);
            return rows;
        }

        private String sourceNode(String sourceKey) {
            String nodeId = identity("source", sourceKey);
            JsonObject row = node(nodeId, NODE_SOURCE);
            row.addProperty("sourceKey", sourceKey);
            return nodeId;
        }

        /**
         * The node of one activation.
         *
         * <p>The source comes from a selected relation where one names this
         * activation, and otherwise from the activation's own canonical
         * address, which is minted as {@code <sourceKey>/region/<region>#<n>}
         * and parsed in exactly that shape here. That is not a guess about
         * which source is nearby - it is the id the activation carries. The
         * target activation is why it matters: it deliberately publishes no
         * relation summary, so a source drawn only from relations would leave
         * every campaign's target unattributed under a gap no evidence could
         * ever close.</p>
         *
         * <p>An occurrence whose id is not in that canonical shape still gets
         * a node - it is a real activation the composition bound ports on -
         * but no source edge and one named gap, because attributing it to
         * whichever source happens to be nearby is exactly the guess the
         * identity rules forbid.</p>
         */
        private String regionNode(String occurrenceId) {
            if (occurrenceId.isEmpty()) return "";
            String nodeId = identity("region", occurrenceId);
            if (nodes.containsKey(nodeId)) return nodeId;
            JsonObject row = node(nodeId, NODE_REGION);
            row.addProperty("occurrenceId", occurrenceId);
            String regionId = firstNonBlank(
                    regionByOccurrence.get(occurrenceId),
                    targetOccurrence.equals(occurrenceId)
                            ? targetRegionId : "");
            row.addProperty("regionId", regionId);
            String sourceKey = firstNonBlank(
                    sourceByOccurrence.get(occurrenceId),
                    canonicalSourceKey(occurrenceId));
            row.addProperty("sourceKey", sourceKey);
            row.addProperty("target", targetOccurrence.equals(occurrenceId));
            JsonObject occurrence = new JsonObject();
            occurrence.addProperty("occurrenceId", occurrenceId);
            occurrence.addProperty("regionId", regionId);
            occurrence.addProperty("sourceKey", sourceKey);
            occurrence.addProperty("nodeId", nodeId);
            occurrence.addProperty("target",
                    targetOccurrence.equals(occurrenceId));
            sourceOccurrences.add(occurrence);
            if (sourceKey.isEmpty()) {
                gap("MODEL", SOURCE_KEY_UNAVAILABLE, occurrenceId,
                        "no selected relation attributes this activation to a"
                                + " source");
                return nodeId;
            }
            structural(SOURCE_CONTAINS_REGION, sourceNode(sourceKey), nodeId);
            return nodeId;
        }

        /** The source half of a canonical occurrence address, or "". */
        private static String canonicalSourceKey(String occurrenceId) {
            int cut = occurrenceId.indexOf("/region/");
            return cut <= 0 ? "" : occurrenceId.substring(0, cut);
        }

        private void structural(String kind, String from, String to) {
            if (from.isEmpty() || to.isEmpty()) return;
            String key = kind + "\n" + from + "\n" + to;
            for (JsonElement element : structuralEdges) {
                if (key.equals(string(element.getAsJsonObject(),
                        "edgeKey"))) {
                    return;
                }
            }
            JsonObject row = new JsonObject();
            row.addProperty("structuralId", identity("structure", key));
            row.addProperty("edgeKey", key);
            row.addProperty("kind", kind);
            row.addProperty("evidenceState", STRUCTURAL);
            row.addProperty("fromNodeId", from);
            row.addProperty("toNodeId", to);
            structuralEdges.add(row);
        }

        // ----- members ------------------------------------------------

        private void relations() {
            for (JsonElement element : localRelations) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String occurrence = string(row, "occurrenceId");
                if (occurrence.isEmpty()) continue;
                String sourceKey = string(row, "sourceKey");
                if (!sourceKey.isEmpty()) {
                    sourceByOccurrence.put(occurrence, sourceKey);
                }
                String regionId = string(row, "regionId");
                if (!regionId.isEmpty()) {
                    regionByOccurrence.put(occurrence, regionId);
                }
            }
            for (JsonElement element : localRelations) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                regionNode(string(row, "occurrenceId"));
            }
            regionNode(targetOccurrence);
        }

        /** Copies declared bounds and observed path counts into the model. */
        private void boundedLoops() {
            JsonObject composition = object(manifest,
                    BoundedLoopComposition.MANIFEST_FIELD);
            for (JsonElement element : array(composition, "boundedLoops")) {
                if (!element.isJsonObject()) continue;
                boundedLoopRows.add(element.getAsJsonObject().deepCopy());
            }
        }

        /**
         * Lifts the sliced field versions, reads and symbols into nodes.
         *
         * <p>A symbol is not a node of the drawing: it names a free input, so
         * it has no incident recorded relation and would only add an isolated
         * dot. It is counted instead, which is the honest record that the
         * slice kept it.</p>
         */
        private void sliceNodes(JsonObject slice) {
            for (JsonElement element : array(slice, "eventIds")) {
                if (element.isJsonPrimitive()) {
                    orderedEvents.add(element.getAsLong());
                }
            }
            for (JsonElement element : array(slice, "nodes")) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String nodeKind = string(row, "nodeKind");
                if (SessionTargetSlice.NODE_SYMBOL.equals(nodeKind)) {
                    symbols.add(string(row, "symbol"));
                    continue;
                }
                long eventId = longInteger(row, "eventId", 0L);
                boolean read = SessionTargetSlice.NODE_READ.equals(nodeKind);
                String nodeId = identity(read ? "read" : "version",
                        String.valueOf(eventId));
                JsonObject graphNode = node(nodeId, read
                        ? NODE_FIELD_READ : NODE_FIELD_VERSION);
                String locationKey = string(row, "locationKey");
                // A map-state version and a map query are nodes of the same
                // two kinds a field version and a field read are: what the
                // location is differs, what the node is does not.  The kind
                // is carried so the drawing can say which, without a third
                // node type nothing else in the model would know about.
                String locationKind = SharedStateEvidence.locationKindOf(
                        locationKey);
                graphNode.addProperty("eventId", eventId);
                graphNode.addProperty("locationKey", locationKey);
                graphNode.addProperty("locationKind", locationKind);
                graphNode.addProperty("ordered",
                        orderedEvents.contains(eventId));
                JsonObject member = new JsonObject();
                member.addProperty("eventId", eventId);
                member.addProperty("locationKey", locationKey);
                member.addProperty("locationKind", locationKind);
                member.addProperty("nodeId", nodeId);
                member.addProperty("ordered", orderedEvents.contains(eventId));
                if (read) {
                    String resolution = string(row, "resolution");
                    graphNode.addProperty("resolution", resolution);
                    member.addProperty("resolution", resolution);
                    fieldReads.add(member);
                } else {
                    graphNode.addProperty("regionId", string(row, "regionId"));
                    graphNode.addProperty("taskId", string(row, "taskId"));
                    member.addProperty("regionId", string(row, "regionId"));
                    member.addProperty("taskId", string(row, "taskId"));
                    fieldVersions.add(member);
                }
                nodeByEvent.put(eventId, nodeId);
            }
        }

        /** The node of one recorded event, minting a bare one if needed. */
        private String eventNode(long eventId) {
            String held = nodeByEvent.get(eventId);
            if (held != null) return held;
            String nodeId = identity("event", String.valueOf(eventId));
            JsonObject row = node(nodeId, NODE_SESSION_EVENT);
            row.addProperty("eventId", eventId);
            row.addProperty("ordered", orderedEvents.contains(eventId));
            nodeByEvent.put(eventId, nodeId);
            sessionEvents++;
            return nodeId;
        }

        private String readNode(long readEventId) {
            String nodeId = identity("read", String.valueOf(readEventId));
            JsonObject row = node(nodeId, NODE_FIELD_READ);
            row.addProperty("eventId", readEventId);
            row.addProperty("ordered", orderedEvents.contains(readEventId));
            nodeByEvent.put(readEventId, nodeId);
            return nodeId;
        }

        private String versionNode(long fieldVersionId) {
            String nodeId = identity("version",
                    String.valueOf(fieldVersionId));
            JsonObject row = node(nodeId, NODE_FIELD_VERSION);
            row.addProperty("eventId", fieldVersionId);
            row.addProperty("ordered",
                    orderedEvents.contains(fieldVersionId));
            nodeByEvent.put(fieldVersionId, nodeId);
            return nodeId;
        }

        private String unknownWriterNode(long readEventId) {
            String nodeId = identity("unknown", String.valueOf(readEventId));
            JsonObject row = node(nodeId, NODE_UNKNOWN_WRITER);
            row.addProperty("readEventId", readEventId);
            return nodeId;
        }

        /** One normalized row per lowered SMT value binding. */
        private void bindings() {
            for (JsonElement element
                    : array(manifest, "recordedValueBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                String kind = string(raw, "kind");
                JsonObject row = new JsonObject();
                String from;
                String to;
                if ("RECORDED_READ_FROM_VALUE_BINDING".equals(kind)) {
                    long read = longInteger(raw, "readEventId", 0L);
                    long version = longInteger(raw, "fieldVersionId", 0L);
                    boolean unknown = bool(raw, "unknown", false);
                    from = unknown ? unknownWriterNode(read)
                            : versionNode(version);
                    to = readNode(read);
                    row.addProperty("evidenceState",
                            unknown ? UNKNOWN_ARM : GUARDED);
                    row.addProperty("readEventId", read);
                    row.addProperty("fieldVersionId", version);
                    row.addProperty("locationKey",
                            string(raw, "locationKey"));
                    row.addProperty("locationKind",
                            string(raw, "locationKind"));
                    row.addProperty("selector", string(raw, "selector"));
                    row.addProperty("arm", string(raw, "arm"));
                    row.addProperty("unknown", unknown);
                    row.addProperty("writerRegionId",
                            string(raw, "writerRegionId"));
                    row.addProperty("writerExists",
                            bool(raw, "writerExists", false));
                    row.addProperty("writerGuardAssertion",
                            string(raw, "writerGuardAssertion"));
                } else if ("RECORDED_GUARDED_READ_PORT_BINDING"
                        .equals(kind)) {
                    long read = longInteger(raw, "readEventId", 0L);
                    from = read > 0L ? readNode(read) : "";
                    to = regionNode(string(raw, "toOccurrenceId"));
                    row.addProperty("evidenceState", GUARDED);
                    row.addProperty("readEventId", read);
                    row.addProperty("locationKey",
                            string(raw, "locationKey"));
                    row.addProperty("toInputPort",
                            string(raw, "toInputPort"));
                    row.addProperty("unknownArm", string(raw,
                            RecordedReadFrom.EDGE_UNKNOWN_ARM));
                } else if (VmHandoffEvidence.BINDING_KIND.equals(kind)) {
                    // The VM attached the sender's expression at this
                    // receiver, and the ledger's own VALUE_HANDOFF edge
                    // relates the two events, so the relation is exact in the
                    // same sense a proved writer is.
                    from = regionNode(string(raw, "fromOccurrenceId"));
                    to = regionNode(string(raw, "toOccurrenceId"));
                    row.addProperty("evidenceState", EXACT);
                    for (String member : new String[]{
                            "toInputPort", "orderAssertion", "exportEventId",
                            CommunicationCatalogContract.PORT_ID,
                            "bindingState"}) {
                        if (raw.has(member)) {
                            row.add(member, raw.get(member).deepCopy());
                        }
                    }
                } else {
                    from = regionNode(string(raw, "fromOccurrenceId"));
                    to = regionNode(string(raw, "toOccurrenceId"));
                    row.addProperty("evidenceState", EXACT);
                    row.addProperty("fromOutputPort",
                            string(raw, "fromOutputPort"));
                    row.addProperty("toInputPort",
                            string(raw, "toInputPort"));
                    row.addProperty("fieldVersionId",
                            longInteger(raw, "fieldVersionId", 0L));
                    row.addProperty("readEventId",
                            longInteger(raw, "readEventId", 0L));
                    row.addProperty("locationKey",
                            string(raw, "locationKey"));
                    row.addProperty("orderAssertion",
                            string(raw, "orderAssertion"));
                    for (String member : new String[]{
                            RecordedReadFrom.EDGE_PROVENANCE,
                            RecordedReadFrom.EDGE_FIELD}) {
                        if (raw.has(member)) {
                            row.add(member, raw.get(member).deepCopy());
                        }
                    }
                }
                row.addProperty("kind", kind);
                row.addProperty("edgeId", string(raw, "edgeId"));
                row.addProperty("fromOccurrenceId",
                        string(raw, "fromOccurrenceId"));
                row.addProperty("toOccurrenceId",
                        string(raw, "toOccurrenceId"));
                row.addProperty("valueAssertion",
                        string(raw, "valueAssertion"));
                addBinding(row, valueBindingKey(raw), from, to);
            }
        }

        /**
         * The resolved trace edges no value binding ever spoke for.
         *
         * <p>They stay in the model as candidates. The composition selected
         * them, so hiding them would understate what it considered; nothing
         * lowered them into a value, so calling them observed would overstate
         * what it proved.</p>
         */
        private void candidates() {
            Set<String> bound = new LinkedHashSet<>();
            for (JsonElement element : valueBindings) {
                String edgeId = string(element.getAsJsonObject(), "edgeId");
                if (!edgeId.isEmpty()) bound.add(edgeId);
            }
            for (JsonElement element
                    : array(manifest, "resolvedEdgeBindings")) {
                if (!element.isJsonPrimitive()) continue;
                String edgeId = element.getAsString();
                if (edgeId.isEmpty() || bound.contains(edgeId)) continue;
                JsonObject edge = resolvedEdges.get(edgeId);
                JsonObject row = new JsonObject();
                row.addProperty("kind", "RESOLVED_EDGE_CANDIDATE");
                row.addProperty("evidenceState", CANDIDATE);
                row.addProperty("edgeId", edgeId);
                row.addProperty("fromOccurrenceId",
                        string(edge, "fromOccurrenceId"));
                row.addProperty("toOccurrenceId",
                        string(edge, "toOccurrenceId"));
                row.addProperty("fromOutputPort",
                        string(edge, "fromOutputPort"));
                row.addProperty("toInputPort", string(edge, "toInputPort"));
                row.addProperty("valueAssertion", "");
                addBinding(row, candidateBindingKey(edgeId),
                        regionNode(string(edge, "fromOccurrenceId")),
                        regionNode(string(edge, "toOccurrenceId")));
            }
        }

        private void addBinding(JsonObject row, String key, String from,
                                String to) {
            if (!bindingKeys.add(key)) return;
            row.addProperty("bindingKey", key);
            row.addProperty("bindingId", identity("binding", key));
            row.addProperty("fromNodeId", from);
            row.addProperty("toNodeId", to);
            if (from.isEmpty() || to.isEmpty()) {
                gap("MODEL", BINDING_ENDPOINT_UNAVAILABLE,
                        firstNonBlank(string(row, "edgeId"), key),
                        "this binding names no drawable producer and consumer"
                                + " pair");
            }
            valueBindings.add(row);
        }

        private void order(JsonArray recordedOrder) {
            Set<String> seen = new LinkedHashSet<>();
            for (JsonElement element : recordedOrder) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String key = orderRelationKey(edge);
                if (!seen.add(key)) continue;
                long before = longInteger(edge, "beforeEventId", 0L);
                long after = longInteger(edge, "afterEventId", 0L);
                JsonObject row = new JsonObject();
                row.addProperty("relationKey", key);
                row.addProperty("relationId", identity("order", key));
                row.addProperty("beforeEventId", before);
                row.addProperty("afterEventId", after);
                row.addProperty("edgeKind", string(edge, "edgeKind"));
                row.addProperty("direct", bool(edge, "direct", false));
                row.addProperty("evidenceState", NATURAL_ORDER);
                row.addProperty("fromNodeId", eventNode(before));
                row.addProperty("toNodeId", eventNode(after));
                if (!orderedEvents.contains(before)
                        || !orderedEvents.contains(after)) {
                    gap("MODEL", ORDER_EVENT_UNAVAILABLE, key,
                            "an endpoint of this order relation has no"
                                    + " position in the sliced order domain");
                }
                eventOrder.add(row);
            }
        }

        private String targetBranch() {
            String region = regionNode(targetOccurrence);
            String site = string(manifest, "fatalSite");
            String nodeId = identity("branch",
                    targetOccurrence + "\n" + site);
            JsonObject row = node(nodeId, NODE_TARGET_BRANCH);
            row.addProperty("occurrenceId", targetOccurrence);
            row.addProperty("regionId", targetRegionId);
            row.addProperty("siteId", site);
            structural(REGION_REACHES_TARGET_BRANCH, region, nodeId);
            return nodeId;
        }

        private JsonObject target(String branchNode, JsonObject recorded,
                                  JsonObject slice) {
            JsonObject target = new JsonObject();
            target.addProperty("fatalSite", string(manifest, "fatalSite"));
            target.addProperty("regionId", targetRegionId);
            target.addProperty("occurrenceId", targetOccurrence);
            target.addProperty("nodeId", branchNode);
            target.addProperty("state", string(manifest, "state"));
            target.addProperty("finalStatus",
                    string(manifest, ConcolicSmtComposer.FINAL_STATUS));
            target.addProperty("partial", bool(recorded, "partial", false));
            target.addProperty("reachesRecordedSlice",
                    bool(slice, "reachesTarget", false));
            target.addProperty("orderDomainFault",
                    string(recorded, "orderDomainFault"));
            target.add("fatalPathAssertion", object(object(manifest,
                    "operandBindingLedger"), "fatalPathAssertion")
                    .deepCopy());
            return target;
        }

        private void collectGaps() {
            for (JsonElement element : array(manifest, "gaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                gap("COMPOSITION", string(raw, "kind"),
                        string(raw, "subject"), "");
            }
            for (JsonElement element : array(manifest, "coverageGaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                gap("COVERAGE", firstNonBlank(string(raw, "reason"),
                                string(raw, "divergenceClass"),
                                string(raw, "kind")),
                        firstNonBlank(string(raw, "subject"),
                                string(raw, "locationKey")),
                        string(raw, "detail"));
            }
        }

        private void gap(String source, String code, String subject,
                         String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("source", source);
            row.addProperty("code", code);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            gaps.add(row);
        }

        private JsonObject counts() {
            int exact = 0;
            int guarded = 0;
            int unknown = 0;
            int candidate = 0;
            for (JsonElement element : valueBindings) {
                String state = string(element.getAsJsonObject(),
                        "evidenceState");
                if (EXACT.equals(state)) exact++;
                else if (GUARDED.equals(state)) guarded++;
                else if (UNKNOWN_ARM.equals(state)) unknown++;
                else candidate++;
            }
            JsonObject counts = new JsonObject();
            counts.addProperty("localRelations", localRelations.size());
            counts.addProperty("boundedLoops", boundedLoopRows.size());
            counts.addProperty("sourceOccurrences", sourceOccurrences.size());
            counts.addProperty("fieldVersions", fieldVersions.size());
            counts.addProperty("fieldReads", fieldReads.size());
            counts.addProperty("sessionEvents", sessionEvents);
            counts.addProperty("recordedSymbols", symbols.size());
            counts.addProperty("nodes", nodes.size());
            counts.addProperty("valueBindings", valueBindings.size());
            counts.addProperty("exactBindings", exact);
            counts.addProperty("guardedBindings", guarded);
            counts.addProperty("unknownArmBindings", unknown);
            counts.addProperty("candidateBindings", candidate);
            counts.addProperty("eventOrderRelations", eventOrder.size());
            counts.addProperty("structuralEdges", structuralEdges.size());
            counts.addProperty("gaps", gaps.size());
            return counts;
        }
    }
}
