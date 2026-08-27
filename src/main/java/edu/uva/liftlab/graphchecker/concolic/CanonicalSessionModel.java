package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

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
 * The evidence census of one composition: which gaps the assembly found and
 * how many bindings of each evidence state the lowered model holds.
 */
public final class CanonicalSessionModel {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "CANONICAL_SESSION_MODEL";
    public static final String AUTHORITY = "CANONICAL_SESSION_MODEL_V1";

    /** Manifest member the composed model travels in. */
    public static final String MANIFEST_FIELD = "canonicalModel";


    /** The VM proved one writer or one delivery; a direct equality. */
    public static final String EXACT = "EXACT";
    /** One arm of a recorded choice, selected by its own Boolean. */
    public static final String GUARDED = "GUARDED";
    /** The unconditional arm that admits a writer nobody recorded. */
    public static final String UNKNOWN_ARM = "UNKNOWN_ARM";
    /** A resolved trace edge that never became a value binding. */
    public static final String CANDIDATE = "CANDIDATE";


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
     */
    public static JsonObject of(JsonObject manifest, JsonArray localRelations,
                                JsonArray resolvedEdges,
                                String targetOccurrence) {
        return new Assembly(manifest, localRelations, resolvedEdges,
                targetOccurrence).build();
    }

    /** One resolved trace edge's endpoints, as the model records them. */
    public static JsonObject resolvedEdge(String edgeId,
                                          String fromOccurrenceId,
                                          String toOccurrenceId,
                                          boolean topologyOnly) {
        JsonObject row = new JsonObject();
        row.addProperty("edgeId", edgeId);
        row.addProperty("fromOccurrenceId", fromOccurrenceId);
        row.addProperty("toOccurrenceId", toOccurrenceId);
        row.addProperty("topologyOnly", topologyOnly);
        return row;
    }

    /** One selected local region relation, as the model records it. */
    public static JsonObject relation(String occurrenceId, String sourceKey) {
        JsonObject row = new JsonObject();
        row.addProperty("occurrenceId", occurrenceId);
        row.addProperty("sourceKey", sourceKey);
        return row;
    }

    /** Whether {@code model} is a canonical model this class produced. */
    public static boolean isModel(JsonObject model) {
        return model != null && KIND.equals(string(model, "kind"))
                && AUTHORITY.equals(string(model, "authority"));
    }

    public static JsonObject read(JsonObject artifact) {
        if (isModel(artifact)) return artifact;
        JsonObject member = object(artifact, MANIFEST_FIELD);
        return isModel(member) ? member : new JsonObject();
    }

    /**
     * The stable key of one SMT value binding.
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
                    + string(row, "toInputPort") + "\n"
                    + longInteger(row, "readEventId", 0L) + "\n"
                    + longInteger(row, "fieldVersionId", 0L) + "\n"
                    + string(row, "caseGuard");
        }
        if ("RECORDED_GUARDED_READ_PORT_BINDING".equals(kind)) {
            return kind + "\n" + string(row, "edgeId") + "\n"
                    + string(row, "toInputPort") + "\n"
                    + longInteger(row, "readEventId", 0L) + "\n"
                    + string(row, "caseGuard");
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


    /** One pass over the composed manifest, building the one model. */
    private static final class Assembly {
        private final JsonObject manifest;
        private final JsonArray localRelations;
        private final Map<String, JsonObject> resolvedEdges =
                new LinkedHashMap<>();
        private final String targetOccurrence;

        private final Map<String, String> sourceByOccurrence =
                new LinkedHashMap<>();
        private final Set<String> occurrences = new LinkedHashSet<>();
        private final JsonArray gaps = new JsonArray();
        private final Set<String> bindingKeys = new LinkedHashSet<>();
        private final Set<String> boundEdgeIds = new LinkedHashSet<>();
        private final Set<Long> orderedEvents = new LinkedHashSet<>();
        private int fieldVersions;
        private int fieldReads;
        private int exact;
        private int guarded;
        private int unknown;
        private int candidate;

        private Assembly(JsonObject manifest, JsonArray localRelations,
                         JsonArray resolvedEdges, String targetOccurrence) {
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
            this.targetOccurrence = firstNonBlank(targetOccurrence);
        }

        private JsonObject build() {
            JsonObject recorded = object(manifest, "recordedSessionModel");
            relations();
            sliceCounts(object(recorded, "targetSlice"));
            bindings();
            candidates();
            order(array(recorded, "order"));
            collectGaps();

            JsonObject model = new JsonObject();
            model.addProperty("schemaVersion", SCHEMA_VERSION);
            model.addProperty("kind", KIND);
            model.addProperty("authority", AUTHORITY);
            model.add("gaps", gaps);
            model.add("counts", counts());
            return model;
        }

        /**
         * Notes one activation, raising the gap the first time an occurrence
         * names no source.  Answers whether the endpoint is nameable at all.
         */
        private boolean occurrence(String occurrenceId) {
            if (occurrenceId.isEmpty()) return false;
            if (!occurrences.add(occurrenceId)) return true;
            String sourceKey = firstNonBlank(
                    sourceByOccurrence.get(occurrenceId),
                    canonicalSourceKey(occurrenceId));
            if (sourceKey.isEmpty()) {
                gap("MODEL", SOURCE_KEY_UNAVAILABLE, occurrenceId,
                        "no selected relation attributes this activation to a"
                                + " source");
            }
            return true;
        }

        /** The source half of a canonical occurrence address, or "". */
        private static String canonicalSourceKey(String occurrenceId) {
            int cut = occurrenceId.indexOf("/region/");
            return cut <= 0 ? "" : occurrenceId.substring(0, cut);
        }


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
            }
            for (JsonElement element : localRelations) {
                if (!element.isJsonObject()) continue;
                occurrence(string(element.getAsJsonObject(),
                        "occurrenceId"));
            }
            occurrence(targetOccurrence);
        }

        /**
         * Counts the sliced field versions and reads, and remembers which
         * events the sliced order domain holds a position for.
         */
        private void sliceCounts(JsonObject slice) {
            for (JsonElement element : array(slice, "eventIds")) {
                if (element.isJsonPrimitive()) {
                    orderedEvents.add(element.getAsLong());
                }
            }
            for (JsonElement element : array(slice, "nodes")) {
                if (!element.isJsonObject()) continue;
                String nodeKind = string(element.getAsJsonObject(),
                        "nodeKind");
                if (SessionTargetSlice.NODE_SYMBOL.equals(nodeKind)) continue;
                if (SessionTargetSlice.NODE_READ.equals(nodeKind)) fieldReads++;
                else fieldVersions++;
            }
        }

        /** One census entry per lowered SMT value binding. */
        private void bindings() {
            for (JsonElement element
                    : array(manifest, "recordedValueBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                String kind = string(raw, "kind");
                String state;
                boolean from;
                boolean to;
                if ("RECORDED_READ_FROM_VALUE_BINDING".equals(kind)) {
                    // Both endpoints of a read-from arm are minted from the
                    // event ids the row carries, so both are always nameable.
                    from = true;
                    to = true;
                    state = bool(raw, "unknown", false)
                            ? UNKNOWN_ARM : GUARDED;
                } else if ("RECORDED_GUARDED_READ_PORT_BINDING"
                        .equals(kind)) {
                    from = longInteger(raw, "readEventId", 0L) > 0L;
                    to = occurrence(string(raw, "toOccurrenceId"));
                    state = GUARDED;
                } else if (VmHandoffEvidence.BINDING_KIND.equals(kind)) {
                    from = occurrence(string(raw,
                            VmHandoffEvidence.PRODUCER_OCCURRENCE_ID));
                    to = occurrence(string(raw, "toOccurrenceId"));
                    state = EXACT;
                } else {
                    from = occurrence(string(raw, "fromOccurrenceId"));
                    to = occurrence(string(raw, "toOccurrenceId"));
                    state = EXACT;
                }
                addBinding(state, valueBindingKey(raw),
                        string(raw, "edgeId"), from && to);
            }
        }

        /**
         * The resolved trace edges no value binding ever spoke for.
         */
        private void candidates() {
            for (JsonElement element
                    : array(manifest, "resolvedEdgeBindings")) {
                if (!element.isJsonPrimitive()) continue;
                String edgeId = element.getAsString();
                if (edgeId.isEmpty() || boundEdgeIds.contains(edgeId)) {
                    continue;
                }
                JsonObject edge = resolvedEdges.get(edgeId);
                if (edge == null) continue;
                boolean from = occurrence(string(edge, "fromOccurrenceId"));
                boolean to = occurrence(string(edge, "toOccurrenceId"));
                // A trace-correlated RPC edge is topology, never value proof:
                // it names its two activations and states nothing else.
                if (bool(edge, "topologyOnly", false)) continue;
                addBinding(CANDIDATE, candidateBindingKey(edgeId), edgeId,
                        from && to);
            }
        }

        private void addBinding(String state, String key, String edgeId,
                                boolean drawable) {
            if (!bindingKeys.add(key)) return;
            if (!edgeId.isEmpty()) boundEdgeIds.add(edgeId);
            if (!drawable) {
                gap("MODEL", BINDING_ENDPOINT_UNAVAILABLE,
                        firstNonBlank(edgeId, key),
                        "this binding names no drawable producer and consumer"
                                + " pair");
            }
            if (EXACT.equals(state)) exact++;
            else if (GUARDED.equals(state)) guarded++;
            else if (UNKNOWN_ARM.equals(state)) unknown++;
            else candidate++;
        }

        private void order(JsonArray recordedOrder) {
            Set<String> seen = new LinkedHashSet<>();
            for (JsonElement element : recordedOrder) {
                if (!element.isJsonObject()) continue;
                JsonObject edge = element.getAsJsonObject();
                String key = orderRelationKey(edge);
                if (!seen.add(key)) continue;
                if (!orderedEvents.contains(
                        longInteger(edge, "beforeEventId", 0L))
                        || !orderedEvents.contains(
                        longInteger(edge, "afterEventId", 0L))) {
                    gap("MODEL", ORDER_EVENT_UNAVAILABLE, key,
                            "an endpoint of this order relation has no"
                                    + " position in the sliced order domain");
                }
            }
        }

        private void collectGaps() {
            for (JsonElement element : array(manifest, "gaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                gap("COMPOSITION", string(raw, "kind"),
                        string(raw, "subject"), string(raw, "detail"));
            }
            for (JsonElement element : array(manifest, "coverageGaps")) {
                if (!element.isJsonObject()) continue;
                JsonObject raw = element.getAsJsonObject();
                String kind = string(raw, "kind");
                String reason = string(raw, "reason");
                boolean reasonIsCode = CoverageDivergence.isDivergence(raw)
                        || SparseReadCutGate.GAP_KIND.equals(kind)
                        || RpcExpressionHandoff.GAP_KIND.equals(kind)
                        || SharedStateEvidence.GAP_KIND.equals(kind)
                        || SessionTargetSlice.GAP_KIND.equals(kind)
                        || BoundedLoopComposition.GAP_KIND.equals(kind);
                gap("COVERAGE", reasonIsCode
                                ? firstNonBlank(reason, kind)
                                : firstNonBlank(kind, reason),
                        // The one gap family that carried an output site -
                        // the importer's bounded-output-version gap - names
                        // its capture binding on the same row, and that key
                        // is read first, so the site was never reached.
                        firstNonBlank(string(raw, "subject"),
                                string(raw, "queryKey"),
                                string(raw, "locationKey"),
                                string(raw, "captureBindingId"),
                                string(raw, "regionId"),
                                string(raw, "pathKey")),
                        reasonIsCode ? string(raw, "detail")
                                : firstNonBlank(string(raw, "detail"),
                                reason));
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
            JsonObject counts = new JsonObject();
            counts.addProperty("fieldVersions", fieldVersions);
            counts.addProperty("fieldReads", fieldReads);
            counts.addProperty("exactBindings", exact);
            counts.addProperty("guardedBindings", guarded);
            counts.addProperty("unknownArmBindings", unknown);
            counts.addProperty("candidateBindings", candidate);
            return counts;
        }
    }
}
