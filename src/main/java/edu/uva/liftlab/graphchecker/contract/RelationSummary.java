package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.RecordedSessionModel;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Set;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical wire carrier for one guarded region relation. */
public final class RelationSummary {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "CONCOLIC_REGION_SUMMARY";
    /** Two path cases of different activations offered to one relation. */
    public static final String MERGE_REFUSED_CROSS_OCCURRENCE =
            "RELATION_MERGE_REFUSED_CROSS_OCCURRENCE";
    /** A merge with no output closure offered a producer's path case. */
    public static final String MERGE_REFUSED_UNCLOSED_PRODUCER =
            "RELATION_MERGE_REFUSED_UNCLOSED_PRODUCER";

    /** Where the execution behind one case ended, as
     *  {@code {kind, exceptionType}}.  Case-local: one path returning normally
     *  says nothing about whether another threw. */
    public static final String TERMINAL = "terminal";
    /** Typed effects whose values are carried by the VM handoff ledger. */
    public static final String INTERACTION_EVENTS = "interactionEvents";
    /** Runtime edge bindings one execution resolved, case-local.  The
     *  importer resolves every edge <em>per path</em> and stamps that path's
     *  provenance, so two cases produce two rows a payload dedup cannot
     *  collapse.  README CASE-1: a row-level union let a case guard enable a
     *  read-from arm only another case observed. */
    public static final String EDGE_BINDINGS = "edgeBindings";
    /** SMT case selectors of the cases that resolved one edge binding.
     *  Present only where the cases disagreed, and minted as the selector
     *  {@link RecordedSessionModel#caseSelector} gives the case's own guard. */
    public static final String CASE_SELECTORS = "caseSelectors";

    private final JsonObject row;
    private final OutputClosureContract outputClosure;
    private final List<JsonObject> edgeBindings;

    private RelationSummary(JsonObject row,
                            OutputClosureContract outputClosure) {
        this.row = row;
        this.outputClosure = outputClosure;
        this.edgeBindings = Collections.unmodifiableList(
                caseScopedEdgeBindings(row, outputClosure));
    }

    /** Edge bindings, each carrying the cases that observed it.  A row-level
     *  binding needs no attribution; a case-local one carries
     *  {@link #CASE_SELECTORS}.  Identical payloads are offered once with the
     *  selectors unioned. */
    private static List<JsonObject> caseScopedEdgeBindings(
            JsonObject row, OutputClosureContract outputClosure) {
        Map<String, JsonObject> byPayload = new LinkedHashMap<>();
        for (JsonElement element : array(row, EDGE_BINDINGS)) {
            if (element.isJsonObject()) {
                byPayload.put(CanonicalJson.render(element.getAsJsonObject()),
                        element.getAsJsonObject().deepCopy());
            }
        }
        // The closure's producer region, because a selector minted here has
        // to be the same constant the case's guard is declared under.
        String region = outputClosure == null ? string(row, "regionId")
                : outputClosure.producer().regionId();
        JsonArray cases = array(object(row, "regionRelation"), "cases");
        Map<String, JsonObject> caseLocal = new LinkedHashMap<>();
        Map<String, Set<String>> selectors = new LinkedHashMap<>();
        for (int index = 0; index < cases.size(); index++) {
            if (!cases.get(index).isJsonObject()) continue;
            JsonObject item = cases.get(index).getAsJsonObject();
            // OCC-1: the selector is minted under the case's own occurrence,
            // which is the relation's address for a single-occurrence
            // relation and the activation's identity otherwise.
            String caseOccurrence = string(item, "occurrenceId");
            if (caseOccurrence.isEmpty()) {
                throw new IllegalArgumentException(
                        "relation case occurrenceId is required");
            }
            String selector = RecordedSessionModel.caseSelector(
                    RecordedSessionModel.caseOwner(region, caseOccurrence,
                            string(item, "caseId"), index));
            for (JsonElement element : array(item, EDGE_BINDINGS)) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                String payload = CanonicalJson.render(binding);
                // A payload the row already states is one every case agreed
                // on.
                if (byPayload.containsKey(payload)) continue;
                caseLocal.put(payload, binding.deepCopy());
                selectors.computeIfAbsent(payload,
                        ignored -> new LinkedHashSet<>()).add(selector);
            }
        }
        List<JsonObject> result = new ArrayList<>(byPayload.values());
        for (Map.Entry<String, JsonObject> entry : caseLocal.entrySet()) {
            JsonObject binding = entry.getValue();
            JsonArray owners = new JsonArray();
            for (String selector : selectors.get(entry.getKey())) {
                owners.add(selector);
            }
            binding.add(CASE_SELECTORS, owners);
            result.add(binding);
        }
        return result;
    }

    public static RelationSummary decode(JsonObject row) {
        if (row == null) {
            throw new IllegalArgumentException("relation summary is required");
        }
        if (!exactSchemaVersion(row)
                || !KIND.equals(string(row, "kind"))) {
            throw new IllegalArgumentException(
                    "relation summary has an unsupported schema");
        }
        return new RelationSummary(row.deepCopy(),
                OutputClosureCodec.decode(row));
    }

    private static boolean exactSchemaVersion(JsonObject row) {
        JsonElement value = row.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(SCHEMA_VERSION).equals(value.getAsString());
    }

    /**
     * Merges the guarded cases of one region occurrence's relation.
     *
     * @param outputClosure the demanded output this relation is closed on
     */
    public static RelationSummary guardedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths) {
        return merge(outputClosure, paths, null);
    }

    /** Exact relation over only the imported VM paths observed so far. */
    public static RelationSummary observedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            String coverageState) {
        if (!"PARTIAL".equals(coverageState)
                && !"SEED_ONLY".equals(coverageState)) {
            throw new IllegalArgumentException(
                    "observed path merge requires incomplete coverage");
        }
        List<String> pathKeys = new ArrayList<>();
        for (PathObservation path : paths) pathKeys.add(path.pathKey());
        Collections.sort(pathKeys);
        JsonArray encodedKeys = new JsonArray();
        for (String key : pathKeys) encodedKeys.add(key);
        JsonObject coverage = new JsonObject();
        coverage.addProperty("schemaVersion", 1);
        coverage.addProperty("kind", "OBSERVED_PATH_COVERAGE");
        coverage.addProperty("authority",
                "IMPORTED_VM_PATH_UNDERAPPROX_V1");
        coverage.addProperty("complete", false);
        coverage.addProperty("coverageState", coverageState);
        coverage.addProperty("observedPathCount", pathKeys.size());
        coverage.addProperty("observedPathSetHash",
                CanonicalJson.sha256(CanonicalJson.render(encodedKeys)));
        coverage.addProperty("constraintProjectionAuthority",
                "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1");
        return merge(outputClosure, paths, coverage);
    }

    private static RelationSummary merge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            JsonObject coverage) {
        List<PathObservation> orderedCases = new ArrayList<>(paths);
        if (orderedCases.isEmpty()) {
            throw new IllegalArgumentException(
                    "guarded path merge requires at least one path");
        }
        Collections.sort(orderedCases,
                Comparator.comparing(PathObservation::relationKey));
        // OCC-1: the relation is closed on one planned address.  Its cases
        // may be several activations of that address, each its own
        // occurrence; what they may never be is two different addresses.
        String occurrenceId = orderedCases.get(0).plannedOccurrenceId();
        String sourceKey = orderedCases.get(0).sourceKey();
        // Both have to agree, or these cases are not cases of one relation.
        for (PathObservation path : orderedCases) {
            if (!occurrenceId.equals(path.plannedOccurrenceId())
                    || !sourceKey.equals(path.sourceKey())) {
                throw new IllegalArgumentException(
                        MERGE_REFUSED_CROSS_OCCURRENCE
                                + ": one relation summary requires one "
                                + "planned address, saw " + occurrenceId
                                + " and " + path.plannedOccurrenceId());
            }
        }
        JsonArray cases = new JsonArray();
        for (PathObservation path : orderedCases) {
            appendPathCases(cases, path);
        }
        if (coverage != null) {
            // One path yields one case per version its output boundary
            // published, so the case count is what ties the relation here.
            coverage.addProperty("observedCaseCount", cases.size());
        }

        JsonArray bindings = hoistAgreedEdgeBindings(cases);

        // Identity comes from the demanded output this relation is closed on.
        // The cross-occurrence guard above has already run, which is what
        // makes reading the occurrence off case zero safe.
        if (outputClosure == null) {
            throw new IllegalArgumentException(
                    MERGE_REFUSED_UNCLOSED_PRODUCER
                            + ": a merged relation requires the demanded "
                            + "output it closes on");
        }
        String region = outputClosure.producer().regionId();
        String relationKey = outputClosure.producer().relationKey();
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("guardProjection", coverage != null
                ? "SELECTIVE_SYMBOLIC_BRANCH_SLICE"
                : "OUTPUT_CLOSURE_BRANCH_SLICE");
        relation.add("cases", cases);
        String relationHash = CanonicalJson.sha256(region + "\n"
                + relationKey + "\n"
                + CanonicalJson.render(cases) + "\n"
                + CanonicalJson.render(bindings) + "\n"
                + (coverage == null ? "CLOSED"
                : CanonicalJson.render(coverage)));

        JsonObject merged = new JsonObject();
        merged.addProperty("schemaVersion", SCHEMA_VERSION);
        merged.addProperty("kind", KIND);
        // Preserve the region that already owns the output closure so
        // VALUE_HANDOFF cases use one selector when recording and lowering.
        merged.addProperty("regionId", region);
        merged.addProperty("sourceKey", sourceKey);
        merged.addProperty("occurrenceId", occurrenceId);
        // Preserve the closure identity downstream stages use to tell a
        // producer relation from a target seed; dropping it made a correctly
        // closed worklist unreadable by the Composer.
        orderedCases.get(0).scope().goalKind().writeToTask(merged);
        merged.addProperty("goalId",
                orderedCases.get(0).scope().goalId());
        orderedCases.get(0).scope().loopBound().writeTo(merged);
        merged.addProperty("summaryId", "SUMMARY." + region
                + ".MERGED." + relationHash);
        merged.addProperty("pathCoverageState", coverage == null
                ? "CLOSED" : string(coverage, "coverageState"));
        OutputClosureCodec.writeTo(merged, outputClosure);
        merged.add(EDGE_BINDINGS, bindings);
        merged.add("regionRelation", relation);
        if (coverage != null) merged.add("pathCoverage", coverage);
        merged.addProperty("relationallyComplete", true);
        return new RelationSummary(merged, outputClosure);
    }

    public JsonObject toJson() { return row.deepCopy(); }
    public OutputClosureContract outputClosure() { return outputClosure; }
    public String summaryId() { return string(row, "summaryId"); }
    public String sourceKey() { return string(row, "sourceKey"); }
    public String occurrenceId() { return string(row, "occurrenceId"); }
    public String regionId() {
        return outputClosure.producer().regionId();
    }
    public String relationKey() {
        return outputClosure.producer().relationKey();
    }
    /** Edge bindings attributed to the cases that resolved them; see
     *  {@link #CASE_SELECTORS}. */
    public List<JsonObject> edgeBindings() { return edgeBindings; }
    /** The relation's path cases, as a copy the caller may annotate. */
    public JsonArray cases() {
        return array(object(row, "regionRelation"), "cases").deepCopy();
    }
    public String pathCoverageState() {
        return string(row, "pathCoverageState");
    }

    /**
     * Leaves each case only the bindings its own execution resolved.  README
     * CASE-1: a binding every case resolved byte for byte is stated once at
     * row level, and everything else stays where it was observed, because
     * widening is the union that let a case guard enable another case's arm.
     *
     * @return the bindings all cases agreed on, in canonical payload order
     */
    private static JsonArray hoistAgreedEdgeBindings(JsonArray cases) {
        NavigableMap<String, JsonObject> agreed = new TreeMap<>();
        boolean first = true;
        for (JsonElement element : cases) {
            if (!element.isJsonObject()) continue;
            Map<String, JsonObject> present = new LinkedHashMap<>();
            for (JsonElement encoded : array(element.getAsJsonObject(),
                    EDGE_BINDINGS)) {
                if (!encoded.isJsonObject()) continue;
                present.put(CanonicalJson.render(encoded.getAsJsonObject()),
                        encoded.getAsJsonObject());
            }
            if (first) {
                agreed.putAll(present);
                first = false;
            } else {
                agreed.keySet().retainAll(present.keySet());
            }
        }
        JsonArray bindings = new JsonArray();
        for (JsonObject binding : agreed.values()) {
            bindings.add(binding.deepCopy());
        }
        for (JsonElement element : cases) {
            if (!element.isJsonObject()) continue;
            JsonObject item = element.getAsJsonObject();
            JsonArray retained = new JsonArray();
            for (JsonElement encoded : array(item, EDGE_BINDINGS)) {
                if (encoded.isJsonObject() && agreed.containsKey(
                        CanonicalJson.render(encoded.getAsJsonObject()))) {
                    continue;
                }
                retained.add(encoded);
            }
            if (retained.size() == 0) item.remove(EDGE_BINDINGS);
            else item.add(EDGE_BINDINGS, retained);
        }
        return bindings;
    }

    public boolean same(RelationSummary other) {
        return other != null && summaryId().equals(other.summaryId());
    }

    /** Expands one imported path into its guarded cases: every
     *  path-times-version combination becomes one case whose guard also
     *  selects the version. */
    private static void appendPathCases(JsonArray cases,
                                        PathObservation path) {
        JsonObject outputs = path.outputExpressions();
        NavigableMap<String, JsonObject> versioned = new TreeMap<>();
        for (String port : outputs.keySet()) {
            JsonElement value = outputs.get(port);
            if (BoundedOutputVersions.isVersionSet(value)) {
                versioned.put(port, value.getAsJsonObject());
            }
        }
        List<Map<String, Integer>> selections =
                independentVersionSelections(versioned);
        for (Map<String, Integer> selection : selections) {
            cases.add(pathCase(path, selection));
        }
    }

    private static List<Map<String, Integer>> independentVersionSelections(
            NavigableMap<String, JsonObject> versioned) {
        List<Map<String, Integer>> selections = new ArrayList<>();
        selections.add(new LinkedHashMap<String, Integer>());
        for (Map.Entry<String, JsonObject> entry : versioned.entrySet()) {
            List<Map<String, Integer>> expanded = new ArrayList<>();
            for (Map<String, Integer> prefix : selections) {
                for (Integer ordinal : BoundedOutputVersions.versions(
                        entry.getValue()).keySet()) {
                    Map<String, Integer> next =
                            new LinkedHashMap<>(prefix);
                    next.put(entry.getKey(), ordinal);
                    expanded.add(next);
                }
            }
            selections = expanded;
        }
        return selections;
    }

    private static JsonObject pathCase(PathObservation path,
                                       Map<String, Integer> selection) {
        JsonObject item = new JsonObject();
        StringBuilder caseId = new StringBuilder("CASE.")
                .append(path.relationKey());
        JsonArray conditions = path.relationPathCondition();
        JsonObject outputs = path.outputExpressions();
        for (Map.Entry<String, Integer> chosen : selection.entrySet()) {
            String port = chosen.getKey();
            JsonObject versionSet = outputs.getAsJsonObject(port);
            NavigableMap<Integer, JsonElement> versions =
                    BoundedOutputVersions.versions(versionSet);
            conditions.add(BoundedOutputVersions.versionSelectionCondition(
                    port, BoundedOutputVersions.outputSiteId(versionSet),
                    chosen.getValue(), versions.lastKey()));
            outputs.add(port,
                    versions.get(chosen.getValue()).deepCopy());
            caseId.append(".V.").append(chosen.getValue());
        }
        item.addProperty("caseId", caseId.toString());
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", conditions);
        item.add("guard", guard);
        item.add("outputExpressions", outputs);
        JsonArray interactionEvents = path.interactionEvents();
        if (interactionEvents.size() > 0) {
            item.add(INTERACTION_EVENTS, interactionEvents);
        }
        JsonArray loopCounts = path.pathLoopCounts();
        if (loopCounts.size() > 0) {
            item.add(LoopBoundPolicy.PATH_LOOP_COUNTS, loopCounts);
        }
        JsonArray loopCountGaps = path.pathLoopCountGaps();
        if (loopCountGaps.size() > 0) {
            item.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS, loopCountGaps);
        }
        PathObservation.TargetReachEvent targetReach =
                path.targetReachEvent();
        if (targetReach != null) {
            item.add(PathObservation.TargetReachEvent.FIELD,
                    targetReach.toJson());
        }
        item.add(TERMINAL, path.terminal());
        item.addProperty("sourceTaskId", path.sourceTaskId());
        // OCC-1: which occurrence this case is.  Two activations of one
        // address are two occurrences that both happened, so the case has to
        // carry its own identity into the formula rather than inheriting the
        // relation's -- otherwise their selectors, order positions and
        // read-from arms all collapse onto one occurrence.
        item.addProperty("occurrenceId", path.occurrenceId());
        item.addProperty(PathObservation.ACTIVATION_ORDINAL,
                path.activationOrdinal());
        item.addProperty(PathObservation.PLANNED_OCCURRENCE_ID,
                path.plannedOccurrenceId());
        item.addProperty(PathObservation.TARGET_REACHED,
                path.targetReached());
        // A partial activation carries only what it captured.
        item.addProperty("relationallyComplete",
                path.relationallyComplete());
        // Case-local evidence.  A union at summary top level would let one
        // replay's guard enable another replay's RPC or map mutation.
        JsonObject recordedSharedState = path.recordedSharedState();
        if (recordedSharedState.size() > 0) {
            item.add(SharedStateEvidence.RECORDED_FIELD, recordedSharedState);
        }
        JsonArray pathBindings = path.edgeBindings();
        if (pathBindings.size() > 0) {
            item.add(EDGE_BINDINGS, pathBindings);
        }
        VmHandoffEvidence.writeTo(item, path.vmHandoffEvents());
        item.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                path.freeSymbols());
        JsonArray symbolicSources = path.symbolicSourceEvidence();
        if (symbolicSources.size() > 0) {
            item.add(SymbolicSourceEvidence.FIELD, symbolicSources);
        }
        return item;
    }
}
