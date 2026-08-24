package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SummaryBranchMapping;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Canonical wire carrier for one guarded region relation. */
public final class RelationSummary {
    /**
     * Two path cases of different activations were offered to one relation.
     */
    public static final String MERGE_REFUSED_CROSS_OCCURRENCE =
            "RELATION_MERGE_REFUSED_CROSS_OCCURRENCE";
    /**
     * A merge with no output closure was offered a producer's path case.
     */
    public static final String MERGE_REFUSED_UNCLOSED_PRODUCER =
            "RELATION_MERGE_REFUSED_UNCLOSED_PRODUCER";

    /**
     * Which branch decisions the execution behind one case took, as
     * {@code {siteId, occurrence, taken}}.
     *
     * <p>README section 5 requires {@code entersLoop} and {@code continue_i}
     * to be bound to the local branch relations that decide them, and the
     * merged relation is the only carrier that reaches the Composer.  Its
     * cases used to state the path condition and nothing about <em>which</em>
     * decisions produced it, so no case could be identified as the one taken
     * at a loop's control site and the guards stayed free.</p>
     *
     * <p>The attribution is the decision's own identity and not a position:
     * {@link PathObservation#projectRelationPathCondition} reindexes the guard,
     * so a {@code summaryPcIndex} would address the wrong term afterwards,
     * while a {@code siteId} is a static name and an {@code occurrence} is the
     * runtime's own counter for it.  Neither is disturbed by projection.  The
     * satisfied predicate itself is deliberately not copied here: where it
     * survives projection it is already a conjunct of {@code guard}, and where
     * it does not, repeating it would reintroduce the path condition this
     * projection exists to narrow.</p>
     */
    public static final String BRANCH_DECISIONS = "branchDecisions";
    /**
     * Why one case states no {@link #BRANCH_DECISIONS}.
     *
     * <p>An imported summary whose {@code branchMappings} did not decode is
     * evidence that was offered and rejected, which is a different fact from a
     * path that recorded no decision.  It is carried so a consumer refuses the
     * case rather than reading the empty attribution as "this path branched
     * nowhere".</p>
     */
    public static final String BRANCH_EVIDENCE_ISSUE = "branchEvidenceIssue";
    /**
     * Where the execution behind one case ended, as
     * {@code {kind, exceptionType}}.
     *
     * <p>Case-local for the same reason the events are: one path of an
     * occurrence returning normally says nothing about whether another path
     * of it threw, and a terminal stated once at summary top level would let
     * either case be read under the other's exit.</p>
     */
    public static final String TERMINAL = "terminal";
    /** Typed effects whose values are carried by the VM handoff ledger. */
    public static final String INTERACTION_EVENTS = "interactionEvents";

    private final JsonObject row;
    private final OutputClosureContract outputClosure;
    private final List<JsonObject> edgeBindings;

    private RelationSummary(JsonObject row,
                            OutputClosureContract outputClosure) {
        this.row = row;
        this.outputClosure = outputClosure;
        List<JsonObject> bindings = new ArrayList<>();
        for (JsonElement element : array(row, "edgeBindings")) {
            if (element.isJsonObject()) {
                bindings.add(element.getAsJsonObject());
            }
        }
        this.edgeBindings = Collections.unmodifiableList(bindings);
    }

    public static RelationSummary decode(JsonObject row) {
        if (row == null) {
            throw new IllegalArgumentException("relation summary is required");
        }
        return new RelationSummary(row.deepCopy(),
                OutputClosureCodec.decode(row));
    }

    /**
     * Merges the guarded cases of one region occurrence's relation.
     *
     * @param outputClosure the demanded output this relation is closed on
     */
    public static RelationSummary guardedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings) {
        return merge(outputClosure, paths, edgeBindings, null);
    }

    /** Exact relation over only the imported VM paths observed so far. */
    public static RelationSummary observedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings,
            String coverageState,
            String manifestState) {
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
        coverage.addProperty("manifestState", manifestState);
        coverage.addProperty("observedPathCount", pathKeys.size());
        coverage.addProperty("observedPathSetHash",
                CanonicalJson.sha256(CanonicalJson.render(encodedKeys)));
        coverage.addProperty("constraintProjectionAuthority",
                "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1");
        return merge(outputClosure, paths, edgeBindings, coverage);
    }

    private static RelationSummary merge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings,
            JsonObject coverage) {
        List<PathObservation> orderedCases = new ArrayList<>(paths);
        if (orderedCases.isEmpty()) {
            throw new IllegalArgumentException(
                    "guarded path merge requires at least one path");
        }
        Collections.sort(orderedCases,
                Comparator.comparing(PathObservation::relationKey));
        String occurrenceId = orderedCases.get(0).occurrenceId();
        String sourceKey = orderedCases.get(0).sourceKey();
        // The occurrence and its source pin one region occurrence.  Both
        // have to agree, or these cases are not cases of one relation.
        for (PathObservation path : orderedCases) {
            if (!occurrenceId.equals(path.occurrenceId())
                    || !sourceKey.equals(path.sourceKey())) {
                throw new IllegalArgumentException(
                        MERGE_REFUSED_CROSS_OCCURRENCE
                                + ": one relation summary requires one "
                                + "occurrence, saw " + occurrenceId + " and "
                                + path.occurrenceId());
            }
        }
        JsonArray cases = new JsonArray();
        for (PathObservation path : orderedCases) {
            appendPathCases(cases, path);
        }
        if (coverage != null) {
            // One path yields one case per version its output boundary
            // published, so the case count is what ties the relation to this
            // merge; the path count and its hash stay as the provenance of
            // which observations were merged.
            coverage.addProperty("observedCaseCount", cases.size());
        }

        Map<String, JsonObject> bindingsByPayload = new LinkedHashMap<>();
        for (JsonObject binding : edgeBindings) {
            bindingsByPayload.put(CanonicalJson.render(binding),
                    binding.deepCopy());
        }
        List<String> bindingKeys =
                new ArrayList<>(bindingsByPayload.keySet());
        Collections.sort(bindingKeys);
        JsonArray bindings = new JsonArray();
        for (String key : bindingKeys) {
            bindings.add(bindingsByPayload.get(key));
        }

        // The merged row's identity comes from the demanded output this
        // relation is closed on.  The cross-occurrence guard above has
        // already run, which is what makes reading the occurrence off case
        // zero safe: these are cases of one region occurrence or the merge
        // never got here.
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
        merged.addProperty("schemaVersion", 1);
        merged.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        // Case-local evidence ownership is reconstructed from the merged
        // row. Preserve the region that already owns the output closure so
        // VALUE_HANDOFF cases use the same selector during recording and
        // lowering.
        merged.addProperty("regionId", region);
        merged.addProperty("sourceKey", sourceKey);
        merged.addProperty("occurrenceId", occurrenceId);
        // The merged row remains an input to every downstream stage that
        // accepts an imported summary.  Preserve the closure identity those
        // stages use to distinguish a producer relation from a target seed;
        // dropping it made a correctly closed worklist unreadable by the
        // Composer.
        orderedCases.get(0).scope().goalKind().writeToTask(merged);
        merged.addProperty("goalId",
                orderedCases.get(0).scope().goalId());
        orderedCases.get(0).scope().loopBound().writeTo(merged);
        merged.addProperty("summaryId", "SUMMARY." + region
                + ".MERGED." + relationHash);
        merged.addProperty("pathCoverageState", coverage == null
                ? "CLOSED" : string(coverage, "coverageState"));
        OutputClosureCodec.writeTo(merged, outputClosure);
        merged.add("edgeBindings", bindings);
        merged.add("regionRelation", relation);
        if (coverage != null) merged.add("pathCoverage", coverage);
        merged.addProperty("relationallyComplete", true);
        return new RelationSummary(merged, outputClosure);
    }

    public JsonObject toJson() { return row.deepCopy(); }
    /** The demanded output this relation closes on. */
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
    public List<JsonObject> edgeBindings() { return edgeBindings; }

    public boolean same(RelationSummary other) {
        return other != null && summaryId().equals(other.summaryId());
    }

    /**
     * Expands one imported path into its guarded relation cases.
     *
     * <p>A port exported as a bounded version set names several site-local
     * write versions of one execution.  Every path-times-version combination
     * becomes one case whose guard also selects the version, so composition
     * keeps the full versioned choice instead of one collapsed value.</p>
     */
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
        // Case-local evidence.  A guard of this case may only enable the
        // events, versions and handoffs the execution behind it produced; a
        // union at summary top level would let one replay's guard enable
        // another replay's RPC or map mutation.
        JsonObject recordedSharedState = path.recordedSharedState();
        if (recordedSharedState.size() > 0) {
            item.add(SharedStateEvidence.RECORDED_FIELD, recordedSharedState);
        }
        VmHandoffEvidence.writeTo(item, path.vmHandoffEvents());
        List<JsonObject> selectorEvidence =
                path.configuredSourceSelectorEvidence();
        if (!selectorEvidence.isEmpty()) {
            JsonArray encodedSelectors = new JsonArray();
            for (JsonObject evidence : selectorEvidence) {
                encodedSelectors.add(evidence.deepCopy());
            }
            item.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD,
                    encodedSelectors);
        }
        JsonArray symbolicSources = path.symbolicSourceEvidence();
        if (symbolicSources.size() > 0) {
            item.add(SymbolicSourceEvidence.FIELD, symbolicSources);
        }
        JsonArray decisions = branchDecisions(path);
        if (decisions.size() > 0) item.add(BRANCH_DECISIONS, decisions);
        String issue = path.branchMappingIssue();
        if (!issue.isEmpty()) item.addProperty(BRANCH_EVIDENCE_ISSUE, issue);
        return item;
    }

    /**
     * The branch decisions one imported path attested, as case attribution.
     *
     * <p>Both authorities are carried.  A witnessed row owns a path-condition
     * term; a concrete observation owns none - and a loop whose iteration
     * count the execution task fixed decides its control site concretely, so
     * keeping only the witnessed half would drop exactly the decisions this
     * attribution exists to name.  Rows are ordered by
     * {@link SummaryBranchMapping#decisionIdentity()}, which
     * {@code fromSummary} has already proven unique, so two imports of one
     * path merge to one canonical case.</p>
     */
    private static JsonArray branchDecisions(PathObservation path) {
        NavigableMap<String, JsonObject> rows = new TreeMap<>();
        for (SummaryBranchMapping mapping : path.branchMappings()) {
            JsonObject row = new JsonObject();
            row.addProperty("siteId", mapping.siteId());
            row.addProperty("occurrence", mapping.occurrence());
            row.addProperty("taken", mapping.sourceTakenOutcome());
            rows.put(mapping.decisionIdentity(), row);
        }
        JsonArray result = new JsonArray();
        for (JsonObject row : rows.values()) result.add(row);
        return result;
    }
}
