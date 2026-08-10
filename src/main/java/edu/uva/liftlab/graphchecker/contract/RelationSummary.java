package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

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

/**
 * Canonical wire carrier for one closed region relation.
 */
public final class RelationSummary {
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

    public static RelationSummary guardedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings) {
        return guardedPathMerge(outputClosure, paths, edgeBindings, true);
    }

    public static RelationSummary guardedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings,
            boolean projectRelationGuards) {
        return merge(outputClosure, paths, edgeBindings,
                projectRelationGuards, null);
    }

    /** Exact relation over only the imported VM paths observed so far. */
    public static RelationSummary observedPathMerge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings,
            String manifestState,
            boolean projectRelationGuards) {
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
        coverage.addProperty("manifestState", manifestState);
        coverage.addProperty("observedPathCount", pathKeys.size());
        coverage.addProperty("observedPathSetHash",
                CanonicalJson.sha256(CanonicalJson.render(encodedKeys)));
        coverage.addProperty("constraintProjectionAuthority",
                projectRelationGuards
                        ? "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1"
                        : "FULL_PATH_COLLISION_FALLBACK");
        return merge(outputClosure, paths, edgeBindings,
                projectRelationGuards, coverage);
    }

    private static RelationSummary merge(
            OutputClosureContract outputClosure,
            Collection<PathObservation> paths,
            Collection<JsonObject> edgeBindings,
            boolean projectRelationGuards,
            JsonObject coverage) {
        List<PathObservation> orderedCases = new ArrayList<>(paths);
        if (orderedCases.isEmpty()) {
            throw new IllegalArgumentException(
                    "guarded path merge requires at least one path");
        }
        Collections.sort(orderedCases,
                Comparator.comparing(projectRelationGuards
                        ? PathObservation::relationKey
                        : PathObservation::pathKey));
        JsonArray cases = new JsonArray();
        for (PathObservation path : orderedCases) {
            appendPathCases(cases, path, projectRelationGuards);
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

        String region = outputClosure.producer().regionId();
        String closureIdentity = outputClosure.closureFingerprint();
        JsonObject occurrenceCatalog = occurrenceCatalog(orderedCases);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.addProperty("guardProjection", coverage != null
                ? projectRelationGuards
                ? "SELECTIVE_SYMBOLIC_BRANCH_SLICE"
                : "FULL_PATH_COLLISION_FALLBACK"
                : projectRelationGuards
                ? "OUTPUT_CLOSURE_BRANCH_SLICE"
                : "FULL_PATH_COLLISION_FALLBACK");
        relation.add("cases", cases);
        String relationHash = CanonicalJson.sha256(region + "\n"
                + closureIdentity + "\n" + CanonicalJson.render(cases)
                + "\n" + CanonicalJson.render(bindings)
                + "\n" + CanonicalJson.render(occurrenceCatalog)
                + "\n" + (coverage == null ? "CLOSED"
                : CanonicalJson.render(coverage)));

        JsonObject merged = new JsonObject();
        merged.addProperty("schemaVersion", 1);
        merged.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        orderedCases.get(0).scope().loopBound().writeTo(merged);
        merged.addProperty("summaryId", "SUMMARY." + region
                + ".MERGED." + relationHash);
        OutputClosureCodec.writeTo(merged, outputClosure);
        if (occurrenceCatalog.size() > 0) {
            String logicalRegionId = orderedCases.get(0)
                    .logicalRegionId();
            String summaryReuseKey = orderedCases.get(0)
                    .summaryReuseKey();
            if (!logicalRegionId.isEmpty()) {
                merged.addProperty("logicalRegionId", logicalRegionId);
            }
            if (!summaryReuseKey.isEmpty()) {
                merged.addProperty("summaryReuseKey", summaryReuseKey);
            }
            merged.add(RegionInstancePlan.OCCURRENCE_CATALOG,
                    occurrenceCatalog);
        }
        merged.add("edgeBindings", bindings);
        merged.add("regionRelation", relation);
        if (coverage != null) merged.add("pathCoverage", coverage);
        merged.addProperty("relationallyComplete", true);
        return new RelationSummary(merged, outputClosure);
    }

    public JsonObject toJson() { return row.deepCopy(); }
    public OutputClosureContract outputClosure() { return outputClosure; }
    public String summaryId() { return string(row, "summaryId"); }
    public String regionId() {
        return outputClosure.producer().regionId();
    }
    public String regionInstanceId() {
        return outputClosure.producer().regionInstanceId();
    }
    public List<JsonObject> edgeBindings() { return edgeBindings; }
    public String logicalRegionId() {
        return string(row, "logicalRegionId");
    }
    public String summaryReuseKey() {
        return string(row, "summaryReuseKey");
    }
    public JsonObject occurrenceInstantiationCatalog() {
        JsonElement value = row.get(RegionInstancePlan.OCCURRENCE_CATALOG);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject().deepCopy() : new JsonObject();
    }

    public boolean same(RelationSummary other) {
        return other != null && summaryId().equals(other.summaryId());
    }

    private static JsonObject occurrenceCatalog(
            List<PathObservation> paths) {
        JsonObject selected = new JsonObject();
        String logicalRegionId = "";
        String summaryReuseKey = "";
        boolean missingCatalog = false;
        for (PathObservation path : paths) {
            JsonObject catalog = path.occurrenceInstantiationCatalog();
            if (catalog.size() == 0) {
                if (!path.logicalRegionId().isEmpty()
                        || !path.summaryReuseKey().isEmpty()
                        || selected.size() > 0) {
                    throw new IllegalArgumentException(
                            "logical closed path is missing its occurrence "
                                    + "catalog");
                }
                missingCatalog = true;
                continue;
            }
            if (missingCatalog) {
                throw new IllegalArgumentException(
                        "closed paths mix legacy and logical occurrence "
                                + "identity");
            }
            if (path.logicalRegionId().isEmpty()
                    || path.summaryReuseKey().isEmpty()) {
                throw new IllegalArgumentException(
                        "occurrence catalog requires logical summary "
                                + "identity");
            }
            if (selected.size() == 0) {
                selected = catalog;
                logicalRegionId = path.logicalRegionId();
                summaryReuseKey = path.summaryReuseKey();
                continue;
            }
            if (!CanonicalJson.render(selected).equals(
                    CanonicalJson.render(catalog))
                    || !logicalRegionId.equals(path.logicalRegionId())
                    || !summaryReuseKey.equals(path.summaryReuseKey())) {
                throw new IllegalArgumentException(
                        "closed paths have conflicting occurrence catalogs");
            }
        }
        return selected.deepCopy();
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
                                        PathObservation path,
                                        boolean projectRelationGuard) {
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
            cases.add(pathCase(path, projectRelationGuard, selection));
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
                                       boolean projectRelationGuard,
                                       Map<String, Integer> selection) {
        JsonObject item = new JsonObject();
        StringBuilder caseId = new StringBuilder("CASE.")
                .append(projectRelationGuard
                        ? path.relationKey() : path.pathKey());
        JsonArray conditions = projectRelationGuard
                ? path.relationPathCondition() : path.pathCondition();
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
        JsonObject identities = path.outputReferenceIdentities();
        if (identities.size() > 0) {
            item.add("outputReferenceIdentities", identities);
        }
        item.addProperty("sourceTaskId", path.sourceTaskId());
        return item;
    }
}
