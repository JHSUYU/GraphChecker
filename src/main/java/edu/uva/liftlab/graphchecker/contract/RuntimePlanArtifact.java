package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.ArtifactIO;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Canonical runtime-planning artifact.
 *
 * <p>The first JSONL row owns the region catalog and runtime edge evidence
 * exactly once; occurrence goals store only edge ids, and {@link #read(Path)}
 * hydrates them back into {@code edgeBindings}.</p>
 */
public final class RuntimePlanArtifact {
    private static final int SCHEMA_VERSION = 2;
    private static final String CATALOG_KIND =
            "CONCOLIC_RUNTIME_MODEL_CATALOG";
    private static final String PLAN_KIND = "CONCOLIC_REGION_PLAN";

    private final List<RegionInstancePlan> plans;
    private final List<JsonObject> regions;
    private final List<JsonObject> gaps;

    private RuntimePlanArtifact(List<RegionInstancePlan> plans,
                                List<JsonObject> regions,
                                List<JsonObject> gaps) {
        this.plans = plans;
        this.regions = regions;
        this.gaps = gaps;
    }

    /** The occurrence plans, decoded once here and never re-parsed. */
    public List<RegionInstancePlan> regionPlans() { return plans; }

    public List<JsonObject> plans() {
        List<JsonObject> result = new ArrayList<>();
        for (RegionInstancePlan plan : plans) {
            result.add(plan.json().deepCopy());
        }
        return result;
    }

    public List<JsonObject> regions() { return copies(regions); }

    /**
     * Gaps the planner raised about the ports this plan was built from.
     *
     * <p>A truncated access history or a container observation stream that
     * hit its capacity is invisible in every artifact downstream of this one,
     * so it is carried here rather than left to the planning JVM's stdout.
     * Older artifacts carry no such member and answer empty.</p>
     */
    public List<JsonObject> gaps() { return copies(gaps); }

    /** Encodes compact plans plus one canonical region/edge catalog. */
    public static String encode(Collection<JsonObject> encodedPlans,
                                Collection<JsonObject> encodedEdges,
                                Collection<JsonObject> encodedRegions) {
        return encode(encodedPlans, encodedEdges, encodedRegions,
                Collections.<JsonObject>emptyList());
    }

    /** As above, carrying the planning gaps the catalog publishes. */
    public static String encode(Collection<JsonObject> encodedPlans,
                                Collection<JsonObject> encodedEdges,
                                Collection<JsonObject> encodedRegions,
                                Collection<JsonObject> encodedGaps) {
        List<JsonObject> edges = copies(encodedEdges);
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(edges);

        StringBuilder output = new StringBuilder();
        output.append(encodeCatalog(edges, copies(encodedRegions),
                copies(encodedGaps)));
        for (JsonObject source : encodedPlans) {
            output.append(CanonicalJson.render(
                    compactBindings(source, catalog))).append('\n');
        }
        return output.toString();
    }

    private static String encodeCatalog(List<JsonObject> edges,
                                        List<JsonObject> encodedRegions,
                                        List<JsonObject> encodedGaps) {
        JsonObject catalog = new JsonObject();
        catalog.addProperty("schemaVersion", SCHEMA_VERSION);
        catalog.addProperty("kind", CATALOG_KIND);
        JsonArray edgeRows = new JsonArray();
        for (JsonObject edge : edges) edgeRows.add(edge.deepCopy());
        catalog.add("edges", edgeRows);
        JsonArray regionRows = new JsonArray();
        for (JsonObject region : encodedRegions) {
            regionRows.add(region.deepCopy());
        }
        catalog.add("regions", regionRows);
        JsonArray gapRows = new JsonArray();
        for (JsonObject gap : encodedGaps) gapRows.add(gap.deepCopy());
        catalog.add("gaps", gapRows);
        return CanonicalJson.render(catalog) + "\n";
    }

    /** Reads one bundle and restores the canonical in-memory binding view. */
    public static RuntimePlanArtifact read(Path path) throws IOException {
        List<JsonObject> rows = readRows(path);
        JsonObject catalog = catalog(rows, path);
        List<JsonObject> compactPlans = new ArrayList<>();
        for (int index = 1; index < rows.size(); index++) {
            JsonObject row = rows.get(index);
            if (!PLAN_KIND.equals(optionalString(row, "kind"))) {
                throw new IOException("unknown runtime plan row kind "
                        + optionalString(row, "kind") + ": " + path + ":"
                        + (index + 1));
            }
            compactPlans.add(row);
        }
        List<JsonObject> edges = objects(array(catalog, "edges"),
                "runtime edge catalog", path);
        List<JsonObject> regions = objects(array(catalog, "regions"),
                "runtime region catalog", path);
        EdgeBindingCatalog bindings;
        try {
            bindings = EdgeBindingCatalog.of(edges);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid runtime edge catalog: " + path,
                    malformed);
        }
        List<RegionInstancePlan> decoded = new ArrayList<>();
        try {
            for (JsonObject plan : compactPlans) {
                decoded.add(RegionInstancePlan.decode(
                        hydrateBindings(plan, bindings)));
            }
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid compact runtime plan: " + path,
                    malformed);
        }
        // One coarse occurrence is one row (README REGION-1); the decode
        // point owns that, and names the duplicate rather than reporting a
        // schema complaint about the artifact it sits in.
        Set<String> occurrences = new LinkedHashSet<>();
        for (RegionInstancePlan plan : decoded) {
            if (!occurrences.add(plan.occurrenceId())) {
                throw new IOException("duplicate region occurrence: "
                        + plan.occurrenceId());
            }
        }
        return new RuntimePlanArtifact(decoded, regions,
                objects(array(catalog, "gaps"), "runtime plan gaps", path));
    }

    private static List<JsonObject> readRows(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("runtime plan artifact not found: " + path);
        }
        return ArtifactIO.readJsonl(path, "malformed runtime plan %1$s:%2$d",
                "non-object runtime plan row %1$s:%2$d");
    }

    private static JsonObject catalog(List<JsonObject> rows, Path path)
            throws IOException {
        if (rows.isEmpty()
                || !CATALOG_KIND.equals(optionalString(rows.get(0), "kind"))
                || optionalInteger(rows.get(0), "schemaVersion", -1)
                != SCHEMA_VERSION) {
            throw new IOException("runtime edge catalog must be the first row: "
                    + path);
        }
        return rows.get(0);
    }

    private static JsonObject compactBindings(
            JsonObject source, EdgeBindingCatalog catalog) {
        JsonObject plan = source.deepCopy();
        for (JsonElement element : array(plan, "closureGoals")) {
            JsonObject goal = element.getAsJsonObject();
            // Compacting twice would replace the stored ids with an empty
            // list, so the second pass is refused rather than absorbed.
            if (goal.has(EdgeBindingCatalog.IDS)) {
                throw new IllegalArgumentException(
                        "runtime plan is already binding-compacted");
            }
            JsonArray ids = catalog.idsOf(
                    array(goal, EdgeBindingCatalog.BINDINGS));
            goal.remove(EdgeBindingCatalog.BINDINGS);
            goal.add(EdgeBindingCatalog.IDS, ids);
        }
        return plan;
    }

    private static JsonObject hydrateBindings(
            JsonObject source, EdgeBindingCatalog catalog) {
        JsonObject plan = source.deepCopy();
        for (JsonElement element : array(plan, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects");
            }
            JsonObject goal = element.getAsJsonObject();
            if (goal.has(EdgeBindingCatalog.BINDINGS)) {
                throw new IllegalArgumentException(
                        "compact runtime plan must not duplicate edgeBindings");
            }
            JsonArray hydrated = catalog.hydrate(
                    array(goal, EdgeBindingCatalog.IDS));
            goal.remove(EdgeBindingCatalog.IDS);
            goal.add(EdgeBindingCatalog.BINDINGS, hydrated);
        }
        return plan;
    }

    private static List<JsonObject> objects(JsonArray values, String label,
                                            Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement value : values) {
            if (!value.isJsonObject()) {
                throw new IOException(label + " contains a non-object: "
                        + path);
            }
            result.add(value.getAsJsonObject());
        }
        return result;
    }

    private static List<JsonObject> copies(
            Collection<JsonObject> values) {
        List<JsonObject> result = new ArrayList<>();
        if (values != null) {
            for (JsonObject value : values) result.add(value.deepCopy());
        }
        return result;
    }

}
