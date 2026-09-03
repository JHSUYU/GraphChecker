package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Canonical runtime-planning artifact.
 *
 * <p>The first JSONL row owns the region-port catalog and runtime edge
 * evidence exactly once; occurrence goals store only edge ids, and
 * {@link #read(Path)} hydrates them back into {@code edgeBindings}.</p>
 */
public final class RuntimePlanArtifact {
    public static final int SCHEMA_VERSION = 2;
    public static final String CATALOG_KIND =
            "CONCOLIC_RUNTIME_MODEL_CATALOG";
    public static final String PLAN_KIND = "CONCOLIC_REGION_PLAN";
    public static final String EDGE_BINDING_IDS = "edgeBindingIds";
    private static final int REGION_SCHEMA_VERSION = 3;
    private static final String REGION_KIND = "SYMBOLIC_REGION";

    private final List<RegionInstancePlan> plans;
    private final List<JsonObject> regions;

    private RuntimePlanArtifact(List<RegionInstancePlan> plans,
                                List<JsonObject> regions) {
        this.plans = plans;
        this.regions = regions;
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

    /** Encodes compact plans plus one canonical region/edge catalog. */
    public static String encode(Collection<JsonObject> encodedPlans,
                                Collection<JsonObject> encodedEdges,
                                Collection<JsonObject> encodedRegions) {
        List<JsonObject> edges = copies(encodedEdges);
        Map<String, JsonObject> edgeById = indexEdges(edges);

        StringBuilder output = new StringBuilder();
        output.append(encodeCatalog(edges,
                compactRegions(encodedRegions)));
        for (JsonObject source : encodedPlans) {
            output.append(CanonicalJson.render(
                    compactBindings(source, edgeById))).append('\n');
        }
        return output.toString();
    }

    private static String encodeCatalog(List<JsonObject> edges,
                                        List<JsonObject> encodedRegions) {
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
        return CanonicalJson.render(catalog) + "\n";
    }

    /** Reads one bundle and restores the canonical in-memory binding view. */
    public static RuntimePlanArtifact read(Path path) throws IOException {
        List<JsonObject> rows = readRows(path);
        JsonObject catalog = catalog(rows, path);
        List<JsonObject> compactPlans = new ArrayList<>();
        for (int index = 1; index < rows.size(); index++) {
            JsonObject row = rows.get(index);
            if (!PLAN_KIND.equals(string(row, "kind"))) {
                throw new IOException("unknown runtime plan row kind "
                        + string(row, "kind") + ": " + path + ":"
                        + (index + 1));
            }
            compactPlans.add(row);
        }
        List<JsonObject> edges = objects(array(catalog, "edges"),
                "runtime edge catalog", path);
        List<JsonObject> regions = objects(array(catalog, "regions"),
                "runtime region catalog", path);
        Map<String, JsonObject> edgeById;
        try {
            edgeById = indexEdges(edges);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid runtime edge catalog: " + path,
                    malformed);
        }
        List<RegionInstancePlan> decoded = new ArrayList<>();
        try {
            for (JsonObject plan : compactPlans) {
                decoded.add(RegionInstancePlan.decode(
                        hydrateBindings(plan, edgeById)));
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
        return new RuntimePlanArtifact(decoded, regions);
    }

    private static List<JsonObject> readRows(Path path) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException("runtime plan artifact not found: " + path);
        }
        List<JsonObject> rows = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) continue;
                JsonElement parsed;
                try {
                    parsed = JsonParser.parseString(line);
                } catch (RuntimeException malformed) {
                    throw new IOException("malformed runtime plan " + path
                            + ":" + lineNumber, malformed);
                }
                if (!parsed.isJsonObject()) {
                    throw new IOException("non-object runtime plan row "
                            + path + ":" + lineNumber);
                }
                rows.add(parsed.getAsJsonObject());
            }
        }
        return rows;
    }

    private static JsonObject catalog(List<JsonObject> rows, Path path)
            throws IOException {
        if (rows.isEmpty()
                || !CATALOG_KIND.equals(string(rows.get(0), "kind"))
                || integer(rows.get(0), "schemaVersion", -1)
                != SCHEMA_VERSION) {
            throw new IOException("runtime edge catalog must be the first row: "
                    + path);
        }
        return rows.get(0);
    }

    private static JsonObject compactBindings(
            JsonObject source, Map<String, JsonObject> edgeById) {
        JsonObject plan = source.deepCopy();
        for (JsonElement element : array(plan, "closureGoals")) {
            JsonObject goal = element.getAsJsonObject();
            // Compacting twice would replace the stored ids with an empty
            // list, so the second pass is refused rather than absorbed.
            if (goal.has(EDGE_BINDING_IDS)) {
                throw new IllegalArgumentException(
                        "runtime plan is already binding-compacted");
            }
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement bindingElement : array(goal,
                    "edgeBindings")) {
                JsonObject binding = bindingElement.getAsJsonObject();
                String id = string(binding, "edgeId");
                JsonObject evidence = edgeById.get(id);
                if (id.isEmpty() || !binding.equals(evidence)) {
                    throw new IllegalArgumentException(
                            "goal binding is absent from the edge catalog: "
                                    + id);
                }
                ids.add(id);
            }
            JsonArray encodedIds = new JsonArray();
            for (String id : ids) encodedIds.add(id);
            goal.remove("edgeBindings");
            goal.add(EDGE_BINDING_IDS, encodedIds);
        }
        return plan;
    }

    private static JsonObject hydrateBindings(
            JsonObject source, Map<String, JsonObject> edgeById) {
        JsonObject plan = source.deepCopy();
        for (JsonElement element : array(plan, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects");
            }
            JsonObject goal = element.getAsJsonObject();
            if (goal.has("edgeBindings")) {
                throw new IllegalArgumentException(
                        "compact runtime plan must not duplicate edgeBindings");
            }
            JsonArray hydrated = new JsonArray();
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement idElement : array(goal, EDGE_BINDING_IDS)) {
                if (!idElement.isJsonPrimitive()
                        || !idElement.getAsJsonPrimitive().isString()
                        || idElement.getAsString().trim().isEmpty()
                        || !ids.add(idElement.getAsString())) {
                    throw new IllegalArgumentException(
                            "edgeBindingIds must be unique nonempty strings");
                }
                JsonObject edge = edgeById.get(idElement.getAsString());
                if (edge == null) {
                    throw new IllegalArgumentException(
                            "unknown runtime edge id "
                                    + idElement.getAsString());
                }
                hydrated.add(edge.deepCopy());
            }
            goal.remove(EDGE_BINDING_IDS);
            goal.add("edgeBindings", hydrated);
        }
        return plan;
    }

    private static Map<String, JsonObject> indexEdges(
            List<JsonObject> edges) {
        Map<String, JsonObject> result = new LinkedHashMap<>();
        for (JsonObject edge : edges) {
            String id = string(edge, "edgeId");
            if (id.isEmpty() || edge.has("bindings")
                    || result.putIfAbsent(id, edge) != null) {
                throw new IllegalArgumentException(
                        "runtime edges must be flat with unique nonempty ids: "
                                + id);
            }
        }
        return result;
    }

    /**
     * Keeps only the region schema needed after runtime planning; the full
     * method, branch and access history stays in the trace/refined graph.
     */
    private static List<JsonObject> compactRegions(
            Collection<JsonObject> encodedRegions) {
        List<JsonObject> result = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        if (encodedRegions == null) return result;
        for (JsonObject source : encodedRegions) {
            if (source == null
                    || !exactSchemaVersion(source, REGION_SCHEMA_VERSION)
                    || !REGION_KIND.equals(string(source, "kind"))) {
                throw new IllegalArgumentException(
                        "runtime region has an unsupported schema");
            }
            JsonObject region = new JsonObject();
            copy(region, source, "schemaVersion");
            copy(region, source, "kind");
            copy(region, source, "regionId");
            String id = string(region, "regionId");
            if (id.isEmpty() || !ids.add(id)) {
                throw new IllegalArgumentException(
                        "runtime region ids must be unique and nonempty: "
                                + id);
            }
            region.add("symbolicInputs", compactPorts(
                    array(source, "symbolicInputs")));
            region.add("outputs", compactPorts(array(source, "outputs")));
            copy(region, source, StaticSymbolicSourceDeclaration.FIELD);
            result.add(region);
        }
        return result;
    }

    private static boolean exactSchemaVersion(JsonObject row, int expected) {
        JsonElement value = row.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(expected).equals(value.getAsString());
    }

    private static JsonArray compactPorts(JsonArray ports) {
        JsonArray result = new JsonArray();
        for (JsonElement element : ports) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "runtime region ports must be objects");
            }
            JsonObject source = element.getAsJsonObject();
            JsonObject port = new JsonObject();
            for (String field : new String[]{
                    "portId", "symbol", "cell", "javaType",
                    "sourceKind", "dependencyRole",
                    "declaredFieldSignature", "accessFieldSignature",
                    "leafFieldSignature", "callerMethod", "unitIndex",
                    // Where a cut port's value is read, by name.  Dropping
                    // the names left the composer to re-derive the capture
                    // from a position - the guess the cut vocabulary exists
                    // to avoid.
                    CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                    CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                    CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                    // Which side of which call site this port is; without
                    // them a consumer has to re-derive the direction from the
                    // id's spelling.
                    CommunicationCatalogContract.PORT_DIRECTION,
                    CommunicationCatalogContract.TRANSPORT,
                    "portRole",
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                    CommunicationCatalogContract.CALL_SITE_ID,
                    CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    "declaredCallee", "accessorImplementationMethod",
                    "fieldPath", "fieldPathDeclarations"}) {
                copy(port, source, field);
            }
            JsonArray accesses = compactProjectionAccesses(
                    array(source, "runtimeAccesses"));
            if (accesses.size() > 0) port.add("runtimeAccesses", accesses);
            if (string(port, "portId").isEmpty()
                    && string(port, "symbol").isEmpty()) {
                throw new IllegalArgumentException(
                        "runtime region port has no stable id");
            }
            result.add(port);
        }
        return result;
    }

    private static JsonArray compactProjectionAccesses(JsonArray accesses) {
        JsonArray result = new JsonArray();
        for (JsonElement element : accesses) {
            if (!element.isJsonObject()) continue;
            JsonObject source = element.getAsJsonObject();
            if (!"EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1"
                    .equals(string(source,
                            "containerMemberIdentityAuthority"))) {
                continue;
            }
            JsonObject access = new JsonObject();
            // The observed event ordinal is the only identity a compacted
            // access needs.
            copy(access, source, "eventSeq");
            copy(access, source, "containerMemberIdentityAuthority");
            copy(access, source, "containerValueObjectId");
            result.add(access);
        }
        return result;
    }

    private static void copy(JsonObject target, JsonObject source,
                             String field) {
        JsonElement value = source.get(field);
        if (value != null && !value.isJsonNull()) {
            target.add(field, value.deepCopy());
        }
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
