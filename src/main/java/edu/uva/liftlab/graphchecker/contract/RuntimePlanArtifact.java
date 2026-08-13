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
import java.util.Collections;
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
 * evidence exactly once. Occurrence goals store only edge ids on disk;
 * {@link #read(Path)} hydrates those ids into the in-memory
 * {@code edgeBindings} view consumed by scheduling. This keeps the semantic
 * APIs unchanged without maintaining separate region/edge artifacts or
 * copying the same binding into every producer and consumer goal.</p>
 */
public final class RuntimePlanArtifact {
    public static final int SCHEMA_VERSION = 2;
    public static final String CATALOG_KIND =
            "CONCOLIC_RUNTIME_MODEL_CATALOG";
    public static final String PLAN_KIND = "CONCOLIC_REGION_PLAN";
    public static final String EDGE_BINDING_IDS = "edgeBindingIds";

    private final List<JsonObject> plans;
    private final List<JsonObject> edgeValidations;
    private final List<JsonObject> regions;

    private RuntimePlanArtifact(List<JsonObject> plans,
                                List<JsonObject> edgeValidations,
                                List<JsonObject> regions) {
        this.plans = immutableCopies(plans);
        this.edgeValidations = immutableCopies(edgeValidations);
        this.regions = immutableCopies(regions);
    }

    public List<JsonObject> plans() {
        return mutableCopies(plans);
    }

    public List<JsonObject> edgeValidations() {
        return mutableCopies(edgeValidations);
    }

    public List<JsonObject> regions() {
        return mutableCopies(regions);
    }

    /** Encodes compact plans plus their one canonical edge catalog. */
    public static String encode(Collection<JsonObject> encodedPlans,
                                Collection<JsonObject> encodedEdges) {
        return encode(encodedPlans, encodedEdges,
                Collections.<JsonObject>emptyList());
    }

    /** Encodes compact plans plus one canonical region/edge catalog. */
    public static String encode(Collection<JsonObject> encodedPlans,
                                Collection<JsonObject> encodedEdges,
                                Collection<JsonObject> encodedRegions) {
        List<JsonObject> edges = copies(encodedEdges);
        Map<String, JsonObject> edgeById = indexEdges(edges);
        List<JsonObject> regions = compactRegions(encodedRegions);

        StringBuilder output = new StringBuilder();
        output.append(encodeCatalog(edges, regions));
        for (JsonObject source : encodedPlans) {
            JsonObject plan = compactBindings(source, edgeById);
            RegionInstancePlan.decode(hydrateBindings(plan, edgeById));
            output.append(CanonicalJson.render(plan)).append('\n');
        }
        return output.toString();
    }

    private static String encodeCatalog(Collection<JsonObject> encodedEdges,
                                        Collection<JsonObject> encodedRegions) {
        List<JsonObject> edges = copies(encodedEdges);
        indexEdges(edges);
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
        List<JsonObject> hydrated = new ArrayList<>();
        try {
            for (JsonObject plan : compactPlans) {
                JsonObject value = hydrateBindings(plan, edgeById);
                RegionInstancePlan.decode(value);
                hydrated.add(value);
            }
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid compact runtime plan: " + path,
                    malformed);
        }
        return new RuntimePlanArtifact(hydrated, edges, regions);
    }

    /** Reads only the canonical catalog, for consumers that do not need goals. */
    public static List<JsonObject> readEdgeValidations(Path path)
            throws IOException {
        JsonObject catalog = catalog(readRows(path), path);
        List<JsonObject> edges = objects(array(catalog, "edges"),
                "runtime edge catalog", path);
        try {
            indexEdges(edges);
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid runtime edge catalog: " + path,
                    malformed);
        }
        return copies(edges);
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
        if (!PLAN_KIND.equals(string(plan, "kind"))) {
            throw new IllegalArgumentException(
                    "runtime plan row must have kind " + PLAN_KIND);
        }
        for (JsonElement element : array(plan, "closureGoals")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "closureGoals must contain objects");
            }
            JsonObject goal = element.getAsJsonObject();
            if (goal.has(EDGE_BINDING_IDS)) {
                throw new IllegalArgumentException(
                        "runtime plan is already binding-compacted");
            }
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement bindingElement : array(goal,
                    "edgeBindings")) {
                if (!bindingElement.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "edgeBindings must contain objects");
                }
                JsonObject binding = bindingElement.getAsJsonObject();
                String id = string(binding, "edgeId");
                JsonObject evidence = edgeById.get(id);
                if (id.isEmpty() || evidence == null
                        || !containsBinding(evidence, binding)) {
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

    private static boolean containsBinding(JsonObject evidence,
                                           JsonObject expected) {
        return evidence.equals(expected);
    }

    /**
     * Keeps only the region schema needed after runtime planning. The full
     * method, branch and access history remains in the trace/refined graph;
     * downstream scheduling and SMT lowering need only stable port metadata.
     */
    private static List<JsonObject> compactRegions(
            Collection<JsonObject> encodedRegions) {
        List<JsonObject> result = new ArrayList<>();
        Set<String> ids = new LinkedHashSet<>();
        if (encodedRegions == null) return result;
        for (JsonObject source : encodedRegions) {
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
            result.add(region);
        }
        return result;
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
                    "materialization", "sourceKind", "dependencyRole",
                    "declaredFieldSignature", "accessFieldSignature",
                    "leafFieldSignature", "callerMethod", "unitIndex",
                    "declaredCallee", "accessorImplementationMethod",
                    "fieldPath", "fieldPathDeclarations",
                    "boundedContainerStateRole",
                    "boundedContainerMemberProjectionAdmission",
                    "containerTimelineWriterPolicy",
                    "boundedContainerMemberProjectionBlocker",
                    "boundedContainerPreStatePorts",
                    "boundedContainerMemberProjections"}) {
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
            boolean boundedProjection = source.has(
                    "boundedContainerMemberProjection");
            boolean referencePut = "EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1"
                    .equals(string(source,
                            "containerMemberIdentityAuthority"));
            if (!boundedProjection && !referencePut) continue;
            JsonObject access = new JsonObject();
            copy(access, source, "eventSeq");
            copy(access, source, "rootCallId");
            if (boundedProjection) {
                copy(access, source,
                        "boundedContainerMemberProjection");
            }
            if (referencePut) {
                copy(access, source,
                        "containerMemberIdentityAuthority");
                copy(access, source, "containerValueObjectId");
            }
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

    private static List<JsonObject> immutableCopies(
            Collection<JsonObject> values) {
        return Collections.unmodifiableList(copies(values));
    }

    private static List<JsonObject> mutableCopies(
            Collection<JsonObject> values) {
        return copies(values);
    }
}
