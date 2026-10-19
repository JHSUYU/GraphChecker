package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class RuntimePlanArtifact {
    private static final int SCHEMA_VERSION = 2;
    private static final String CATALOG_KIND =
            "CONCOLIC_RUNTIME_MODEL_CATALOG";
    private static final String PLAN_KIND = "CONCOLIC_REGION_PLAN";

    private final List<RegionInstancePlan> plans;
    private final List<JsonObject> regions;

    private RuntimePlanArtifact(List<RegionInstancePlan> plans,
                                List<JsonObject> regions) {
        this.plans = plans;
        this.regions = regions;
    }

    public List<RegionInstancePlan> regionPlans() { return plans; }

    public List<JsonObject> regions() { return copies(regions); }

    public static void write(Writer output,
                             Collection<JsonObject> encodedRegions,
                             Collection<JsonObject> encodedGaps,
                             Iterable<JsonObject> encodedPlans)
            throws IOException {
        output.write(encodeCatalog(encodedRegions, encodedGaps));
        for (JsonObject source : encodedPlans) {
            output.write(CanonicalJson.render(source));
            output.write('\n');
        }
    }

    private static String encodeCatalog(Collection<JsonObject> encodedRegions,
                                        Collection<JsonObject> encodedGaps) {
        JsonObject catalog = new JsonObject();
        catalog.addProperty("schemaVersion", SCHEMA_VERSION);
        catalog.addProperty("kind", CATALOG_KIND);
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
        List<JsonObject> regions = objects(array(catalog, "regions"),
                "runtime region catalog", path);
        List<RegionInstancePlan> decoded = new ArrayList<>();
        try {
            for (JsonObject plan : compactPlans) {
                decoded.add(RegionInstancePlan.decode(plan));
            }
        } catch (IllegalArgumentException malformed) {
            throw new IOException("invalid runtime plan row: " + path,
                    malformed);
        }
        Set<String> occurrences = new LinkedHashSet<>();
        for (RegionInstancePlan plan : decoded) {
            if (!occurrences.add(plan.occurrenceId())) {
                throw new IOException("duplicate region occurrence: "
                        + plan.occurrenceId());
            }
        }
        objects(array(catalog, "gaps"), "runtime plan gaps", path);
        return new RuntimePlanArtifact(decoded, regions);
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

    private static List<JsonObject> copies(Collection<JsonObject> values) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject value : values) result.add(value.deepCopy());
        return result;
    }
}
