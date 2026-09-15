package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The one runtime edge catalog, and the one way to reference it.
 *
 * <p>A runtime edge binding is immutable evidence named by its own
 * {@code edgeId}.  The same binding is selected by many occurrence goals and
 * by many execution tasks, so writing it out wherever it is selected restates
 * one catalog once per selection: measured on a recorded campaign, 364,006
 * task-row selections of 3,678 distinct bindings, 387 MB of the 516 MB of
 * published task plans.</p>
 *
 * <p>Rows therefore publish {@code edgeBindingIds} and the reader hydrates
 * them against the catalog the artifact already carries.  An id with no
 * catalog row is a corrupt pairing of artifacts, not a row to skip, so it is
 * refused by name.</p>
 */
public final class EdgeBindingCatalog {
    /** Inline bindings, as a decoded row carries them. */
    public static final String BINDINGS = "edgeBindings";
    /** Catalog references, as a published row carries them. */
    public static final String IDS = "edgeBindingIds";

    private final Map<String, JsonObject> byId;

    private EdgeBindingCatalog(Map<String, JsonObject> byId) {
        this.byId = byId;
    }

    /** Indexes one flat catalog; duplicate or nested rows are refused. */
    public static EdgeBindingCatalog of(Collection<JsonObject> edges) {
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        if (edges != null) {
            for (JsonObject edge : edges) {
                String id = optionalString(edge, "edgeId");
                if (id.isEmpty() || edge.has("bindings")
                        || byId.putIfAbsent(id, edge) != null) {
                    throw new IllegalArgumentException(
                            "runtime edges must be flat with unique nonempty"
                                    + " ids: " + id);
                }
            }
        }
        return new EdgeBindingCatalog(byId);
    }

    public int size() { return byId.size(); }

    /**
     * The ids of bindings this catalog accounts for, in selection order.
     *
     * <p>A binding that is absent, or that differs from the catalog row of
     * the same id, means the row and the catalog describe different runs.
     * Publishing its id would silently substitute the catalog's evidence for
     * the row's, so it is refused instead.</p>
     */
    public JsonArray idsOf(JsonArray bindings) {
        Set<String> ids = new LinkedHashSet<>();
        for (JsonElement element : bindings == null
                ? new JsonArray() : bindings) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "edgeBindings must contain objects");
            }
            JsonObject binding = element.getAsJsonObject();
            String id = optionalString(binding, "edgeId");
            if (id.isEmpty() || !binding.equals(byId.get(id))) {
                throw new IllegalArgumentException(
                        "edge binding is absent from the edge catalog: " + id);
            }
            ids.add(id);
        }
        JsonArray result = new JsonArray();
        for (String id : ids) result.add(id);
        return result;
    }

    /** The bindings named by one id list, in the order it names them. */
    public JsonArray hydrate(JsonArray ids) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (JsonElement element : ids == null ? new JsonArray() : ids) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()
                    || element.getAsString().trim().isEmpty()
                    || !seen.add(element.getAsString())) {
                throw new IllegalArgumentException(
                        "edgeBindingIds must be unique nonempty strings");
            }
            JsonObject edge = byId.get(element.getAsString());
            if (edge == null) {
                throw new IllegalArgumentException(
                        "unknown runtime edge id " + element.getAsString());
            }
            result.add(edge.deepCopy());
        }
        return result;
    }

}
