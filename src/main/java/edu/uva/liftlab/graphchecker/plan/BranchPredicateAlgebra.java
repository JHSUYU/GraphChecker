package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public final class BranchPredicateAlgebra {
    private static final Map<String, String> COMPLEMENTS = complements();

    private BranchPredicateAlgebra() {
    }

    static JsonElement canonicalView(JsonElement predicate,
                                     Map<JsonElement, JsonElement> views) {
        if (predicate == null) return JsonNull.INSTANCE;
        List<JsonElement> pending = new ArrayList<JsonElement>();
        pending.add(predicate);
        while (!pending.isEmpty()) {
            JsonElement node = pending.get(pending.size() - 1);
            if (!composite(node) || views.containsKey(node)) {
                pending.remove(pending.size() - 1);
                continue;
            }
            boolean ready = true;
            for (JsonElement child : node.isJsonArray()
                    ? node.getAsJsonArray()
                    : node.getAsJsonObject().asMap().values()) {
                if (composite(child) && !views.containsKey(child)) {
                    pending.add(child);
                    ready = false;
                }
            }
            if (!ready) continue;
            pending.remove(pending.size() - 1);
            views.put(node, node.isJsonArray()
                    ? view(node.getAsJsonArray(), views)
                    : view(node.getAsJsonObject(), views));
        }
        return composite(predicate) ? views.get(predicate) : predicate;
    }

    private static boolean composite(JsonElement value) {
        return value != null && (value.isJsonArray() || value.isJsonObject());
    }

    private static JsonElement view(JsonArray source,
                                    Map<JsonElement, JsonElement> views) {
        JsonArray copy = null;
        for (int index = 0; index < source.size(); index++) {
            JsonElement child = source.get(index);
            JsonElement canonical = composite(child) ? views.get(child)
                    : child;
            if (copy == null && canonical != child) {
                copy = new JsonArray();
                for (int prior = 0; prior < index; prior++) {
                    copy.add(source.get(prior));
                }
            }
            if (copy != null) copy.add(canonical);
        }
        return copy == null ? source : copy;
    }

    private static JsonElement view(JsonObject source,
                                    Map<JsonElement, JsonElement> views) {
        JsonObject copy = null;
        int index = 0;
        for (Map.Entry<String, JsonElement> field : source.entrySet()) {
            JsonElement child = field.getValue();
            JsonElement canonical = child == null || child.isJsonNull()
                    ? null : composite(child) ? views.get(child) : child;
            if (copy == null && canonical != child) {
                copy = new JsonObject();
                int prior = 0;
                for (Map.Entry<String, JsonElement> existing
                        : source.entrySet()) {
                    if (prior++ == index) break;
                    copy.add(existing.getKey(), existing.getValue());
                }
            }
            if (copy != null && canonical != null) {
                copy.add(field.getKey(), canonical);
            }
            index++;
        }
        return copy == null ? source : copy;
    }

    public static String complementOperator(String operator) {
        String result = COMPLEMENTS.get(operator);
        if (result == null) {
            throw new IllegalArgumentException(
                    "unsupported binary comparison operator: " + operator);
        }
        return result;
    }

    private static Map<String, String> complements() {
        Map<String, String> result = new LinkedHashMap<>();
        result.put("==", "!=");
        result.put("!=", "==");
        result.put("<", ">=");
        result.put("<=", ">");
        result.put(">", "<=");
        result.put(">=", "<");
        return Collections.unmodifiableMap(result);
    }
}
