package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/** The single polarity algebra for binary concolic branch predicates. */
public final class BranchPredicateAlgebra {
    private static final Map<String, String> COMPLEMENTS = complements();

    private BranchPredicateAlgebra() {
    }

    /** Capture view of a VM-owned predicate with null members removed.
     *  Copy-on-write: untouched subtrees keep their identity (decoder anchors).
     *  Each node once, children first, on a stack: the capture runs on the
     *  workload's thread, whose stack a recursion along a deep predicate
     *  would overflow. */
    static JsonElement canonicalView(JsonElement predicate) {
        if (predicate == null) return JsonNull.INSTANCE;
        Map<JsonElement, JsonElement> views =
                new IdentityHashMap<JsonElement, JsonElement>();
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

    /** One array, each item's view already in {@code views}. */
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

    /** One object without its null members, each member's view already in
     *  {@code views}. */
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
