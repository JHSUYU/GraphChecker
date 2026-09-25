package edu.uva.liftlab.graphchecker.plan;



import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.Map;


/** The single polarity algebra for binary concolic branch predicates. */
public final class BranchPredicateAlgebra {
    private static final Map<String, String> COMPLEMENTS = complements();
    private BranchPredicateAlgebra() {
    }

    /** Capture view of a VM-owned predicate with null members removed.
     *  Copy-on-write: untouched subtrees keep their identity (decoder anchors).
     */
    static JsonElement canonicalView(JsonElement predicate) {
        return canonicalView(predicate,
                new IdentityHashMap<JsonElement, JsonElement>());
    }

    private static JsonElement canonicalView(
            JsonElement value,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return value == null ? JsonNull.INSTANCE : value;
        }
        JsonElement held = memo.get(value);
        if (held != null) return held;
        if (value.isJsonArray()) {
            JsonArray source = value.getAsJsonArray();
            JsonArray copy = null;
            for (int index = 0; index < source.size(); index++) {
                JsonElement child = source.get(index);
                JsonElement canonical = canonicalView(child, memo);
                if (copy == null && canonical != child) {
                    copy = new JsonArray();
                    for (int prior = 0; prior < index; prior++) {
                        copy.add(source.get(prior));
                    }
                }
                if (copy != null) copy.add(canonical);
            }
            JsonElement result = copy == null ? source : copy;
            memo.put(value, result);
            return result;
        }
        JsonObject source = value.getAsJsonObject();
        JsonObject copy = null;
        int index = 0;
        for (Map.Entry<String, JsonElement> field : source.entrySet()) {
            JsonElement child = field.getValue();
            JsonElement canonical = child == null || child.isJsonNull()
                    ? null : canonicalView(child, memo);
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
        JsonElement result = copy == null ? source : copy;
        memo.put(value, result);
        return result;
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
