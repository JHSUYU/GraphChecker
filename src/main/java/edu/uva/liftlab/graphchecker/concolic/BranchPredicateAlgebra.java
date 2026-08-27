package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** The single polarity algebra for binary concolic branch predicates. */
public final class BranchPredicateAlgebra {
    private static final Map<String, String> COMPLEMENTS = complements();
    private BranchPredicateAlgebra() {
    }

    public static JsonElement canonical(JsonElement predicate) {
        return CanonicalJson.copy(withoutNullMembers(predicate));
    }

    /** Drops object members whose value is JSON null. */
    private static JsonElement withoutNullMembers(JsonElement value) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return value == null ? JsonNull.INSTANCE : value;
        }
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement item : value.getAsJsonArray()) {
                result.add(withoutNullMembers(item));
            }
            return result;
        }
        JsonObject result = new JsonObject();
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            JsonElement member = entry.getValue();
            if (member == null || member.isJsonNull()) continue;
            result.add(entry.getKey(), withoutNullMembers(member));
        }
        return result;
    }

    public static JsonElement complement(JsonElement predicate) {
        JsonElement canonical = canonical(predicate);
        if (canonical.isJsonObject()) {
            JsonObject object = canonical.getAsJsonObject();
            String type = string(object, "_type");
            if ("BinaryExpression".equals(type)) {
                String opposite = COMPLEMENTS.get(string(object, "_op"));
                if (opposite != null) {
                    object.addProperty("_op", opposite);
                    return CanonicalJson.copy(object);
                }
            }
            if ("NotExpression".equals(type)
                    || "LogicalNotExpression".equals(type)) {
                JsonElement operand = object.get("_operand");
                return operand == null ? JsonNull.INSTANCE
                        : CanonicalJson.copy(operand);
            }
        }
        JsonObject result = new JsonObject();
        result.addProperty("_type", "NotExpression");
        result.add("_operand", canonical);
        return CanonicalJson.copy(result);
    }

    public static boolean equivalent(JsonElement left, JsonElement right) {
        return CanonicalJson.render(canonical(left))
                .equals(CanonicalJson.render(canonical(right)));
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
