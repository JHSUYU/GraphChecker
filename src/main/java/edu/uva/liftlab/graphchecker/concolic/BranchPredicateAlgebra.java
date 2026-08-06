package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The single polarity algebra for binary concolic branch predicates.
 *
 * <p>Every predicate accepted or returned here is detached from its caller's
 * JSON tree and has recursively sorted object keys.  This gives witness hashes
 * and replay comparisons one representation independent of Gson insertion
 * order.</p>
 */
public final class BranchPredicateAlgebra {
    private static final Map<String, String> COMPLEMENTS = complements();
    private BranchPredicateAlgebra() {
    }

    public static JsonElement canonical(JsonElement predicate) {
        return CanonicalJson.copy(predicate);
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
        return CanonicalJson.render(left).equals(CanonicalJson.render(right));
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
