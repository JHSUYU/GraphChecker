package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
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
        return CanonicalJson.copy(withoutNullMembers(predicate));
    }

    /**
     * Drops object members whose value is JSON null.
     *
     * <p>One predicate reaches a comparison by two routes. The VM's own
     * serialization of the recorded path condition is spliced into a result
     * verbatim, so an optional member the VM emitted as {@code null} -- an
     * absent path guard on a read-from arm is the ordinary case -- survives.
     * The same predicate copied through the Java runtime and written back out
     * loses that member, because a JSON writer that does not serialize nulls
     * treats "present and null" and "absent" as the same thing. They do mean
     * the same thing, and a canonical form that disagrees turns one predicate
     * into two and rejects a branch witness that matches its own recording
     * exactly.</p>
     *
     * <p>Only object members are dropped. A null inside an array is a
     * position, and removing it would renumber every element after it.</p>
     */
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
