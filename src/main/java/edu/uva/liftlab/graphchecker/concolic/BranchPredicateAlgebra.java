package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
    private static final Pattern REGION_INPUT_PORT = Pattern.compile(
            "(REGION(?:\\.[A-Za-z0-9-]+)+\\.in\\.[0-9]+)");

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

    /**
     * Compares predicates captured in different executions of one branch.
     *
     * <p>The customized VM names a non-null {@code String} from its runtime
     * class (for example {@code M_L'String'_REGION.4.in.6_...}), but names
     * the same input as a generic field reference when a replay materializes
     * {@code null} ({@code M_L_field_REGION.4.in.6_...}).  The concrete value
     * must not change the logical identity of the input.  For replay
     * comparison only, an expression symbol containing exactly one canonical
     * region input port is therefore projected to that port.  Solver-facing
     * predicates and immutable witness hashes retain the original VM
     * expression.</p>
     */
    public static boolean replayEquivalent(JsonElement left,
                                           JsonElement right) {
        if (equivalent(left, right)) return true;
        return equivalent(portableReplayIdentity(left),
                portableReplayIdentity(right));
    }

    public static boolean isComparisonOperator(String operator) {
        return COMPLEMENTS.containsKey(operator);
    }

    public static String complementOperator(String operator) {
        String result = COMPLEMENTS.get(operator);
        if (result == null) {
            throw new IllegalArgumentException(
                    "unsupported binary comparison operator: " + operator);
        }
        return result;
    }

    public static String fingerprint(JsonElement predicate) {
        return CanonicalJson.sha256(canonical(predicate));
    }

    private static JsonElement portableReplayIdentity(JsonElement value) {
        if (value == null || value.isJsonNull()
                || value.isJsonPrimitive()) {
            return CanonicalJson.copy(value);
        }
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            for (JsonElement element : value.getAsJsonArray()) {
                result.add(portableReplayIdentity(element));
            }
            return CanonicalJson.copy(result);
        }
        JsonObject result = new JsonObject();
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            result.add(entry.getKey(), portableReplayIdentity(
                    entry.getValue()));
        }
        if ("SymbolExpression".equals(string(result, "_type"))) {
            String port = uniqueInputPort(string(result, "_exp"));
            if (!port.isEmpty()) {
                result.addProperty("_exp", "$INPUT_PORT:" + port);
                // The VM's reference descriptor is value-sensitive for null
                // replays, so it is not part of portable input identity.
                result.remove("_java_type");
            }
        }
        return CanonicalJson.copy(result);
    }

    private static String uniqueInputPort(String symbol) {
        Set<String> ports = new LinkedHashSet<>();
        Matcher matcher = REGION_INPUT_PORT.matcher(symbol == null
                ? "" : symbol);
        while (matcher.find()) ports.add(matcher.group(1));
        return ports.size() == 1 ? ports.iterator().next() : "";
    }

    private static String string(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
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
