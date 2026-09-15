package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import edu.uva.liftlab.graphchecker.d3.smt.VmExpressionIr;

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
import java.util.Set;
import java.util.TreeSet;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/** The single polarity algebra for binary concolic branch predicates. */
public final class BranchPredicateAlgebra {
    private static final String SUPPORT_PREFIX = "BRANCH_SUPPORT.v1.";
    /** Joins a leaf's java type to its VM symbol in a support entry. */
    static final char SUPPORT_LEAF_SEPARATOR = '\u0000';
    private static final String SUPPORT_DOMAIN =
            "GraphChecker/branch-symbolic-support/v1\n";
    private static final Map<String, String> COMPLEMENTS = complements();
    private BranchPredicateAlgebra() {
    }

    public static JsonElement canonical(JsonElement predicate) {
        return canonicalCopy(predicate,
                new IdentityHashMap<JsonElement, JsonElement>());
    }

    /** Defensive canonical copy which retains sharing inside an expression DAG. */
    private static JsonElement canonicalCopy(
            JsonElement value,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return value == null ? JsonNull.INSTANCE : value.deepCopy();
        }
        JsonElement held = memo.get(value);
        if (held != null) return held;
        if (value.isJsonArray()) {
            JsonArray result = new JsonArray();
            memo.put(value, result);
            for (JsonElement item : value.getAsJsonArray()) {
                result.add(canonicalCopy(item, memo));
            }
            return result;
        }
        JsonObject result = new JsonObject();
        memo.put(value, result);
        List<String> names = new ArrayList<>();
        for (Map.Entry<String, JsonElement> entry
                : value.getAsJsonObject().entrySet()) {
            if (entry.getValue() != null && !entry.getValue().isJsonNull()) {
                names.add(entry.getKey());
            }
        }
        Collections.sort(names);
        for (String name : names) {
            JsonElement member = value.getAsJsonObject().get(name);
            if (member == null || member.isJsonNull()) continue;
            result.add(name, canonicalCopy(member, memo));
        }
        return result;
    }

    /**
     * Immutable capture path for VM-owned predicates.  Canonical rendering
     * already sorts object members, so capture only needs to remove null
     * members.  Copy-on-write keeps every untouched expression identity tied
     * to its decoder anchor.
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

    public static JsonElement complement(JsonElement predicate) {
        return CanonicalJson.copy(complementView(predicate));
    }

    /** Immutable-DAG complement used while assembling a solver task. */
    static JsonElement complementView(JsonElement predicate) {
        JsonElement canonical = canonicalView(predicate);
        if (canonical.isJsonObject()) {
            JsonObject object = canonical.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("BinaryExpression".equals(type)) {
                String opposite = COMPLEMENTS.get(optionalString(object, "_op"));
                if (opposite != null) {
                    JsonObject result = new JsonObject();
                    for (Map.Entry<String, JsonElement> field
                            : object.entrySet()) {
                        if (!"_op".equals(field.getKey())) {
                            result.add(field.getKey(), field.getValue());
                        }
                    }
                    result.addProperty("_op", opposite);
                    return result;
                }
            }
            if ("NotExpression".equals(type)
                    || "LogicalNotExpression".equals(type)) {
                JsonElement operand = object.get("_operand");
                return operand == null ? JsonNull.INSTANCE
                        : operand;
            }
        }
        JsonObject result = new JsonObject();
        result.addProperty("_type", "NotExpression");
        result.add("_operand", canonical);
        return result;
    }

    public static boolean equivalent(JsonElement left, JsonElement right) {
        if (left == right) return true;
        JsonElement canonicalLeft = canonicalView(left);
        JsonElement canonicalRight = canonicalView(right);
        if (canonicalLeft == canonicalRight) return true;
        if (expression(canonicalLeft) && expression(canonicalRight)) {
            SharedExpressionTable.Anchors anchors =
                    new SharedExpressionTable.Anchors();
            return anchors.contentAnchor(canonicalLeft).equals(
                    anchors.contentAnchor(canonicalRight));
        }
        return CanonicalJson.render(canonicalLeft)
                .equals(CanonicalJson.render(canonicalRight));
    }

    /**
     * Stable identity of the symbolic leaves that select one branch case.
     *
     * <p>The full predicate is deliberately not hashed here. Runtime values
     * such as a clock reading may legitimately change between the seed and
     * replay while the propagated element being tested stays the same. The
     * VM-assigned symbolic leaves name that element across the replay. An
     * empty result means the predicate has no such identity and callers must
     * retain their exact occurrence address.</p>
     */
    public static String symbolicSupportDigest(JsonElement predicate) {
        Set<String> support = symbolicSupport(predicate);
        if (support.isEmpty()) return "";
        StringBuilder encoded = new StringBuilder(SUPPORT_DOMAIN);
        for (String leaf : support) {
            encoded.append(leaf.length()).append(':').append(leaf)
                    .append('\n');
        }
        return SUPPORT_PREFIX + ArtifactIO.sha256(encoded.toString());
    }

    static boolean validSymbolicSupportDigest(String digest) {
        if (digest == null || !digest.startsWith(SUPPORT_PREFIX)
                || digest.length() != SUPPORT_PREFIX.length() + 64) {
            return false;
        }
        for (int index = SUPPORT_PREFIX.length(); index < digest.length();
             index++) {
            char value = digest.charAt(index);
            if (!(value >= '0' && value <= '9'
                    || value >= 'a' && value <= 'f')) {
                return false;
            }
        }
        return true;
    }

    /**
     * The symbolic leaves one predicate tests, each the leaf's java type
     * joined to its VM symbol by {@link #SUPPORT_LEAF_SEPARATOR}.
     *
     * <p>Exactly the set {@link #symbolicSupportDigest} hashes, handed back
     * instead of hashed. A planner that has to decide whether a branch can
     * still move needs the leaves themselves, not their identity: a digest
     * answers "is this the same branch" and this answers "what could change
     * it". Nothing else about the predicate is reported, for the same reason
     * the digest ignores it - a runtime value may differ between the seed and
     * a replay while the element being tested does not.</p>
     *
     * <p>The walk descends into every field of every node, guarded-read
     * candidate arms included. That is deliberate: a guarded read's value is
     * whichever writer arm the query selects, so an arm's expression is part
     * of what the condition tests even though the arm selector itself is a
     * solver Boolean rather than a symbol.</p>
     *
     * <p>The predicate must already be expanded: a
     * {@link SharedExpressionTable#REFERENCE_TYPE} node carries no leaves of
     * its own, so a compact DAG would under-report.</p>
     */
    public static Set<String> symbolicSupport(JsonElement predicate) {
        Set<String> support = new TreeSet<>();
        collectSymbolicSupport(predicate, support,
                Collections.newSetFromMap(
                        new IdentityHashMap<JsonElement, Boolean>()));
        return support;
    }

    /** Whether a predicate carries a reference no expansion resolved. */
    public static boolean hasUnexpandedReference(JsonElement predicate) {
        return unexpanded(predicate, Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>()));
    }

    private static boolean unexpanded(JsonElement value,
                                      Set<JsonElement> seen) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()
                || !seen.add(value)) {
            return false;
        }
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                if (unexpanded(child, seen)) return true;
            }
            return false;
        }
        JsonObject object = value.getAsJsonObject();
        if (SharedExpressionTable.isReference(object)) return true;
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            if (unexpanded(field.getValue(), seen)) return true;
        }
        return false;
    }

    private static void collectSymbolicSupport(
            JsonElement value, Set<String> support, Set<JsonElement> seen) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()
                || !seen.add(value)) {
            return;
        }
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                collectSymbolicSupport(child, support, seen);
            }
            return;
        }
        JsonObject object = value.getAsJsonObject();
        if ("SymbolExpression".equals(optionalString(object, "_type"))) {
            String symbol = optionalString(object, "_exp");
            if (!symbol.isEmpty()
                    && !VmExpressionIr.SYMBOLIC_NULL.equals(symbol)
                    && !"V".equals(symbol)) {
                support.add(optionalString(object, "_java_type")
                        + SUPPORT_LEAF_SEPARATOR + symbol);
            }
            return;
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            collectSymbolicSupport(field.getValue(), support, seen);
        }
    }

    private static boolean expression(JsonElement value) {
        return value != null && value.isJsonObject()
                && !optionalString(value.getAsJsonObject(), "_type").isEmpty();
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
