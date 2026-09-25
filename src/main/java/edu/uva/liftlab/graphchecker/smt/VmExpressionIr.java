package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.function.Predicate;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The one reading of the VM's expression IR: operator vocabulary, constant
 * payloads, literal shapes and root patterns.
 */
public final class VmExpressionIr {

    /** The VM's spelling of a symbolic null reference. */
    public static final String SYMBOLIC_NULL = "N";
    /** Transparent VM marker installed at a consumer-side value boundary. */
    public static final String CONSUMER_BOUNDARY_TYPE =
            "ConsumerBoundaryExpression";
    /** Persisted reference to one replay-independent boundary family. */
    public static final String CONSUMER_BOUNDARY_REFERENCE_TYPE =
            "ConsumerBoundaryReference";
    static final String RPC_ATTACH = "RPC_ATTACH";
    static final String FIELD_READ = "FIELD_READ";
    static final String BOUNDARY_KIND = "boundaryKind";
    static final String EVENT_ID = "eventId";
    static final String TOPOLOGY_EPOCH = "topologyEpoch";
    public static final String EXPRESSION = "expression";

    /**
     * Exact serialization of {@code InstanceSymbolExp} (allocated oop plus
     * its positive rid).  Field roots {@code M_L_field_*} must not match.
     */
    private static final Pattern ALLOCATED_INSTANCE_REFERENCE =
            Pattern.compile("^M_L'[^']+'_([1-9][0-9]*)$");

    /**
     * Exact serialization of {@code ArraySymbolExp}; the final number is the
     * array-state version, not an identity.
     */
    private static final Pattern ALLOCATED_ARRAY_REFERENCE =
            Pattern.compile("^A(?:[ZBCSIJFDL]|\\[)_([1-9][0-9]*)-([0-9]+)$");
    /** Runtime-evidence identity assigned to one propagated map state. */
    private static final Pattern CANONICAL_MAP_STATE_REFERENCE =
            Pattern.compile("^MAP_STATE\\.v1\\.[0-9a-f]{64}$");

    /** One exact VM value root: the symbol the VM minted for one site. */
    private static final String SYMBOL_TYPE = "SymbolExpression";
    /** A VM read that named the write it read from. */

    private VmExpressionIr() {
    }

    /**
     * True when the tree carries a symbol, a read-from or a consumer boundary
     * (even around a constant: its producer still decides when it arrives).
     * A plain constant fold may be minted afresh.
     */
    public static boolean carriesPropagatedValue(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                if (carriesPropagatedValue(child)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        String type = optionalString(node, "_type");
        if (SYMBOL_TYPE.equals(type)
                || CONSUMER_BOUNDARY_TYPE.equals(type)
                || VmRows.GUARDED_READ_TYPE.equals(type)) {
            return true;
        }
        for (java.util.Map.Entry<String, JsonElement> member
                : node.entrySet()) {
            if (!"_type".equals(member.getKey())
                    && carriesPropagatedValue(member.getValue())) {
                return true;
            }
        }
        return false;
    }

    /**
     * True only when the tree names at least one VM symbol root, looking
     * through {@code ReadFrom}/{@code ConsumerBoundary} wrappers.  A declared
     * source needs this, not {@link #carriesPropagatedValue}: a
     * constant-written field arrives wrapped and would never get a root.
     */
    public static boolean carriesSymbolicValue(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                if (carriesSymbolicValue(child)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        if (SYMBOL_TYPE.equals(optionalString(node, "_type"))) return true;
        for (java.util.Map.Entry<String, JsonElement> member
                : node.entrySet()) {
            if (!"_type".equals(member.getKey())
                    && carriesSymbolicValue(member.getValue())) {
                return true;
            }
        }
        return false;
    }

    /** The expression, only when the VM stated one exact, complete root. */
    public static JsonObject exactSymbolRoot(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject root = expression.getAsJsonObject();
        return SYMBOL_TYPE.equals(optionalString(root, "_type"))
                && !optionalString(root, "_exp").isEmpty()
                && !optionalString(root, "_java_type").isEmpty()
                && !VmRows.truncated(
                root) ? root : null;
    }

    public static boolean isConsumerBoundary(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && CONSUMER_BOUNDARY_TYPE.equals(optionalString(
                expression.getAsJsonObject(), "_type"));
    }

    public static boolean isConsumerBoundaryReference(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && CONSUMER_BOUNDARY_REFERENCE_TYPE.equals(optionalString(
                expression.getAsJsonObject(), "_type"));
    }

    /** Whether runtime carrier evidence gave this state a replay-stable id. */
    public static boolean isCanonicalMapStateReference(String raw) {
        return raw != null
                && CANONICAL_MAP_STATE_REFERENCE.matcher(raw).matches();
    }


    public static boolean isJavaParseInt(String name) {
        return "java/lang/Integer parseInt".equals(firstNonBlank(name));
    }

    public static boolean isJavaSplitElement(String name) {
        return "java/lang/String splitElement".equals(firstNonBlank(name));
    }

    public static String comparison(String operator) {
        if ("<".equals(operator) || ">".equals(operator)
                || "<=".equals(operator) || ">=".equals(operator)) {
            return operator;
        }
        return "";
    }

    public static String arithmetic(String operator) {
        if ("+".equals(operator) || "-".equals(operator)
                || "*".equals(operator)) return operator;
        return "";
    }

    public static boolean arithmeticOperator(String operator) {
        return "+".equals(operator) || "-".equals(operator)
                || "*".equals(operator) || "@".equals(operator)
                || "/".equals(operator) || "%".equals(operator);
    }

    public static boolean bitwiseOperator(String operator) {
        return "&".equals(operator) || "|".equals(operator)
                || "^".equals(operator);
    }

    public static boolean shiftOperator(String operator) {
        return "<<".equals(operator) || ">>".equals(operator)
                || ">>>".equals(operator);
    }

    public static String quote(String value) {
        String exact = value == null ? "" : value;
        return "\"" + exact.replace("\"", "\"\"") + "\"";
    }

    public static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    public static boolean isPrimitiveIntExpression(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String javaType = optionalString(object, "_java_type");
        return "I".equals(javaType) || "int".equals(javaType);
    }

    public static String exactStringLiteral(JsonElement expression,
                                     Predicate<String> stringTyped) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        if (!("ConStringSymbolExp".equals(type)
                || "ConstExpr".equals(type)
                || "ConSymbolExp".equals(type))) return null;
        if (!stringTyped.test(optionalString(object, "_java_type"))) {
            return null;
        }
        return constantPayload(optionalString(object, "_exp"));
    }

}
