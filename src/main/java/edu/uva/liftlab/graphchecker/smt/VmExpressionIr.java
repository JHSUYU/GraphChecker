package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The one reading of the VM's expression IR: operator vocabulary, constant
 * payloads, literal shapes and root patterns.
 */
public final class VmExpressionIr {

    /** The VM's spelling of a symbolic null reference. */
    public static final String SYMBOLIC_NULL = "N";
    /** The VM's spelling of void, its other built-in symbol. */
    public static final String SYMBOLIC_VOID = "V";
    /**
     * A value the VM declined to state in full (a String past its bound):
     * {@code {"_type":"TruncatedValue","length":n}}, read as unstated.
     */
    public static final String TRUNCATED_VALUE_TYPE = "TruncatedValue";
    /** Transparent VM marker installed at a consumer-side value boundary. */
    private static final String CONSUMER_BOUNDARY_TYPE =
            "ConsumerBoundaryExpression";
    /** Persisted reference to one replay-independent boundary family. */
    private static final String CONSUMER_BOUNDARY_REFERENCE_TYPE =
            "ConsumerBoundaryReference";
    /** The member a wrapper (boundary, observed version) holds its value in. */
    public static final String EXPRESSION = "expression";

    /** Runtime-evidence identity assigned to one propagated map state. */
    private static final Pattern CANONICAL_MAP_STATE_REFERENCE =
            Pattern.compile("^MAP_STATE\\.v1\\.[0-9a-f]{64}$");

    /** One exact VM value root: the symbol the VM minted for one site. */
    public static final String SYMBOL_TYPE = "SymbolExpression";

    /** The VM's node for one {@code java.lang.String} method's result. */
    public static final String STRING_OPERATION_TYPE = "OpStrExpression";

    private static final Set<String> BOOLEAN_STRING_OPERATIONS =
            new HashSet<String>(Arrays.asList(
                    "isEmpty", "equals", "equalsIgnoreCase", "contains",
                    "startsWith", "endsWith", "matches"));
    private static final Set<String> INT_STRING_OPERATIONS =
            new HashSet<String>(Arrays.asList(
                    "length", "indexOf", "lastIndexOf", "charAt",
                    "compareTo", "compareToIgnoreCase", "hashCode",
                    "codePointAt"));

    private VmExpressionIr() {
    }

    /**
     * The java type of what one {@code String} operation returns: the VM's
     * node states none, and its operands' types are not its own
     * ({@code length} of a string is an int).
     */
    public static String stringOperationType(String operation) {
        if (BOOLEAN_STRING_OPERATIONS.contains(operation)) return "Z";
        if (INT_STRING_OPERATIONS.contains(operation)) return "I";
        return "Ljava/lang/String;";
    }

    /** One node's {@code _type}, or "" for anything but an object. */
    public static String typeOf(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                ? optionalString(expression.getAsJsonObject(), "_type") : "";
    }

    /**
     * True when the tree carries a symbol, a read-from or a consumer boundary
     * (even around a constant: its producer still decides when it arrives).
     * A plain constant fold may be minted afresh.
     */
    public static boolean carriesPropagatedValue(JsonElement expression) {
        return carries(expression, type -> SYMBOL_TYPE.equals(type)
                || CONSUMER_BOUNDARY_TYPE.equals(type)
                || VmRows.GUARDED_READ_TYPE.equals(type));
    }

    /**
     * True only when the tree names at least one VM symbol root, looking
     * through {@code ReadFrom}/{@code ConsumerBoundary} wrappers.  A declared
     * source needs this, not {@link #carriesPropagatedValue}: a
     * constant-written field arrives wrapped and would never get a root.
     */
    public static boolean carriesSymbolicValue(JsonElement expression) {
        return carries(expression, SYMBOL_TYPE::equals);
    }

    /** Whether any node of the tree has a {@code _type} {@code wanted}
     *  names ({@link ExpressionWalk}: walked as a tree, a shared chain is
     *  2^depth paths). */
    private static boolean carries(JsonElement expression,
                                   Predicate<String> wanted) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            if (wanted.test(optionalString(walk.next(), "_type"))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether a symbol's {@code _exp} is one of the VM's built-in constants
     * (null, void) and not a name: every null check spells the same "N".
     */
    public static boolean builtinSymbol(String raw) {
        return SYMBOLIC_NULL.equals(raw) || SYMBOLIC_VOID.equals(raw);
    }

    /** The expression, only when the VM stated one exact, complete root. */
    public static JsonObject exactSymbolRoot(JsonElement expression) {
        if (!SYMBOL_TYPE.equals(typeOf(expression))) return null;
        JsonObject root = expression.getAsJsonObject();
        return !optionalString(root, "_exp").isEmpty()
                && !optionalString(root, "_java_type").isEmpty()
                && !VmRows.truncated(root) ? root : null;
    }

    /**
     * Whether this node is a consumer boundary, inline or by reference:
     * either way it stands for the value in its {@link #EXPRESSION}.
     */
    public static boolean consumerBoundary(JsonElement expression) {
        String type = typeOf(expression);
        return CONSUMER_BOUNDARY_TYPE.equals(type)
                || CONSUMER_BOUNDARY_REFERENCE_TYPE.equals(type);
    }

    /** Whether runtime carrier evidence gave this state a replay-stable id. */
    public static boolean isCanonicalMapStateReference(String raw) {
        return raw != null
                && CANONICAL_MAP_STATE_REFERENCE.matcher(raw).matches();
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

    /** A String constant as the VM spells one ({@link #constantPayload}
     *  reads the text back). */
    public static JsonObject stringConstant(String text) {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConStringSymbolExp");
        constant.addProperty("_exp", "Y_L'String'_" + text);
        constant.addProperty("_java_type", "java/lang/String");
        return constant;
    }

    /** One {@code String} operation as the VM spells one, un-negated. */
    public static JsonObject stringOperation(String name, JsonArray params) {
        JsonObject operation = new JsonObject();
        operation.addProperty("_type", STRING_OPERATION_TYPE);
        operation.addProperty("_name", name);
        operation.addProperty("_is_not", false);
        operation.add("_param_list", params);
        return operation;
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
