package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.function.Predicate;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The one reading of the custom VM's expression IR the Composer and the
 * path-flip Solver share: operator vocabulary, constant payloads, and the
 * literal shapes both encoders must agree on before either lowers a term.
 *
 * <p>Where the two encoders resolve a Java type differently the difference is
 * a parameter, never a second copy: {@code stringTyped} is the caller's own
 * Java-type-to-sort decision.</p>
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
     * Exact serialization of {@code InstanceSymbolExp}: the VM can only
     * construct it from an allocated oop and appends that object's positive
     * symbolic runtime id.  Field roots ({@code M_L_field_*}) and unknown
     * writer placeholders deliberately do not match.
     */
    private static final Pattern ALLOCATED_INSTANCE_REFERENCE =
            Pattern.compile("^M_L'[^']+'_([1-9][0-9]*)$");

    /**
     * Exact serialization of {@code ArraySymbolExp}.  Like an
     * {@link #ALLOCATED_INSTANCE_REFERENCE}, this is minted from a concrete
     * array shadow.  The final number is the array-state version, not another
     * object identity.
     */
    private static final Pattern ALLOCATED_ARRAY_REFERENCE =
            Pattern.compile("^A(?:[ZBCSIJFDL]|\\[)_([1-9][0-9]*)-([0-9]+)$");
    /** Runtime-evidence identity assigned to one propagated map state. */
    private static final Pattern CANONICAL_MAP_STATE_REFERENCE =
            Pattern.compile("^MAP_STATE\\.v1\\.[0-9a-f]{64}$");

    /** One exact VM value root: the symbol the VM minted for one site. */
    private static final String SYMBOL_TYPE = "SymbolExpression";
    /** A VM read that named the write it read from. */
    private static final String READ_FROM_TYPE = "ReadFromExpression";

    private VmExpressionIr() {
    }

    /**
     * True when the expression tree already carries symbolic value or exact
     * consumer provenance.  A consumer boundary around a constant counts:
     * its producer case and path condition still decide when that constant
     * reaches the reader.  A structural constant fold with neither a root
     * nor a boundary does not, and may be minted afresh.
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
                || READ_FROM_TYPE.equals(type)) {
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
     * True only when the tree names at least one VM symbol root.
     *
     * <p>The difference from {@link #carriesPropagatedValue} is the one a
     * declared source needs.  A field that is only ever written from
     * constants still reaches its reader wrapped in a {@code ReadFrom} or a
     * {@code ConsumerBoundary} once a shared-state carrier is installed, so
     * the looser predicate answers "already propagated" and the mint is
     * skipped -- which is why an experiment could declare a field symbolic
     * and still get no root for it.  This one looks through those wrappers
     * and asks whether anything symbolic is actually inside.  It is the same
     * rule the {@code CausynthSymbolicSource} hook path applies to its own
     * pre-carrier read.</p>
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
