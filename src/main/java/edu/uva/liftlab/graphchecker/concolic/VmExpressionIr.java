package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.List;
import java.util.function.Predicate;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

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
    static final String CONSUMER_BOUNDARY_TYPE =
            "ConsumerBoundaryExpression";
    /** Persisted reference to one replay-independent boundary family. */
    static final String CONSUMER_BOUNDARY_REFERENCE_TYPE =
            "ConsumerBoundaryReference";
    static final String RPC_ATTACH = "RPC_ATTACH";
    static final String FIELD_READ = "FIELD_READ";
    static final String BOUNDARY_KIND = "boundaryKind";
    static final String EVENT_ID = "eventId";
    static final String FAMILY_KEY = "familyKey";
    static final String TOPOLOGY_EPOCH = "topologyEpoch";
    static final String EXPRESSION = "expression";

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
                && !SharedStateEvidence.containsVmSerializationTruncation(
                root) ? root : null;
    }

    static boolean isConsumerBoundary(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && CONSUMER_BOUNDARY_TYPE.equals(optionalString(
                expression.getAsJsonObject(), "_type"));
    }

    static boolean isConsumerBoundaryReference(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && CONSUMER_BOUNDARY_REFERENCE_TYPE.equals(optionalString(
                expression.getAsJsonObject(), "_type"));
    }

    /**
     * Validates the raw, session-local wrapper emitted by the VM.  The
     * replay-independent family key is deliberately not required here: only
     * the Java evidence join is allowed to add it.
     */
    static String consumerBoundaryFault(JsonElement expression,
                                        String expectedKind,
                                        long expectedEventId) {
        if (!isConsumerBoundary(expression)) {
            return "expression is not a ConsumerBoundaryExpression";
        }
        JsonObject row = expression.getAsJsonObject();
        String kind = optionalString(row, BOUNDARY_KIND);
        if (!(RPC_ATTACH.equals(kind) || FIELD_READ.equals(kind))) {
            return "consumer boundary has an unsupported kind";
        }
        if (expectedKind != null && !expectedKind.isEmpty()
                && !expectedKind.equals(kind)) {
            return "consumer boundary kind disagrees with its evidence";
        }
        long eventId = longValue(row, EVENT_ID);
        if (eventId <= 0L) {
            return "consumer boundary names no dynamic event";
        }
        if (expectedEventId > 0L && eventId != expectedEventId) {
            return "consumer boundary event disagrees with its evidence";
        }
        if (optionalString(row, "_java_type").isEmpty()) {
            return "consumer boundary names no Java type";
        }
        JsonElement payload = row.get(EXPRESSION);
        if (payload == null || payload.isJsonNull()
                || !payload.isJsonObject()) {
            return "consumer boundary carries no expression payload";
        }
        if (SharedStateEvidence.containsVmSerializationTruncation(payload)) {
            return "consumer boundary payload was truncated";
        }
        return "";
    }

    static JsonObject boundaryReference(JsonObject boundary,
                                        String familyKey) {
        JsonObject reference = JsonFields.shallowCopy(boundary);
        reference.addProperty("_type", CONSUMER_BOUNDARY_REFERENCE_TYPE);
        reference.addProperty(FAMILY_KEY, familyKey == null ? "" : familyKey);
        return reference;
    }

    private static long longValue(JsonObject row, String field) {
        JsonElement value = row == null ? null : row.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) return -1L;
        try {
            return value.getAsLong();
        } catch (RuntimeException ignored) {
            return -1L;
        }
    }

    static boolean isAllocatedInstanceReference(String raw) {
        return raw != null
                && ALLOCATED_INSTANCE_REFERENCE.matcher(raw).matches();
    }

    static boolean isAllocatedArrayReference(String raw) {
        return raw != null
                && ALLOCATED_ARRAY_REFERENCE.matcher(raw).matches();
    }

    /**
     * Exact serialization of {@code PlaceHolderSymbolExp} for a reference:
     * an oop the VM observed as an operand without a shadow to name it, so
     * it carries the class and no identity.  It names no root and no object.
     */
    private static final Pattern UNTRACKED_REFERENCE_PLACEHOLDER =
            Pattern.compile("^P_L'[^']+'_$");

    /** Whether the VM left this reference operand unnamed (no shadow). */
    static boolean isUntrackedReferencePlaceholder(String raw) {
        return raw != null
                && UNTRACKED_REFERENCE_PLACEHOLDER.matcher(raw).matches();
    }

    /** Whether runtime carrier evidence gave this state a replay-stable id. */
    static boolean isCanonicalMapStateReference(String raw) {
        return raw != null
                && CANONICAL_MAP_STATE_REFERENCE.matcher(raw).matches();
    }

    /**
     * A VM-local identity created only after a concrete oop already exists.
     * It is an existential witness for the recorded execution, never a
     * writable symbolic input.
     */
    static boolean isExecutionLocalStructuralWitness(String raw) {
        return isAllocatedInstanceReference(raw)
                || isAllocatedArrayReference(raw)
                || isCanonicalMapStateReference(raw);
    }



    static boolean isJavaParseInt(String name) {
        return "java/lang/Integer parseInt".equals(firstNonBlank(name));
    }

    static boolean isJavaSplitElement(String name) {
        return "java/lang/String splitElement".equals(firstNonBlank(name));
    }

    static String comparison(String operator) {
        if ("<".equals(operator) || ">".equals(operator)
                || "<=".equals(operator) || ">=".equals(operator)) {
            return operator;
        }
        return "";
    }

    static String arithmetic(String operator) {
        if ("+".equals(operator) || "-".equals(operator)
                || "*".equals(operator)) return operator;
        return "";
    }

    static boolean arithmeticOperator(String operator) {
        return "+".equals(operator) || "-".equals(operator)
                || "*".equals(operator) || "@".equals(operator)
                || "/".equals(operator) || "%".equals(operator);
    }

    static boolean bitwiseOperator(String operator) {
        return "&".equals(operator) || "|".equals(operator)
                || "^".equals(operator);
    }

    static boolean shiftOperator(String operator) {
        return "<<".equals(operator) || ">>".equals(operator)
                || ">>>".equals(operator);
    }

    static String quote(String value) {
        String exact = value == null ? "" : value;
        return "\"" + exact.replace("\"", "\"\"") + "\"";
    }

    static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    static boolean isPrimitiveIntExpression(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String javaType = optionalString(object, "_java_type");
        return "I".equals(javaType) || "int".equals(javaType);
    }

    static Integer exactIntLiteral(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        if (!("ConstExpr".equals(type) || "ConSymbolExp".equals(type))) {
            return null;
        }
        String javaType = optionalString(object, "_java_type");
        if (!("I".equals(javaType) || "int".equals(javaType))) {
            return null;
        }
        String value = constantPayload(optionalString(object, "_exp"));
        if (!value.matches("-?[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    static String exactStringLiteral(JsonElement expression,
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

    static boolean provablyStringValued(JsonElement expression,
                                        Predicate<String> stringTyped) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        if ("ConStringSymbolExp".equals(type)) return true;
        if ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type)
                || "ConstExpr".equals(type)) {
            return stringTyped.test(optionalString(object, "_java_type"));
        }
        if (!"OpStrExpression".equals(type)
                || optionalBool(object, "_is_not", false)) return false;
        String operation = optionalString(object, "_name");
        if ("toString".equals(operation)) {
            JsonArray params = array(object, "_param_list");
            return params.size() == 1
                    && isPrimitiveIntExpression(params.get(0));
        }
        if (!"concat".equals(operation)) return false;
        JsonArray params = array(object, "_param_list");
        if (params.size() == 0) return false;
        for (JsonElement parameter : params) {
            if (!provablyStringValued(parameter, stringTyped)) return false;
        }
        return true;
    }

    static boolean flattenConcat(JsonElement expression,
                                 List<JsonElement> result) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        JsonObject object = expression.getAsJsonObject();
        if (!"OpStrExpression".equals(optionalString(object, "_type"))
                || !"concat".equals(optionalString(object, "_name"))
                || optionalBool(object, "_is_not", false)) {
            return false;
        }
        JsonArray params = array(object, "_param_list");
        if (params.size() == 0) return false;
        for (JsonElement parameter : params) {
            if (parameter != null && parameter.isJsonObject()
                    && "OpStrExpression".equals(optionalString(
                    parameter.getAsJsonObject(), "_type"))
                    && "concat".equals(optionalString(
                    parameter.getAsJsonObject(), "_name"))) {
                if (!flattenConcat(parameter, result)) return false;
            } else {
                result.add(parameter);
            }
        }
        return true;
    }
}
