package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.List;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The one reading of the custom VM's expression IR the Composer and the
 * path-flip Solver share: operator vocabulary, constant payloads, and the
 * literal shapes both encoders must agree on before either lowers a term.
 *
 * <p>Where the two encoders resolve a Java type differently the difference is
 * a parameter, never a second copy: {@code stringTyped} is the caller's own
 * Java-type-to-sort decision.</p>
 */
final class VmExpressionIr {

    private VmExpressionIr() {
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
        String javaType = string(object, "_java_type");
        return "I".equals(javaType) || "int".equals(javaType);
    }

    static Integer exactIntLiteral(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if (!("ConstExpr".equals(type) || "ConSymbolExp".equals(type))) {
            return null;
        }
        String javaType = string(object, "_java_type");
        if (!("I".equals(javaType) || "int".equals(javaType))) {
            return null;
        }
        String value = constantPayload(string(object, "_exp"));
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
        String type = string(object, "_type");
        if (!("ConStringSymbolExp".equals(type)
                || "ConstExpr".equals(type)
                || "ConSymbolExp".equals(type))) return null;
        if (!stringTyped.test(string(object, "_java_type"))) {
            return null;
        }
        return constantPayload(string(object, "_exp"));
    }

    static boolean provablyStringValued(JsonElement expression,
                                        Predicate<String> stringTyped) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("ConStringSymbolExp".equals(type)) return true;
        if ("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type)
                || "ConstExpr".equals(type)) {
            return stringTyped.test(string(object, "_java_type"));
        }
        if (!"OpStrExpression".equals(type)
                || bool(object, "_is_not", false)) return false;
        String operation = string(object, "_name");
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
        if (!"OpStrExpression".equals(string(object, "_type"))
                || !"concat".equals(string(object, "_name"))
                || bool(object, "_is_not", false)) {
            return false;
        }
        JsonArray params = array(object, "_param_list");
        if (params.size() == 0) return false;
        for (JsonElement parameter : params) {
            if (parameter != null && parameter.isJsonObject()
                    && "OpStrExpression".equals(string(
                    parameter.getAsJsonObject(), "_type"))
                    && "concat".equals(string(
                    parameter.getAsJsonObject(), "_name"))) {
                if (!flattenConcat(parameter, result)) return false;
            } else {
                result.add(parameter);
            }
        }
        return true;
    }
}
