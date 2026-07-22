package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/** Path-local input closure for exact VM-guarded constant outputs. */
final class PathRelationInputClosure {
    private static final String FIELD_CONSTANT_AUTHORITY =
            "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_PATH_GUARD";
    private static final String RETURN_CONSTANT_AUTHORITY =
            "EXACT_METHOD_RETURN_VALUE_WITH_VM_ATTESTED_PATH_GUARD";
    static final String PROOF_AUTHORITY =
            "EXACT_VM_WITNESS_GUARDED_CONSTANT_OUTPUT_PLUS_"
                    + "UNEXECUTED_LAZY_INPUT_V1";

    private PathRelationInputClosure() {
    }

    static JsonObject proveGuardedConstantUnusedInput(
            JsonObject activation, String inputPort,
            JsonArray pathCondition, JsonObject outputExpressions,
            boolean outputComplete, String outputAuthority,
            boolean sliceOperationallyAdmitted) {
        if (!outputComplete || !sliceOperationallyAdmitted
                || !(FIELD_CONSTANT_AUTHORITY.equals(outputAuthority)
                || RETURN_CONSTANT_AUTHORITY.equals(outputAuthority))
                || pathCondition == null || pathCondition.size() == 0
                || outputExpressions == null
                || outputExpressions.size() == 0) {
            return null;
        }
        for (Map.Entry<String, JsonElement> entry
                : outputExpressions.entrySet()) {
            if (!isTypedConstant(entry.getValue())) return null;
        }

        Set<String> relationSymbols = freeSymbols(pathCondition);
        relationSymbols.addAll(freeSymbols(outputExpressions));
        for (String symbol : relationSymbols) {
            if (containsPortReference(symbol, inputPort)) return null;
        }

        JsonObject uniqueAction = null;
        int actionCount = 0;
        for (JsonElement element : runtimeActions(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!inputPort.equals(string(action, "symbol"))) continue;
            actionCount++;
            uniqueAction = action;
        }
        if (actionCount != 1 || uniqueAction == null
                || !bool(uniqueAction, "lazy")) {
            return null;
        }

        JsonObject proof = new JsonObject();
        proof.addProperty("inputPort", inputPort);
        proof.addProperty("outputRelationAuthority", outputAuthority);
        proof.addProperty("pathConditionCount", pathCondition.size());
        proof.addProperty("materializationBindingMode",
                string(uniqueAction, "bindingMode"));
        proof.addProperty("authority", PROOF_AUTHORITY);
        return proof;
    }

    static Set<String> freeSymbols(JsonElement expression) {
        Set<String> result = new LinkedHashSet<>();
        collectFreeSymbols(expression, result);
        return result;
    }

    private static void collectFreeSymbols(JsonElement expression,
                                           Set<String> result) {
        if (expression == null || expression.isJsonNull()) return;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                collectFreeSymbols(element, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if (("SymbolExpression".equals(type)
                || "ConSymbolExp".equals(type))
                && !isVmNullLiteral(object)) {
            String symbol = string(object, "_exp");
            if (!symbol.isEmpty()) result.add(symbol);
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            if (!"_exp".equals(entry.getKey())
                    && !"_code_position".equals(entry.getKey())) {
                collectFreeSymbols(entry.getValue(), result);
            }
        }
    }

    private static boolean isVmNullLiteral(JsonObject expression) {
        return "SymbolExpression".equals(string(expression, "_type"))
                && "N".equals(string(expression, "_exp"));
    }

    private static boolean isTypedConstant(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && "ConstExpr".equals(string(expression.getAsJsonObject(),
                "_type"))
                && !string(expression.getAsJsonObject(), "_java_type")
                .isEmpty()
                && !string(expression.getAsJsonObject(), "_exp").isEmpty();
    }

    private static JsonArray runtimeActions(JsonObject activation) {
        JsonArray refined = array(activation, "materializations");
        return refined.size() > 0 ? refined : array(activation, "symbolize");
    }

    private static boolean containsPortReference(String expression,
                                                 String port) {
        int start = expression.indexOf(port);
        while (start >= 0) {
            int end = start + port.length();
            boolean leftBoundary = start == 0
                    || !Character.isLetterOrDigit(expression.charAt(
                    start - 1));
            boolean rightBoundary = end == expression.length()
                    || !Character.isLetterOrDigit(expression.charAt(end));
            if (leftBoundary && rightBoundary) return true;
            start = expression.indexOf(port, start + 1);
        }
        return false;
    }

    private static JsonArray array(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static String string(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value != null && value.isJsonPrimitive()
                ? value.getAsString() : "";
    }

    private static boolean bool(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        try {
            return value != null && value.isJsonPrimitive()
                    && value.getAsBoolean();
        } catch (RuntimeException malformed) {
            return false;
        }
    }
}
