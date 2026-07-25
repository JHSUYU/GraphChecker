package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Path-local input closure for exact VM-guarded constant outputs. */
final class PathRelationInputClosure {
    private static final String FIELD_CONSTANT_AUTHORITY =
            "EXACT_FIELD_ASSIGNMENT_RHS_WITH_VM_ATTESTED_PATH_GUARD";

    private PathRelationInputClosure() {
    }

    static boolean guardedConstantUnusedInput(
            JsonObject activation, String inputPort,
            JsonArray pathCondition, JsonObject outputExpressions,
            boolean outputComplete, String outputAuthority,
            boolean sliceOperationallyAdmitted) {
        if (!outputComplete || !sliceOperationallyAdmitted
                || !FIELD_CONSTANT_AUTHORITY.equals(outputAuthority)
                || pathCondition == null || pathCondition.size() == 0
                || outputExpressions == null
                || outputExpressions.size() == 0) {
            return false;
        }
        for (Map.Entry<String, JsonElement> entry
                : outputExpressions.entrySet()) {
            if (!isTypedConstant(entry.getValue())) return false;
        }

        Set<String> relationSymbols = freeSymbols(pathCondition);
        relationSymbols.addAll(freeSymbols(outputExpressions));
        for (String symbol : relationSymbols) {
            if (containsPortReference(symbol, inputPort)) return false;
        }

        JsonObject uniqueAction = null;
        for (JsonElement element : runtimeActions(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!inputPort.equals(string(action, "symbol"))) continue;
            if (uniqueAction != null) return false;
            uniqueAction = action;
        }
        if (uniqueAction == null || !bool(uniqueAction, "lazy", false)) {
            return false;
        }
        return true;
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
        return InputActionCatalog.decode(activation).symbolic();
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

}
