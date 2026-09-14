package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.ExpressionTable;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * PLACEHOLDER (branch refactor/d3-explore only) for the composer's lowering.
 *
 * <p>The one lowering of a recorded VM expression into SMT-LIB is
 * {@code d3.compose.SmtLowering}, written on branch refactor/d3-compose and
 * used by the composer AND by this package's flip solver.  Until that branch
 * lands, this thin stand-in lowers the subset of the {@code EXPR.v1} IR the
 * explore tests need, with exactly the surface the flip solver calls:
 * {@link #of(ExpressionTable)} and {@link #lower(String)}.  It is deleted by
 * the merge; nothing here is a second lowering to keep.</p>
 */
public final class SmtLowering {
    private final ExpressionTable expressions;

    private SmtLowering(ExpressionTable expressions) {
        this.expressions = expressions == null
                ? ExpressionTable.empty() : expressions;
    }

    public static SmtLowering of(ExpressionTable expressions) {
        return new SmtLowering(expressions);
    }

    /** One expression of this session, lowered, or a named refusal. */
    public Lowered lower(String expressionRef) {
        JsonObject expression = expressionRef == null ? null
                : expressions.expression(expressionRef);
        if (expression == null) {
            return Lowered.refused("ABSENT_EXPRESSION:" + expressionRef);
        }
        Lowered lowered = new Lowered();
        lowered.text = term(expression, lowered);
        return lowered;
    }

    private String term(JsonElement expression, Lowered into) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            into.refusal = "ABSENT_EXPRESSION";
            return "";
        }
        JsonObject node = expression.getAsJsonObject();
        String type = string(node, "_type");
        String raw = string(node, "_exp");
        String javaType = string(node, "_java_type");
        if ("SymbolExpression".equals(type)) {
            into.declarations.put(raw, sortOf(javaType));
            return raw;
        }
        if ("ConstExpr".equals(type) || "ConSymbolExp".equals(type)) {
            String payload = payload(raw);
            if ("Z".equals(javaType) || "boolean".equals(javaType)) {
                return "0".equals(payload) || "false".equals(payload)
                        ? "false" : "true";
            }
            return payload.startsWith("-")
                    ? "(- " + payload.substring(1) + ")" : payload;
        }
        if ("NotExpression".equals(type)) {
            return "(not " + term(node.get("_operand"), into) + ")";
        }
        if ("BinaryExpression".equals(type)) {
            String operator = operator(string(node, "_op"));
            if (operator.isEmpty()) {
                into.refusal = "UNSUPPORTED_OPERATOR:" + string(node, "_op");
                return "";
            }
            return "(" + operator + " " + term(node.get("_left"), into) + " "
                    + term(node.get("_right"), into) + ")";
        }
        into.refusal = "UNKNOWN_EXPRESSION_TYPE:"
                + (type.isEmpty() ? "MISSING_TYPE" : type);
        return "";
    }

    private static String operator(String vm) {
        if ("==".equals(vm)) return "=";
        if ("!=".equals(vm)) return "distinct";
        if ("<".equals(vm) || "<=".equals(vm) || ">".equals(vm)
                || ">=".equals(vm) || "+".equals(vm) || "-".equals(vm)
                || "*".equals(vm)) {
            return vm;
        }
        return "";
    }

    /** The sort one Java type descriptor lowers to. */
    public static String sortOf(String javaType) {
        return "Z".equals(javaType) || "boolean".equals(javaType)
                ? "Bool" : "Int";
    }

    private static String payload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
    }

    private static String string(JsonObject node, String member) {
        JsonElement value = node.get(member);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }

    /** One lowered expression: its text, its free symbols, or a refusal. */
    public static final class Lowered {
        private String text = "";
        private String refusal = "";
        private final Map<String, String> declarations =
                new LinkedHashMap<String, String>();

        private static Lowered refused(String reason) {
            Lowered lowered = new Lowered();
            lowered.refusal = reason;
            return lowered;
        }

        public boolean ok() {
            return refusal.isEmpty() && !text.isEmpty();
        }

        public String text() {
            return text;
        }

        public String refusal() {
            return refusal;
        }

        /** Every free symbol the text names, with its sort. */
        public Map<String, String> declarations() {
            return declarations;
        }
    }
}
