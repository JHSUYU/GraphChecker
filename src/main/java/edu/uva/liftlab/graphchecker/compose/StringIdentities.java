package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class StringIdentities {
    private StringIdentities() {
    }

    public static JsonElement renderedValue(JsonElement string,
                                            boolean bool) {
        List<Part> parts = template(string);
        if (parts == null || parts.size() != 1) return null;
        Part part = parts.get(0);
        return part.kind == (bool ? Kind.BOOL : Kind.DEC) ? part.operand
                : null;
    }

    enum Kind {
        LITERAL, DEC, BOOL, STR
    }

    static final class Part {
        final Kind kind;
        final String literal;
        final JsonElement node;
        final JsonElement operand;
        final String javaType;

        private Part(Kind kind, String literal, JsonElement node,
                     JsonElement operand, String javaType) {
            this.kind = kind;
            this.literal = literal;
            this.node = node;
            this.operand = operand;
            this.javaType = javaType;
        }

        private static Part literal(String text) {
            return new Part(Kind.LITERAL, text, null, null, "");
        }
    }

    private static final int MAX_PARTS = 256;

    private static final String CONCAT = "concat";
    private static final String TO_STRING = "toString";
    private static final String VALUE_OF = "valueOf";

    static JsonObject asRenderings(JsonObject stringOperation) {
        String name = optionalString(stringOperation, "_name");
        JsonArray params = array(stringOperation, "_param_list");
        if (VALUE_OF.equals(name) && params.size() == 1
                && primitive(params.get(0))) {
            return VmExpressionIr.stringOperation(TO_STRING, params);
        }
        if (!CONCAT.equals(name)) return null;
        JsonArray rendered = new JsonArray();
        boolean changed = false;
        for (JsonElement param : params) {
            if (primitive(param)) {
                rendered.add(rendering(param));
                changed = true;
            } else {
                rendered.add(param);
            }
        }
        return changed ? VmExpressionIr.stringOperation(CONCAT, rendered)
                : null;
    }

    static JsonElement parsedOperand(boolean parseInt, JsonElement argument) {
        List<Part> parts = template(argument);
        if (parts == null || parts.size() != 1
                || parts.get(0).kind != Kind.DEC) {
            return null;
        }
        Part rendering = parts.get(0);
        return parseInt && "J".equals(rendering.javaType) ? null
                : rendering.operand;
    }

    enum Truth {
        FLAG,
        NEGATED,
        NEVER
    }

    static BooleanTest booleanTest(JsonArray params, boolean ignoreCase) {
        if (params.size() != 2) return null;
        for (int flag = 0; flag < 2; flag++) {
            String literal = stringLiteral(params.get(1 - flag));
            List<Part> parts = literal == null ? null
                    : template(params.get(flag));
            if (parts == null || parts.size() != 1
                    || parts.get(0).kind != Kind.BOOL) {
                continue;
            }
            boolean isTrue = ignoreCase ? literal.equalsIgnoreCase("true")
                    : literal.equals("true");
            boolean isFalse = ignoreCase ? literal.equalsIgnoreCase("false")
                    : literal.equals("false");
            return new BooleanTest(parts.get(0).operand, isTrue ? Truth.FLAG
                    : isFalse ? Truth.NEGATED : Truth.NEVER);
        }
        return null;
    }

    static final class BooleanTest {
        final JsonElement flag;
        final Truth truth;

        private BooleanTest(JsonElement flag, Truth truth) {
            this.flag = flag;
            this.truth = truth;
        }
    }

    static List<Part[]> pieceWise(JsonElement left, JsonElement right) {
        List<Part> one = template(left);
        List<Part> other = template(right);
        if (one == null || other == null || one.size() != other.size()) {
            return null;
        }
        List<Part[]> pairs = new ArrayList<Part[]>();
        boolean rendering = false;
        for (int index = 0; index < one.size(); index++) {
            Part a = one.get(index);
            Part b = other.get(index);
            if (a.kind != b.kind) return null;
            if (a.kind == Kind.LITERAL) {
                if (!a.literal.equals(b.literal)) return null;
                continue;
            }
            if (!oneReading(one, index)) return null;
            rendering |= a.kind != Kind.STR;
            pairs.add(new Part[]{a, b});
        }
        return rendering ? pairs : null;
    }

    private static boolean oneReading(List<Part> parts, int index) {
        Kind kind = parts.get(index).kind;
        if (kind == Kind.BOOL) return true;
        if (kind == Kind.DEC) {
            if (index + 1 == parts.size()) return true;
            Part next = parts.get(index + 1);
            return next.kind == Kind.BOOL || next.kind == Kind.LITERAL
                    && !Character.isDigit(next.literal.charAt(0));
        }
        for (int after = index + 1; after < parts.size(); after++) {
            if (parts.get(after).kind != Kind.LITERAL) return false;
        }
        return true;
    }

    static JsonElement splitElement(JsonObject call) {
        JsonArray params = array(call, "_param_list");
        if (params.size() != 3) return null;
        String regex = stringLiteral(params.get(1));
        Character delimiter = regex == null ? null : literalDelimiter(regex);
        Integer wanted = intLiteral(params.get(2));
        List<Part> parts = delimiter == null || wanted == null ? null
                : template(params.get(0));
        if (parts == null) return null;
        char d = delimiter;
        List<Part> element = new ArrayList<Part>();
        int passed = 0;
        for (Part part : parts) {
            if (part.kind == Kind.LITERAL) {
                String text = part.literal;
                int from = 0;
                while (true) {
                    int at = text.indexOf(d, from);
                    if (passed == wanted) {
                        String piece = text.substring(from,
                                at < 0 ? text.length() : at);
                        if (!piece.isEmpty()) element.add(Part.literal(piece));
                    }
                    if (at < 0) break;
                    if (++passed > wanted) return pieces(element);
                    from = at + 1;
                }
            } else if (!free(part, d)) {
                return null;
            } else if (passed == wanted) {
                element.add(part);
            }
        }
        return passed == wanted ? pieces(element) : null;
    }

    static List<Part> template(JsonElement string) {
        List<Part> parts = new ArrayList<Part>();
        StringBuilder literal = new StringBuilder();
        Deque<JsonElement> pending = new ArrayDeque<JsonElement>();
        pending.push(string);
        int visited = 0;
        while (!pending.isEmpty()) {
            if (++visited > MAX_PARTS) return null;
            JsonElement node = pending.pop();
            while (VmExpressionIr.consumerBoundary(node)) {
                node = node.getAsJsonObject().get(VmExpressionIr.EXPRESSION);
            }
            String text = stringLiteral(node);
            if (text != null) {
                literal.append(text);
                continue;
            }
            JsonArray params = stringOperationParams(node, CONCAT);
            if (params != null) {
                for (int index = params.size() - 1; index >= 0; index--) {
                    pending.push(params.get(index));
                }
                continue;
            }
            JsonElement element = splitElementCall(node) ? splitElement(
                    node.getAsJsonObject()) : null;
            if (element != null) {
                pending.push(element);
                continue;
            }
            if (literal.length() > 0) {
                parts.add(Part.literal(literal.toString()));
                literal.setLength(0);
            }
            parts.add(piece(node));
        }
        if (literal.length() > 0) parts.add(Part.literal(literal.toString()));
        return parts;
    }

    private static Part piece(JsonElement node) {
        JsonElement operand = null;
        JsonElement rendering = node;
        JsonArray rendered = stringOperationParams(node, TO_STRING);
        if (rendered == null) rendered = stringOperationParams(node, VALUE_OF);
        if (rendered != null && rendered.size() == 1) {
            operand = rendered.get(0);
        } else if (primitive(node)) {
            operand = node;
            rendering = rendering(node);
        }
        String type = operand == null ? "" : statedPrimitive(operand);
        Kind kind = "Z".equals(type) ? Kind.BOOL
                : type.length() == 1 && "BSIJ".contains(type) ? Kind.DEC
                : Kind.STR;
        return kind == Kind.STR ? new Part(Kind.STR, null, rendering, null, "")
                : new Part(kind, null, rendering, operand, type);
    }

    private static JsonElement pieces(List<Part> element) {
        if (element.isEmpty()) return null;
        JsonArray nodes = new JsonArray();
        for (Part part : element) {
            nodes.add(part.kind == Kind.LITERAL
                    ? VmExpressionIr.stringConstant(part.literal) : part.node);
        }
        return nodes.size() == 1 ? nodes.get(0)
                : VmExpressionIr.stringOperation(CONCAT, nodes);
    }

    private static boolean free(Part part, char delimiter) {
        if (part.kind == Kind.DEC) return "-0123456789".indexOf(delimiter) < 0;
        return part.kind == Kind.BOOL && "truefals".indexOf(delimiter) < 0;
    }

    static Character literalDelimiter(String regex) {
        char c;
        if (regex.length() == 1 && ".$|()[{^?*+\\".indexOf(regex.charAt(0))
                < 0) {
            c = regex.charAt(0);
        } else if (regex.length() == 2 && regex.charAt(0) == '\\'
                && !isAsciiLetterOrDigit(regex.charAt(1))) {
            c = regex.charAt(1);
        } else {
            return null;
        }
        return Character.isSurrogate(c) ? null : c;
    }

    private static boolean isAsciiLetterOrDigit(char c) {
        return c >= '0' && c <= '9' || c >= 'a' && c <= 'z'
                || c >= 'A' && c <= 'Z';
    }

    private static boolean primitive(JsonElement node) {
        return !statedPrimitive(node).isEmpty()
                || "BinaryExpression".equals(VmExpressionIr.typeOf(node));
    }

    private static String statedPrimitive(JsonElement node) {
        String type = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                VmTermLowering.expressionJavaType(node));
        return JavaPrimitiveSmtSemantics.primitive(type) ? type : "";
    }

    private static JsonObject rendering(JsonElement primitive) {
        JsonArray params = new JsonArray();
        params.add(primitive);
        return VmExpressionIr.stringOperation(TO_STRING, params);
    }

    private static boolean splitElementCall(JsonElement node) {
        return "MethodExpression".equals(VmExpressionIr.typeOf(node))
                && VmExpressionIr.isJavaSplitElement(optionalString(
                node.getAsJsonObject(), "_name"));
    }

    private static JsonArray stringOperationParams(JsonElement node,
                                                   String name) {
        if (!VmExpressionIr.STRING_OPERATION_TYPE.equals(
                VmExpressionIr.typeOf(node))) {
            return null;
        }
        JsonObject operation = node.getAsJsonObject();
        JsonElement negated = operation.get("_is_not");
        if (!name.equals(optionalString(operation, "_name"))
                || negated != null && negated.isJsonPrimitive()
                && negated.getAsBoolean()) {
            return null;
        }
        return array(operation, "_param_list");
    }

    static String stringLiteral(JsonElement node) {
        return VmExpressionIr.exactStringLiteral(node,
                type -> JavaSmtSorts.sortOfJava(type) == Sort.STRING);
    }

    static Integer intLiteral(JsonElement node) {
        String value = VmExpressionIr.exactStringLiteral(node,
                type -> "I".equals(JavaPrimitiveSmtSemantics
                        .javaTypeDescriptor(type)));
        try {
            return value == null ? null : Integer.valueOf(value);
        } catch (NumberFormatException notAnInt) {
            return null;
        }
    }
}
