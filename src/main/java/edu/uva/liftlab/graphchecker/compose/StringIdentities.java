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

/**
 * WIRE-CODEC §6.2: the exact identities of Java's decimal and boolean String
 * renderings, read on the VM's expression IR before any SMT text is written,
 * so a value that crossed as text is compared, parsed and split as the number
 * or flag it renders, without the String theory.  Each answers what the
 * lowering ({@link SmtLowering}) lowers in a node's place, or null where the
 * identity does not hold; then the node lowers as it always did.
 *
 * <p>A RENDERING is the VM's {@code toString} (or {@code valueOf}) of one
 * primitive: {@code Byte/Short/Integer/Long.toString} and
 * {@code String.valueOf} of an integral are its canonical decimal (a DEC
 * piece), of a boolean {@code "true"}/{@code "false"} (a BOOL piece).  A
 * TEMPLATE is a String node seen as its pieces: {@code concat} flattened
 * (through consumer boundaries, which the lowering sees through too), a split
 * element as the pieces of its segment, String constants as literal text,
 * renderings of a primitive the node's type states as DEC or BOOL, anything
 * else an opaque STR piece.  A read is never looked through: its value is the
 * write a family pairs it with.</p>
 */
final class StringIdentities {
    private StringIdentities() {
    }

    /** What one piece of a template is. */
    enum Kind {
        LITERAL, DEC, BOOL, STR
    }

    /** One piece of a template. */
    static final class Part {
        final Kind kind;
        /** LITERAL: the text. */
        final String literal;
        /** DEC, BOOL: the rendering; STR: the String node. */
        final JsonElement node;
        /** DEC, BOOL: the value rendered. */
        final JsonElement operand;
        /** DEC, BOOL: the JVM descriptor of the value rendered. */
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

    /**
     * The most pieces one template is read to: a {@code concat} DAG that
     * shares a subterm is a tree of 2^depth pieces, so past this bound no
     * identity is tried and the node lowers as it did.
     */
    private static final int MAX_PARTS = 256;

    private static final String CONCAT = "concat";
    private static final String TO_STRING = "toString";
    private static final String VALUE_OF = "valueOf";

    /**
     * {@code String.valueOf} of one primitive is its {@code toString}, and a
     * primitive operand of {@code concat} is appended as its
     * {@code toString} ({@code StringBuilder.append(p)}): the node rewritten
     * so, or null when it is neither.
     */
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

    /**
     * {@code Integer.parseInt}/{@code Long.parseLong} (radix 10) of a lone
     * decimal rendering {@code toString(e)} is {@code e}: the operand
     * {@code e}, or null.  {@code parseInt} of a long's rendering is no
     * identity (it throws outside the int range).
     */
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

    /** What a comparison of a boolean's rendering with a literal is. */
    enum Truth {
        /** The flag itself. */
        FLAG,
        /** The flag negated. */
        NEGATED,
        /** Never: the literal renders neither value. */
        NEVER
    }

    /**
     * {@code equals} (or {@code equalsIgnoreCase}) of a lone boolean
     * rendering and a String literal, either way round: the flag, its
     * negation, or never ({@code Boolean.parseBoolean(s)} is
     * {@code "true".equalsIgnoreCase(s)}).  Null when the operands are not
     * that pair.
     */
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
            // Java's own comparison: equalsIgnoreCase folds more than ASCII.
            boolean isTrue = ignoreCase ? literal.equalsIgnoreCase("true")
                    : literal.equals("true");
            boolean isFalse = ignoreCase ? literal.equalsIgnoreCase("false")
                    : literal.equals("false");
            return new BooleanTest(parts.get(0).operand, isTrue ? Truth.FLAG
                    : isFalse ? Truth.NEGATED : Truth.NEVER);
        }
        return null;
    }

    /** A boolean rendering compared with a literal: which flag, and how. */
    static final class BooleanTest {
        final JsonElement flag;
        final Truth truth;

        private BooleanTest(JsonElement flag, Truth truth) {
            this.flag = flag;
            this.truth = truth;
        }
    }

    /**
     * {@code equals} of two templates with one skeleton (the same literals
     * and kinds of piece, in order) is piece-wise equality, when each
     * string has one reading into those pieces: a DEC piece is followed by
     * the end or by a piece that cannot start with a digit (its text is
     * {@code -?[0-9]+}), a BOOL piece is {@code true} or {@code false} by
     * its first character, and a STR piece is followed by literals alone.
     * Decimal and boolean renderings are injective, so the strings are
     * equal exactly when each DEC pair, BOOL pair and STR pair is.  The
     * pairs, in order, or null (also when no rendering is among them: then
     * there is nothing to gain over the String equality).
     */
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

    /** Whether the piece at {@code index} has one extent in any string. */
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

    /**
     * Element {@code i} of {@code s.split(d)} (the VM's
     * {@code splitElement(s, d, i)}) where {@code s} is a template whose
     * pieces up to that element's end are literals and renderings free of
     * {@code d}: that element's pieces, as a node.  {@code d} must be
     * split literally (Java's one-character fast path); the element must be
     * non-empty (an empty one exists only if a later one does not end
     * empty).  Null otherwise.
     */
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

    /**
     * The template one String node is, or null past {@link #MAX_PARTS};
     * adjacent literals merged, empty ones dropped.
     */
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

    /** One non-literal, non-concat piece of a template. */
    private static Part piece(JsonElement node) {
        JsonElement operand = null;
        JsonElement rendering = node;
        JsonArray rendered = stringOperationParams(node, TO_STRING);
        if (rendered == null) rendered = stringOperationParams(node, VALUE_OF);
        if (rendered != null && rendered.size() == 1) {
            operand = rendered.get(0);
        } else if (primitive(node)) {
            // concat(..., p, ...) appends p's rendering.
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

    /** The pieces of one split element, as one node, or null if empty. */
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

    /** Whether a rendering never contains the delimiter. */
    private static boolean free(Part part, char delimiter) {
        if (part.kind == Kind.DEC) return "-0123456789".indexOf(delimiter) < 0;
        return part.kind == Kind.BOOL && "truefals".indexOf(delimiter) < 0;
    }

    /**
     * The one character {@code String.split(regex)} splits at literally
     * (JDK 8's fast path): one character no regex operator, or a
     * backslash and one character neither a letter nor a digit; never a
     * surrogate.  Null for any other regex.
     */
    private static Character literalDelimiter(String regex) {
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

    /**
     * Whether a node is one Java primitive value: a stated primitive type,
     * or an operator (a binary or a negation), whose value is always a
     * promoted primitive.
     */
    private static boolean primitive(JsonElement node) {
        String type = VmExpressionIr.typeOf(node);
        return !statedPrimitive(node).isEmpty()
                || "BinaryExpression".equals(type)
                || "NotExpression".equals(type);
    }

    /**
     * The primitive descriptor a node's type states ({@code Z B C S I J F
     * D}; a negation is {@code Z}), else "".
     */
    private static String statedPrimitive(JsonElement node) {
        if ("NotExpression".equals(VmExpressionIr.typeOf(node))) return "Z";
        String type = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                VmTermLowering.expressionJavaType(node));
        return JavaPrimitiveSmtSemantics.primitive(type) ? type : "";
    }

    /** The VM's {@code toString} of one primitive. */
    private static JsonObject rendering(JsonElement primitive) {
        JsonArray params = new JsonArray();
        params.add(primitive);
        return VmExpressionIr.stringOperation(TO_STRING, params);
    }

    /** Whether a node is the VM's {@code splitElement} of a split. */
    private static boolean splitElementCall(JsonElement node) {
        return "MethodExpression".equals(VmExpressionIr.typeOf(node))
                && VmExpressionIr.isJavaSplitElement(optionalString(
                node.getAsJsonObject(), "_name"));
    }

    /** The parameters of an un-negated String operation of this name. */
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

    /** The String this node is exactly a constant of, or null. */
    private static String stringLiteral(JsonElement node) {
        return VmExpressionIr.exactStringLiteral(node,
                type -> JavaSmtSorts.sortOfJava(type) == Sort.STRING);
    }

    /** The int this node is exactly a constant of, or null. */
    private static Integer intLiteral(JsonElement node) {
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
