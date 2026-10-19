package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.FloatingKind;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class VmTermLowering {
    private VmTermLowering() {
    }

    public static String received(AttachRow attach) {
        String answered = attach.answeredValue() == null ? ""
                : attach.answeredValue().trim();
        if (!answered.isEmpty()) return answered;
        String arrival = attach.arrival() == null ? "" : attach.arrival();
        return !arrival.isEmpty()
                && JavaSmtSorts.sortOfJava(attach.javaType()) == Sort.STRING
                ? new JsonPrimitive(arrival).toString() : arrival;
    }

    public static String smtLiteral(String value, Sort sort) {
        String text = value == null ? "" : value.trim();
        if (sort == Sort.BOOL) {
            return "true".equals(text) || "1".equals(text) ? "true"
                    : "false".equals(text) || "0".equals(text) ? "false" : "";
        }
        if (sort == Sort.INT) {
            return JavaPrimitiveSmtSemantics.integralLiteral(text);
        }
        if (sort == Sort.FLOAT32 || sort == Sort.FLOAT64) {
            String literal = JavaPrimitiveSmtSemantics.floatingLiteral(text,
                    floatingKind(sort));
            return literal == null ? "" : literal;
        }
        if (sort == Sort.STRING) {
            String content = ReadRow.stringContent(text);
            return content == null ? "" : VmExpressionIr.quote(content);
        }
        if (sort == Sort.REF) {
            return VmExpressionIr.SYMBOLIC_NULL.equals(text) ? "nullRef" : "";
        }
        return "";
    }

    public static String smtName(String value) {
        String normalized = (value == null || value.trim().isEmpty()
                ? "anonymous" : value).replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        return normalized;
    }

    public enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), VALUE("Value"),
        ARRAY_VALUE("IndexedState"), MAP("AssocState"),
        UNKNOWN("");

        public final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        public boolean containerState() {
            return this == ARRAY_VALUE || this == MAP;
        }

        public boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
        }
    }

    public static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort.floating();
    }

    public static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    public static ContainerSmtCodec.Sort unboxedCellSort(Sort sort) {
        return sort == Sort.BOOL ? ContainerSmtCodec.Sort.BOOL
                : sort == Sort.REF ? ContainerSmtCodec.Sort.REF
                : sort == Sort.FLOAT32 ? ContainerSmtCodec.Sort.FLOAT32
                : sort == Sort.FLOAT64 ? ContainerSmtCodec.Sort.FLOAT64
                : sort == Sort.STRING ? ContainerSmtCodec.Sort.STRING
                : ContainerSmtCodec.Sort.VALUE;
    }

    public static ContainerSmtCodec.Sort containerSortOf(Sort sort) {
        return sort == null || sort == Sort.UNKNOWN ? null
                : sort == Sort.BOOL ? ContainerSmtCodec.Sort.BOOL
                : sort == Sort.INT ? ContainerSmtCodec.Sort.INT
                : sort == Sort.FLOAT32 ? ContainerSmtCodec.Sort.FLOAT32
                : sort == Sort.FLOAT64 ? ContainerSmtCodec.Sort.FLOAT64
                : sort == Sort.STRING ? ContainerSmtCodec.Sort.STRING
                : sort == Sort.REF ? ContainerSmtCodec.Sort.REF
                : sort == Sort.VALUE ? ContainerSmtCodec.Sort.VALUE
                : sort == Sort.ARRAY_VALUE ? ContainerSmtCodec.Sort.INDEXED
                : ContainerSmtCodec.Sort.ASSOCIATIVE;
    }

    public static Sort sortOfContainer(ContainerSmtCodec.Sort sort) {
        return sort == null ? Sort.UNKNOWN
                : sort == ContainerSmtCodec.Sort.BOOL ? Sort.BOOL
                : sort == ContainerSmtCodec.Sort.INT ? Sort.INT
                : sort == ContainerSmtCodec.Sort.FLOAT32 ? Sort.FLOAT32
                : sort == ContainerSmtCodec.Sort.FLOAT64 ? Sort.FLOAT64
                : sort == ContainerSmtCodec.Sort.STRING ? Sort.STRING
                : sort == ContainerSmtCodec.Sort.REF ? Sort.REF
                : sort == ContainerSmtCodec.Sort.VALUE ? Sort.VALUE
                : sort == ContainerSmtCodec.Sort.INDEXED ? Sort.ARRAY_VALUE
                : Sort.MAP;
    }

    public enum Reason {
        UNSUPPORTED_JAVA_NUMERIC_PROMOTION(
                "UnsupportedJavaNumericPromotion", true),
        JAVA_CAST_SOURCE_SORT_CONFLICT("JavaCastSourceSortConflict", false),
        UNSUPPORTED_JAVA_CAST("MODEL_SEMANTICS_MISSING:TypeCastExpression",
                false),
        MODEL_SEMANTICS_MISSING("MODEL_SEMANTICS_MISSING", false),

        AMBIGUOUS_JAVA_INTEGRAL_UNARY_WIDTH(
                "AmbiguousJavaIntegralUnaryWidth", false),
        NON_NUMERIC_OR_UNKNOWN_UNARY("NonNumericOrUnknownUnary", false),
        MALFORMED_JVM_LCMP_OPERANDS("MalformedJvmLcmpOperands", false),
        MALFORMED_JVM_FLOATING_COMPARE_OPERANDS(
                "MalformedJvmFloatingCompareOperands", false),
        NON_BOOLEAN_LOGIC("NonBooleanLogic", false),
        BINARY_SORT_CONFLICT("BinarySortConflict", false),
        NON_NUMERIC_COMPARISON("NonNumericComparison", false),
        AMBIGUOUS_JAVA_INTEGRAL_BITWISE_WIDTH(
                "AmbiguousJavaIntegralBitwiseWidth", false),
        AMBIGUOUS_JAVA_INTEGRAL_SHIFT("AmbiguousJavaIntegralShift", false),
        NON_NUMERIC_ARITHMETIC("NonNumericArithmetic", false),
        JAVA_FLOATING_REMAINDER_UNMODELED(
                "JavaFloatingRemainderUnmodeled", false),
        JAVA_FLOATING_OPERATOR_UNMODELED(
                "JavaFloatingOperatorUnmodeled", false),
        AMBIGUOUS_JAVA_INTEGRAL_BINARY_WIDTH(
                "AmbiguousJavaIntegralBinaryWidth", false),
        BINARY_OPERATOR("BinaryOperator", false),

        INVALID_JAVA_BOOLEAN_LITERAL("InvalidJavaBooleanLiteral", false),
        INVALID_NUMERIC_LITERAL("InvalidNumericLiteral", false),
        UNSUPPORTED_CONSTANT_TYPE("UnsupportedConstantType", false),

        JAVA_STRING_NULLNESS_UNKNOWN("JavaStringNullnessUnknown", false),

        ABSENT_EXPRESSION("ABSENT_EXPRESSION", false),
        UNKNOWN_EXPRESSION_TYPE("", false);

        private final String composed;
        private final boolean composedNamesOrigin;

        Reason(String composed, boolean composedNamesOrigin) {
            this.composed = composed;
            this.composedNamesOrigin = composedNamesOrigin;
        }

        public String composedSubject(String origin, String detail) {
            return join(composed, composedNamesOrigin ? origin : "", detail);
        }
        private static String join(String... parts) {
            StringBuilder subject = new StringBuilder();
            for (String part : parts) {
                if (part == null || part.isEmpty()) continue;
                if (subject.length() > 0) subject.append(':');
                subject.append(part);
            }
            return subject.toString();
        }
    }

    public static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if ("MethodExpression".equals(optionalString(object, "_type"))) {
            return optionalString(JsonFields.object(object, "_res_exp"),
                    "_java_type");
        }
        return optionalString(object, "_java_type");
    }

    public static final String JAVA_INT_TO_STRING =
            "(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))";

    public static final String JAVA_ASCII_LOWER = asciiCase("java_ascii_lower",
            65, 90, "+");

    public static final String JAVA_ASCII_UPPER = asciiCase("java_ascii_upper",
            97, 122, "-");

    private static String asciiCase(String name, int from, int to,
                                    String shift) {
        String code = "(str.to_code (str.at s 0))";
        return "(define-fun-rec " + name + " ((s String)) String"
                + " (ite (= s \"\") \"\""
                + " (str.++ (ite (and (<= " + from + " " + code + ") (<= "
                + code + " " + to + ")) (str.from_code (" + shift + " "
                + code + " 32)) (str.at s 0))"
                + " (" + name + " (str.substr s 1 (- (str.len s) 1))))))";
    }

    public static final String JAVA_CHARS = "(set-option :encoding bmp)";

    public static List<String> preamble() {
        List<String> lines = new ArrayList<>();
        lines.add("(set-option :smt.arith.solver 2)");
        lines.add(JAVA_CHARS);
        lines.add("(declare-sort Ref 0)");
        lines.add(ContainerStateModel.valueDatatypeDeclaration());
        lines.add("(declare-const nullRef Ref)");
        lines.addAll(ContainerStateModel.preamble());
        return lines;
    }

    public static String and(List<String> terms) {
        return booleanNary(terms, true);
    }

    public static String or(List<String> terms) {
        return booleanNary(terms, false);
    }

    private static String booleanNary(List<String> terms,
                                      boolean conjunction) {
        List<String> filtered = new ArrayList<>();
        for (String term : terms) {
            String value = term == null ? "" : term.trim();
            if (value.isEmpty()
                    || (conjunction ? "true" : "false").equals(value)) continue;
            if ((conjunction ? "false" : "true").equals(value)) return value;
            filtered.add(term);
        }
        if (filtered.isEmpty()) return conjunction ? "true" : "false";
        if (filtered.size() == 1) return filtered.get(0);
        StringBuilder result = new StringBuilder(conjunction
                ? "(and" : "(or");
        for (String term : filtered) result.append(' ').append(term);
        return result.append(')').toString();
    }

    public static String integralRange(String lower, String value, String upper) {
        return "(and (<= " + lower + " " + value + ") (<= " + value + " "
                + upper + "))";
    }

    public static final class Term {
        public final String text;
        public final Sort sort;
        public final IntegralWidth integralWidth;
        public final String stringNullness;
        public final String stringReferenceOrigin;
        public final String precondition;

        private Term(String text, Sort sort, IntegralWidth integralWidth,
                     String stringNullness, String stringReferenceOrigin,
                     String precondition) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.stringNullness = stringNullness == null
                    ? "" : stringNullness;
            this.stringReferenceOrigin = stringReferenceOrigin == null
                    ? "" : stringReferenceOrigin;
            this.precondition = firstNonBlank(precondition, "true");
        }

        public static Term of(String text, Sort sort) {
            return of(text, sort, IntegralWidth.NONE);
        }

        public static Term of(String text, Sort sort, IntegralWidth integralWidth) {
            return of(text, sort, integralWidth, "", "", "true");
        }

        public static Term of(String text, Sort sort, IntegralWidth integralWidth,
                       String stringNullness, String stringReferenceOrigin,
                       String precondition) {
            return new Term(text, sort, integralWidth,
                    sort == Sort.STRING
                            ? firstNonBlank(stringNullness, "false") : "",
                    sort == Sort.STRING
                            ? firstNonBlank(stringReferenceOrigin) : "",
                    precondition);
        }

        public static Term vm(String text, Sort sort,
                              IntegralWidth integralWidth) {
            return new Term(text, sort, integralWidth, "", "", "true");
        }

        public static Term nonNullString(String text, String precondition) {
            return of(text, Sort.STRING, IntegralWidth.NONE, "false", "",
                    precondition);
        }

        public Term withPrecondition(String value) {
            return new Term(text, sort, integralWidth, stringNullness,
                    stringReferenceOrigin, value);
        }

        public Term withText(String value, String nullness) {
            return new Term(value, sort, integralWidth, nullness,
                    stringReferenceOrigin, precondition);
        }

        public boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
        }

        public boolean isNullReference() {
            return sort == Sort.REF && "nullRef".equals(text);
        }
    }
}
