package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.FloatingKind;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The SMT lowering vocabulary ({@link Sort}, {@link Term}, {@link Reason},
 * the preamble) and the static helpers {@link SmtLowering} lowers with.
 */
public final class VmTermLowering {
    private VmTermLowering() {
    }

    /**
     * One recorded value as an SMT literal of this sort, or "" when it is
     * none: a Bool {@code true}/{@code false} (the VM's {@code 1}/{@code 0}),
     * an integral's decimal, a floating value's IEEE bits as the VM records
     * them, a String's content from its JSON string literal, quoted (Java
     * null, {@code N}, is no String).
     */
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
        return "";
    }

    /**
     * What binds one codec hole to one arm (WIRE-CODEC §6.1, §6.3): the
     * formula, or the gap that refuses the arm by name.
     */
    public static final class HoleArm {
        /** The binding, or "" when the arm is refused. */
        public final String formula;
        /** Null when bound, else the kind of the refusal. */
        public final GapKind refusal;
        public final String detail;

        private HoleArm(String formula, GapKind refusal, String detail) {
            this.formula = formula;
            this.refusal = refusal;
            this.detail = detail;
        }

        private static HoleArm refused(GapKind kind, String detail) {
            return new HoleArm("", kind, detail);
        }
    }

    /**
     * THE HOLE-ARM RULE (WIRE-CODEC §6.1, §6.3): {@code target}, the hole's
     * symbol at the DECODED leaf's {@code holeType}, bound to what one arm
     * delivered -- the operand the producer's export cut out of its leaf,
     * of {@code operandType}.
     * <ul>
     *   <li>The same sort is equality; an integral operand of a narrower
     *       type is widened by Java's rule (its range lies inside the
     *       hole's: JSON writes an {@code Integer} and decodes a
     *       {@code Long}).  A narrowing, or any other change of sort
     *       (integral and floating, a float read back as a double through
     *       its decimal text), refuses the arm by name.</li>
     *   <li>A String operand of an integral or boolean hole is its
     *       canonical rendering read back: {@code (java_int_to_string v)}
     *       or {@code "true"}/{@code "false"} is the operand, within the
     *       hole's range -- the only place the String theory stands for a
     *       hole, for an arm whose leaf was not cut at a rendering.</li>
     *   <li>A hole is minted only on a present, non-null leaf: an arm that
     *       delivers Java null refuses ({@code CODEC_MISMATCH NULL_LEAF}), a
     *       String that may be null holds only where it is not, and one
     *       whose nullness nothing states is refused by name.</li>
     * </ul>
     */
    public static HoleArm holeArm(String target, Term delivered,
                                  String operandType, String holeType) {
        Sort hole = JavaSmtSorts.sortOfJava(holeType);
        if (delivered.isNullReference()) {
            return HoleArm.refused(GapKind.CODEC_MISMATCH, "NULL_LEAF: the "
                    + "arm delivers Java null, and a hole is minted only on "
                    + "a present, non-null leaf");
        }
        if (delivered.sort == Sort.STRING) {
            if (delivered.stringNullness.isEmpty()) {
                return HoleArm.refused(GapKind.UNSTATED_VALUE,
                        Reason.JAVA_STRING_NULLNESS_UNKNOWN.composed + ": the"
                                + " arm delivers a String whose nullness "
                                + "nothing states, and the hole holds only "
                                + "where it is not null");
            }
            String read = reading(target, delivered.text, hole, holeType);
            if (read == null) return changed(operandType, holeType);
            List<String> held = new ArrayList<String>();
            if (!"false".equals(delivered.stringNullness)) {
                held.add("(not " + delivered.stringNullness + ")");
            }
            held.add(read);
            return new HoleArm(and(held), null, "");
        }
        if (delivered.sort != hole) return changed(operandType, holeType);
        if (hole == Sort.INT && !widens(operandType, holeType)) {
            return HoleArm.refused(GapKind.UNSTATED_VALUE, "HoleNarrowed: "
                    + "the arm delivers a " + operandType + " to a hole the "
                    + "consumer decoded as " + holeType + ", which holds "
                    + "fewer values, so Java widening does not bind it");
        }
        return new HoleArm("(= " + target + " " + delivered.text + ")",
                null, "");
    }

    /** A hole of this sort read off a String operand, or null for none. */
    private static String reading(String target, String string, Sort hole,
                                  String holeType) {
        if (hole == Sort.STRING) return "(= " + target + " " + string + ")";
        if (hole == Sort.BOOL) {
            return "(and (or (= " + string + " \"true\") (= " + string
                    + " \"false\")) (= " + target + " (= " + string
                    + " \"true\")))";
        }
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType(holeType);
        if (hole != Sort.INT || domain == null) return null;
        return "(and (= (java_int_to_string " + target + ") " + string + ") "
                + integralRange(domain.lower, target, domain.upper) + ")";
    }

    private static HoleArm changed(String operandType, String holeType) {
        return HoleArm.refused(GapKind.UNSTATED_VALUE, "HoleSortChanged: the "
                + "arm delivers a " + operandType + " to a hole the consumer "
                + "decoded as " + holeType + ": no Java widening and no "
                + "reading of a rendering takes the one to the other");
    }

    /** Whether every value of one integral type is one of another's. */
    private static boolean widens(String narrower, String wider) {
        JavaPrimitiveSmtSemantics.IntegralDomain from =
                JavaPrimitiveSmtSemantics.domainOfJavaType(narrower);
        JavaPrimitiveSmtSemantics.IntegralDomain to =
                JavaPrimitiveSmtSemantics.domainOfJavaType(wider);
        return from != null && to != null
                && numeral(to.lower).compareTo(numeral(from.lower)) <= 0
                && numeral(from.upper).compareTo(numeral(to.upper)) <= 0;
    }

    /** An SMT integer numeral, {@code (- n)} for a negative one. */
    private static BigInteger numeral(String smt) {
        String text = smt.trim();
        if (!text.startsWith("(-")) return new BigInteger(text);
        return new BigInteger(text.substring(2, text.length() - 1).trim())
                .negate();
    }

    /** The same text, spelled the way an SMT symbol may be spelled. */
    public static String smtName(String value) {
        String normalized = (value == null || value.trim().isEmpty()
                ? "anonymous" : value).replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        return normalized;
    }

    /** The SMT sort one lowered Java value carries. */
    public enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), VALUE("Value"),
        ARRAY_VALUE("IndexedState"), MAP("AssocState"),
        /** The solver's "no Java sort is known" sentinel. */
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

        /** Whether a recorded literal of this sort is its own value. */
        public boolean scalar() {
            return this == BOOL || this == INT || floating()
                    || this == STRING;
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

    /** The Java sort one boxed container cell unboxes to. */
    public static ContainerSmtCodec.Sort unboxedCellSort(Sort sort) {
        return sort == Sort.BOOL ? ContainerSmtCodec.Sort.BOOL
                : sort == Sort.REF ? ContainerSmtCodec.Sort.REF
                : sort == Sort.FLOAT32 ? ContainerSmtCodec.Sort.FLOAT32
                : sort == Sort.FLOAT64 ? ContainerSmtCodec.Sort.FLOAT64
                : sort == Sort.STRING ? ContainerSmtCodec.Sort.STRING
                : ContainerSmtCodec.Sort.VALUE;
    }

    /** The container codec's sort for one lowered value, or null. */
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

    /** The lowered sort one container codec value carries. */
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

    /** A named refusal reason. */
    public enum Reason {
        UNSUPPORTED_JAVA_NUMERIC_PROMOTION(
                "UnsupportedJavaNumericPromotion", true),
        JAVA_CAST_SOURCE_SORT_CONFLICT("JavaCastSourceSortConflict", false),
        UNSUPPORTED_JAVA_CAST("MODEL_SEMANTICS_MISSING:TypeCastExpression",
                false),
        MODEL_SEMANTICS_MISSING("MODEL_SEMANTICS_MISSING", false),

        // Binary operators.
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

        // Constants.
        INVALID_JAVA_BOOLEAN_LITERAL("InvalidJavaBooleanLiteral", false),
        INVALID_NUMERIC_LITERAL("InvalidNumericLiteral", false),
        UNSUPPORTED_CONSTANT_TYPE("UnsupportedConstantType", false),

        /** A String whose Java nullness this lowering does not know. */
        JAVA_STRING_NULLNESS_UNKNOWN("JavaStringNullnessUnknown", false),

        // Expression dispatch.
        ABSENT_EXPRESSION("ABSENT_EXPRESSION", false),
        MALFORMED_NOT("MalformedNot", false),
        /** Named by the expression type alone. */
        UNKNOWN_EXPRESSION_TYPE("", false);

        private final String composed;
        private final boolean composedNamesOrigin;

        Reason(String composed, boolean composedNamesOrigin) {
            this.composed = composed;
            this.composedNamesOrigin = composedNamesOrigin;
        }

        /** The refusal subject: reason, origin if asked for, detail. */
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

    /** The Java type one VM expression states it evaluates to. */
    public static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if ("MethodExpression".equals(optionalString(object, "_type"))) {
            return optionalString(JsonFields.object(object, "_res_exp"),
                    "_java_type");
        }
        return optionalString(object, "_java_type");
    }

    /** str.from_int covers only non-negative integers; Java's decimal
     *  Integer.toString needs the leading '-' spelled out. */
    public static final String JAVA_INT_TO_STRING =
            "(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))";

    /** The declarations every lowered query opens with. */
    public static List<String> preamble() {
        List<String> lines = new ArrayList<>();
        // Wrapping arithmetic yields nested "mod 2^32" terms that only z3's
        // simplex arithmetic closes; a strategy choice, not a meaning change.
        lines.add("(set-option :smt.arith.solver 2)");
        lines.add("(declare-sort Ref 0)");
        lines.add(ContainerStateModel.valueDatatypeDeclaration());
        lines.add("(declare-const nullRef Ref)");
        lines.addAll(ContainerStateModel.preamble());
        return lines;
    }

    /** The conjunction of these predicates, with the trivial ones and the
     *  outer parentheses of a one-element conjunction removed. */
    public static String and(List<String> terms) {
        return booleanNary(terms, true);
    }

    /** The disjunction of these predicates, likewise flattened. */
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

    /** One lowered value's Java integral domain, as an SMT predicate. */
    public static String integralRange(String lower, String value, String upper) {
        return "(and (<= " + lower + " " + value + ") (<= " + value + " "
                + upper + "))";
    }

    /** One lowered VM expression: its SMT text plus its Java-level facts. */
    public static final class Term {
        public final String text;
        public final Sort sort;
        public final IntegralWidth integralWidth;
        /** Empty when unknown, "false" when a known non-null String, else
         *  the nullable reference companion Bool. */
        public final String stringNullness;
        /** Stable provenance used only for Java reference identity. */
        public final String stringReferenceOrigin;
        /** Java evaluation definedness (notably String dereference guards). */
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

        /** A term whose String definedness is tracked: an unstated
         *  nullness on a String means "known non-null". */
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

        /** A container codec's value: a String's nullness stays unknown. */
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

        public boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
        }

        public boolean isNullReference() {
            return sort == Sort.REF && "nullRef".equals(text);
        }
    }
}
