package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * The one SMT lowering vocabulary shared by {@code ConcolicSmtComposer
 * .Emitter} and {@code ConcolicConstraintSolver.Encoder}.  They differ only
 * in the three policies {@link Policy} names: an unsupported construct
 * becomes a fresh unconstrained symbol in the composer and a {@code null}
 * term in the solver; the composer threads Java evaluation definedness
 * through {@link Term#precondition} while the solver asserts it eagerly;
 * and the solver tags every refusal with an {@code origin} string.
 */
final class VmTermLowering {
    private VmTermLowering() {
    }

    /** The SMT sort one lowered Java value carries. */
    enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), VALUE("Value"),
        ARRAY_VALUE("IndexedState"), MAP("AssocState"),
        /** The solver's "no Java sort is known" sentinel. */
        UNKNOWN("");

        final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        boolean containerState() {
            return this == ARRAY_VALUE || this == MAP;
        }

        boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
        }

        /** The solver's frozen spelling, frozen into its symbol names. */
        String replayName() {
            return this == MAP ? "ASSOCIATIVE"
                    : this == ARRAY_VALUE ? "INDEXED" : name();
        }
    }

    static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort.floating();
    }

    static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    /** The Java sort one boxed container cell unboxes to. */
    static ContainerSmtCodec.Sort unboxedCellSort(Sort sort) {
        return sort == Sort.BOOL ? ContainerSmtCodec.Sort.BOOL
                : sort == Sort.REF ? ContainerSmtCodec.Sort.REF
                : sort == Sort.FLOAT32 ? ContainerSmtCodec.Sort.FLOAT32
                : sort == Sort.FLOAT64 ? ContainerSmtCodec.Sort.FLOAT64
                : sort == Sort.STRING ? ContainerSmtCodec.Sort.STRING
                : ContainerSmtCodec.Sort.VALUE;
    }

    /** The container codec's sort for one lowered value, or null. */
    static ContainerSmtCodec.Sort containerSortOf(Sort sort) {
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
    static Sort sortOfContainer(ContainerSmtCodec.Sort sort) {
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

    /** What a lowering caller owns; everything else here is shared. */
    interface Policy {
        /** Lowers a sub-expression at the named diagnostic position. */
        Term lower(JsonElement expression, Sort expected, String origin);

        /** Records a refusal and yields the term lowering continues with. */
        Term refuse(Reason reason, String origin, String detail, Sort sort);

        /** Carries Java evaluation definedness from the inputs. */
        Term dependent(Term result, Term... inputs);

        /** The sort one JVM cast descriptor denotes for this caller. */
        Sort castSort(String descriptor);

        /** The integer this element exactly renders, or a named gap. */
        RenderedInteger renderedInteger(JsonElement element, String origin);

        /** States {@link #javaIntRange} for one parsed integer. */
        void assertJavaIntRange(Term integer);
    }

    /** A refusal, in the composer's spelling beside the solver's. */
    enum Reason {
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

        /** A term no container cell can carry. */
        CANNOT_BOX("CannotBox", false),

        // Expression dispatch.
        ABSENT_EXPRESSION("ABSENT_EXPRESSION", false),
        MALFORMED_NOT("MalformedNot", false),
        /** The composer names the type alone; the solver names it too. */
        UNKNOWN_EXPRESSION_TYPE("", false);

        private final String composed;
        private final boolean composedNamesOrigin;

        Reason(String composed, boolean composedNamesOrigin) {
            this.composed = composed;
            this.composedNamesOrigin = composedNamesOrigin;
        }

        /** The composer names the reason first, the solver the position. */
        String composedSubject(String origin, String detail) {
            return join(composed, composedNamesOrigin ? origin : "", detail);
        }

        String solverSubject(String origin, String detail) {
            return join(origin, name(), detail);
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

    /** Java binary numeric promotion of one operand to a floating sort. */
    static Term floatingPromotion(Policy policy, Term term, Sort target,
                                  String origin) {
        FloatingKind targetKind = floatingKind(target);
        if (term.sort == target) return term;
        if (term.sort.floating()) {
            String converted = JavaPrimitiveSmtSemantics.floatingConversion(
                    term.text, floatingKind(term.sort), targetKind);
            if (converted != null) {
                return policy.dependent(Term.of(converted, target), term);
            }
        } else if (term.sort == Sort.INT
                && term.integralWidth != IntegralWidth.NONE) {
            String converted = JavaPrimitiveSmtSemantics.integralToFloating(
                    term.text, targetKind);
            if (converted != null) {
                return policy.dependent(Term.of(converted, target), term);
            }
        }
        return policy.refuse(Reason.UNSUPPORTED_JAVA_NUMERIC_PROMOTION,
                origin, term.sort + "->" + target, target);
    }

    /** One JVM primitive conversion; every other cast is a named gap. */
    static Term typeCast(Policy policy, JsonObject expression,
                         String origin) {
        JsonElement sourceExpression = expression.get("_exp");
        Term source = policy.lower(sourceExpression, null,
                origin + ":castSource");
        String sourceType = JavaPrimitiveSmtSemantics.primitiveDescriptor(
                firstNonBlank(optionalString(expression, "sourceJavaType"),
                        expressionJavaType(sourceExpression)));
        String targetType = JavaPrimitiveSmtSemantics.primitiveDescriptor(
                firstNonBlank(optionalString(expression, "targetJavaType"),
                        optionalString(expression, "_java_type")));
        Sort sourceSort = policy.castSort(sourceType);
        Sort targetSort = policy.castSort(targetType);
        // A VALUE target says nothing about the cast; a reference is the
        // one thing every non-primitive cast produces.
        Sort refused = targetSort == Sort.VALUE ? Sort.REF : targetSort;
        boolean primitivePair = JavaPrimitiveSmtSemantics
                .primitiveNumericDescriptor(sourceType)
                && JavaPrimitiveSmtSemantics
                .primitiveNumericDescriptor(targetType);
        if (source != null && primitivePair && source.sort == sourceSort) {
            String conversion = JavaPrimitiveSmtSemantics.primitiveCast(
                    source.text, sourceType, targetType);
            if (conversion != null) {
                return policy.dependent(Term.of(conversion, targetSort,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(
                                targetType)), source);
            }
        } else if (source != null && primitivePair) {
            return policy.refuse(Reason.JAVA_CAST_SOURCE_SORT_CONFLICT,
                    origin, firstNonBlank(sourceType, "UNKNOWN") + ":"
                            + source.sort + "!=" + sourceSort, refused);
        }
        return policy.refuse(Reason.UNSUPPORTED_JAVA_CAST, origin,
                firstNonBlank(sourceType, "UNKNOWN") + "->"
                        + firstNonBlank(targetType, "UNKNOWN"), refused);
    }

    /** One container or string operation the codec could not close. */
    static Term codecGap(Policy policy, String operation, String gap,
                         String origin, Sort sort) {
        return policy.refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                operation + ":" + gap, sort);
    }

    /** The Java type one VM expression states it evaluates to. */
    static String expressionJavaType(JsonElement expression) {
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
    static final String JAVA_INT_TO_STRING =
            "(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))";

    /** The declarations every lowered query opens with.  The two callers
     *  froze nullRef on either side of the Value datatype; inert to SMT. */
    static List<String> preamble(boolean nullRefBeforeValueDatatype) {
        List<String> lines = new ArrayList<>();
        // Both lowerers spell Java integral arithmetic as two's-complement
        // wrapping, so either query is dense in nested Int
        // "mod 4294967296" terms over container sizes and indices.  Z3's
        // default arithmetic engine does not close those, while its
        // simplex-based one does, so a query names the engine it is meant
        // to be read with rather than leaving a plain "z3 query.smt2" to
        // diverge.  This selects a strategy; it does not change what the
        // query says, and it belongs beside the encoding that provokes it
        // rather than in one caller.
        lines.add("(set-option :smt.arith.solver 2)");
        lines.add("(declare-sort Ref 0)");
        if (nullRefBeforeValueDatatype) {
            lines.add("(declare-const nullRef Ref)");
        }
        lines.add(ContainerSmtCodec.valueDatatypeDeclaration());
        if (!nullRefBeforeValueDatatype) {
            lines.add("(declare-const nullRef Ref)");
        }
        lines.addAll(ContainerSmtCodec.preamble());
        return lines;
    }

    /** Records one read-time use, refusing a doubly-claimed identity. */
    static void recordGuardedReadUse(
            Map<String, Map<String, GuardedReadUse>> uses,
            String readIdentity, String projectionIdentity,
            String activation, Collection<String> selectors,
            Consumer<String> ambiguous) {
        String identity = GuardedReadNaming.useIdentity(projectionIdentity,
                activation);
        GuardedReadUse use = new GuardedReadUse(activation, selectors);
        GuardedReadUse held = uses.computeIfAbsent(readIdentity,
                ignored -> new LinkedHashMap<>()).putIfAbsent(identity, use);
        if (held != null && !held.same(use)) ambiguous.accept(identity);
    }

    /** The integer an element exactly renders, or the gap that stopped it. */
    static final class RenderedInteger {
        final Term integer;
        final String gap;

        RenderedInteger(Term integer, String gap) {
            this.integer = integer;
            this.gap = gap == null ? "" : gap;
        }
    }

    /** Integer.parseInt inverts Integer.toString only on an element that is
     *  that rendering and nothing else, in decimal, and in Java's int range
     *  - which is then stated as the parse's definedness. */
    static Term parseIntTerm(Policy policy, JsonObject expression,
                             String origin) {
        String name = "java/lang/Integer.parseInt";
        JsonArray params = JsonFields.array(expression, "_param_list");
        if (params.size() != 1 && params.size() != 2) {
            return codecGap(policy, name, "ARITY", origin, Sort.INT);
        }
        if (params.size() == 2) {
            Integer radix = VmExpressionIr.exactIntLiteral(params.get(1));
            if (radix == null || radix != 10) {
                return codecGap(policy, name, "RADIX_NOT_LITERAL_10", origin,
                        Sort.INT);
            }
        }
        RenderedInteger rendered = policy.renderedInteger(params.get(0),
                origin);
        if (!rendered.gap.isEmpty()) {
            return codecGap(policy, name, rendered.gap, origin, Sort.INT);
        }
        Term integer = rendered.integer;
        if (integer == null || integer.sort != Sort.INT) {
            return codecGap(policy, name, "ROUNDTRIP_SOURCE_NOT_INT", origin,
                    Sort.INT);
        }
        policy.assertJavaIntRange(integer);
        return integer;
    }

    /** The conjunction of these predicates, with the trivial ones and the
     *  outer parentheses of a one-element conjunction removed. */
    static String and(List<String> terms) {
        return booleanNary(terms, true);
    }

    /** The disjunction of these predicates, likewise flattened. */
    static String or(List<String> terms) {
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
    static String integralRange(String lower, String value, String upper) {
        return "(and (<= " + lower + " " + value + ") (<= " + value + " "
                + upper + "))";
    }

    /** Java's int range, stated over one lowered integer. */
    static String javaIntRange(String integer) {
        return integralRange("(- 2147483648)", integer, "2147483647");
    }

    /** Java's decimal Integer.toString of one lowered integer. */
    static Term javaIntString(Term integer) {
        return Term.nonNullString("(java_int_to_string " + integer.text + ")",
                integer.precondition);
    }

    /** One lowered VM expression: its SMT text plus its Java-level facts. */
    static final class Term {
        final String text;
        final Sort sort;
        final IntegralWidth integralWidth;
        /** Empty when unknown, "false" when a known non-null String, else
         *  the nullable reference companion Bool. */
        final String stringNullness;
        /** Stable provenance used only for Java reference identity. */
        final String stringReferenceOrigin;
        /** Java evaluation definedness (notably String dereference guards). */
        final String precondition;

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
        static Term of(String text, Sort sort) {
            return of(text, sort, IntegralWidth.NONE);
        }

        static Term of(String text, Sort sort, IntegralWidth integralWidth) {
            return of(text, sort, integralWidth, "", "", "true");
        }

        static Term of(String text, Sort sort, IntegralWidth integralWidth,
                       String stringNullness, String stringReferenceOrigin,
                       String precondition) {
            return new Term(text, sort, integralWidth,
                    sort == Sort.STRING
                            ? firstNonBlank(stringNullness, "false") : "",
                    sort == Sort.STRING
                            ? firstNonBlank(stringReferenceOrigin) : "",
                    precondition);
        }

        /** A term carrying exactly the facts given: an unstated String
         *  nullness stays unknown, the solver's refusal trigger. */
        static Term vm(String text, Sort sort) {
            return vm(text, sort, IntegralWidth.NONE, "", "");
        }

        static Term vm(String text, Sort sort, IntegralWidth integralWidth) {
            return vm(text, sort, integralWidth, "", "");
        }

        static Term vm(String text, Sort sort, IntegralWidth integralWidth,
                       String stringNullness, String stringReferenceOrigin) {
            return new Term(text, sort, integralWidth, stringNullness,
                    stringReferenceOrigin, "true");
        }

        static Term nullableString(String text, String nullness,
                                   String referenceOrigin) {
            return of(text, Sort.STRING, IntegralWidth.NONE, nullness,
                    referenceOrigin, "true");
        }

        static Term nonNullString(String text, String precondition) {
            return of(text, Sort.STRING, IntegralWidth.NONE, "false", "",
                    precondition);
        }

        Term withPrecondition(String value) {
            return new Term(text, sort, integralWidth, stringNullness,
                    stringReferenceOrigin, value);
        }

        boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
        }

        boolean isNullReference() {
            return sort == Sort.REF && "nullRef".equals(text);
        }
    }

    /** One read-time use: its activation and its candidate writers. */
    static final class GuardedReadUse {
        final String activation;
        final List<String> selectors;

        GuardedReadUse(String activation, Collection<String> selectors) {
            this.activation = activation;
            this.selectors = new ArrayList<>(selectors);
            Collections.sort(this.selectors);
        }

        boolean same(GuardedReadUse other) {
            return other != null && activation.equals(other.activation)
                    && selectors.equals(other.selectors);
        }
    }
}
