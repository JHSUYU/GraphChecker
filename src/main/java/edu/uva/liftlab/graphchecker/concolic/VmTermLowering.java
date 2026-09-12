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
 * The one SMT lowering vocabulary shared by the two producers of VM
 * expression terms: {@code ConcolicSmtComposer.Emitter}, which composes the
 * whole causal candidate, and {@code ConcolicConstraintSolver.Encoder},
 * which encodes one path-flip query.
 *
 * <p>The two differ only in three declared policies, which stay with their
 * callers: an unsupported construct becomes a fresh unconstrained symbol in
 * the composer and a {@code null} term in the solver; the composer threads
 * Java evaluation definedness (notably String dereference guards) through
 * {@link Term#precondition} while the solver asserts it eagerly; and the
 * solver tags every refusal with an {@code origin} diagnostic string.
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

        /**
         * The solver's frozen spelling of a container sort.  It names the
         * sort inside shared-term identities, which minted symbol names are
         * derived from, and inside a replay model assignment's valueType.
         */
        String replayName() {
            return this == MAP ? "ASSOCIATIVE"
                    : this == ARRAY_VALUE ? "INDEXED" : name();
        }

        boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
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


    /**
     * The three policies one lowering caller owns.  Everything else about
     * lowering a VM expression is the same for both callers.
     */
    interface Policy {
        /**
         * Lowers a sub-expression.  {@code origin} names the position for a
         * solver diagnostic and is ignored by the composer.
         */
        Term lower(JsonElement expression, Sort expected, String origin);

        /**
         * Records one unsupported construct and yields the term lowering
         * continues with: a fresh unconstrained value of {@code sort} in the
         * composer, {@code null} - "no term at all" - in the solver.
         */
        Term refuse(Reason reason, String origin, String detail, Sort sort);

        /**
         * Threads Java evaluation definedness from the inputs into the
         * result.  The composer carries it as a precondition; the solver has
         * already asserted it and returns the result unchanged.
         */
        Term dependent(Term result, Term... inputs);

        /** The sort one JVM cast descriptor denotes for this caller. */
        Sort castSort(String descriptor);

        /**
         * The integer this element is the exact Integer.toString rendering
         * of.  The two callers prove the round trip over different element
         * analyses, so each states its own gap.
         */
        RenderedInteger renderedInteger(JsonElement element, String origin);

        /** States {@link #javaIntRange} for one parsed integer. */
        void assertJavaIntRange(Term integer);
    }

    /**
     * One named reason a construct could not be lowered.  The two callers
     * spell the same reason differently in their artifacts, so each reason
     * carries the composer's spelling beside the solver's constant name.
     */
    enum Reason {
        UNSUPPORTED_JAVA_NUMERIC_PROMOTION(
                "UnsupportedJavaNumericPromotion", true),
        JAVA_CAST_SOURCE_SORT_CONFLICT("JavaCastSourceSortConflict", false),
        UNSUPPORTED_JAVA_CAST("MODEL_SEMANTICS_MISSING:TypeCastExpression",
                false),
        MODEL_SEMANTICS_MISSING("MODEL_SEMANTICS_MISSING", false);

        /** The composer's spelling of this reason. */
        private final String composed;
        /** Whether the composer names the position beside the reason. */
        private final boolean composedNamesOrigin;

        Reason(String composed, boolean composedNamesOrigin) {
            this.composed = composed;
            this.composedNamesOrigin = composedNamesOrigin;
        }

        /** The composer's refusal subject: the reason first. */
        String composedSubject(String origin, String detail) {
            return join(composed, composedNamesOrigin ? origin : "", detail);
        }

        /** The solver's refusal subject: the position first. */
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


    /**
     * SMT-LIB's str.from_int is defined only for non-negative integers, so
     * Java's decimal Integer.toString needs the leading '-' spelled out.
     */
    static final String JAVA_INT_TO_STRING =
            "(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))";

    /**
     * The sort, datatype and helper declarations every lowered query opens
     * with.  The two callers froze the nullRef declaration on either side of
     * the Value datatype; the position is inert to SMT and is kept as each
     * emitted it so their bytes do not move.
     */
    static List<String> preamble(boolean nullRefBeforeValueDatatype) {
        List<String> lines = new ArrayList<>();
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

    /** The container codec's sort for one lowered value, or null. */
    static ContainerSmtCodec.Sort containerSortOf(Sort sort) {
        if (sort == null) return null;
        switch (sort) {
            case BOOL: return ContainerSmtCodec.Sort.BOOL;
            case INT: return ContainerSmtCodec.Sort.INT;
            case FLOAT32: return ContainerSmtCodec.Sort.FLOAT32;
            case FLOAT64: return ContainerSmtCodec.Sort.FLOAT64;
            case STRING: return ContainerSmtCodec.Sort.STRING;
            case REF: return ContainerSmtCodec.Sort.REF;
            case VALUE: return ContainerSmtCodec.Sort.VALUE;
            case ARRAY_VALUE: return ContainerSmtCodec.Sort.INDEXED;
            case MAP: return ContainerSmtCodec.Sort.ASSOCIATIVE;
            default: return null;
        }
    }

    /** The lowered sort one container codec value carries. */
    static Sort sortOfContainer(ContainerSmtCodec.Sort sort) {
        if (sort == null) return Sort.UNKNOWN;
        switch (sort) {
            case BOOL: return Sort.BOOL;
            case INT: return Sort.INT;
            case FLOAT32: return Sort.FLOAT32;
            case FLOAT64: return Sort.FLOAT64;
            case STRING: return Sort.STRING;
            case REF: return Sort.REF;
            case VALUE: return Sort.VALUE;
            case INDEXED: return Sort.ARRAY_VALUE;
            default: return Sort.MAP;
        }
    }

    /**
     * Records one read-time use of a guarded read under the identity the two
     * callers already agree on, refusing when the same use is claimed twice
     * with different candidates.
     */
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


    /** The name Integer.parseInt is refused under. */
    private static final String PARSE_INT = "java/lang/Integer.parseInt";

    /**
     * The integer an element is the exact Integer.toString rendering of, or
     * the named gap that stopped the round-trip proof.
     */
    static final class RenderedInteger {
        private final Term integer;
        private final String gap;

        private RenderedInteger(Term integer, String gap) {
            this.integer = integer;
            this.gap = gap;
        }

        static RenderedInteger of(Term integer) {
            return new RenderedInteger(integer, "");
        }

        static RenderedInteger gap(String gap) {
            return new RenderedInteger(null, gap);
        }
    }

    /**
     * Integer.parseInt inverts Integer.toString only on an element that is
     * that rendering and nothing else, in decimal, and only inside Java's
     * int range - which is then stated as the parse's definedness.
     */
    static Term parseIntTerm(Policy policy, JsonObject expression,
                             String origin) {
        JsonArray params = JsonFields.array(expression, "_param_list");
        if (params.size() != 1 && params.size() != 2) {
            return codecGap(policy, PARSE_INT, "ARITY", origin, Sort.INT);
        }
        if (params.size() == 2) {
            Integer radix = VmExpressionIr.exactIntLiteral(params.get(1));
            if (radix == null || radix != 10) {
                return codecGap(policy, PARSE_INT, "RADIX_NOT_LITERAL_10",
                        origin, Sort.INT);
            }
        }
        RenderedInteger rendered = policy.renderedInteger(params.get(0),
                origin);
        if (!rendered.gap.isEmpty()) {
            return codecGap(policy, PARSE_INT, rendered.gap, origin,
                    Sort.INT);
        }
        Term integer = rendered.integer;
        if (integer == null || integer.sort != Sort.INT) {
            return codecGap(policy, PARSE_INT, "ROUNDTRIP_SOURCE_NOT_INT",
                    origin, Sort.INT);
        }
        policy.assertJavaIntRange(integer);
        return integer;
    }

    /** Java's int range, stated over one lowered integer. */
    static String javaIntRange(String integer) {
        return "(and (<= (- 2147483648) " + integer + ") (<= " + integer
                + " 2147483647))";
    }

    /** Java's decimal Integer.toString of one lowered integer. */
    static Term javaIntString(Term integer) {
        return Term.nonNullString("(java_int_to_string " + integer.text + ")",
                integer.precondition);
    }

    /** One String predicate, possibly negated by its call site. */
    static Term booleanStringResult(String predicate, boolean negated,
                                    String precondition) {
        return Term.of(negated ? "(not " + predicate + ")" : predicate,
                Sort.BOOL).withPrecondition(precondition);
    }

    /** One lowered VM expression: its SMT text plus its Java-level facts. */
    static final class Term {
        final String text;
        final Sort sort;
        final IntegralWidth integralWidth;
        /** Empty when unknown.  "false" means a known non-null String; any
         * other value is the nullable reference companion Bool. */
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

        /**
         * A term whose String definedness is tracked: an unstated nullness on
         * a String is the composer's "known non-null", and a nullness on a
         * non-String is not a fact at all.
         */
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

        /**
         * A term carrying exactly the facts it was given: an unstated String
         * nullness stays unknown, which is the solver's refusal trigger.
         */
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

    /**
     * One read-time use of a guarded read: the activation it was read under
     * and the candidate writers it may have come from.
     */
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
