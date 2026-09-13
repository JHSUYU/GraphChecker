package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Reason;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Term;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmetic;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmeticOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.bitwiseOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.comparison;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.constantPayload;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isPrimitiveIntExpression;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.quote;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.shiftOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.and;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.floatingKind;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.numeric;

/**
 * The one lowering of a recorded VM expression into SMT-LIB, shared by
 * {@code ConcolicSmtComposer.Emitter} (final composition) and
 * {@code ConcolicConstraintSolver.Encoder} (path flipping).
 *
 * <p>Both callers lower the same IR with the same operator semantics and
 * emit the same text for it.  What they do <em>not</em> share is stated as
 * abstract methods here and nowhere else:
 *
 * <ul>
 *   <li>a refused construct becomes a fresh unconstrained composer term and
 *       a {@code null} solver term ({@link VmTermLowering.Policy#refuse});</li>
 *   <li>Java evaluation definedness is threaded through
 *       {@link Term#precondition} by the composer and asserted eagerly by
 *       the solver ({@link #definedResult}, {@link #stringDefinedness});</li>
 *   <li>the two name Java types with different granularity
 *       ({@link #sortOfJavaType}).</li>
 * </ul>
 *
 * <p>Everything else below is one implementation.  Where the two used to
 * disagree on <em>semantics</em> rather than on plumbing, the composer's
 * model won and the solver's refusal was deleted; each such case carries
 * the argument for why the model is sound for flipping too.
 */
abstract class VmLoweringCore implements VmTermLowering.Policy {

    // ------------------------------------------------------------------
    // What the two callers own.
    // ------------------------------------------------------------------

    /** One lowered value with no definedness obligation of its own. */
    final Term result(String text, Sort sort, Term... inputs) {
        return definedResult(text, sort, IntegralWidth.NONE, "true", inputs);
    }

    final Term result(String text, Sort sort, IntegralWidth width,
                      Term... inputs) {
        return definedResult(text, sort, width, "true", inputs);
    }

    /**
     * One lowered value that Java evaluates only where {@code definedness}
     * holds.  The composer carries it on the term; the solver states it.
     */
    abstract Term definedResult(String text, Sort sort, IntegralWidth width,
                                String definedness, Term... inputs);

    /**
     * One lowered {@code &&} or {@code ||}.  Its definedness is exactly its
     * operands': Java evaluates the right one only where the left decided
     * nothing, so an operand obligation must not escape that guard.  The
     * obligation is therefore the caller's to state or to carry.
     */
    abstract Term shortCircuit(String text, Term left, Term right,
                               boolean conjunction);

    /**
     * The definedness of one Java String operation.  Every term in
     * {@code dereferenced} is a receiver the operation dereferences, so
     * evaluation proves it non-null; every term in {@code evaluated} only
     * contributes its own definedness.  Returns {@code null} when the
     * caller refuses instead of stating it.
     */
    abstract String stringDefinedness(String origin, String operation,
                                      List<Term> dereferenced,
                                      List<Term> evaluated);

    /** States the Java domain of one lowered integral value. */
    abstract void assertJavaIntegralDomain(String term, Sort sort,
                                           String javaType, String identity);

    /** The sort this caller gives one recorded Java type. */
    abstract Sort sortOfJavaType(String javaType);

    /** Records that the query uses {@code java_int_to_string}. */
    abstract void noteJavaIntToString();

    /** One recorded symbol. */
    abstract Term symbolTerm(JsonObject expression, Sort expected,
                             String origin);

    /** One recorded environment placeholder. */
    abstract Term placeholderTerm(JsonObject expression, String origin);

    /** One recorded guarded read of shared state. */
    abstract Term guardedReadTerm(JsonObject expression, Sort expected,
                                  String origin);

    /** One recorded merge of a value over its producer's cases. */
    abstract Term caseMergeTerm(JsonObject expression, Sort expected,
                                String origin);

    /** One recorded container relation, or one field projection of one. */
    abstract Term containerTerm(JsonObject expression, boolean field,
                                String origin);

    /** The Java String.split prefix round trip, which the two prove with
     *  different amounts of evidence. */
    abstract Term splitElementTerm(JsonObject expression, String origin);

    /** The sort a refused MethodExpression still has to carry. */
    abstract Sort methodResultSort(JsonObject expression, String origin);

    // ------------------------------------------------------------------
    // Dispatch.
    // ------------------------------------------------------------------

    /** Lowers one recorded VM expression of any kind. */
    final Term dispatch(JsonElement expression, Sort expected,
                        String origin) {
        if (expression == null || expression.isJsonNull()
                || !expression.isJsonObject()) {
            return refuse(Reason.ABSENT_EXPRESSION, origin, "",
                    expected == null ? Sort.REF : expected);
        }
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        if ("SymbolExpression".equals(type)) {
            return symbolTerm(object, expected, origin);
        }
        if (ContainerSmtCodec.constantKind(type)) {
            return constant(object, expected, origin);
        }
        if ("BinaryExpression".equals(type)) {
            return binary(object, origin);
        }
        if ("OpStrExpression".equals(type)) {
            return stringOperation(object, origin);
        }
        if ("NotExpression".equals(type)) {
            Term operand = lower(object.get("_operand"), Sort.BOOL,
                    origin + ":not");
            if (operand == null || operand.sort != Sort.BOOL) {
                return refuse(Reason.MALFORMED_NOT, origin, "", Sort.BOOL);
            }
            return result("(not " + operand.text + ")", Sort.BOOL, operand);
        }
        if ("PlaceholderExpression".equals(type)) {
            return placeholderTerm(object, origin);
        }
        if ("TypeCastExpression".equals(type)) {
            return VmTermLowering.typeCast(this, object, origin);
        }
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)) {
            return guardedReadTerm(object, expected, origin);
        }
        if (SymbolicPropagationClosure.ITE_TYPE.equals(type)) {
            return caseMergeTerm(object, expected, origin);
        }
        if (VmExpressionIr.CONSUMER_BOUNDARY_TYPE.equals(type)
                || VmExpressionIr.CONSUMER_BOUNDARY_REFERENCE_TYPE
                .equals(type)) {
            // Online path flipping and non-final SMT uses see an anchor as
            // the exact value already propagated by the VM.  Final
            // composition normally replaces it with a case merge first.
            return lower(object.get(VmExpressionIr.EXPRESSION), expected,
                    origin + ":consumer-boundary");
        }
        if ("MethodExpression".equals(type)) {
            return methodTerm(object, origin);
        }
        if (ContainerSmtCodec.handles(object)) {
            return containerTerm(object, false, origin);
        }
        if (ContainerSmtCodec.handlesField(object)) {
            return containerTerm(object, true, origin);
        }
        return refuse(Reason.UNKNOWN_EXPRESSION_TYPE, origin,
                type.isEmpty() ? "MISSING_TYPE" : type,
                expected == null ? Sort.VALUE : expected);
    }

    /**
     * The two Java library methods whose exact value relation this lowering
     * proves; every other call is a named gap.
     */
    final Term methodTerm(JsonObject expression, String origin) {
        String method = optionalString(expression, "_name");
        if (VmExpressionIr.isJavaParseInt(method)) {
            return VmTermLowering.parseIntTerm(this, expression, origin);
        }
        if (VmExpressionIr.isJavaSplitElement(method)) {
            return splitElementTerm(expression, origin);
        }
        return refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "MethodExpression:" + firstNonBlank(method, "unknown"),
                methodResultSort(expression, origin));
    }

    // ------------------------------------------------------------------
    // Binary operators.
    // ------------------------------------------------------------------

    /** One recorded {@code BinaryExpression}. */
    final Term binary(JsonObject expression, String origin) {
        String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                optionalString(expression, "_op"));
        JsonElement leftExpression = expression.get("_left");
        if (leftExpression == null || leftExpression.isJsonNull()) {
            return unary(expression, operator, origin);
        }
        Term left = lower(leftExpression, null, origin + ":left");
        Term right = lower(expression.get("_right"),
                left == null ? null : left.sort, origin + ":right");
        if (left == null || right == null) return null;
        // A JVM reference comparison against the integer 0 is a null test.
        if (left.sort != right.sort && right.isZero()
                && left.sort == Sort.REF) {
            right = result("nullRef", Sort.REF);
        } else if (left.sort != right.sort && left.isZero()
                && right.sort == Sort.REF) {
            left = result("nullRef", Sort.REF);
        }
        if ("--".equals(operator)) {
            if (left.sort == Sort.INT && right.sort == Sort.INT
                    && left.integralWidth == IntegralWidth.JAVA_LONG
                    && right.integralWidth == IntegralWidth.JAVA_LONG) {
                return result(JavaPrimitiveSmtSemantics
                        .integralCompareResult(left.text, right.text),
                        Sort.INT, IntegralWidth.JAVA_INT, left, right);
            }
            return refusedJvmCompare(Reason.MALFORMED_JVM_LCMP_OPERANDS,
                    origin, left.sort + ":" + left.integralWidth + ":"
                            + right.sort + ":" + right.integralWidth);
        }
        if ("--l".equals(operator) || "--g".equals(operator)) {
            if (left.sort == right.sort && left.sort.floating()) {
                return result(JavaPrimitiveSmtSemantics
                        .floatingCompareResult(left.text, right.text,
                                "--g".equals(operator)), Sort.INT,
                        IntegralWidth.JAVA_INT, left, right);
            }
            return refusedJvmCompare(
                    Reason.MALFORMED_JVM_FLOATING_COMPARE_OPERANDS, origin,
                    operator + ":" + left.sort + ":" + right.sort);
        }
        if (left.sort != right.sort && numeric(left.sort)
                && numeric(right.sort)
                && (left.sort.floating() || right.sort.floating())) {
            Sort promoted = left.sort == Sort.FLOAT64
                    || right.sort == Sort.FLOAT64
                    ? Sort.FLOAT64 : Sort.FLOAT32;
            left = VmTermLowering.floatingPromotion(this, left, promoted,
                    origin + ":left");
            right = VmTermLowering.floatingPromotion(this, right, promoted,
                    origin + ":right");
            if (left == null || right == null) return null;
        }
        boolean equality = "==".equals(operator) || "!=".equals(operator);
        if (equality && (left.sort == Sort.STRING && right.isNullReference()
                || right.sort == Sort.STRING && left.isNullReference())) {
            Term string = left.sort == Sort.STRING ? left : right;
            if (string.stringNullness.isEmpty()) {
                return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                        operator, Sort.BOOL);
            }
            return result("!=".equals(operator)
                    ? "(not " + string.stringNullness + ")"
                    : string.stringNullness, Sort.BOOL, left, right);
        }
        if (left.sort != right.sort && equality
                && (left.isNullReference() || right.isNullReference())) {
            // Java primitives are never null.  This is the one mixed-sort
            // binary relation whose semantics can be closed without an
            // agreed sort for the two operands.
            return result("!=".equals(operator) ? "true" : "false",
                    Sort.BOOL, left, right);
        }
        if ("&&".equals(operator) || "||".equals(operator)) {
            if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                return refuse(Reason.NON_BOOLEAN_LOGIC, origin,
                        operator + ":" + left.sort + ":" + right.sort,
                        Sort.BOOL);
            }
            boolean conjunction = "&&".equals(operator);
            return shortCircuit("(" + (conjunction ? "and" : "or") + " "
                    + left.text + " " + right.text + ")", left, right,
                    conjunction);
        }
        if (left.sort != right.sort
                && (left.sort == Sort.VALUE) != (right.sort == Sort.VALUE)
                && !equality) {
            // Exactly one side is a boxed container cell.  Arithmetic and
            // ordering on it are operations on the element's declared
            // type, not on the tagged transport value, so unbox by that
            // type rather than refusing the pair.  Reference cells and
            // cells of unknown type come back unchanged and fall into the
            // refusal below.
            if (left.sort == Sort.VALUE) {
                left = fromValue(left, VmTermLowering.expressionJavaType(
                        expression.get("_left")), origin);
            } else {
                right = fromValue(right, VmTermLowering.expressionJavaType(
                        expression.get("_right")), origin);
            }
            if (left == null || right == null) return null;
        }
        if (left.sort != right.sort) {
            Sort resultSort = equality || !comparison(operator).isEmpty()
                    ? Sort.BOOL : left.sort;
            return refuse(Reason.BINARY_SORT_CONFLICT, origin,
                    operator + ":" + left.sort + "!=" + right.sort,
                    resultSort);
        }
        if (equality) {
            return equality(expression, operator, left, right, origin);
        }
        String smt = comparison(operator);
        if (!smt.isEmpty()) {
            if (!numeric(left.sort) || !numeric(right.sort)) {
                return refuse(Reason.NON_NUMERIC_COMPARISON, origin,
                        operator + ":" + left.sort, Sort.BOOL);
            }
            if (left.sort.floating()) {
                return result(JavaPrimitiveSmtSemantics.floatingComparison(
                        operator, left.text, right.text), Sort.BOOL,
                        left, right);
            }
            return result("(" + smt + " " + left.text + " " + right.text
                    + ")", Sort.BOOL, left, right);
        }
        if (bitwiseOperator(operator)) {
            IntegralWidth width = promotedIntegralWidth(left, right);
            if (width == IntegralWidth.NONE) {
                return refuse(
                        Reason.AMBIGUOUS_JAVA_INTEGRAL_BITWISE_WIDTH, origin,
                        operator + ":" + left.integralWidth + ":"
                                + right.integralWidth, Sort.INT);
            }
            return result(JavaPrimitiveSmtSemantics.bitwise(operator,
                    left.text, right.text, width), Sort.INT, width,
                    left, right);
        }
        if (shiftOperator(operator)) {
            if (left.sort != Sort.INT || right.sort != Sort.INT
                    || left.integralWidth == IntegralWidth.NONE) {
                return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_SHIFT, origin,
                        operator + ":" + left.integralWidth + ":"
                                + right.integralWidth, Sort.INT);
            }
            return result(JavaPrimitiveSmtSemantics.shift(operator,
                    left.text, right.text, left.integralWidth), Sort.INT,
                    left.integralWidth, left, right);
        }
        if (arithmeticOperator(operator)) {
            return arithmeticTerm(operator, left, right, origin);
        }
        return refuse(Reason.BINARY_OPERATOR, origin, operator, Sort.BOOL);
    }

    private Term unary(JsonObject expression, String operator,
                       String origin) {
        Term operand = lower(expression.get("_right"), null,
                origin + ":operand");
        Sort operandSort = operand == null ? Sort.UNKNOWN : operand.sort;
        if ("-".equals(operator) && operand != null
                && numeric(operandSort)) {
            if (operandSort.floating()) {
                return result(JavaPrimitiveSmtSemantics.floatingNegate(
                        operand.text), operandSort, operand);
            }
            if (operand.integralWidth != IntegralWidth.NONE) {
                return result(JavaPrimitiveSmtSemantics.wrap("(- "
                        + operand.text + ")", operand.integralWidth),
                        Sort.INT, operand.integralWidth, operand);
            }
            return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_UNARY_WIDTH, origin,
                    firstNonBlank(operator, "MISSING"), Sort.INT);
        }
        if ("~".equals(operator) && operand != null
                && operandSort == Sort.INT
                && operand.integralWidth != IntegralWidth.NONE) {
            return result(JavaPrimitiveSmtSemantics.complement(operand.text,
                    operand.integralWidth), Sort.INT, operand.integralWidth,
                    operand);
        }
        return refuse(Reason.NON_NUMERIC_OR_UNKNOWN_UNARY, origin,
                firstNonBlank(operator, "MISSING") + ":" + operandSort,
                operandSort);
    }

    /**
     * A malformed JVM {@code lcmp}/{@code fcmp} still has the int result
     * sort its bytecode promises, so the refused term keeps that width.
     */
    private Term refusedJvmCompare(Reason reason, String origin,
                                   String detail) {
        Term refused = refuse(reason, origin, detail, Sort.INT);
        return refused == null ? null
                : Term.of(refused.text, Sort.INT, IntegralWidth.JAVA_INT);
    }

    private Term equality(JsonObject expression, String operator,
                          Term left, Term right, String origin) {
        if (left.text.equals(right.text)) {
            return result("==".equals(operator) ? "true" : "false",
                    Sort.BOOL, left, right);
        }
        if (left.sort == Sort.STRING) {
            return stringIdentity(expression, operator, left, right, origin);
        }
        if (left.sort.floating()) {
            return result(JavaPrimitiveSmtSemantics.floatingComparison(
                    operator, left.text, right.text), Sort.BOOL,
                    left, right);
        }
        String equals = "(= " + left.text + " " + right.text + ")";
        return result("!=".equals(operator) ? "(not " + equals + ")"
                : equals, Sort.BOOL, left, right);
    }

    /**
     * Java {@code ==} between two Strings is reference identity.  Three
     * cases close it exactly and the rest stays refused.
     */
    private Term stringIdentity(JsonObject expression, String operator,
                                Term left, Term right, String origin) {
        if (ContainerSmtCodec.handlesFieldBinding(expression)) {
            Term symbol = ContainerSmtCodec.handlesField(
                    expression.get("_left")) ? right : left;
            String materialization = ContainerSmtCodec
                    .materializedStringEquality(left.text, right.text,
                            symbol.stringNullness);
            if (materialization.isEmpty()) {
                return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                        "MATERIALIZATION:" + operator, Sort.BOOL);
            }
            return result(materialization, Sort.BOOL, left, right);
        }
        if (!left.stringReferenceOrigin.isEmpty()
                && left.stringReferenceOrigin.equals(
                right.stringReferenceOrigin)) {
            return result("!=".equals(operator) ? "false" : "true",
                    Sort.BOOL, left, right);
        }
        // One side a String literal decides this by content.
        //
        // Java's == on Strings is reference identity, and a literal is
        // interned, so `lit == x` holds exactly when x is that interned
        // object.  Content equality is the same relation over the values
        // the other side can actually take: it is a recorded expression,
        // so every value in its range is a String this execution really
        // produced, and two equal Strings in one interning pool are one
        // object.  HDFS's own SerialNumberManager string table is exactly
        // this comparison, and refusing it discarded the whole formula
        // around it.
        //
        // With no literal on either side the relation is still reference
        // identity between two unknown objects, which content equality
        // would genuinely over-approximate, so that stays refused.
        Term literalSide = stringLiteral(expression.get("_left")) != null
                ? left
                : stringLiteral(expression.get("_right")) != null
                ? right : null;
        if (literalSide != null) {
            Term symbolSide = literalSide == left ? right : left;
            String equals = ContainerSmtCodec.materializedStringEquality(
                    left.text, right.text, symbolSide.stringNullness);
            if (!equals.isEmpty()) {
                return result("!=".equals(operator) ? "(not " + equals + ")"
                        : equals, Sort.BOOL, left, right);
            }
        }
        Term refused = refuse(Reason.MODEL_SEMANTICS_MISSING, origin,
                "JAVA_STRING_REFERENCE_IDENTITY:" + operator, Sort.BOOL);
        return refused == null ? null : dependent(refused, left, right);
    }

    private Term arithmeticTerm(String operator, Term left, Term right,
                                String origin) {
        if (!numeric(left.sort) || !numeric(right.sort)) {
            return refuse(Reason.NON_NUMERIC_ARITHMETIC, origin,
                    operator + ":" + left.sort, left.sort);
        }
        Sort resultSort = left.sort;
        if ("%".equals(operator) && resultSort.floating()) {
            // SMT's fp.rem is the IEEE remainder, which rounds the
            // quotient to even where Java's % truncates it.
            return refuse(Reason.JAVA_FLOATING_REMAINDER_UNMODELED, origin,
                    "", resultSort);
        }
        if (resultSort.floating()) {
            String floating = JavaPrimitiveSmtSemantics.floatingArithmetic(
                    operator, left.text, right.text);
            if (floating != null) {
                return result(floating, resultSort, left, right);
            }
            return refuse(Reason.JAVA_FLOATING_OPERATOR_UNMODELED, origin,
                    operator, resultSort);
        }
        IntegralWidth width = promotedIntegralWidth(left, right);
        if (width == IntegralWidth.NONE) {
            return refuse(Reason.AMBIGUOUS_JAVA_INTEGRAL_BINARY_WIDTH,
                    origin, operator + ":" + left.integralWidth + ":"
                            + right.integralWidth, Sort.INT);
        }
        if ("@".equals(operator) || "/".equals(operator)
                || "%".equals(operator)) {
            // Java truncates toward zero and takes the dividend's sign; a
            // zero divisor throws rather than producing a value, so it is
            // stated as the operation's definedness instead of being left
            // to the solver's choice.
            String quotient = "%".equals(operator)
                    ? JavaPrimitiveSmtSemantics.integralRemainder(left.text,
                    right.text, width)
                    : JavaPrimitiveSmtSemantics.integralDivision(left.text,
                    right.text, width);
            return definedResult(quotient, Sort.INT, width,
                    JavaPrimitiveSmtSemantics.integralDivisorDefined(
                            right.text), left, right);
        }
        return result(JavaPrimitiveSmtSemantics.wrap("("
                + arithmetic(operator) + " " + left.text + " " + right.text
                + ")", width), Sort.INT, width, left, right);
    }

    // ------------------------------------------------------------------
    // Constants.
    // ------------------------------------------------------------------

    /** One recorded constant expression. */
    final Term constant(JsonObject expression, Sort expected, String origin) {
        String raw = optionalString(expression, "_exp");
        String javaType = optionalString(expression, "_java_type");
        String value = constantPayload(raw);
        Sort sort = sortOfJavaType(javaType);
        // The JVM has no boolean comparison instruction, so a boolean is
        // recorded as the int the comparison consumed.  A literal that is
        // neither 0 nor 1 is not a Java boolean and is refused rather than
        // guessed at.
        if (expected == Sort.BOOL && (sort == Sort.BOOL
                || sort == Sort.INT)) {
            return booleanLiteral(value, raw, origin);
        }
        if (expected == Sort.REF && ("0".equals(value)
                || VmExpressionIr.SYMBOLIC_NULL.equals(raw))) {
            return result("nullRef", Sort.REF);
        }
        if (sort == Sort.BOOL) return booleanLiteral(value, raw, origin);
        if (sort.floating()) {
            String literal = JavaPrimitiveSmtSemantics.floatingLiteral(value,
                    floatingKind(sort));
            return literal == null
                    ? refuse(Reason.INVALID_NUMERIC_LITERAL, origin,
                    sort + ":" + firstNonBlank(raw, "MISSING"), sort)
                    : result(literal, sort);
        }
        if (sort == Sort.INT) {
            String literal = SmtModelValueCodec.integerLiteral(value);
            return literal == null
                    ? refuse(Reason.INVALID_NUMERIC_LITERAL, origin,
                    sort + ":" + firstNonBlank(raw, "MISSING"), sort)
                    : result(literal, Sort.INT, JavaPrimitiveSmtSemantics
                    .widthOfJavaType(javaType));
        }
        if (sort == Sort.STRING) {
            return Term.nonNullString(quote(value), "true");
        }
        if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
            return result("nullRef", Sort.REF);
        }
        return refuse(Reason.UNSUPPORTED_CONSTANT_TYPE, origin,
                firstNonBlank(javaType, "MISSING"),
                sort == Sort.VALUE ? Sort.REF : sort);
    }

    private Term booleanLiteral(String value, String raw, String origin) {
        if (!"0".equals(value) && !"1".equals(value)) {
            return refuse(Reason.INVALID_JAVA_BOOLEAN_LITERAL, origin,
                    firstNonBlank(raw, "MISSING"), Sort.BOOL);
        }
        return result("1".equals(value) ? "true" : "false", Sort.BOOL);
    }

    // ------------------------------------------------------------------
    // String operations.
    // ------------------------------------------------------------------

    /** One recorded {@code OpStrExpression}. */
    final Term stringOperation(JsonObject expression, String origin) {
        String operation = optionalString(expression, "_name");
        boolean negated = optionalBool(expression, "_is_not", false);
        JsonArray params = array(expression, "_param_list");
        if ("isEmpty".equals(operation)) {
            StringParameters strings = stringParameters(params, 1,
                    operation, origin, Sort.BOOL);
            if (!strings.complete()) return strings.refusal;
            String defined = stringDefinedness(origin, operation,
                    strings.terms, Collections.<Term>emptyList());
            if (defined == null) return null;
            return booleanStringResult("(= (str.len "
                    + strings.terms.get(0).text + ") 0)", negated, defined);
        }
        if ("length".equals(operation)) {
            if (negated) {
                return codecGap(operation, "NEGATED_VALUE_OPERATION", origin,
                        Sort.INT);
            }
            StringParameters strings = stringParameters(params, 1,
                    operation, origin, Sort.INT);
            if (!strings.complete()) return strings.refusal;
            String defined = stringDefinedness(origin, operation,
                    strings.terms, Collections.<Term>emptyList());
            if (defined == null) return null;
            String text = "(str.len " + strings.terms.get(0).text + ")";
            Term length = definedResult(text, Sort.INT,
                    IntegralWidth.JAVA_INT, defined);
            assertJavaIntegralDomain(text, Sort.INT, "I",
                    "java_string_length");
            return length;
        }
        if ("equals".equals(operation)) {
            return stringEquals(params, negated, origin);
        }
        if ("contains".equals(operation) || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            StringParameters strings = stringParameters(params, 2,
                    operation, origin, Sort.BOOL);
            if (!strings.complete()) return strings.refusal;
            String defined = stringDefinedness(origin, operation,
                    strings.terms, Collections.<Term>emptyList());
            if (defined == null) return null;
            String receiver = strings.terms.get(0).text;
            String argument = strings.terms.get(1).text;
            String predicate = "contains".equals(operation)
                    ? "(str.contains " + receiver + " " + argument + ")"
                    : "startsWith".equals(operation)
                    ? "(str.prefixof " + argument + " " + receiver + ")"
                    : "(str.suffixof " + argument + " " + receiver + ")";
            return booleanStringResult(predicate, negated, defined);
        }
        if (negated) {
            return codecGap(firstNonBlank(operation, "unknown"),
                    "NEGATED_VALUE_OPERATION", origin, Sort.STRING);
        }
        if ("concat".equals(operation)) {
            if (params.size() == 0) {
                return codecGap(operation, "EMPTY", origin, Sort.STRING);
            }
            StringParameters strings = stringParameters(params,
                    params.size(), operation, origin, Sort.STRING);
            if (!strings.complete()) return strings.refusal;
            String defined = stringDefinedness(origin, operation,
                    strings.terms, Collections.<Term>emptyList());
            if (defined == null) return null;
            if (strings.terms.size() == 1) {
                return Term.nonNullString(strings.terms.get(0).text, defined);
            }
            StringBuilder result = new StringBuilder("(str.++");
            for (Term value : strings.terms) {
                result.append(' ').append(value.text);
            }
            return Term.nonNullString(result.append(')').toString(), defined);
        }
        if ("toString".equals(operation)) {
            if (params.size() != 1
                    || !isPrimitiveIntExpression(params.get(0))) {
                return codecGap(operation, "REQUIRES_ONE_PRIMITIVE_INT",
                        origin, Sort.STRING);
            }
            Term integer = lower(params.get(0), Sort.INT,
                    origin + ":toString");
            if (integer == null || integer.sort != Sort.INT) {
                return codecGap(operation, "NON_INT_TERM", origin,
                        Sort.STRING);
            }
            assertJavaIntRange(integer);
            return javaIntString(integer);
        }
        return codecGap(firstNonBlank(operation, "unknown"),
                "UNSUPPORTED_OPERATION", origin, Sort.STRING);
    }

    /** Java String.equals requires a non-null receiver but accepts null. */
    private Term stringEquals(JsonArray params, boolean negated,
                              String origin) {
        if (params.size() != 2) {
            return codecGap("equals", "ARITY", origin, Sort.BOOL);
        }
        Term receiver = lower(params.get(0), null,
                origin + ":equals:parameter0");
        Term argument = lower(params.get(1), null,
                origin + ":equals:parameter1");
        if (receiver == null || argument == null) return null;
        if (receiver.sort != Sort.STRING) {
            return codecGap("equals", "NON_STRING_PARAMETER", origin,
                    Sort.BOOL);
        }
        String predicate;
        if (argument.isNullReference()) {
            predicate = "false";
        } else if (argument.sort != Sort.STRING) {
            return codecGap("equals", "ARGUMENT_DYNAMIC_TYPE_UNMODELED",
                    origin, Sort.BOOL);
        } else if (argument.stringNullness.isEmpty()) {
            return refuse(Reason.JAVA_STRING_NULLNESS_UNKNOWN, origin,
                    "equals:1", Sort.BOOL);
        } else {
            predicate = and(Arrays.asList(stringNonNull(argument),
                    "(= " + receiver.text + " " + argument.text + ")"));
        }
        String defined = stringDefinedness(origin, "equals",
                Collections.singletonList(receiver),
                Collections.singletonList(argument));
        if (defined == null) return null;
        return booleanStringResult(predicate, negated, defined);
    }

    /**
     * The parameters of one String operation, each of them a String, or
     * {@code null} once the arity or a parameter's sort refused it.
     */
    private StringParameters stringParameters(JsonArray params, int arity,
                                              String operation,
                                              String origin,
                                              Sort resultSort) {
        if (params.size() != arity) {
            return StringParameters.refused(codecGap(operation, "ARITY",
                    origin, resultSort));
        }
        List<Term> result = new ArrayList<>();
        for (int index = 0; index < params.size(); index++) {
            // Passing STRING as an expected sort would let a malformed
            // primitive SymbolExpression be declared as String.  Derive
            // the sort from the parameter instead and check it here.
            Term value = lower(params.get(index), null,
                    origin + ":" + operation + ":parameter" + index);
            if (value == null) return StringParameters.refused(null);
            if (value.sort != Sort.STRING) {
                return StringParameters.refused(codecGap(operation,
                        "NON_STRING_PARAMETER", origin, resultSort));
            }
            result.add(value);
        }
        return new StringParameters(result, null);
    }

    /** Either every parameter as a String term, or the refusal. */
    private static final class StringParameters {
        private final List<Term> terms;
        private final Term refusal;

        private StringParameters(List<Term> terms, Term refusal) {
            this.terms = terms;
            this.refusal = refusal;
        }

        private static StringParameters refused(Term refusal) {
            return new StringParameters(null, refusal);
        }

        private boolean complete() {
            return terms != null;
        }
    }

    final Term booleanStringResult(String predicate, boolean negated,
                                   String definedness) {
        return definedResult(negated ? "(not " + predicate + ")" : predicate,
                Sort.BOOL, IntegralWidth.NONE, definedness);
    }

    /** "true" when this String is known non-null, else the negated Bool. */
    static String stringNonNull(Term term) {
        if (term.sort != Sort.STRING) return "false";
        return "false".equals(term.stringNullness) ? "true"
                : "(not " + term.stringNullness + ")";
    }

    /** Java's decimal Integer.toString of one lowered integer. */
    final Term javaIntString(Term integer) {
        noteJavaIntToString();
        return VmTermLowering.javaIntString(integer);
    }

    /** One String or container operation the codec could not close. */
    final Term codecGap(String operation, String gap, String origin,
                        Sort sort) {
        return VmTermLowering.codecGap(this, "OpStrExpression." + operation,
                gap, origin, sort);
    }

    // ------------------------------------------------------------------
    // Boxed container cells.
    // ------------------------------------------------------------------

    /** Unboxes one container cell by the element's declared Java type. */
    final Term fromValue(Term value, String javaType, String origin) {
        if (value == null || value.sort != Sort.VALUE) return value;
        String kind = ContainerSmtCodec.unboxableCellKind(javaType);
        if (kind.isEmpty()) return value;
        String defined = and(Arrays.asList(value.precondition,
                "((_ is " + kind + ") " + value.text + ")"));
        String integral = ContainerSmtCodec.unboxIntegral(value.text,
                javaType);
        if (!integral.isEmpty()) {
            return definedResult(integral, Sort.INT,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType),
                    defined);
        }
        if ("VBool".equals(kind)) {
            return definedResult("(valueBool " + value.text + ")",
                    Sort.BOOL, IntegralWidth.NONE, defined);
        }
        if ("VFloat".equals(kind)) {
            return definedResult("(valueFloat " + value.text + ")",
                    Sort.FLOAT32, IntegralWidth.NONE, defined);
        }
        if ("VDouble".equals(kind)) {
            return definedResult("(valueDouble " + value.text + ")",
                    Sort.FLOAT64, IntegralWidth.NONE, defined);
        }
        if ("VString".equals(kind)) {
            // The cell tag is part of `defined`, so the unboxed String is
            // the one a VString cell holds and is therefore non-null.
            return Term.nonNullString("(valueString " + value.text + ")",
                    defined);
        }
        return value;
    }

    // ------------------------------------------------------------------
    // Small shared predicates.
    // ------------------------------------------------------------------

    /** Java binary numeric promotion of two integral operands. */
    static IntegralWidth promotedIntegralWidth(Term left, Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
    }

    /** The String this expression is exactly a literal of, or null. */
    final String stringLiteral(JsonElement expression) {
        return VmExpressionIr.exactStringLiteral(expression,
                type -> sortOfJavaType(type) == Sort.STRING);
    }

    /**
     * Admits only a split delimiter that is one ordinary literal
     * character.  {@code decimalText} additionally excludes the characters
     * that occur inside Java's decimal rendering of an int, which a prefix
     * round trip must not be split on.
     */
    static String delimiterGap(String value, boolean decimalText) {
        if (value == null || value.length() != 1) {
            return "REGEX_NOT_SAFE_SINGLE_LITERAL";
        }
        char delimiter = value.charAt(0);
        if (Character.isISOControl(delimiter)) {
            return "REGEX_NOT_SAFE_SINGLE_LITERAL";
        }
        if ("\\.^$|?*+()[]{}".indexOf(delimiter) >= 0) {
            return "REGEX_NOT_SAFE_SINGLE_LITERAL";
        }
        if (decimalText && (Character.isDigit(delimiter)
                || delimiter == '-')) {
            return "DELIMITER_OCCURS_IN_JAVA_INT_TEXT";
        }
        return "";
    }
}
