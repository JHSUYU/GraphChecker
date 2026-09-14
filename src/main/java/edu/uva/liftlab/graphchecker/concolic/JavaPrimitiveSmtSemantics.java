package edu.uva.liftlab.graphchecker.concolic;

import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

/** Shared SMT semantics for Java's integral computational types. */
public final class JavaPrimitiveSmtSemantics {
    public static final String INT_WRAP_DEFINITION =
            "(define-fun java_int_wrap ((i Int)) Int"
                    + " (- (mod (+ i 2147483648) 4294967296)"
                    + " 2147483648))";
    public static final String LONG_WRAP_DEFINITION =
            "(define-fun java_long_wrap ((i Int)) Int"
                    + " (- (mod (+ i 9223372036854775808)"
                    + " 18446744073709551616) 9223372036854775808))";

    public enum IntegralWidth {
        NONE,
        JAVA_INT,
        JAVA_LONG
    }

    /** Java's two binary IEEE-754 computational formats. */
    public enum FloatingKind {
        NONE,
        JAVA_FLOAT,
        JAVA_DOUBLE
    }

    public static final class IntegralDomain {
        public final String lower;
        public final String upper;
        public final IntegralWidth width;

        private IntegralDomain(String lower, String upper,
                               IntegralWidth width) {
            this.lower = lower;
            this.upper = upper;
            this.width = width;
        }
    }

    private JavaPrimitiveSmtSemantics() {
    }

    /** Normalizes a source type or VM name to one JVM descriptor. */
    public static String javaTypeDescriptor(String javaType) {
        String value = javaType == null ? ""
                : javaType.trim().replace('.', '/');
        if (value.isEmpty() || value.startsWith("[")) return value;
        int dimensions = 0;
        while (value.endsWith("[]")) {
            dimensions++;
            value = value.substring(0, value.length() - 2);
        }
        String descriptor;
        if (value.length() == 1 && "ZBCSIJFDV".contains(value)) {
            descriptor = value;
        } else if ("boolean".equals(value)) descriptor = "Z";
        else if ("byte".equals(value)) descriptor = "B";
        else if ("char".equals(value)) descriptor = "C";
        else if ("short".equals(value)) descriptor = "S";
        else if ("int".equals(value)) descriptor = "I";
        else if ("long".equals(value)) descriptor = "J";
        else if ("float".equals(value)) descriptor = "F";
        else if ("double".equals(value)) descriptor = "D";
        else if ("void".equals(value)) descriptor = "V";
        else if (value.startsWith("L") && value.endsWith(";")) {
            descriptor = value;
        } else {
            descriptor = "L" + value + ";";
        }
        StringBuilder result = new StringBuilder(dimensions
                + descriptor.length());
        for (int index = 0; index < dimensions; index++) result.append('[');
        return result.append(descriptor).toString();
    }

    /**
     * Whether a location of this Java type carries an object <em>identity</em>
     * the solver can arm over rather than a scalar it can assign.
     *
     * <p>The scalar leaf contract represents a primitive, a {@code String},
     * a boxed primitive and a primitive array, and the container algebra
     * represents a collection as bounded state.  What was left with no
     * representation at all is the plain object reference -- the shape of
     * {@code BlockTokenSecretManager#currentKey} -- whose versions are the
     * identities its writers installed.  Such a location is shared state in
     * exactly the sense the version store already models: a read through it
     * selects one of the recorded writers, and the value the read yields is
     * a field <em>of the object that writer installed</em>.</p>
     *
     * <p>Arrays are excluded because an array is state rather than identity,
     * and the boxed types because the scalar contract already unwraps them.
     * {@code java.lang.Object} is excluded as well: it names no class whose
     * fields a dependent read could resolve, and it is the declared type a
     * container most often hides behind, which the static shape test cannot
     * see through.</p>
     */
    public static boolean referenceIdentityCarrier(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        if (!descriptor.startsWith("L") || !descriptor.endsWith(";")
                || descriptor.length() <= 2) {
            return false;
        }
        if (JavaContainerTypes.shape(javaType)
                != JavaContainerTypes.Shape.NONE) {
            return false;
        }
        return !SCALAR_REFERENCE_DESCRIPTORS.contains(descriptor);
    }

    /** Reference descriptors the scalar leaf contract already represents. */
    private static final java.util.Set<String> SCALAR_REFERENCE_DESCRIPTORS =
            java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(java.util.Arrays.asList(
                            "Ljava/lang/String;", "Ljava/lang/Boolean;",
                            "Ljava/lang/Byte;", "Ljava/lang/Character;",
                            "Ljava/lang/Short;", "Ljava/lang/Integer;",
                            "Ljava/lang/Long;", "Ljava/lang/Float;",
                            "Ljava/lang/Double;", "Ljava/lang/Object;")));

    /**
     * The closed value range of one integral Java type, as {@code {minimum,
     * maximum}}, or null when the type names no integral range.  A boolean
     * is not one: two named values are not a span of values.
     */
    public static BigInteger[] integralRange(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        if ("B".equals(descriptor)) {
            return range(Byte.MIN_VALUE, Byte.MAX_VALUE);
        }
        if ("C".equals(descriptor)) {
            return range(0, Character.MAX_VALUE);
        }
        if ("S".equals(descriptor)) {
            return range(Short.MIN_VALUE, Short.MAX_VALUE);
        }
        if ("I".equals(descriptor)) {
            return range(Integer.MIN_VALUE, Integer.MAX_VALUE);
        }
        if ("J".equals(descriptor)) {
            return range(Long.MIN_VALUE, Long.MAX_VALUE);
        }
        return null;
    }

    private static BigInteger[] range(long minimum, long maximum) {
        return new BigInteger[] {BigInteger.valueOf(minimum),
                BigInteger.valueOf(maximum)};
    }

    public static IntegralWidth widthOfJavaType(String javaType) {
        IntegralDomain domain = domainOfJavaType(javaType);
        return domain == null ? IntegralWidth.NONE : domain.width;
    }

    static FloatingKind floatingKindOfJavaType(String javaType) {
        String type = normalize(javaType);
        if ("F".equals(type) || "java/lang/Float".equals(type)) {
            return FloatingKind.JAVA_FLOAT;
        }
        if ("D".equals(type) || "java/lang/Double".equals(type)) {
            return FloatingKind.JAVA_DOUBLE;
        }
        return FloatingKind.NONE;
    }

    /**
     * Encodes the VM's decimal F/D literal by first asking Java to perform
     * exactly the same decimal-to-binary conversion used by replay, then
     * supplying those raw IEEE bits to SMT.
     */
    static String floatingLiteral(String value, FloatingKind kind) {
        if (kind == null || kind == FloatingKind.NONE || value == null) {
            return null;
        }
        String normalized = floatingParserLiteral(value.trim());
        try {
            if (kind == FloatingKind.JAVA_FLOAT) {
                int bits = Float.floatToRawIntBits(Float.parseFloat(
                        normalized));
                return "((_ to_fp 8 24) #x" + String.format(Locale.ROOT,
                        "%08x", bits) + ")";
            }
            long bits = Double.doubleToRawLongBits(Double.parseDouble(
                    normalized));
            return "((_ to_fp 11 53) #x" + String.format(Locale.ROOT,
                    "%016x", bits) + ")";
        } catch (NumberFormatException malformed) {
            return null;
        }
    }

    static String floatingNegate(String operand) {
        return "(fp.neg " + operand + ")";
    }

    static String floatingComparison(String operator, String left,
                                     String right) {
        String predicate;
        if ("==".equals(operator)) predicate = "fp.eq";
        else if ("!=".equals(operator)) predicate = "fp.eq";
        else if ("<".equals(operator)) predicate = "fp.lt";
        else if ("<=".equals(operator)) predicate = "fp.leq";
        else if (">".equals(operator)) predicate = "fp.gt";
        else if (">=".equals(operator)) predicate = "fp.geq";
        else return null;
        String comparison = "(" + predicate + " " + left + " "
                + right + ")";
        return "!=".equals(operator) ? "(not " + comparison + ")"
                : comparison;
    }

    static String floatingArithmetic(String operator, String left,
                                     String right) {
        String operation;
        if ("+".equals(operator)) operation = "fp.add";
        else if ("-".equals(operator)) operation = "fp.sub";
        else if ("*".equals(operator)) operation = "fp.mul";
        else if ("@".equals(operator) || "/".equals(operator)) {
            operation = "fp.div";
        } else {
            // SMT fp.rem is IEEE remainder, not Java's truncating %.
            return null;
        }
        return "(" + operation + " RNE " + left + " " + right + ")";
    }

    /** Exact JVM {@code fcmp*}/{@code dcmp*} result. */
    static String floatingCompareResult(String left, String right,
                                        boolean nanIsGreater) {
        String nanResult = nanIsGreater ? "1" : "(- 1)";
        return "(ite (or (fp.isNaN " + left + ") (fp.isNaN " + right
                + ")) " + nanResult + " (ite (fp.lt " + left + " "
                + right + ") (- 1) (ite (fp.gt " + left + " " + right
                + ") 1 0)))";
    }

    /** Exact JVM {@code lcmp} result in the shared mathematical-Int model. */
    static String integralCompareResult(String left, String right) {
        return "(ite (< " + left + " " + right + ") (- 1)"
                + " (ite (> " + left + " " + right + ") 1 0))";
    }

    static String floatingConversion(String value, FloatingKind source,
                                     FloatingKind target) {
        if (source == null || target == null
                || source == FloatingKind.NONE
                || target == FloatingKind.NONE) {
            return null;
        }
        if (source == target) return value;
        if (target == FloatingKind.JAVA_FLOAT) {
            return "((_ to_fp 8 24) RNE " + value + ")";
        }
        return "((_ to_fp 11 53) RNE " + value + ")";
    }

    static String integralToFloating(String value, FloatingKind target) {
        if (target == FloatingKind.JAVA_FLOAT) {
            return "((_ to_fp 8 24) RNE (to_real " + value + "))";
        }
        if (target == FloatingKind.JAVA_DOUBLE) {
            return "((_ to_fp 11 53) RNE (to_real " + value + "))";
        }
        return null;
    }

    /**
     * Lowers one Java primitive conversion without introducing a fresh SMT
     * value.
     */
    static String primitiveCast(String value, String sourceJavaType,
                                String targetJavaType) {
        String source = primitiveDescriptor(sourceJavaType);
        String target = primitiveDescriptor(targetJavaType);
        if (value == null || !primitiveNumericDescriptor(source)
                || !primitiveNumericDescriptor(target)) {
            return null;
        }
        if (source.equals(target)) return value;

        boolean sourceIntegral = integralDescriptor(source);
        boolean targetIntegral = integralDescriptor(target);
        if (sourceIntegral && targetIntegral) {
            return integralCast(value, source, target);
        }

        FloatingKind sourceFloating = floatingKindOfJavaType(source);
        FloatingKind targetFloating = floatingKindOfJavaType(target);
        if (sourceIntegral && targetFloating != FloatingKind.NONE) {
            return integralToFloating(value, targetFloating);
        }
        if (sourceFloating != FloatingKind.NONE
                && targetFloating != FloatingKind.NONE) {
            return floatingConversion(value, sourceFloating,
                    targetFloating);
        }
        if (sourceFloating != FloatingKind.NONE && targetIntegral
                && ("I".equals(target) || "J".equals(target))) {
            return floatingToIntegral(value, sourceFloating, target);
        }
        return null;
    }

    static String primitiveDescriptor(String javaType) {
        String type = javaType == null ? ""
                : javaType.trim().replace('.', '/');
        return javaTypeDescriptor(type);
    }

    static boolean primitiveNumericDescriptor(String descriptor) {
        return descriptor != null && descriptor.length() == 1
                && "BCSIJFD".contains(descriptor);
    }

    private static boolean integralDescriptor(String descriptor) {
        return descriptor != null && descriptor.length() == 1
                && "BCSIJ".contains(descriptor);
    }

    private static String integralCast(String value, String source,
                                       String target) {
        if ("B".equals(target)) return signedLowBits(value, 8);
        if ("C".equals(target)) return "(mod " + value + " 65536)";
        if ("S".equals(target)) return signedLowBits(value, 16);
        if ("I".equals(target)) {
            return "J".equals(source) ? "(java_int_wrap " + value + ")"
                    : value;
        }
        if ("J".equals(target)) {
            // Every B/C/S/I value is exactly representable as a Java long.
            return value;
        }
        return null;
    }

    private static String signedLowBits(String value, int width) {
        long modulus = 1L << width;
        long half = modulus >>> 1;
        return "(- (mod (+ " + value + " " + half + ") " + modulus
                + ") " + half + ")";
    }

    private static String floatingToIntegral(String value,
                                             FloatingKind source,
                                             String target) {
        final int width;
        final String lower;
        final String upper;
        final String modulus;
        if ("I".equals(target)) {
            width = 32;
            lower = "(- 2147483648)";
            upper = "2147483647";
            modulus = "4294967296";
        } else if ("J".equals(target)) {
            width = 64;
            lower = "(- 9223372036854775808)";
            upper = "9223372036854775807";
            modulus = "18446744073709551616";
        } else {
            return null;
        }

        String lowerFloating = integralToFloating(lower, source);
        String upperFloating = integralToFloating(upper, source);
        String bits = "((_ fp.to_sbv " + width + ") RTZ " + value + ")";
        String signedInteger = "(let ((java_cast_bits " + bits + "))"
                + " (ite (= ((_ extract " + (width - 1) + " "
                + (width - 1) + ") java_cast_bits) #b1)"
                + " (- (bv2int java_cast_bits) " + modulus + ")"
                + " (bv2int java_cast_bits)))";
        return "(ite (fp.isNaN " + value + ") 0"
                + " (ite (fp.geq " + value + " " + upperFloating + ") "
                + upper + " (ite (fp.leq " + value + " "
                + lowerFloating + ") " + lower + " " + signedInteger
                + ")))";
    }

    private static String floatingParserLiteral(String value) {
        String lower = value.toLowerCase(Locale.ROOT);
        if ("nan".equals(lower) || "+nan".equals(lower)
                || "-nan".equals(lower)) return "NaN";
        if ("inf".equals(lower) || "+inf".equals(lower)
                || "infinity".equals(lower)
                || "+infinity".equals(lower)) return "Infinity";
        if ("-inf".equals(lower) || "-infinity".equals(lower)) {
            return "-Infinity";
        }
        return value;
    }

    /** Returns the runtime value domain of an explicitly typed Java leaf. */
    public static IntegralDomain domainOfJavaType(String javaType) {
        String type = normalize(javaType);
        if ("Z".equals(type) || "java/lang/Boolean".equals(type)) {
            return new IntegralDomain("0", "1", IntegralWidth.JAVA_INT);
        }
        if ("B".equals(type) || "java/lang/Byte".equals(type)) {
            return new IntegralDomain("(- 128)", "127",
                    IntegralWidth.JAVA_INT);
        }
        if ("C".equals(type) || "java/lang/Character".equals(type)) {
            return new IntegralDomain("0", "65535",
                    IntegralWidth.JAVA_INT);
        }
        if ("S".equals(type) || "java/lang/Short".equals(type)) {
            return new IntegralDomain("(- 32768)", "32767",
                    IntegralWidth.JAVA_INT);
        }
        if ("I".equals(type) || "java/lang/Integer".equals(type)) {
            return new IntegralDomain("(- 2147483648)", "2147483647",
                    IntegralWidth.JAVA_INT);
        }
        if ("J".equals(type) || "java/lang/Long".equals(type)) {
            return new IntegralDomain("(- 9223372036854775808)",
                    "9223372036854775807", IntegralWidth.JAVA_LONG);
        }
        return null;
    }

    /** Java binary numeric promotion, but only when both widths are known. */
    static IntegralWidth promote(IntegralWidth left, IntegralWidth right) {
        if (left == null || right == null
                || left == IntegralWidth.NONE
                || right == IntegralWidth.NONE) {
            return IntegralWidth.NONE;
        }
        if (left == IntegralWidth.JAVA_LONG
                || right == IntegralWidth.JAVA_LONG) {
            return IntegralWidth.JAVA_LONG;
        }
        return IntegralWidth.JAVA_INT;
    }

    static String wrap(String expression, IntegralWidth width) {
        if (width == IntegralWidth.JAVA_INT) {
            return "(java_int_wrap " + expression + ")";
        }
        if (width == IntegralWidth.JAVA_LONG) {
            return "(java_long_wrap " + expression + ")";
        }
        throw new IllegalArgumentException(
                "cannot wrap an ambiguous integral expression");
    }

    /** Exact Java two's-complement lowering for integral bitwise operators. */
    static String bitwise(String operator, String left, String right,
                          IntegralWidth width) {
        BigInteger constant = integerLiteral(right);
        String variable = left;
        if (constant == null) {
            constant = integerLiteral(left);
            variable = right;
        }
        if (constant != null) {
            return constantBitwise(operator, variable, constant, width);
        }
        String smtOperator;
        if ("&".equals(operator)) smtOperator = "bvand";
        else if ("|".equals(operator)) smtOperator = "bvor";
        else if ("^".equals(operator)) smtOperator = "bvxor";
        else throw new IllegalArgumentException(
                    "not a Java integral bitwise operator: " + operator);
        int bits = bits(width);
        return wrap("(bv2int (" + smtOperator + " ((_ int2bv " + bits
                + ") " + left + ") ((_ int2bv " + bits + ") "
                + right + ")))", width);
    }

    /** Exact Java shift lowering, including the JVM shift-distance mask. */
    static String shift(String operator, String left, String right,
                        IntegralWidth width) {
        BigInteger constant = integerLiteral(right);
        if (constant != null) {
            int bits = bits(width);
            int distance = constant.mod(BigInteger.valueOf(bits)).intValue();
            BigInteger factor = BigInteger.ONE.shiftLeft(distance);
            if ("<<".equals(operator)) {
                return wrap("(* " + left + " " + factor + ")", width);
            }
            if (">>".equals(operator)) {
                return wrap("(div " + left + " " + factor + ")", width);
            }
            if (">>>".equals(operator)) {
                BigInteger modulus = BigInteger.ONE.shiftLeft(bits);
                return wrap("(div (mod " + left + " " + modulus + ") "
                        + factor + ")", width);
            }
        }
        String smtOperator;
        if ("<<".equals(operator)) smtOperator = "bvshl";
        else if (">>".equals(operator)) smtOperator = "bvashr";
        else if (">>>".equals(operator)) smtOperator = "bvlshr";
        else throw new IllegalArgumentException(
                    "not a Java integral shift operator: " + operator);
        int bits = bits(width);
        return wrap("(bv2int (" + smtOperator + " ((_ int2bv " + bits
                + ") " + left + ") ((_ int2bv " + bits + ") (mod "
                + right + " " + bits + "))))", width);
    }

    /**
     * Exact Java integral division (JLS 15.17.2): the quotient is truncated
     * toward zero, not floored as SMT-LIB's Euclidean {@code div} is, so the
     * negative dividend is reflected through zero.  {@code MIN_VALUE / -1}
     * needs no special case: it produces the mathematical {@code 2^(n-1)},
     * which the width's wrap turns back into {@code MIN_VALUE}, exactly as
     * the JVM's overflow rule states.
     */
    static String integralDivision(String left, String right,
                                   IntegralWidth width) {
        return wrap("(let ((java_idiv_a " + left + ")"
                + " (java_idiv_b " + right + "))"
                + " (ite (>= java_idiv_a 0) (div java_idiv_a java_idiv_b)"
                + " (- (div (- java_idiv_a) java_idiv_b))))", width);
    }

    /**
     * Exact Java integral remainder (JLS 15.17.3): {@code a % b} takes the
     * sign of the dividend, where SMT-LIB's Euclidean {@code mod} is always
     * non-negative.  Reflecting a negative dividend through zero gives Java's
     * {@code a - (a / b) * b} for every pair, {@code MIN_VALUE % -1 == 0}
     * included, and the result never leaves the width.
     */
    static String integralRemainder(String left, String right,
                                    IntegralWidth width) {
        return wrap("(let ((java_irem_a " + left + ")"
                + " (java_irem_b " + right + "))"
                + " (ite (>= java_irem_a 0) (mod java_irem_a java_irem_b)"
                + " (- (mod (- java_irem_a) java_irem_b))))", width);
    }

    /**
     * Definedness of one Java integral {@code /} or {@code %}: a zero divisor
     * throws {@code ArithmeticException} instead of producing a value, while
     * SMT-LIB leaves division by zero uninterpreted, so the divisor must be
     * stated non-zero rather than left for the solver to choose.
     */
    static String integralDivisorDefined(String right) {
        BigInteger literal = integerLiteral(right);
        if (literal != null) {
            return literal.signum() == 0 ? "false" : "true";
        }
        return "(not (= " + right + " 0))";
    }

    /** Exact Java integral complement. */
    static String complement(String operand, IntegralWidth width) {
        int bits = bits(width);
        return wrap("(bv2int (bvnot ((_ int2bv " + bits + ") "
                + operand + ")))", width);
    }

    private static int bits(IntegralWidth width) {
        if (width == IntegralWidth.JAVA_INT) return 32;
        if (width == IntegralWidth.JAVA_LONG) return 64;
        throw new IllegalArgumentException(
                "cannot lower an ambiguous integral bit operation");
    }

    /**
     * Normalize the concolic VM's expression-IR spelling to Java's spelling.
     * The VM deliberately serializes {@code iushr}/{@code lushr} as
     * {@code >>u}; Java source and the SMT lowering use {@code >>>}.
     */
    static String canonicalVmOperator(String operator) {
        return ">>u".equals(operator) ? ">>>" : operator;
    }

    private static String constantBitwise(String operator, String variable,
                                          BigInteger rawMask,
                                          IntegralWidth width) {
        int bits = bits(width);
        BigInteger modulus = BigInteger.ONE.shiftLeft(bits);
        BigInteger mask = rawMask.mod(modulus);
        String unsigned = "(mod " + variable + " " + modulus + ")";
        List<String> selectedBits = new ArrayList<>();
        for (int bit = 0; bit < bits; bit++) {
            if (!mask.testBit(bit)) continue;
            BigInteger factor = BigInteger.ONE.shiftLeft(bit);
            selectedBits.add("(* (mod (div " + unsigned + " " + factor
                    + ") 2) " + factor + ")");
        }
        String intersection;
        if (selectedBits.isEmpty()) intersection = "0";
        else if (selectedBits.size() == 1) intersection = selectedBits.get(0);
        else intersection = "(+ " + String.join(" ", selectedBits) + ")";
        String expression;
        if ("&".equals(operator)) expression = intersection;
        else if ("|".equals(operator)) {
            expression = "(- (+ " + unsigned + " " + mask + ") "
                    + intersection + ")";
        } else if ("^".equals(operator)) {
            expression = "(- (+ " + unsigned + " " + mask + ") (* 2 "
                    + intersection + "))";
        } else {
            throw new IllegalArgumentException(
                    "not a Java integral bitwise operator: " + operator);
        }
        return wrap(expression, width);
    }

    private static BigInteger integerLiteral(String expression) {
        if (expression == null) return null;
        String value = expression.trim();
        try {
            return new BigInteger(value);
        } catch (NumberFormatException ignored) {
            if (value.startsWith("(- ") && value.endsWith(")")) {
                try {
                    return new BigInteger(value.substring(3,
                            value.length() - 1).trim()).negate();
                } catch (NumberFormatException alsoNotLiteral) {
                    return null;
                }
            }
            return null;
        }
    }

    private static String normalize(String javaType) {
        String type = primitiveDescriptor(javaType);
        if (type.startsWith("L") && type.endsWith(";")
                && type.length() > 2) {
            return type.substring(1, type.length() - 1);
        }
        return type;
    }
}
