package edu.uva.liftlab.graphchecker.smt;


import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.TimeUnit;

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

    /** {@code Long.MAX_VALUE}, as an SMT-LIB numeral. */
    private static final String JAVA_LONG_MAX = "9223372036854775807";

    /**
     * A CLOCK cell's domain {@code [floor, ceiling]} in its ticks, the one spelling
     * for {@code explore.FlipQuery} and {@code compose.Composer}.  The floor
     * is the cell's own reading (a clock never turns back); the ceiling is
     * {@link #clockSkewCeiling}.  Both bounds are needed: no ceiling lets z3
     * pass {@code 2^63}, a floor of 0 lets it park models near 1970.
     */
    public static String clockDomain(String variable, String floor,
                                     String ceiling) {
        return "(and (>= " + variable + " " + floor + ") (<= " + variable
                + " " + ceiling + "))";
    }

    /** Default forward clock window, 30 days; override in root-domains.jsonl. */
    public static final long CLOCK_SKEW_WINDOW_NANOS = TimeUnit.DAYS.toNanos(30);

    /**
     * One span of time in the ticks of a clock whose tick is {@code
     * clockNanos} nanoseconds ({@code RootMintRow#clockNanos}).  In
     * milliseconds for every clock, a {@code nanoTime} reading could move
     * 2.6 seconds, never the hour of SOLR-18406's commit reservation.
     */
    public static long clockTicks(long nanos, long clockNanos) {
        if (clockNanos <= 0L) {
            throw new IllegalArgumentException("a clock's tick is a positive"
                    + " number of nanoseconds: " + clockNanos);
        }
        return nanos / clockNanos;
    }

    /**
     * {@code reading + } {@link #CLOCK_SKEW_WINDOW_NANOS} in the clock's
     * ticks.  Trap: never {@code Long.MAX_VALUE} when a reading exists --
     * the SMT sum cannot wrap but the JVM's does, so a flip would be
     * admitted by overflow.
     */
    public static String clockSkewCeiling(String reading, long clockNanos) {
        if (reading == null || reading.trim().isEmpty()) {
            return JAVA_LONG_MAX;
        }
        try {
            BigInteger instant = new BigInteger(reading.trim());
            if (instant.signum() < 0 || !fitsJavaLong(instant)) {
                return JAVA_LONG_MAX;
            }
            BigInteger ceiling = instant.add(BigInteger.valueOf(
                    clockTicks(CLOCK_SKEW_WINDOW_NANOS, clockNanos)));
            return fitsJavaLong(ceiling) ? ceiling.toString()
                    : JAVA_LONG_MAX;
        } catch (NumberFormatException notAnInstant) {
            return JAVA_LONG_MAX;
        }
    }

    /** Whether this decimal is a value a Java {@code long} can hold. */
    public static boolean fitsJavaLong(BigInteger value) {
        return value != null
                && value.bitLength() < Long.SIZE;
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
     * THE type-name normalisation (shell removed, dotted), shared by
     * {@link JavaPrimitiveBoxing} and {@link JavaContainerTypes}.
     */
    public static String typeName(String javaType) {
        String value = javaType == null ? "" : javaType.trim();
        if (value.startsWith("L") && value.endsWith(";")) {
            value = value.substring(1, value.length() - 1);
        }
        return value.replace('/', '.');
    }

    /** Whether one Java type name IS a primitive (not a wrapper). */
    public static boolean primitive(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        return descriptor.length() == 1 && "ZBCSIJFD".contains(descriptor);
    }

    public static IntegralWidth widthOfJavaType(String javaType) {
        IntegralDomain domain = domainOfJavaType(javaType);
        return domain == null ? IntegralWidth.NONE : domain.width;
    }

    private static FloatingKind floatingKindOfJavaType(String javaType) {
        String type = normalize(javaType);
        if ("F".equals(type) || "java.lang.Float".equals(type)) {
            return FloatingKind.JAVA_FLOAT;
        }
        if ("D".equals(type) || "java.lang.Double".equals(type)) {
            return FloatingKind.JAVA_DOUBLE;
        }
        return FloatingKind.NONE;
    }

    /**
     * One recorded decimal integer as SMT-LIB spells it ({@code (- N)} when
     * negative), or "" when the text is not one.
     */
    public static String integralLiteral(String value) {
        String text = value == null ? "" : value.trim();
        // An absurdly long run is no value any execution produced.
        if (text.isEmpty() || text.length() > 1024) return "";
        try {
            BigInteger number = new BigInteger(text);
            return number.signum() < 0
                    ? "(- " + number.negate() + ")" : number.toString();
        } catch (NumberFormatException notAnInteger) {
            return "";
        }
    }

    /** The VM's F/D literal as raw IEEE bits, parsed exactly as replay does. */
    public static String floatingLiteral(String value, FloatingKind kind) {
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

    public static String floatingNegate(String operand) {
        return "(fp.neg " + operand + ")";
    }

    public static String floatingComparison(String operator, String left,
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

    public static String floatingArithmetic(String operator, String left,
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
    public static String floatingCompareResult(String left, String right,
                                        boolean nanIsGreater) {
        String nanResult = nanIsGreater ? "1" : "(- 1)";
        return "(ite (or (fp.isNaN " + left + ") (fp.isNaN " + right
                + ")) " + nanResult + " (ite (fp.lt " + left + " "
                + right + ") (- 1) (ite (fp.gt " + left + " " + right
                + ") 1 0)))";
    }

    /** Exact JVM {@code lcmp} result in the shared mathematical-Int model. */
    public static String integralCompareResult(String left, String right) {
        return "(ite (< " + left + " " + right + ") (- 1)"
                + " (ite (> " + left + " " + right + ") 1 0))";
    }

    public static String floatingConversion(String value, FloatingKind source,
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

    public static String integralToFloating(String value, FloatingKind target) {
        if (target == FloatingKind.JAVA_FLOAT) {
            return "((_ to_fp 8 24) RNE (to_real " + value + "))";
        }
        if (target == FloatingKind.JAVA_DOUBLE) {
            return "((_ to_fp 11 53) RNE (to_real " + value + "))";
        }
        return null;
    }

    /** One Java primitive conversion, with no fresh SMT value. */
    public static String primitiveCast(String value, String sourceJavaType,
                                String targetJavaType) {
        String source = javaTypeDescriptor(sourceJavaType);
        String target = javaTypeDescriptor(targetJavaType);
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

    public static boolean primitiveNumericDescriptor(String descriptor) {
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
        if ("Z".equals(type) || "java.lang.Boolean".equals(type)) {
            return new IntegralDomain("0", "1", IntegralWidth.JAVA_INT);
        }
        if ("B".equals(type) || "java.lang.Byte".equals(type)) {
            return new IntegralDomain("(- 128)", "127",
                    IntegralWidth.JAVA_INT);
        }
        if ("C".equals(type) || "java.lang.Character".equals(type)) {
            return new IntegralDomain("0", "65535",
                    IntegralWidth.JAVA_INT);
        }
        if ("S".equals(type) || "java.lang.Short".equals(type)) {
            return new IntegralDomain("(- 32768)", "32767",
                    IntegralWidth.JAVA_INT);
        }
        if ("I".equals(type) || "java.lang.Integer".equals(type)) {
            return new IntegralDomain("(- 2147483648)", "2147483647",
                    IntegralWidth.JAVA_INT);
        }
        if ("J".equals(type) || "java.lang.Long".equals(type)) {
            return new IntegralDomain("(- 9223372036854775808)",
                    "9223372036854775807", IntegralWidth.JAVA_LONG);
        }
        return null;
    }

    /** Java binary numeric promotion, but only when both widths are known. */
    public static IntegralWidth promote(IntegralWidth left, IntegralWidth right) {
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

    public static String wrap(String expression, IntegralWidth width) {
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
    public static String bitwise(String operator, String left, String right,
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
    public static String shift(String operator, String left, String right,
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

    /** Java {@code /} (JLS 15.17.2): truncates toward zero, unlike SMT div. */
    public static String integralDivision(String left, String right,
                                   IntegralWidth width) {
        return wrap("(let ((java_idiv_a " + left + ")"
                + " (java_idiv_b " + right + "))"
                + " (ite (>= java_idiv_a 0) (div java_idiv_a java_idiv_b)"
                + " (- (div (- java_idiv_a) java_idiv_b))))", width);
    }

    /** Java {@code %} (JLS 15.17.3): the dividend's sign, unlike SMT mod. */
    public static String integralRemainder(String left, String right,
                                    IntegralWidth width) {
        return wrap("(let ((java_irem_a " + left + ")"
                + " (java_irem_b " + right + "))"
                + " (ite (>= java_irem_a 0) (mod java_irem_a java_irem_b)"
                + " (- (mod (- java_irem_a) java_irem_b))))", width);
    }

    /**
     * Definedness of Java {@code /} or {@code %}: the divisor is non-zero
     * (SMT-LIB leaves division by zero uninterpreted; Java throws).
     */
    public static String integralDivisorDefined(String right) {
        BigInteger literal = integerLiteral(right);
        if (literal != null) {
            return literal.signum() == 0 ? "false" : "true";
        }
        return "(not (= " + right + " 0))";
    }

    /** Exact Java integral complement. */
    public static String complement(String operand, IntegralWidth width) {
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

    /** The VM spells {@code iushr}/{@code lushr} as {@code >>u}; Java as {@code >>>}. */
    public static String canonicalVmOperator(String operator) {
        return ">>u".equals(operator) ? ">>>" : operator;
    }

    /**
     * A bitwise operator against a constant mask, in integer arithmetic: the
     * operand's unsigned value bound ONCE by a {@code let}, each bit the mask
     * selects read off it.  Spelled out per bit, the operand's text was
     * copied once per bit, and an operand that is itself such a term grew
     * by that factor at every level: hdfs-17960 e2's flip queries were one
     * 75 MB {@code define-fun} (a snapshot id packed by shifts and masks,
     * one variable spelled 377,858 times) that took 60-77 s to lower and 6
     * GB of heap before z3 parsed it.  z3 shares the bound term either way.
     */
    private static String constantBitwise(String operator, String variable,
                                          BigInteger rawMask,
                                          IntegralWidth width) {
        int bits = bits(width);
        BigInteger modulus = BigInteger.ONE.shiftLeft(bits);
        BigInteger mask = rawMask.mod(modulus);
        String unsigned = "java_bits_u";
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
        return wrap("(let ((" + unsigned + " (mod " + variable + " "
                + modulus + "))) " + expression + ")", width);
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

    /** The descriptor, with its shell removed. */
    private static String normalize(String javaType) {
        return typeName(javaTypeDescriptor(javaType));
    }
}
