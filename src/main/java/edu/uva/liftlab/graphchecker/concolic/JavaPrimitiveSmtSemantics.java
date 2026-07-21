package edu.uva.liftlab.graphchecker.concolic;

import java.util.Locale;

/**
 * Shared SMT semantics for Java's integral computational types.
 *
 * <p>Both concolic encoders use SMT {@code Int} as their transport sort.  A
 * width therefore has to travel beside the SMT sort: otherwise an {@code
 * iadd} and an {@code ladd} are indistinguishable and silently acquire
 * unbounded mathematical-integer semantics.  Widths are admitted only from
 * explicit Java types (or from operations whose operands already carry such
 * widths).</p>
 */
final class JavaPrimitiveSmtSemantics {
    static final String INT_WRAP_DEFINITION =
            "(define-fun java_int_wrap ((i Int)) Int"
                    + " (- (mod (+ i 2147483648) 4294967296)"
                    + " 2147483648))";
    static final String LONG_WRAP_DEFINITION =
            "(define-fun java_long_wrap ((i Int)) Int"
                    + " (- (mod (+ i 9223372036854775808)"
                    + " 18446744073709551616) 9223372036854775808))";

    enum IntegralWidth {
        NONE,
        JAVA_INT,
        JAVA_LONG
    }

    /** Java's two binary IEEE-754 computational formats. */
    enum FloatingKind {
        NONE("", 0),
        JAVA_FLOAT("(_ FloatingPoint 8 24)", 32),
        JAVA_DOUBLE("(_ FloatingPoint 11 53)", 64);

        final String smtSort;
        final int bitWidth;

        FloatingKind(String smtSort, int bitWidth) {
            this.smtSort = smtSort;
            this.bitWidth = bitWidth;
        }
    }

    static final class IntegralDomain {
        final String lower;
        final String upper;
        final IntegralWidth width;

        private IntegralDomain(String lower, String upper,
                               IntegralWidth width) {
            this.lower = lower;
            this.upper = upper;
            this.width = width;
        }
    }

    private JavaPrimitiveSmtSemantics() {
    }

    static IntegralWidth widthOfJavaType(String javaType) {
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

    /** Java binary numeric promotion for already-floating operands. */
    static FloatingKind promote(FloatingKind left, FloatingKind right) {
        if (left == null || right == null || left == FloatingKind.NONE
                || right == FloatingKind.NONE) {
            return FloatingKind.NONE;
        }
        return left == FloatingKind.JAVA_DOUBLE
                || right == FloatingKind.JAVA_DOUBLE
                ? FloatingKind.JAVA_DOUBLE : FloatingKind.JAVA_FLOAT;
    }

    /**
     * Encodes the VM's decimal F/D literal by first asking Java to perform
     * exactly the same decimal-to-binary conversion used by replay, then
     * supplying those raw IEEE bits to SMT.  This preserves NaN, infinities,
     * subnormals and the sign of zero; no mathematical-Real approximation is
     * involved.
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

    /**
     * Exact JVM {@code fcmp*}/{@code dcmp*} result.  These bytecodes produce
     * the Java {@code int} trichotomy value -1/0/1; their two variants differ
     * only in the value chosen when either operand is NaN.  Keeping that
     * result as an SMT term lets the following {@code if*} opcode express its
     * real guard instead of freezing the one concrete comparison witnessed
     * during tracing.
     */
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
     * value.  The source and target descriptors are part of the operation's
     * semantics: the common SMT {@code Int} transport sort alone cannot
     * distinguish {@code l2i}, {@code i2b}, and {@code i2l}.
     *
     * <p>The returned term implements the JVM conversion instructions (and
     * the corresponding JLS narrowing conversions) exactly.  Integral
     * narrowing retains the low bits, IEEE-754 conversions use round-to-
     * nearest/ties-to-even, and floating-to-integral conversion uses Java's
     * NaN-zero, round-toward-zero, and saturation rules.  {@code null} means
     * the descriptor pair is not a supported primitive conversion.</p>
     */
    static String primitiveCast(String value, String sourceJavaType,
                                String targetJavaType) {
        String source = primitiveDescriptor(sourceJavaType);
        String target = primitiveTargetDescriptor(targetJavaType, source);
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

    /** Normalizes source descriptors emitted by both old and current VMs. */
    static String primitiveDescriptor(String javaType) {
        String type = javaType == null ? ""
                : javaType.trim().replace('.', '/');
        if ("boolean".equals(type)) return "Z";
        if ("byte".equals(type)) return "B";
        if ("char".equals(type)) return "C";
        if ("short".equals(type)) return "S";
        if ("int".equals(type)) return "I";
        if ("long".equals(type)) return "J";
        if ("float".equals(type)) return "F";
        if ("double".equals(type)) return "D";
        // Do not rewrite reference descriptors: diagnostics and legacy
        // readers rely on their exact L...; spelling.
        return type;
    }

    /**
     * Normalizes a cast target while preserving compatibility with the old
     * VM's ambiguous bare {@code L} spelling for primitive long.
     */
    static String primitiveTargetDescriptor(String javaType,
                                            String sourceDescriptor) {
        String target = primitiveDescriptor(javaType);
        return "L".equals(target)
                && primitiveNumericDescriptor(sourceDescriptor)
                ? "J" : target;
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
    static IntegralDomain domainOfJavaType(String javaType) {
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

    private static String normalize(String javaType) {
        String type = javaType == null ? ""
                : javaType.trim().replace('.', '/');
        if ("boolean".equals(type)) return "Z";
        if ("byte".equals(type)) return "B";
        if ("char".equals(type)) return "C";
        if ("short".equals(type)) return "S";
        if ("int".equals(type)) return "I";
        if ("long".equals(type)) return "J";
        if ("float".equals(type)) return "F";
        if ("double".equals(type)) return "D";
        if (type.startsWith("L") && type.endsWith(";")
                && type.length() > 2) {
            return type.substring(1, type.length() - 1);
        }
        return type;
    }
}
