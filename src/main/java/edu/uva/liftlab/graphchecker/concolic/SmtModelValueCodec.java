package edu.uva.liftlab.graphchecker.concolic;

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * Lossless syntax handling for the scalar values returned by Z3.
 *
 * <p>This class deliberately accepts only the small, exact SMT value grammar
 * that the replay layer understands: decimal/integer atoms, unary minus,
 * rational division, booleans, and SMT-LIB quoted strings.  Algebraic or
 * otherwise unfamiliar model values are rejected instead of being rewritten
 * into a different Java value.</p>
 */
public final class SmtModelValueCodec {
    private static final MathContext REAL_REPLAY_CONTEXT =
            MathContext.DECIMAL128;

    private SmtModelValueCodec() {
    }

    /** Flattens only an ordinary unary-negative numeric atom. */
    public static String normalizeScalar(String value) {
        String raw = value == null ? "" : value.trim();
        List<String> negative = applicationArguments(raw, "-");
        if (negative != null && negative.size() == 1
                && numericAtom(negative.get(0))) {
            try {
                return new BigDecimal(negative.get(0)).negate()
                        .toPlainString();
            } catch (NumberFormatException ignored) {
                return raw;
            }
        }
        return raw;
    }

    /**
     * Converts an exact SMT Real model value to a Java decimal literal.
     * Returns {@code null} for an unsupported expression, division by zero,
     * or a value that cannot be represented as a finite Java double.
     */
    public static String realToJavaLiteral(String value) {
        String raw = value == null ? "" : value.trim();
        if ("NaN".equals(raw) || "Infinity".equals(raw)
                || "-Infinity".equals(raw)) return raw;
        if (raw.matches("-0(?:\\.0+)?(?:[eE][+-]?0+)?")) return "-0.0";
        BigDecimal decimal = real(raw, 0);
        if (decimal == null) return null;
        double represented = decimal.doubleValue();
        if (Double.isNaN(represented) || Double.isInfinite(represented)) {
            return null;
        }
        return Double.toString(represented);
    }

    /**
     * Decodes the exact bit-vector returned by {@code fp.to_ieee_bv} into a
     * Java parser literal.  Java's decimal rendering round-trips every finite
     * value; the named spellings preserve NaN, infinities, and signed zero.
     */
    public static String floatingPointBitsToJavaLiteral(String value,
                                                        String descriptor) {
        String raw = value == null ? "" : value.trim();
        int width = "F".equals(descriptor) ? 32
                : "D".equals(descriptor) ? 64 : 0;
        if (width == 0) return null;
        BigInteger bits = bitVector(raw, width);
        if (bits == null) return null;
        if (width == 32) {
            float decoded = Float.intBitsToFloat(bits.intValue());
            if (Float.isNaN(decoded)) return "NaN";
            if (decoded == Float.POSITIVE_INFINITY) return "Infinity";
            if (decoded == Float.NEGATIVE_INFINITY) return "-Infinity";
            return Float.toString(decoded);
        }
        double decoded = Double.longBitsToDouble(bits.longValue());
        if (Double.isNaN(decoded)) return "NaN";
        if (decoded == Double.POSITIVE_INFINITY) return "Infinity";
        if (decoded == Double.NEGATIVE_INFINITY) return "-Infinity";
        return Double.toString(decoded);
    }

    /** Decodes the canonical FP terms printed by Z3 {@code get-value}. */
    public static String floatingPointTermToJavaLiteral(String value,
                                                        String descriptor) {
        String raw = value == null ? "" : value.trim();
        String direct = floatingPointBitsToJavaLiteral(raw, descriptor);
        if (direct != null) return direct;
        int exponentWidth = "F".equals(descriptor) ? 8
                : "D".equals(descriptor) ? 11 : 0;
        int significandWidth = "F".equals(descriptor) ? 23
                : "D".equals(descriptor) ? 52 : 0;
        if (exponentWidth == 0) return null;

        List<String> special = applicationArguments(raw, "_");
        if (special != null && special.size() == 3
                && Integer.toString(exponentWidth).equals(special.get(1))
                && Integer.toString(significandWidth + 1).equals(
                special.get(2))) {
            if ("+zero".equals(special.get(0))) return "0.0";
            if ("-zero".equals(special.get(0))) return "-0.0";
            if ("+oo".equals(special.get(0))) return "Infinity";
            if ("-oo".equals(special.get(0))) return "-Infinity";
            if ("NaN".equals(special.get(0))) return "NaN";
        }

        List<String> fields = applicationArguments(raw, "fp");
        if (fields == null || fields.size() != 3) return null;
        String sign = bitString(fields.get(0), 1);
        String exponent = bitString(fields.get(1), exponentWidth);
        String significand = bitString(fields.get(2), significandWidth);
        if (sign == null || exponent == null || significand == null) {
            return null;
        }
        BigInteger bits = new BigInteger(sign + exponent + significand, 2);
        String hex = bits.toString(16);
        int digits = (1 + exponentWidth + significandWidth) / 4;
        StringBuilder padded = new StringBuilder("#x");
        for (int index = hex.length(); index < digits; index++) {
            padded.append('0');
        }
        return floatingPointBitsToJavaLiteral(padded.append(hex).toString(),
                descriptor);
    }

    /** Decodes SMT-LIB's doubled-quote escaping. */
    public static String decodeString(String value) {
        String raw = value == null ? "" : value;
        if (raw.length() >= 2 && raw.charAt(0) == '"'
                && raw.charAt(raw.length() - 1) == '"') {
            raw = raw.substring(1, raw.length() - 1);
        }
        return raw.replace("\"\"", "\"");
    }

    private static BigDecimal real(String expression, int depth) {
        if (depth > 16) return null;
        String raw = expression == null ? "" : expression.trim();
        if (numericAtom(raw)) {
            try {
                return new BigDecimal(raw);
            } catch (NumberFormatException ignored) {
                return null;
            }
        }
        List<String> negative = applicationArguments(raw, "-");
        if (negative != null && negative.size() == 1) {
            BigDecimal operand = real(negative.get(0), depth + 1);
            return operand == null ? null : operand.negate();
        }
        List<String> quotient = applicationArguments(raw, "/");
        if (quotient != null && quotient.size() == 2) {
            BigDecimal numerator = real(quotient.get(0), depth + 1);
            BigDecimal denominator = real(quotient.get(1), depth + 1);
            if (numerator == null || denominator == null
                    || denominator.signum() == 0) {
                return null;
            }
            return numerator.divide(denominator, REAL_REPLAY_CONTEXT);
        }
        return null;
    }

    private static BigInteger bitVector(String value, int width) {
        try {
            if (value.startsWith("#x")
                    && value.length() == 2 + width / 4) {
                return new BigInteger(value.substring(2), 16);
            }
            if (value.startsWith("#b")
                    && value.length() == 2 + width) {
                return new BigInteger(value.substring(2), 2);
            }
            List<String> bv = applicationArguments(value, "_");
            if (bv != null && bv.size() == 2
                    && bv.get(0).startsWith("bv")
                    && Integer.toString(width).equals(bv.get(1))) {
                BigInteger result = new BigInteger(
                        bv.get(0).substring(2));
                return result.signum() >= 0
                        && result.bitLength() <= width ? result : null;
            }
        } catch (RuntimeException malformed) {
            return null;
        }
        return null;
    }

    private static String bitString(String value, int width) {
        String raw = value == null ? "" : value.trim();
        String bits;
        if (raw.startsWith("#b")) {
            bits = raw.substring(2);
        } else if (raw.startsWith("#x")) {
            try {
                bits = new BigInteger(raw.substring(2), 16).toString(2);
            } catch (RuntimeException malformed) {
                return null;
            }
        } else {
            return null;
        }
        if (bits.length() > width) return null;
        StringBuilder result = new StringBuilder(width);
        for (int index = bits.length(); index < width; index++) {
            result.append('0');
        }
        return result.append(bits).toString();
    }

    private static boolean numericAtom(String value) {
        return value != null && value.matches(
                "[+-]?(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?"
                        + "(?:[eE][+-]?[0-9]+)?");
    }

    private static List<String> applicationArguments(String expression,
                                                     String operator) {
        if (expression == null || operator == null
                || expression.length() < operator.length() + 3
                || expression.charAt(0) != '('
                || expression.charAt(expression.length() - 1) != ')') {
            return null;
        }
        String body = expression.substring(1, expression.length() - 1)
                .trim();
        if (!body.startsWith(operator)
                || body.length() == operator.length()
                || !Character.isWhitespace(body.charAt(operator.length()))) {
            return null;
        }
        body = body.substring(operator.length()).trim();
        List<String> result = new ArrayList<>();
        int start = -1;
        int depth = 0;
        boolean quoted = false;
        for (int index = 0; index <= body.length(); index++) {
            char current = index == body.length() ? ' ' : body.charAt(index);
            if (current == '"') {
                if (quoted && index + 1 < body.length()
                        && body.charAt(index + 1) == '"') {
                    index++;
                } else {
                    quoted = !quoted;
                }
            } else if (!quoted && current == '(') {
                depth++;
            } else if (!quoted && current == ')') {
                if (--depth < 0) return null;
            }
            boolean separator = !quoted && depth == 0
                    && Character.isWhitespace(current);
            if (start < 0) {
                if (!separator) start = index;
            } else if (separator) {
                result.add(body.substring(start, index));
                start = -1;
            }
        }
        return quoted || depth != 0 ? null : result;
    }
}
