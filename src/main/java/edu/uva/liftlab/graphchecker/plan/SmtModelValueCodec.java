package edu.uva.liftlab.graphchecker.plan;

import java.math.BigDecimal;
import java.math.MathContext;
import java.util.ArrayList;
import java.util.List;

/** Lossless syntax handling for the scalar values returned by Z3. */
public final class SmtModelValueCodec {
    private static final MathContext REAL_REPLAY_CONTEXT =
            MathContext.DECIMAL128;

    private SmtModelValueCodec() {
    }

    /** Converts an exact SMT Real model value to a Java decimal literal. */
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

    private static boolean numericAtom(String value) {
        return value != null && value.matches(
                "[+-]?(?:0|[1-9][0-9]*)(?:\\.[0-9]+)?"
                        + "(?:[eE][+-]?[0-9]+)?");
    }

    private static List<String> applicationArguments(String expression,
                                                     String operator) {
        List<String> items = applicationItems(expression);
        if (items == null || items.size() < 2 || operator == null
                || !operator.equals(items.get(0))) {
            return null;
        }
        return new ArrayList<>(items.subList(1, items.size()));
    }

    /** Splits one SMT application; nested terms and "" strings stay intact. */
    static List<String> applicationItems(String expression) {
        if (expression == null || expression.length() < 2
                || expression.charAt(0) != '('
                || expression.charAt(expression.length() - 1) != ')') {
            return null;
        }
        String body = expression.substring(1, expression.length() - 1)
                .trim();
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
            } else if (!quoted && current == ')' && --depth < 0) {
                return null;
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
