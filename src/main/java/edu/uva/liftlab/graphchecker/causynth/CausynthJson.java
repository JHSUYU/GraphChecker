package edu.uva.liftlab.graphchecker.causynth;

import java.util.Collection;
import java.util.Map;

/** Deterministic JSON serialization used by Causynth static artifacts. */
public final class CausynthJson {
    private CausynthJson() {
    }

    public static String write(Object value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof String) {
            return quote((String) value);
        }
        if (value instanceof Number || value instanceof Boolean) {
            return String.valueOf(value);
        }
        if (value instanceof Map) {
            StringBuilder builder = new StringBuilder();
            builder.append('{');
            boolean first = true;
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                if (!first) {
                    builder.append(',');
                }
                first = false;
                builder.append(quote(String.valueOf(entry.getKey())));
                builder.append(':');
                builder.append(write(entry.getValue()));
            }
            builder.append('}');
            return builder.toString();
        }
        if (value instanceof Collection) {
            StringBuilder builder = new StringBuilder();
            builder.append('[');
            boolean first = true;
            for (Object item : (Collection<?>) value) {
                if (!first) {
                    builder.append(',');
                }
                first = false;
                builder.append(write(item));
            }
            builder.append(']');
            return builder.toString();
        }
        return quote(String.valueOf(value));
    }

    public static String objectWithoutNulls(Object... fields) {
        StringBuilder result = new StringBuilder("{");
        for (int index = 0; fields != null
                && index + 1 < fields.length; index += 2) {
            if (fields[index + 1] == null) continue;
            if (result.length() > 1) result.append(',');
            result.append(quote(String.valueOf(fields[index]))).append(':')
                    .append(write(fields[index + 1]));
        }
        return result.append('}').toString();
    }

    private static String quote(String value) {
        StringBuilder builder = new StringBuilder(value.length() + 16);
        builder.append('"');
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            switch (ch) {
                case '"':
                    builder.append("\\\"");
                    break;
                case '\\':
                    builder.append("\\\\");
                    break;
                case '\n':
                    builder.append("\\n");
                    break;
                case '\r':
                    builder.append("\\r");
                    break;
                case '\t':
                    builder.append("\\t");
                    break;
                default:
                    if (ch < 0x20) {
                        builder.append(String.format("\\u%04x", (int) ch));
                    } else {
                        builder.append(ch);
                    }
            }
        }
        builder.append('"');
        return builder.toString();
    }
}
