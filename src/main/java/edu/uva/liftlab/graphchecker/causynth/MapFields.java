package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.GZIPInputStream;

/**
 * The one JSONL-row coercion family: null, JSON {@code null} and a wrong-typed
 * member mean the same thing everywhere.
 */
public final class MapFields {
    private static final Type ROW =
            new TypeToken<Map<String, Object>>() { }.getType();
    /** Whole numbers stay whole: a row id is not a double. */
    private static final Gson ROWS = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();

    private MapFields() {
    }

    /** The one JSONL byte source: UTF-8 lines, gzip by file name. */
    public static BufferedReader rowReader(File file) throws IOException {
        InputStream bytes = Files.newInputStream(file.toPath());
        try {
            if (file.getName().endsWith(".gz")) {
                bytes = new GZIPInputStream(bytes);
            }
            return new BufferedReader(new InputStreamReader(bytes,
                    StandardCharsets.UTF_8));
        } catch (IOException refused) {
            bytes.close();
            throw refused;
        }
    }

    /** The one JSONL reader: one row per non-blank line; null refused. */
    public static List<Map<String, Object>> readRows(File file)
            throws IOException {
        List<Map<String, Object>> result = new ArrayList<>();
        try (BufferedReader lines = rowReader(file)) {
            String line;
            while ((line = lines.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                Map<String, Object> row = ROWS.fromJson(line, ROW);
                if (row == null) {
                    throw new IOException("null row in " + file);
                }
                result.add(row);
            }
        }
        return result;
    }

    /** The numeric elements of a list member; anything else is dropped. */
    public static Set<Long> longValues(Object value) {
        Set<Long> result = new LinkedHashSet<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Number) {
                    result.add(((Number) item).longValue());
                }
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    public static List<Map<String, Object>> rows(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                if (item instanceof Map<?, ?>) {
                    result.add((Map<String, Object>) item);
                }
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    public static Map<String, Object> asMap(Object value) {
        return value instanceof Map<?, ?> ? (Map<String, Object>) value : null;
    }

    public static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }

    /** {@link #text} with a JSON {@code null} literal read as absent. */
    public static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    public static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (value instanceof Collection<?>) {
            for (Object item : (Collection<?>) value) {
                String text = text(item);
                if (!text.isEmpty()) result.add(text);
            }
        }
        return result;
    }

    public static int number(Object value, int fallback) {
        return value instanceof Number ? ((Number) value).intValue() : fallback;
    }

    public static long longNumber(Object value, long fallback) {
        return value instanceof Number ? ((Number) value).longValue() : fallback;
    }

    /** A string with a null read as absent, for values already typed. */
    public static String safe(String value) {
        return value == null ? "" : value;
    }

    public static String firstNonEmpty(String left, String right) {
        return left == null || left.isEmpty() ? right : left;
    }

    /** One row from alternating key and value arguments, in that order. */
    public static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> row = new LinkedHashMap<>();
        for (int index = 0; index + 1 < keyValues.length; index += 2) {
            row.put(String.valueOf(keyValues[index]), keyValues[index + 1]);
        }
        return row;
    }

    public static Boolean booleanValue(Object value) {
        if (value instanceof Boolean) return (Boolean) value;
        if ("true".equalsIgnoreCase(text(value))) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(text(value))) return Boolean.FALSE;
        return null;
    }
}
