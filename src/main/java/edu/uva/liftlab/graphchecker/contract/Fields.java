package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Field checks and defensive copies for the contract's immutable values;
 * construction fails closed, naming the field.
 */
final class Fields {
    private Fields() {
    }

    /** {@code value}, or a refusal naming {@code field}; an empty string is
     *  a statement. */
    static <T> T required(T value, String field) {
        if (value == null) {
            throw new IllegalArgumentException(field + " is required");
        }
        return value;
    }

    /** {@code value} trimmed, refusing null and blank, naming {@code field}. */
    static String text(String value, String field) {
        String stated = value == null ? "" : value.trim();
        if (stated.isEmpty()) {
            throw new IllegalArgumentException(field + " is required");
        }
        return stated;
    }

    /** {@code value} or null; a blank optional is no statement at all. */
    static String optional(String value) {
        if (value == null) return null;
        return value.trim().isEmpty() ? null : value;
    }

    /** {@code value}, refusing anything below 1, naming {@code field}. */
    static int ordinal(int value, String field) {
        if (value < 1) {
            throw new IllegalArgumentException(
                    field + " is 1-based; got " + value);
        }
        return value;
    }

    /**
     * The number spelled after the marker at {@code marker} (of
     * {@code markerLength} chars) to the end of {@code value}; -1 unless the
     * marker is past index 0 and followed by digits only.
     */
    static int trailingNumber(String value, int marker, int markerLength) {
        int start = marker + markerLength;
        if (marker <= 0 || start >= value.length()) return -1;
        for (int index = start; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) return -1;
        }
        return Integer.parseInt(value.substring(start));
    }

    /** {@code value}, refusing anything below 0, naming {@code field}. */
    static long nonNegative(long value, String field) {
        if (value < 0) {
            throw new IllegalArgumentException(
                    field + " cannot be negative; got " + value);
        }
        return value;
    }

    /** The same check, for an int. */
    static int nonNegative(int value, String field) {
        nonNegative((long) value, field);
        return value;
    }

    /** An unmodifiable copy; a null list is the empty one. */
    static <T> List<T> copy(List<T> values) {
        if (values == null || values.isEmpty()) {
            return Collections.emptyList();
        }
        List<T> copied = new ArrayList<>(values.size());
        for (T value : values) {
            copied.add(required(value, "list element"));
        }
        return Collections.unmodifiableList(copied);
    }

    /** An unmodifiable copy in iteration order; a null map is the empty one. */
    static <K, V> Map<K, V> copy(Map<K, V> values) {
        if (values == null || values.isEmpty()) {
            return Collections.emptyMap();
        }
        Map<K, V> copied = new LinkedHashMap<>();
        for (Map.Entry<K, V> entry : values.entrySet()) {
            copied.put(required(entry.getKey(), "map key"),
                    required(entry.getValue(), "map value"));
        }
        return Collections.unmodifiableMap(copied);
    }

    /** An unmodifiable copy in iteration order; a null set is the empty one. */
    static <T> Set<T> copy(Set<T> values) {
        if (values == null || values.isEmpty()) {
            return Collections.emptySet();
        }
        Set<T> copied = new LinkedHashSet<>();
        for (T value : values) {
            copied.add(required(value, "set element"));
        }
        return Collections.unmodifiableSet(copied);
    }
}
