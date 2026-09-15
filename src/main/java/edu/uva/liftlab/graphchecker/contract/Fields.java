package edu.uva.liftlab.graphchecker.contract;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Field checks and defensive copies shared by every contract value class.
 *
 * <p>The types in this package are immutable values that several modules mint
 * and several others read back out of JSON.  A field a producer leaves null is
 * a hole a consumer discovers much later, so construction refuses it here,
 * naming the field -- the fail-closed rule the design applies to evidence
 * applies to the evidence's own shape.</p>
 */
final class Fields {
    private Fields() {
    }

    /** {@code value}, or a refusal naming {@code field}. */
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

    /** {@code value}, refusing null only: an empty statement is a statement. */
    static String stated(String value, String field) {
        return required(value, field);
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

    /** {@code value}, refusing anything below 0, naming {@code field}. */
    static int count(int value, String field) {
        if (value < 0) {
            throw new IllegalArgumentException(
                    field + " cannot be negative; got " + value);
        }
        return value;
    }

    /** {@code value}, refusing anything below 0, naming {@code field}. */
    static long sequence(long value, String field) {
        if (value < 0) {
            throw new IllegalArgumentException(
                    field + " cannot be negative; got " + value);
        }
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
