package edu.uva.liftlab.graphchecker.contract;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/** Canonical static-type classifier for the V2 container algebra. */
public final class JavaContainerTypes {
    public enum Shape {
        NONE, INDEXED, ASSOCIATIVE
    }

    private static final Set<String> INDEXED =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.List", "java.util.AbstractList",
                    "java.util.ArrayList", "java.util.Queue",
                    "java.util.Deque", "java.util.ArrayDeque")));
    private static final Set<String> ASSOCIATIVE =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Map", "java.util.HashMap",
                    "java.util.LinkedHashMap", "java.util.Set",
                    "java.util.HashSet", "java.util.LinkedHashSet")));

    private JavaContainerTypes() {
    }

    public static Shape shape(String type) {
        String value = normalize(type);
        if (value.startsWith("[") || value.endsWith("[]")) {
            return Shape.INDEXED;
        }
        if (INDEXED.contains(value)) return Shape.INDEXED;
        if (ASSOCIATIVE.contains(value)) return Shape.ASSOCIATIVE;
        return Shape.NONE;
    }

    private static String normalize(String type) {
        String value = type == null ? "" : type.trim();
        if (value.startsWith("L") && value.endsWith(";")) {
            value = value.substring(1, value.length() - 1);
        }
        return value.replace('/', '.');
    }
}
