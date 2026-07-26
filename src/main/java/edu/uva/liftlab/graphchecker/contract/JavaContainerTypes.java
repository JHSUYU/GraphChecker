package edu.uva.liftlab.graphchecker.contract;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/** Canonical recognition of Map declarations carried by static artifacts. */
public final class JavaContainerTypes {
    private static final Set<String> MAP_TYPES = Collections.unmodifiableSet(
            new LinkedHashSet<>(Arrays.asList(
                    "java.util.Map", "java.util.SortedMap",
                    "java.util.NavigableMap", "java.util.HashMap",
                    "java.util.LinkedHashMap", "java.util.TreeMap",
                    "java.util.Hashtable", "java.util.WeakHashMap",
                    "java.util.IdentityHashMap",
                    "java.util.concurrent.ConcurrentMap",
                    "java.util.concurrent.ConcurrentHashMap",
                    "java.util.concurrent.ConcurrentNavigableMap",
                    "java.util.concurrent.ConcurrentSkipListMap")));

    private JavaContainerTypes() {
    }

    public static boolean isMap(String type) {
        String value = type == null ? "" : type.trim();
        if (value.startsWith("L") && value.endsWith(";")) {
            value = value.substring(1, value.length() - 1)
                    .replace('/', '.');
        } else {
            value = value.replace('/', '.');
        }
        if (MAP_TYPES.contains(value)) {
            return true;
        }
        if (value.isEmpty() || value.startsWith("[")
                || value.endsWith("[]")) {
            return false;
        }
        try {
            ClassLoader loader = Thread.currentThread()
                    .getContextClassLoader();
            Class<?> declared = Class.forName(value, false,
                    loader == null ? JavaContainerTypes.class
                            .getClassLoader() : loader);
            return java.util.Map.class.isAssignableFrom(declared);
        } catch (Throwable unavailable) {
            return false;
        }
    }
}
