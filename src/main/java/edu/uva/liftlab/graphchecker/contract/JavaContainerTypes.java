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
    private static final Set<String> MAPS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Map", "java.util.HashMap",
                    "java.util.LinkedHashMap")));
    private static final Set<String> SETS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Set",
                    "java.util.HashSet", "java.util.LinkedHashSet")));
    private static final Set<String> STRUCTURAL_TRAVERSAL =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Iterator", "java.util.ListIterator",
                    "java.util.Map$Entry", "java.util.Map.Entry",
                    "java.util.Enumeration")));
    private static final Set<String> INDEXED_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean add(java.lang.Object)",
                    "boolean offer(java.lang.Object)",
                    "boolean contains(java.lang.Object)",
                    "boolean isEmpty()", "int size()",
                    "java.lang.Object element()", "java.lang.Object get(int)",
                    "java.lang.Object peek()", "java.lang.Object poll()",
                    "java.lang.Object remove()",
                    "java.lang.Object remove(int)",
                    "java.lang.Object set(int,java.lang.Object)",
                    "java.util.Iterator iterator()")));
    private static final Set<String> MAP_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean containsKey(java.lang.Object)",
                    "boolean isEmpty()", "int size()",
                    "java.lang.Object get(java.lang.Object)",
                    "java.lang.Object put(java.lang.Object,java.lang.Object)",
                    "java.lang.Object remove(java.lang.Object)",
                    "java.util.Collection values()",
                    "java.util.Set entrySet()", "java.util.Set keySet()")));
    private static final Set<String> SET_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean add(java.lang.Object)",
                    "boolean contains(java.lang.Object)",
                    "boolean isEmpty()",
                    "boolean remove(java.lang.Object)", "int size()",
                    "java.util.Iterator iterator()")));
    private static final Set<String> ITERATOR_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean hasNext()", "java.lang.Object next()")));
    private static final Set<String> ENTRY_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.lang.Object getKey()",
                    "java.lang.Object getValue()")));

    private JavaContainerTypes() {
    }

    public static Shape shape(String type) {
        String value = normalize(type);
        if (value.startsWith("[") || value.endsWith("[]")) {
            return Shape.INDEXED;
        }
        if (INDEXED.contains(value)) return Shape.INDEXED;
        if (MAPS.contains(value) || SETS.contains(value)) {
            return Shape.ASSOCIATIVE;
        }
        return Shape.NONE;
    }

    /**
     * Returns whether calls on this type select structure owned by a Java
     * container. Their reference results are projections of that structure,
     * not independent external inputs.
     */
    public static boolean structuralTraversalOwner(String type) {
        String value = normalize(type);
        return shape(value) != Shape.NONE
                || STRUCTURAL_TRAVERSAL.contains(value);
    }

    /**
     * Returns whether the exact Soot signature names a result-bearing
     * operation modeled by the custom JDK container algebra.
     */
    public static boolean symbolicResultOperation(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        if (method == null) return false;
        if (INDEXED.contains(method.owner)) {
            return INDEXED_RESULTS.contains(method.subsignature);
        }
        if (MAPS.contains(method.owner)) {
            return MAP_RESULTS.contains(method.subsignature);
        }
        if (SETS.contains(method.owner)) {
            return SET_RESULTS.contains(method.subsignature);
        }
        if ("java.util.Iterator".equals(method.owner)
                || "java.util.ListIterator".equals(method.owner)) {
            return ITERATOR_RESULTS.contains(method.subsignature);
        }
        return ("java.util.Map$Entry".equals(method.owner)
                || "java.util.Map.Entry".equals(method.owner))
                && ENTRY_RESULTS.contains(method.subsignature);
    }

    public static boolean symbolicResultReturn(String cell) {
        String value = cell == null ? "" : cell.trim();
        return value.endsWith(".return")
                && symbolicResultOperation(value.substring(
                0, value.length() - ".return".length()));
    }

    private static String normalize(String type) {
        String value = type == null ? "" : type.trim();
        if (value.startsWith("L") && value.endsWith(";")) {
            value = value.substring(1, value.length() - 1);
        }
        return value.replace('/', '.');
    }

    private static final class MethodSignature {
        private final String owner;
        private final String subsignature;

        private MethodSignature(String owner, String subsignature) {
            this.owner = owner;
            this.subsignature = subsignature;
        }

        private static MethodSignature parse(String signature) {
            String value = signature == null ? "" : signature.trim();
            int ownerEnd = value.indexOf(':');
            if (!value.startsWith("<") || !value.endsWith(">")
                    || ownerEnd <= 1) {
                return null;
            }
            String subsignature = value.substring(ownerEnd + 1,
                    value.length() - 1).trim();
            int separator = subsignature.indexOf(' ');
            if (separator <= 0 || separator + 1 >= subsignature.length()) {
                return null;
            }
            String returnType = subsignature.substring(0, separator);
            return "void".equals(returnType) ? null
                    : new MethodSignature(
                    normalize(value.substring(1, ownerEnd)),
                    subsignature);
        }
    }
}
