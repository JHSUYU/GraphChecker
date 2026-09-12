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
    private static final Set<String> CARDINALITY_OWNERS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.util.Collection", "java.util.List",
                    "java.util.AbstractList", "java.util.ArrayList",
                    "java.util.Queue", "java.util.Deque",
                    "java.util.ArrayDeque", "java.util.Set",
                    "java.util.HashSet", "java.util.LinkedHashSet",
                    "java.util.Map", "java.util.HashMap",
                    "java.util.LinkedHashMap")));
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
                    "java.util.Iterator iterator()",
                    "java.util.ListIterator listIterator()")));
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
    private static final Set<String> INDEXED_MUTATORS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean add(java.lang.Object)",
                    "boolean offer(java.lang.Object)",
                    "java.lang.Object poll()",
                    "java.lang.Object remove()",
                    "java.lang.Object remove(int)",
                    "java.lang.Object set(int,java.lang.Object)",
                    // Positional insertion and truncation return nothing, so
                    // they reach a signature parser that once rejected every
                    // void return.  They are still exact state transitions
                    // the container algebra publishes (INSERT and CLEAR).
                    "void add(int,java.lang.Object)",
                    "void clear()")));
    private static final Set<String> MAP_MUTATORS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.lang.Object put(java.lang.Object,java.lang.Object)",
                    "java.lang.Object remove(java.lang.Object)")));
    private static final Set<String> SET_MUTATORS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean add(java.lang.Object)",
                    "boolean remove(java.lang.Object)")));
    private static final Set<String> ITERATOR_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "boolean hasNext()", "java.lang.Object next()",
                    "int nextIndex()")));
    private static final Set<String> ENTRY_RESULTS =
            Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(
                    "java.lang.Object getKey()",
                    "java.lang.Object getValue()")));

    private JavaContainerTypes() {
    }

    /**
     * The shape of one declared field type whose WHOLE state a selected
     * carrier versions, or {@link Shape#NONE} when the field is a reference
     * slot instead.
     *
     * <p>This is deliberately narrower than {@link #shape(String)}: arrays
     * already have their own element locations, and a set is not versioned
     * whole by any carrier this build selects.  It is also deliberately
     * name-based rather than reflective, so the answer does not depend on
     * which types happen to be loadable in the deciding JVM.</p>
     */
    public static Shape wholeStateShape(String type) {
        String value = erase(normalize(type));
        if (value.isEmpty() || value.startsWith("[")
                || value.endsWith("[]")) {
            return Shape.NONE;
        }
        if (INDEXED.contains(value)) return Shape.INDEXED;
        return MAPS.contains(value) ? Shape.ASSOCIATIVE : Shape.NONE;
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

    /** Whether the exact Soot signature names a result-bearing operation
     *  modeled by the custom JDK container algebra. */
    public static boolean symbolicResultOperation(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        if (method == null) return false;
        if (modeledContainerOperation(method)) return true;
        if ("java.util.Iterator".equals(method.owner)
                || "java.util.ListIterator".equals(method.owner)) {
            return ITERATOR_RESULTS.contains(method.subsignature);
        }
        return ("java.util.Map$Entry".equals(method.owner)
                || "java.util.Map.Entry".equals(method.owner))
                && ENTRY_RESULTS.contains(method.subsignature);
    }

    private static boolean modeledContainerOperation(MethodSignature method) {
        if (INDEXED.contains(method.owner)) {
            return INDEXED_RESULTS.contains(method.subsignature);
        }
        if (MAPS.contains(method.owner)) {
            return MAP_RESULTS.contains(method.subsignature);
        }
        return SETS.contains(method.owner)
                && SET_RESULTS.contains(method.subsignature);
    }

    /** Exact state-changing operation already modeled by the container algebra. */
    public static boolean modeledContainerMutator(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        if (method == null) {
            return false;
        }
        if (INDEXED.contains(method.owner)) {
            return INDEXED_MUTATORS.contains(method.subsignature);
        }
        if (MAPS.contains(method.owner)) {
            return MAP_MUTATORS.contains(method.subsignature);
        }
        return SETS.contains(method.owner)
                && SET_MUTATORS.contains(method.subsignature);
    }

    /** Exact associative insertion whose receiver/key/value identify a member. */
    public static boolean associativePut(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        return method != null && MAPS.contains(method.owner)
                && "java.lang.Object put(java.lang.Object,java.lang.Object)"
                .equals(method.subsignature);
    }

    /**
     * Exact predicates whose value is the position of a structural traversal
     * rather than an element's semantic state.  A failure-directed loop may
     * observe them, but changing one would change the frozen container shape
     * instead of exercising a data decision inside the loop.
     */
    public static boolean structuralIterationPredicate(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        if (method == null) return false;
        if ("java.util.Iterator".equals(method.owner)) {
            return "boolean hasNext()".equals(method.subsignature);
        }
        if ("java.util.ListIterator".equals(method.owner)) {
            return "boolean hasNext()".equals(method.subsignature)
                    || "boolean hasPrevious()".equals(
                    method.subsignature);
        }
        return "java.util.Enumeration".equals(method.owner)
                && "boolean hasMoreElements()".equals(
                method.subsignature);
    }

    /** Exact collection operations which expose only cardinality. */
    public static boolean structuralCardinalityOperation(String signature) {
        MethodSignature method = MethodSignature.parse(signature);
        return method != null && CARDINALITY_OWNERS.contains(method.owner)
                && ("int size()".equals(method.subsignature)
                || "boolean isEmpty()".equals(method.subsignature));
    }

    public static boolean symbolicResultReturn(String cell) {
        String value = cell == null ? "" : cell.trim();
        return value.endsWith(".return")
                && symbolicResultOperation(value.substring(
                0, value.length() - ".return".length()));
    }

    /** Drops a generic argument list, which a declared type may carry. */
    private static String erase(String type) {
        String value = type == null ? "" : type.trim();
        int generic = value.indexOf('<');
        return generic < 0 ? value : value.substring(0, generic).trim();
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
            // A void return is not a parse failure.  Every result-bearing
            // predicate matches against a set whose members all name their
            // return type, so a void subsignature can only match an
            // operation that is genuinely declared void - today the indexed
            // mutators add(int,E) and clear().
            return new MethodSignature(
                    normalize(value.substring(1, ownerEnd)),
                    subsignature);
        }
    }
}
