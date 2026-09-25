package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;

import edu.uva.liftlab.graphchecker.compose.VmTermLowering.Sort;


/**
 * Which {@link VmTermLowering.Sort} a recorded Java type denotes; every
 * caller reads it here.
 */
public final class JavaSmtSorts {
    private JavaSmtSorts() {
    }

    /** The sort a recorded Java type or descriptor denotes. */
    public static Sort sortOfJava(String type) {
        if (type == null) return Sort.VALUE;
        String normalized = type.replace('.', '/');
        Sort container = containerSort(normalized);
        if (container != Sort.VALUE) return container;
        String className = normalized.startsWith("L")
                && normalized.endsWith(";") && normalized.length() > 2
                ? normalized.substring(1, normalized.length() - 1)
                : normalized;
        if ("Z".equals(type) || "boolean".equals(type)) return Sort.BOOL;
        if ("B".equals(type) || "C".equals(type)
                || "S".equals(type) || "I".equals(type)
                || "J".equals(type)
                || "byte".equals(type) || "char".equals(type)
                || "short".equals(type) || "int".equals(type)
                || "long".equals(type)) return Sort.INT;
        if ("F".equals(type) || "float".equals(type)) return Sort.FLOAT32;
        if ("D".equals(type) || "double".equals(type)) return Sort.FLOAT64;
        if ("java/lang/Boolean".equals(className)) return Sort.BOOL;
        if ("java/lang/Byte".equals(className)
                || "java/lang/Character".equals(className)
                || "java/lang/Short".equals(className)
                || "java/lang/Integer".equals(className)
                || "java/lang/Long".equals(className)) return Sort.INT;
        if ("java/lang/Float".equals(className)) return Sort.FLOAT32;
        if ("java/lang/Double".equals(className)) return Sort.FLOAT64;
        if ("String".equals(className)
                || "java/lang/String".equals(className)) return Sort.STRING;
        if (type.isEmpty()) return Sort.VALUE;
        return Sort.REF;
    }

    /** The sort one JVM cast descriptor denotes. */
    public static Sort castSort(String descriptor) {
        if (descriptor == null) return Sort.VALUE;
        if ("Z".equals(descriptor) || "B".equals(descriptor)
                || "C".equals(descriptor) || "S".equals(descriptor)
                || "I".equals(descriptor) || "J".equals(descriptor)) {
            return Sort.INT;
        }
        if ("F".equals(descriptor)) return Sort.FLOAT32;
        if ("D".equals(descriptor)) return Sort.FLOAT64;
        if (descriptor.startsWith("L") || descriptor.startsWith("[")) {
            return Sort.REF;
        }
        return Sort.VALUE;
    }

    private static Sort containerSort(String type) {
        JavaContainerTypes.Shape shape = JavaContainerTypes.shape(type);
        return shape == JavaContainerTypes.Shape.ASSOCIATIVE ? Sort.MAP
                : shape == JavaContainerTypes.Shape.INDEXED
                ? Sort.ARRAY_VALUE : Sort.VALUE;
    }

}
