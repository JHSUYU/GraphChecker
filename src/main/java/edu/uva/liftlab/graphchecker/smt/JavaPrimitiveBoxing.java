package edu.uva.liftlab.graphchecker.smt;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

public final class JavaPrimitiveBoxing {
    private static final Map<String, Primitive> BY_WRAPPER;

    static {
        Map<String, Primitive> values = new LinkedHashMap<>();
        add(values, "java.lang.Boolean", "boolean", "booleanValue", "Z");
        add(values, "java.lang.Byte", "byte", "byteValue", "B");
        add(values, "java.lang.Short", "short", "shortValue", "S");
        add(values, "java.lang.Character", "char", "charValue", "C");
        add(values, "java.lang.Integer", "int", "intValue", "I");
        add(values, "java.lang.Long", "long", "longValue", "J");
        add(values, "java.lang.Float", "float", "floatValue", "F");
        add(values, "java.lang.Double", "double", "doubleValue", "D");
        BY_WRAPPER = Collections.unmodifiableMap(values);
    }

    private JavaPrimitiveBoxing() {
    }

    public static boolean unboxReturn(String cell) {
        return unboxing(returnMethod(cell));
    }

    public static boolean unboxing(String methodSignature) {
        String signature = methodSignature == null ? ""
                : methodSignature.trim();
        for (Primitive primitive : BY_WRAPPER.values()) {
            if (signature.equals("<" + primitive.wrapper + ": "
                    + primitive.javaType + " " + primitive.accessor
                    + "()>")) {
                return true;
            }
        }
        return false;
    }

    public static String valueDescriptor(String descriptor) {
        String stated = descriptor == null ? "" : descriptor.trim();
        String primitive = stated.startsWith("L") && stated.endsWith(";")
                ? primitiveDescriptor(stated) : "";
        return primitive.isEmpty() ? stated : primitive;
    }

    public static String primitiveDescriptor(String wrapperType) {
        Primitive primitive = BY_WRAPPER.get(
                JavaPrimitiveSmtSemantics.typeName(wrapperType));
        return primitive == null ? "" : primitive.descriptor;
    }

    private static void add(Map<String, Primitive> values, String wrapper,
                            String javaType, String accessor,
                            String descriptor) {
        values.put(wrapper, new Primitive(wrapper, javaType, accessor,
                descriptor));
    }

    private static String returnMethod(String cell) {
        String value = cell == null ? "" : cell.trim();
        return value.endsWith(".return")
                ? value.substring(0, value.length() - ".return".length())
                : "";
    }

    private static final class Primitive {
        private final String wrapper;
        private final String javaType;
        private final String accessor;
        private final String descriptor;

        private Primitive(String wrapper, String javaType, String accessor,
                          String descriptor) {
            this.wrapper = wrapper;
            this.javaType = javaType;
            this.accessor = accessor;
            this.descriptor = descriptor;
        }
    }
}
