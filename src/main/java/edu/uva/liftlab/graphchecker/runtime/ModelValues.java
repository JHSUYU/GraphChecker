package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

import edu.uva.liftlab.graphchecker.plan.SmtModelValueCodec;

final class ModelValues {
    private ModelValues() {
    }

    enum UnsupportedReplayValue { INSTANCE }

    static Object coerce(String valueType, String value,
                         Class<?> requestedType) {
        String type = nonNull(valueType).toUpperCase();
        String raw = nonNull(value).trim();
        try {
            if ((requestedType == null || !requestedType.isPrimitive())
                    && ("NULL".equals(type)
                    || "null".equalsIgnoreCase(raw))) {
                return null;
            }
            if (requestedType == boolean.class
                    || requestedType == Boolean.class
                    || "BOOL".equals(type)) {
                return "true".equalsIgnoreCase(raw) || "1".equals(raw);
            }
            if (requestedType == byte.class || requestedType == Byte.class) {
                return Byte.valueOf(raw);
            }
            if (requestedType == short.class || requestedType == Short.class) {
                return Short.valueOf(raw);
            }
            if (requestedType == char.class
                    || requestedType == Character.class) {
                return raw.length() == 1 ? raw.charAt(0)
                        : (char) Integer.parseInt(raw);
            }
            if (requestedType == int.class || requestedType == Integer.class) {
                return Integer.valueOf(raw);
            }
            if (requestedType == long.class || requestedType == Long.class
                    || "INT".equals(type) && requestedType == null) {
                return Long.valueOf(raw);
            }
            if (requestedType == float.class || requestedType == Float.class) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Float.valueOf(decimal);
            }
            if (requestedType == double.class || requestedType == Double.class
                    || "REAL".equals(type) && requestedType == null) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Double.valueOf(decimal);
            }
            if (requestedType == String.class || "STRING".equals(type)) {
                return SmtModelValueCodec.decodeString(raw);
            }
        } catch (RuntimeException ignored) {
            return UnsupportedReplayValue.INSTANCE;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    static boolean isPrimitiveBox(Object value) {
        return value instanceof Boolean || value instanceof Byte
                || value instanceof Short || value instanceof Character
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double;
    }
}
