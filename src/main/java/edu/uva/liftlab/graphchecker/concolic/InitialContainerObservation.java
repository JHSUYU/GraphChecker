package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Recognizes sparse initial-container reads and their concrete replay
 * observations.
 *
 * <p>The VM records {@code READ(initialState, selector) == concreteValue} so
 * a path can be replayed. That equality is a materialization observation,
 * not part of the region's symbolic relation. Only a concrete array/list
 * index or primitive/String map key is replayable.</p>
 */
final class InitialContainerObservation {
    private InitialContainerObservation() {
    }

    static Read initialRead(JsonObject expression) {
        if (expression == null
                || !"ContainerRelation".equals(string(expression, "_type"))) {
            return null;
        }
        String shape = string(expression, "shape");
        String operation = string(expression, "operation");
        if (!"INDEXED".equals(shape) && !"ASSOCIATIVE".equals(shape)) {
            return null;
        }
        if (!"READ".equals(operation) && !"NEXT".equals(operation)) {
            return null;
        }
        String iterationProjection = "ASSOCIATIVE".equals(shape)
                && "NEXT".equals(operation)
                ? iterationProjection(expression.get("receiver")) : "";
        if ("ASSOCIATIVE".equals(shape) && "NEXT".equals(operation)
                && iterationProjection.isEmpty()) {
            return null;
        }
        JsonObject state = initialState(expression.get("receiver"), shape,
                !iterationProjection.isEmpty());
        if (!"ContainerRelation".equals(string(state, "_type"))
                || !shape.equals(string(state, "shape"))
                || !"STATE".equals(string(state, "operation"))) {
            return null;
        }
        JsonObject identity = object(state, "receiver");
        String symbol = "SymbolExpression".equals(string(identity, "_type"))
                ? string(identity, "_exp") : "";
        String inputPort = inputPort(symbol);
        if (inputPort.isEmpty()) {
            return null;
        }
        JsonArray arguments = JsonFields.array(expression, "arguments");
        JsonObject selector = arguments.size() == 1
                && concreteScalar(arguments.get(0))
                ? arguments.get(0).getAsJsonObject() : null;
        Integer index = ("INDEXED".equals(shape)
                || !iterationProjection.isEmpty()) && selector != null
                ? concreteIndex(selector) : null;
        if ("ASSOCIATIVE".equals(shape)
                && iterationProjection.isEmpty() && selector != null
                && !replayableMapKey(selector)) {
            selector = null;
        }
        return new Read(shape, symbol, inputPort, index, selector,
                iterationProjection, string(expression, "_java_type"));
    }

    private static JsonObject initialState(JsonElement expression,
                                           String shape,
                                           boolean allowView) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            if (!"ContainerRelation".equals(string(relation, "_type"))
                    || !shape.equals(string(relation, "shape"))) {
                return new JsonObject();
            }
            String operation = string(relation, "operation");
            if ("STATE".equals(operation)) return relation;
            if (!"ITERATOR".equals(operation)
                    && !(allowView && ("KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)))) {
                return new JsonObject();
            }
            cursor = relation.get("receiver");
        }
        return new JsonObject();
    }

    private static String iterationProjection(JsonElement expression) {
        JsonElement cursor = expression;
        String projection = "";
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            if (!"ContainerRelation".equals(string(relation, "_type"))
                    || !"ASSOCIATIVE".equals(string(relation, "shape"))) {
                return "";
            }
            String operation = string(relation, "operation");
            if ("KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) {
                String candidate = "KEY_VIEW".equals(operation)
                        ? "KEY" : "VALUE";
                if (!projection.isEmpty()
                        && !projection.equals(candidate)) {
                    return "";
                }
                projection = candidate;
            } else if (!"ITERATOR".equals(operation)
                    && !"STATE".equals(operation)) {
                return "";
            }
            if ("STATE".equals(operation)) break;
            cursor = relation.get("receiver");
        }
        return projection;
    }

    /**
     * Extracts the exact region input carried by either a semantic port name
     * or the VM's canonical reference-field materialization symbol.
     */
    private static String inputPort(String symbol) {
        String value = symbol == null ? "" : symbol;
        String referenceFieldPrefix = "M_L_field_";
        String arrayFieldPrefix = "M_[_field_";
        int start;
        if (value.startsWith("REGION.")) {
            start = 0;
        } else if (value.startsWith(referenceFieldPrefix)) {
            start = referenceFieldPrefix.length();
        } else if (value.startsWith(arrayFieldPrefix)) {
            start = arrayFieldPrefix.length();
        } else {
            return "";
        }
        int cursor = start + "REGION.".length();
        int regionEnd = digitsEnd(value, cursor);
        if (regionEnd == cursor || !value.startsWith(".in.", regionEnd)) {
            return "";
        }
        cursor = regionEnd + ".in.".length();
        int portEnd = digitsEnd(value, cursor);
        if (portEnd == cursor) {
            return "";
        }
        if (portEnd < value.length()) {
            char delimiter = value.charAt(portEnd);
            if (delimiter != '.' && delimiter != '_') {
                return "";
            }
        }
        return value.substring(start, portEnd);
    }

    private static int digitsEnd(String value, int start) {
        int cursor = start;
        while (cursor < value.length()
                && Character.isDigit(value.charAt(cursor))) {
            cursor++;
        }
        return cursor;
    }

    static boolean isConcreteEquality(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        JsonObject binary = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(string(binary, "_type"))
                || !"==".equals(string(binary, "_op"))) {
            return false;
        }
        return observedRead(binary.get("_left"), binary.get("_right"))
                || observedRead(binary.get("_right"),
                binary.get("_left"));
    }

    private static boolean observedRead(JsonElement readElement,
                                        JsonElement valueElement) {
        if (readElement == null || !readElement.isJsonObject()
                || !concreteScalar(valueElement)
                || !valueElement.isJsonObject()) {
            return false;
        }
        Read read = initialRead(readElement.getAsJsonObject());
        return read != null && read.concreteSelector()
                && primitiveFamily(read.javaType).equals(primitiveFamily(
                string(valueElement.getAsJsonObject(), "_java_type")));
    }

    private static boolean replayableMapKey(JsonObject expression) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                string(expression, "_java_type"));
        return descriptor.length() == 1
                && "ZBCSIJ".contains(descriptor);
    }

    private static Integer concreteIndex(JsonElement expression) {
        if (!concreteScalar(expression) || !expression.isJsonObject()) {
            return null;
        }
        JsonObject constant = expression.getAsJsonObject();
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                string(constant, "_java_type"));
        if (descriptor.length() != 1 || !"BCSIJ".contains(descriptor)) {
            return null;
        }
        try {
            long value = Long.parseLong(constantPayload(
                    string(constant, "_exp")));
            return value < Integer.MIN_VALUE || value > Integer.MAX_VALUE
                    ? null : (int) value;
        } catch (NumberFormatException malformed) {
            return null;
        }
    }

    private static boolean concreteScalar(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        String type = string(expression.getAsJsonObject(), "_type");
        return "ConstExpr".equals(type) || "ConSymbolExp".equals(type)
                || "ConStringSymbolExp".equals(type);
    }

    private static String primitiveFamily(String javaType) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                javaType);
        if ("Z".equals(descriptor)) {
            return "BOOL";
        }
        if (descriptor.length() == 1
                && "BCSIJ".contains(descriptor)) {
            return "INT";
        }
        if ("F".equals(descriptor) || "D".equals(descriptor)) {
            return "REAL";
        }
        return descriptor;
    }

    private static String constantPayload(String encoded) {
        String value = encoded == null ? "" : encoded;
        int first = value.indexOf('_');
        int second = value.indexOf('_', first + 1);
        return second < 0 ? value : value.substring(second + 1);
    }

    static final class Read {
        final String shape;
        final String stateSymbol;
        final String inputPort;
        final Integer index;
        final JsonObject selector;
        final String iterationProjection;
        final String javaType;

        private Read(String shape, String stateSymbol, String inputPort,
                     Integer index, JsonObject selector,
                     String iterationProjection, String javaType) {
            this.shape = shape;
            this.stateSymbol = stateSymbol;
            this.inputPort = inputPort;
            this.index = index;
            this.selector = selector == null ? null : selector.deepCopy();
            this.iterationProjection = iterationProjection;
            this.javaType = javaType;
        }

        boolean concreteSelector() {
            return "INDEXED".equals(shape) ? index != null
                    : !iterationProjection.isEmpty()
                    ? index != null : selector != null;
        }

        String selectorIdentity() {
            return "INDEXED".equals(shape)
                    ? String.valueOf(index)
                    : !iterationProjection.isEmpty()
                    ? "ITERATION:" + iterationProjection + ":" + index
                    : selector == null ? ""
                    : CanonicalJson.render(selector);
        }

        String keyJavaType() {
            return selector == null ? "" : string(selector, "_java_type");
        }

        String keyValue() {
            return selector == null ? ""
                    : constantPayload(string(selector, "_exp"));
        }
    }
}
