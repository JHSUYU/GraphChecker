package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Recognizes sparse initial-container reads and their concrete replay
 * observations.
 *
 * <p>The VM records {@code READ(initialState, selector) == concreteValue} so
 * a path can be replayed. That equality is a materialization observation,
 * not part of the region's symbolic relation. Only a concrete array/list
 * index or primitive/String map key is replayable.</p>
 */
public final class InitialContainerObservation {
    private InitialContainerObservation() {
    }

    static Read initialRead(JsonObject expression) {
        if (expression == null
                || !"ContainerRelation".equals(optionalString(expression, "_type"))) {
            return null;
        }
        String shape = optionalString(expression, "shape");
        String operation = optionalString(expression, "operation");
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
        if (!"ContainerRelation".equals(optionalString(state, "_type"))
                || !shape.equals(optionalString(state, "shape"))
                || !"STATE".equals(optionalString(state, "operation"))) {
            return null;
        }
        JsonObject identity = object(state, "receiver");
        String symbol = "SymbolExpression".equals(optionalString(identity, "_type"))
                ? optionalString(identity, "_exp") : "";
        String inputPort = inputPort(symbol);
        if (inputPort.isEmpty()) {
            return null;
        }
        JsonArray arguments = JsonFields.array(expression, "arguments");
        JsonObject selectorExpression = arguments.size() == 1
                && arguments.get(0).isJsonObject()
                ? arguments.get(0).getAsJsonObject() : null;
        JsonObject selector = selectorExpression != null
                && concreteScalar(selectorExpression)
                ? selectorExpression : null;
        Integer index = ("INDEXED".equals(shape)
                || !iterationProjection.isEmpty()) && selector != null
                ? concreteIndex(selector) : null;
        if ("ASSOCIATIVE".equals(shape)
                && iterationProjection.isEmpty() && selector != null
                && !replayableMapKey(selector)) {
            selector = null;
        }
        return new Read(shape, symbol, inputPort, index, selector,
                selectorExpression, iterationProjection,
                optionalString(expression, "_java_type"));
    }

    private static JsonObject initialState(JsonElement expression,
                                           String shape,
                                           boolean allowView) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            JsonArray alternatives = propagatedContainerAlternatives(
                    relation);
            if (alternatives != null) {
                JsonObject selected = null;
                String selectedIdentity = "";
                for (JsonElement alternative : alternatives) {
                    JsonObject candidate = initialState(alternative, shape,
                            allowView);
                    if (candidate.size() == 0) return new JsonObject();
                    String identity = CanonicalJson.render(candidate);
                    if (selected == null) {
                        selected = candidate;
                        selectedIdentity = identity;
                    } else if (!selectedIdentity.equals(identity)) {
                        return new JsonObject();
                    }
                }
                return selected == null ? new JsonObject() : selected;
            }
            if (!"ContainerRelation".equals(optionalString(relation, "_type"))
                    || !shape.equals(optionalString(relation, "shape"))) {
                return new JsonObject();
            }
            String operation = optionalString(relation, "operation");
            if ("STATE".equals(operation)) return relation;
            boolean associativeMutation = "ASSOCIATIVE".equals(shape)
                    && ("PUT".equals(operation)
                    || "REMOVE".equals(operation)
                    || "REMOVE_IF".equals(operation)
                    || "CLEAR".equals(operation)
                    || "REMOVE_AT".equals(operation));
            // The indexed mutations, which are the exact vocabulary the
            // container algebra publishes for an indexed whole-state carrier.
            // Without them the first add or remove on a selected List ends
            // the walk, so every traversal read of it stops being an initial
            // observation and cannot be replayed.
            boolean indexedMutation = "INDEXED".equals(shape)
                    && ("APPEND".equals(operation)
                    || "INSERT".equals(operation)
                    || "REMOVE".equals(operation)
                    || "WRITE".equals(operation)
                    || "CLEAR".equals(operation));
            if (!"ITERATOR".equals(operation)
                    && !associativeMutation
                    && !indexedMutation
                    && !"SNAPSHOT_BASE".equals(operation)
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
            JsonArray alternatives = propagatedContainerAlternatives(
                    relation);
            if (alternatives != null) {
                String selected = "";
                for (JsonElement alternative : alternatives) {
                    String candidate = iterationProjection(alternative);
                    if (candidate.isEmpty()) return "";
                    if (selected.isEmpty()) {
                        selected = candidate;
                    } else if (!selected.equals(candidate)) {
                        return "";
                    }
                }
                return selected;
            }
            if (!"ContainerRelation".equals(optionalString(relation, "_type"))
                    || !"ASSOCIATIVE".equals(optionalString(relation, "shape"))) {
                return "";
            }
            String operation = optionalString(relation, "operation");
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

    /** Values hidden only by provenance/choice wrappers. Every arm must
     * resolve to the same container state before it is treated as one replay
     * boundary. */
    private static JsonArray propagatedContainerAlternatives(
            JsonObject expression) {
        if (VmExpressionIr.isConsumerBoundary(expression)
                || VmExpressionIr.isConsumerBoundaryReference(expression)) {
            JsonArray result = new JsonArray();
            JsonElement value = expression.get(VmExpressionIr.EXPRESSION);
            if (value != null) result.add(value);
            return result;
        }
        String type = optionalString(expression, "_type");
        String armsField;
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)) {
            armsField = "candidates";
        } else if (SymbolicPropagationClosure.ITE_TYPE.equals(type)) {
            armsField = "arms";
        } else {
            return null;
        }
        JsonArray result = new JsonArray();
        for (JsonElement encoded : JsonFields.array(expression, armsField)) {
            if (!encoded.isJsonObject()) return new JsonArray();
            JsonElement value = encoded.getAsJsonObject().get("expression");
            if (value == null) return new JsonArray();
            result.add(value);
        }
        return result;
    }

    /**
     * Extracts the exact region input carried by either a semantic port name
     * or the VM's canonical reference-field materialization symbol.
     */
    private static String inputPort(String symbol) {
        String value = symbol == null ? "" : symbol;
        if (VmExpressionIr.isCanonicalMapStateReference(value)) {
            return value;
        }
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
        if (!value.startsWith("REGION.", start)) {
            return "";
        }
        int inputMarker = value.indexOf(".in.",
                start + "REGION.".length());
        if (inputMarker < 0 || !stableToken(value,
                start + "REGION.".length(), inputMarker)) {
            return "";
        }
        int cursor = inputMarker + ".in.".length();
        int portEnd = tokenEnd(value, cursor);
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

    private static int tokenEnd(String value, int start) {
        int cursor = start;
        while (cursor < value.length()
                && stableTokenCharacter(value.charAt(cursor))) {
            cursor++;
        }
        return cursor;
    }

    private static boolean stableToken(String value, int start, int end) {
        if (start >= end) return false;
        for (int index = start; index < end; index++) {
            char current = value.charAt(index);
            if (current != '.' && !stableTokenCharacter(current)) {
                return false;
            }
        }
        return true;
    }

    private static boolean stableTokenCharacter(char value) {
        return Character.isLetterOrDigit(value) || value == '-';
    }

    static boolean isConcreteEquality(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return false;
        }
        JsonObject binary = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(binary, "_type"))
                || !"==".equals(optionalString(binary, "_op"))) {
            return false;
        }
        return observedRead(binary.get("_left"), binary.get("_right"))
                || observedRead(binary.get("_right"),
                binary.get("_left"));
    }

    private static boolean observedRead(JsonElement readElement,
                                        JsonElement valueElement) {
        if (readElement == null || !readElement.isJsonObject()
                || !valueElement.isJsonObject()) {
            return false;
        }
        JsonObject relation = readElement.getAsJsonObject();
        JsonObject value = valueElement.getAsJsonObject();
        String symbol = optionalString(value, "_exp");
        if ("ContainerRelation".equals(optionalString(relation, "_type"))
                && ("READ".equals(optionalString(relation, "operation"))
                || "NEXT".equals(optionalString(relation, "operation")))
                && "L".equals(optionalString(relation, "_java_type"))
                && "SymbolExpression".equals(optionalString(value, "_type"))
                && (VmExpressionIr.SYMBOLIC_NULL.equals(symbol)
                || VmExpressionIr.isAllocatedInstanceReference(symbol))) {
            return true;
        }
        Read read = initialRead(relation);
        if (read == null || !read.concreteSelector()
                && !read.dynamicAssociativeSelector()) {
            return false;
        }
        if (concreteScalar(value)) {
            return read.concreteSelector()
                    && primitiveFamily(read.javaType).equals(
                    primitiveFamily(optionalString(value, "_java_type")));
        }
        return false;
    }

    private static boolean replayableMapKey(JsonObject expression) {
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                optionalString(expression, "_java_type"));
        return descriptor.length() == 1
                && "ZBCSIJ".contains(descriptor);
    }

    private static Integer concreteIndex(JsonElement expression) {
        if (!concreteScalar(expression) || !expression.isJsonObject()) {
            return null;
        }
        JsonObject constant = expression.getAsJsonObject();
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                optionalString(constant, "_java_type"));
        if (descriptor.length() != 1 || !"BCSIJ".contains(descriptor)) {
            return null;
        }
        try {
            long value = Long.parseLong(constantPayload(
                    optionalString(constant, "_exp")));
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
        String type = optionalString(expression.getAsJsonObject(), "_type");
        return ContainerSmtCodec.constantKind(type);
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
        final JsonObject selectorExpression;
        final String iterationProjection;
        final String javaType;

        private Read(String shape, String stateSymbol, String inputPort,
                     Integer index, JsonObject selector,
                     JsonObject selectorExpression,
                     String iterationProjection, String javaType) {
            this.shape = shape;
            this.stateSymbol = stateSymbol;
            this.inputPort = inputPort;
            this.index = index;
            // Import has already made this expression DAG immutable. Keeping
            // the shared nodes preserves content-address identity and avoids
            // re-expanding the propagated key once per writer candidate.
            this.selector = selector;
            this.selectorExpression = selectorExpression;
            this.iterationProjection = iterationProjection;
            this.javaType = javaType;
        }

        boolean concreteSelector() {
            return "INDEXED".equals(shape) ? index != null
                    : !iterationProjection.isEmpty()
                    ? index != null : selector != null;
        }

        /**
         * A selected associative read need not replay the old concrete key.
         * The runtime can materialize the value at the same access ordinal,
         * leaving the replay's own key and Map semantics intact.
         */
        boolean dynamicAssociativeSelector() {
            return "ASSOCIATIVE".equals(shape)
                    && iterationProjection.isEmpty()
                    && selector == null && selectorExpression != null;
        }

    }
}
