package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** The single SMT lowering for VM container operations. */
public final class ContainerSmtCodec {
    public static final String EXPRESSION_TYPE = "ContainerRelation";

    private ContainerSmtCodec() {
    }

    /**
     * Both operations denote the exact empty container.  They state different
     * provenance, which the caller keeps; the lowering is the same.
     */
    static boolean emptiesState(String operation) {
        return "CLEAR".equals(operation) || "SNAPSHOT_BASE".equals(operation);
    }

    /** One tagged transport value shared by path solving and composition. */
    static String valueDatatypeDeclaration() {
        return "(declare-datatypes () ((Value"
                + " (VByte (valueByte Int))"
                + " (VChar (valueChar Int))"
                + " (VShort (valueShort Int))"
                + " (VInt (valueInt Int))"
                + " (VLong (valueLong Int))"
                + " (VFloat (valueFloat (_ FloatingPoint 8 24)))"
                + " (VDouble (valueDouble (_ FloatingPoint 11 53)))"
                + " (VBool (valueBool Bool))"
                + " (VRef (valueRef Ref))"
                + " (VString (valueString String)))))";
    }

    static String boxIntegral(String value, String javaType) {
        String constructor = integralValuePart(javaType, true);
        return constructor.isEmpty() ? "" : "(" + constructor + " "
                + value + ")";
    }

    static String unboxIntegral(String value, String javaType) {
        String accessor = integralValuePart(javaType, false);
        return accessor.isEmpty() ? "" : "(" + accessor + " "
                + value + ")";
    }

    static String valueKind(String javaType) {
        String integral = integralValuePart(javaType, true);
        if (!integral.isEmpty()) return integral;
        String descriptor = JavaPrimitiveBoxing
                .primitiveDescriptor(javaType);
        if (descriptor.isEmpty()) {
            descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(javaType);
        }
        if ("Z".equals(descriptor)) return "VBool";
        if ("F".equals(descriptor)) return "VFloat";
        if ("D".equals(descriptor)) return "VDouble";
        if ("Ljava/lang/String;".equals(descriptor)) return "VString";
        if ("L".equals(javaType) || descriptor.startsWith("L")
                || descriptor.startsWith("[")) {
            return "VRef";
        }
        return "";
    }

    private static String integralValuePart(
            String javaType, boolean constructor) {
        String descriptor = JavaPrimitiveBoxing
                .primitiveDescriptor(javaType);
        if (descriptor.isEmpty()) {
            descriptor = JavaPrimitiveSmtSemantics
                    .javaTypeDescriptor(javaType);
        }
        String name = "B".equals(descriptor) ? "Byte"
                : "C".equals(descriptor) ? "Char"
                : "S".equals(descriptor) ? "Short"
                : "I".equals(descriptor) ? "Int"
                : "J".equals(descriptor) ? "Long" : "";
        return name.isEmpty() ? ""
                : (constructor ? "V" : "value") + name;
    }

    public static List<String> preamble() {
        return Collections.unmodifiableList(Arrays.asList(
                "(declare-datatypes () ((IndexedState"
                        + " (mkIndexedState"
                        + " (indexed_size Int)"
                        + " (indexed_elements (Array Int Value))))))",
                "(declare-datatypes () ((AssocState"
                        + " (mkAssocState"
                        + " (assoc_size Int)"
                        + " (assoc_present (Array Value Bool))"
                        + " (assoc_values (Array Value Value))"
                        + " (assoc_order (Array Int Value))"
                        + " (assoc_position (Array Value Int))))))",
                "(declare-fun indexed_state_of (Ref) IndexedState)",
                "(declare-fun assoc_state_of (Ref) AssocState)",
                "(define-fun indexed_read ((s IndexedState) (i Int)) Value"
                        + " (select (indexed_elements s) i))",
                "(define-fun indexed_write ((s IndexedState) (i Int)"
                        + " (v Value)) IndexedState"
                        + " (mkIndexedState (indexed_size s)"
                        + " (store (indexed_elements s) i v)))",
                "(define-fun indexed_append ((s IndexedState) (v Value))"
                        + " IndexedState (mkIndexedState"
                        + " (+ (indexed_size s) 1)"
                        + " (store (indexed_elements s)"
                        + " (indexed_size s) v)))",
                "(define-fun indexed_insert ((s IndexedState) (i Int)"
                        + " (v Value)) IndexedState (mkIndexedState"
                        + " (+ (indexed_size s) 1)"
                        + " (lambda ((q Int)) (ite (< q i)"
                        + " (select (indexed_elements s) q)"
                        + " (ite (= q i) v"
                        + " (select (indexed_elements s) (- q 1)))))))",
                "(define-fun indexed_remove ((s IndexedState) (i Int))"
                        + " IndexedState (mkIndexedState"
                        + " (- (indexed_size s) 1)"
                        + " (lambda ((q Int)) (ite (< q i)"
                        + " (select (indexed_elements s) q)"
                        + " (select (indexed_elements s) (+ q 1))))))",
                "(define-fun indexed_contains ((s IndexedState) (v Value))"
                        + " Bool (exists ((i Int))"
                        + " (and (<= 0 i) (< i (indexed_size s))"
                        + " (= (indexed_read s i) v))))",
                "(define-fun assoc_has ((s AssocState) (k Value)) Bool"
                        + " (select (assoc_present s) k))",
                "(define-fun assoc_read ((s AssocState) (k Value)) Value"
                        + " (select (assoc_values s) k))",
                "(define-fun assoc_key_at ((s AssocState) (i Int)) Value"
                        + " (select (assoc_order s) i))",
                "(define-fun assoc_value_at ((s AssocState) (i Int)) Value"
                        + " (assoc_read s (assoc_key_at s i)))",
                "(define-fun assoc_put ((s AssocState) (k Value)"
                        + " (v Value)) AssocState"
                        + " (mkAssocState"
                        + " (ite (assoc_has s k) (assoc_size s)"
                        + " (+ (assoc_size s) 1))"
                        + " (store (assoc_present s) k true)"
                        + " (store (assoc_values s) k v)"
                        + " (ite (assoc_has s k) (assoc_order s)"
                        + " (store (assoc_order s) (assoc_size s) k))"
                        + " (ite (assoc_has s k) (assoc_position s)"
                        + " (store (assoc_position s) k"
                        + " (assoc_size s)))))"
                ,
                associativeRemoveDefinition()
        ));
    }

    private static String associativeRemoveDefinition() {
        int bound = LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY;
        StringBuilder order = new StringBuilder("(assoc_order s)");
        StringBuilder position =
                new StringBuilder("(store (assoc_position s) k (- 1))");
        for (int slot = 0; slot < bound; slot++) {
            String key = "(select (assoc_order s) " + slot + ")";
            String oldPosition = "(select (assoc_position s) " + key + ")";
            order.insert(0, "(store ").append(' ').append(slot)
                    .append(" (ite (and (<= p ").append(slot)
                    .append(") (< ").append(slot)
                    .append(" (- (assoc_size s) 1))) ")
                    .append("(select (assoc_order s) ").append(slot + 1)
                    .append(") ").append(key).append("))");
            position.insert(0, "(store ").append(' ').append(key)
                    .append(" (ite (and (not (= ").append(key).append(" k))")
                    .append(" (assoc_has s ").append(key).append(") (> ")
                    .append(oldPosition).append(" p)) (- ")
                    .append(oldPosition).append(" 1) ")
                    .append(oldPosition).append("))");
        }
        return "(define-fun assoc_remove ((s AssocState) (k Value))"
                + " AssocState"
                + " (ite (assoc_has s k)"
                + " (let ((p (select (assoc_position s) k)))"
                + " (mkAssocState"
                + " (- (assoc_size s) 1)"
                + " (store (assoc_present s) k false)"
                + " (assoc_values s) " + order + " " + position + "))"
                + " s))";
    }

    public static boolean handles(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && EXPRESSION_TYPE.equals(
                string(expression.getAsJsonObject(), "_type"));
    }

    public static boolean handlesField(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && "FieldAccessExpression".equals(
                string(expression.getAsJsonObject(), "_type"));
    }

    public static boolean handlesFieldBinding(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject binary = expression.getAsJsonObject();
        String position = string(binary, "_code_position");
        if (!"BinaryExpression".equals(string(binary, "_type"))
                || !"==".equals(string(binary, "_op"))
                || position.indexOf(
                "java.lang.System.symbolizeExactField(") < 0
                && position.indexOf(
                "java.lang.System.symbolizeField(") < 0
                && position.indexOf("java.lang.System.symbolize(") < 0) {
            return false;
        }
        return handlesField(binary.get("_left"))
                && symbol(binary.get("_right"))
                || handlesField(binary.get("_right"))
                && symbol(binary.get("_left"));
    }

    public static boolean handlesAccessConstraint(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject binary = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(string(binary, "_type"))) {
            return false;
        }
        JsonElement left = binary.get("_left");
        JsonElement right = binary.get("_right");
        return handles(left) || handles(right)
                || constant(left) && constant(right);
    }

    private static boolean constant(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        String type = string(expression.getAsJsonObject(), "_type");
        return "ConstExpr".equals(type) || "ConSymbolExp".equals(type)
                || "ConStringSymbolExp".equals(type);
    }

    public static String materializedStringEquality(
            String left, String right, String symbolNullness) {
        if (symbolNullness == null || symbolNullness.isEmpty()) return "";
        String equality = "(= " + left + " " + right + ")";
        return "false".equals(symbolNullness) ? equality
                : "(and " + equality + " (not "
                + symbolNullness + "))";
    }

    private static boolean symbol(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && "SymbolExpression".equals(
                string(expression.getAsJsonObject(), "_type"));
    }

    public static Term field(JsonObject expression, Host host) {
        Term owner = host.operand(expression.get("owner"), Sort.REF);
        if (owner == null) return null;
        String ownerClass = string(expression, "ownerClass");
        String javaType = string(expression, "_java_type");
        if (boxedPrimitiveValue(owner, ownerClass, javaType)) {
            return owner;
        }
        return host.field(owner, ownerClass,
                JsonFields.integer(expression, "fieldOffset", -1), javaType);
    }

    private static boolean boxedPrimitiveValue(
            Term owner, String ownerClass, String javaType) {
        if ("java/lang/Boolean".equals(ownerClass)) {
            return "Z".equals(javaType) && owner.sort == Sort.BOOL;
        }
        if ("java/lang/Float".equals(ownerClass)) {
            return "F".equals(javaType) && owner.sort == Sort.FLOAT32;
        }
        if ("java/lang/Double".equals(ownerClass)) {
            return "D".equals(javaType) && owner.sort == Sort.FLOAT64;
        }
        return ("java/lang/Byte".equals(ownerClass)
                && "B".equals(javaType)
                || "java/lang/Character".equals(ownerClass)
                && "C".equals(javaType)
                || "java/lang/Short".equals(ownerClass)
                && "S".equals(javaType)
                || "java/lang/Integer".equals(ownerClass)
                && "I".equals(javaType)
                || "java/lang/Long".equals(ownerClass)
                && "J".equals(javaType))
                && owner.sort == Sort.INT;
    }

    /** Rewrites an indexed read to the element it provably selects. */
    static JsonElement selectedIndexedElement(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return expression;
        }
        JsonObject object = expression.getAsJsonObject();
        JsonArray arguments = array(object, "arguments");
        if (!EXPRESSION_TYPE.equals(string(object, "_type"))
                || !"INDEXED".equals(string(object, "shape"))
                || !"READ".equals(string(object, "operation"))
                || arguments.size() != 1) {
            return expression;
        }
        JsonElement stored = storedIndexedWrite(object.get("receiver"),
                arguments.get(0));
        return stored == null ? expression : selectedIndexedElement(stored);
    }

    /** Resolves {@code READ(WRITE(s, j, v), i)} to the stored {@code v}. */
    private static JsonElement storedIndexedWrite(JsonElement receiver,
                                                  JsonElement index) {
        Integer wanted = exactIndexLiteral(index);
        if (wanted == null) return null;
        JsonElement cursor = receiver;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject node = cursor.getAsJsonObject();
            JsonArray arguments = array(node, "arguments");
            if (!EXPRESSION_TYPE.equals(string(node, "_type"))
                    || !"INDEXED".equals(string(node, "shape"))
                    || !"WRITE".equals(string(node, "operation"))
                    || arguments.size() != 2) {
                return null;
            }
            Integer written = exactIndexLiteral(arguments.get(0));
            if (written == null) return null;
            if (written.intValue() == wanted.intValue()) {
                return arguments.get(1);
            }
            cursor = node.get("receiver");
        }
        return null;
    }

    /** Skips the writes a size query cannot observe. */
    private static JsonElement sizePreservingIndexedReceiver(
            JsonElement receiver) {
        JsonElement cursor = receiver;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject node = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(node, "_type"))
                    || !"INDEXED".equals(string(node, "shape"))
                    || !"WRITE".equals(string(node, "operation"))
                    || array(node, "arguments").size() != 2
                    || node.get("receiver") == null) {
                return cursor;
            }
            cursor = node.get("receiver");
        }
        return receiver;
    }

    /** One exact {@code int} literal, or null when nothing is decided. */
    private static Integer exactIndexLiteral(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if (!"ConstExpr".equals(type) && !"ConSymbolExp".equals(type)) {
            return null;
        }
        String javaType = string(object, "_java_type");
        if (!"I".equals(javaType) && !"int".equals(javaType)) return null;
        String payload = string(object, "_exp");
        int first = payload.indexOf('_');
        int second = first < 0 ? -1 : payload.indexOf('_', first + 1);
        String value = second < 0 ? payload : payload.substring(second + 1);
        if (!value.matches("-?[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    public static Term term(JsonObject expression, Host host) {
        String shape = string(expression, "shape");
        String operation = string(expression, "operation");
        String javaType = string(expression, "_java_type");
        if ("STATE".equals(operation)) {
            Sort stateSort = "INDEXED".equals(shape)
                    ? Sort.INDEXED : Sort.ASSOCIATIVE;
            Term state = host.state(expression.get("receiver"), stateSort);
            JsonArray arguments = array(expression, "arguments");
            if (state == null || stateSort != Sort.INDEXED
                    || arguments.size() == 0) {
                return state;
            }
            if (arguments.size() != 1) {
                host.unsupported("ContainerRelation:INDEXED:STATE:arity="
                        + arguments.size());
                return null;
            }
            Term size = host.operand(arguments.get(0), Sort.INT);
            return size == null ? null : new Term(
                    "(mkIndexedState " + size.text
                            + " (indexed_elements " + state.text + "))",
                    Sort.INDEXED);
        }
        if ("KEY".equals(operation) || "VALUE".equals(operation)) {
            Entry entry = entry(expression.get("receiver"), host);
            if (entry == null) {
                host.unsupported("ContainerRelation:malformed-entry:"
                        + operation);
                return null;
            }
            requireAssociativeMember(entry.state, entry.index, host);
            String value = "KEY".equals(operation)
                    ? "(assoc_key_at " + entry.state.text + " "
                    + entry.index.text + ")"
                    : "(assoc_value_at " + entry.state.text + " "
                    + entry.index.text + ")";
            return host.unbox(new Term(value, Sort.VALUE), javaType);
        }
        if ("INDEXED".equals(shape) && "NEXT".equals(operation)) {
            JsonArray positions = array(expression, "arguments");
            if (positions.size() != 1) {
                host.unsupported("ContainerRelation:INDEXED:NEXT:arity="
                        + positions.size());
                return null;
            }
            Term cursor = host.operand(expression.get("receiver"),
                    Sort.INDEXED);
            Term index = host.operand(positions.get(0), Sort.INT);
            if (cursor != null && index != null) {
                requireIndexedMember(cursor, index, host);
            }
            return cursor == null || index == null ? null
                    : host.unbox(new Term("(indexed_read " + cursor.text
                    + " " + index.text + ")", Sort.VALUE), javaType);
        }
        if ("ASSOCIATIVE".equals(shape) && "NEXT".equals(operation)) {
            View view = view(expression.get("receiver"), host);
            JsonArray positions = array(expression, "arguments");
            if (view == null || positions.size() != 1
                    || "ENTRY_VIEW".equals(view.kind)) {
                host.unsupported(
                        "ContainerRelation:ASSOCIATIVE:NEXT:view");
                return null;
            }
            Term index = host.operand(positions.get(0), Sort.INT);
            if (index == null) return null;
            requireAssociativeMember(view.state, index, host);
            String value = "KEY_VIEW".equals(view.kind)
                    ? "(assoc_key_at " + view.state.text + " "
                    + index.text + ")"
                    : "(assoc_value_at " + view.state.text + " "
                    + index.text + ")";
            return host.unbox(new Term(value, Sort.VALUE), javaType);
        }
        if ("OBSERVE_KEY".equals(operation)
                || "OBSERVE_VALUE".equals(operation)) {
            Entry entry = entry(expression.get("receiver"), host);
            JsonArray observed = array(expression, "arguments");
            if (entry == null || observed.size() != 1) {
                host.unsupported("ContainerRelation:malformed-observation:"
                        + operation);
                return null;
            }
            Term value = host.box(observed.get(0));
            if (value == null) return null;
            requireAssociativeMember(entry.state, entry.index, host);
            String selected = "OBSERVE_KEY".equals(operation)
                    ? "(assoc_key_at " + entry.state.text + " "
                    + entry.index.text + ")"
                    : "(assoc_value_at " + entry.state.text + " "
                    + entry.index.text + ")";
            return new Term("(= " + selected + " " + value.text + ")",
                    Sort.BOOL);
        }
        if ("HAS_NEXT".equals(operation)) {
            Sort stateSort = "INDEXED".equals(shape)
                    ? Sort.INDEXED : Sort.ASSOCIATIVE;
            Term state = stateSort == Sort.ASSOCIATIVE
                    ? associativeState(expression.get("receiver"), host)
                    : host.operand(expression.get("receiver"), stateSort);
            JsonArray positions = array(expression, "arguments");
            Term position = positions.size() == 1
                    ? host.operand(positions.get(0), Sort.INT) : null;
            if (state == null || position == null) {
                host.unsupported("ContainerRelation:" + shape
                        + ":HAS_NEXT");
                return null;
            }
            String size = stateSort == Sort.INDEXED
                    ? "(indexed_size " + state.text + ")"
                    : "(assoc_size " + state.text + ")";
            return new Term("(and (<= 0 " + position.text + ") (< "
                    + position.text + " " + size + "))", Sort.BOOL);
        }
        JsonArray arguments = array(expression, "arguments");
        if (emptiesState(operation)) {
            if (arguments.size() != 0) {
                host.unsupported("ContainerRelation:" + shape + ":"
                        + operation + ":arity=" + arguments.size());
                return null;
            }
            if ("INDEXED".equals(shape)) {
                return new Term("(mkIndexedState 0"
                        + " ((as const (Array Int Value))"
                        + " (VRef nullRef)))", Sort.INDEXED);
            }
            if ("ASSOCIATIVE".equals(shape)) {
                return new Term("(mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " ((as const (Array Value Value))"
                        + " (VRef nullRef))"
                        + " ((as const (Array Int Value))"
                        + " (VRef nullRef))"
                        + " ((as const (Array Value Int)) (- 1)))",
                        Sort.ASSOCIATIVE);
            }
        }
        if ("INDEXED".equals(shape)) {
            JsonElement receiverIr = expression.get("receiver");
            boolean preserveReceiver = host.preserveContainerIdentity(
                    receiverIr, Sort.INDEXED);
            if ("READ".equals(operation) && arguments.size() == 1
                    && !preserveReceiver) {
                JsonElement stored = storedIndexedWrite(receiverIr,
                        arguments.get(0));
                if (stored != null) {
                    return host.unbox(host.box(stored), javaType);
                }
            }
            if ("SIZE".equals(operation) && !preserveReceiver) {
                receiverIr = sizePreservingIndexedReceiver(receiverIr);
            }
            Term receiver = host.operand(receiverIr, Sort.INDEXED);
            if (receiver == null) return null;
            if ("ITERATOR".equals(operation)) return receiver;
            if ("SIZE".equals(operation)) {
                return javaContainerSize("(indexed_size " + receiver.text
                        + ")", host);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                if (index != null) {
                    requireIndexedMember(receiver, index, host);
                }
                return index == null ? null
                        : host.unbox(new Term("(indexed_read "
                        + receiver.text + " " + index.text + ")",
                        Sort.VALUE), javaType);
            }
            if ("WRITE".equals(operation) && arguments.size() == 2) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                Term value = host.box(arguments.get(1));
                return index == null || value == null ? null
                        : new Term("(indexed_write " + receiver.text + " "
                        + index.text + " " + value.text + ")",
                        Sort.INDEXED);
            }
            if ("APPEND".equals(operation) && arguments.size() == 1) {
                Term value = host.box(arguments.get(0));
                return value == null ? null
                        : new Term("(indexed_append " + receiver.text + " "
                        + value.text + ")", Sort.INDEXED);
            }
            if ("INSERT".equals(operation) && arguments.size() == 2) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                Term value = host.box(arguments.get(1));
                return index == null || value == null ? null
                        : new Term("(indexed_insert " + receiver.text + " "
                        + index.text + " " + value.text + ")",
                        Sort.INDEXED);
            }
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                return index == null ? null
                        : new Term("(indexed_remove " + receiver.text + " "
                        + index.text + ")", Sort.INDEXED);
            }
            if ("CONTAINS".equals(operation) && arguments.size() == 1) {
                Term value = host.box(arguments.get(0));
                return value == null ? null
                        : new Term("(indexed_contains " + receiver.text + " "
                        + value.text + ")", Sort.BOOL);
            }
            if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
                return new Term("(= (indexed_size " + receiver.text + ") 0)",
                        Sort.BOOL);
            }
        } else if ("ASSOCIATIVE".equals(shape)) {
            if ("SIZE".equals(operation)) {
                return associativeSize(expression.get("receiver"), host);
            }
            if ("CONTAINS".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : associativeHas(expression.get("receiver"),
                        key, host);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : host.unbox(associativeRead(
                        expression.get("receiver"), key, host), javaType);
            }
            if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
                Term size = associativeSize(
                        expression.get("receiver"), host);
                return size == null ? null
                        : new Term("(= " + size.text + " 0)", Sort.BOOL);
            }
            Term receiver = associativeState(expression.get("receiver"),
                    host);
            if (receiver == null) return null;
            if ("ITERATOR".equals(operation)
                    || "ENTRY_VIEW".equals(operation)
                    || "KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) return receiver;
            if ("PUT".equals(operation) && arguments.size() == 2) {
                Term key = host.box(arguments.get(0));
                Term value = host.box(arguments.get(1));
                return key == null || value == null ? null
                        : new Term("(assoc_put " + receiver.text + " "
                        + key.text + " " + value.text + ")",
                        Sort.ASSOCIATIVE);
            }
            if ("REMOVE_AT".equals(operation)
                    && arguments.size() == 1) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                if (index == null) return null;
                requireAssociativeMember(receiver, index, host);
                return new Term("(assoc_remove " + receiver.text
                        + " (assoc_key_at " + receiver.text + " "
                        + index.text + "))", Sort.ASSOCIATIVE);
            }
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : new Term("(assoc_remove " + receiver.text + " "
                        + key.text + ")", Sort.ASSOCIATIVE);
            }
            if ("REMOVE_IF".equals(operation) && arguments.size() == 1) {
                // The map after a conditional remove is the map with the key
                // gone when the guard holds, and unchanged otherwise: the
                // symbolic branch the removeExpiredKeys it.remove() fired
                // under, carried as the op's guard.  Read/has short-circuit
                // this via the mutation walk; this state form is for a
                // REMOVE_IF nested as another op's receiver.
                Term key = host.box(arguments.get(0));
                Term guard = host.operand(expression.get("guard"), Sort.BOOL);
                return key == null || guard == null ? null
                        : new Term("(ite " + guard.text + " (assoc_remove "
                        + receiver.text + " " + key.text + ") "
                        + receiver.text + ")", Sort.ASSOCIATIVE);
            }
        }
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
    }

    private static Term associativeHas(
            JsonElement expression, Term key, Host host) {
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            return state == null ? null
                    : new Term("(assoc_has " + state.text + " "
                    + key.text + ")", Sort.BOOL);
        }
        if (emptiesState(mutation.operation)) {
            return new Term("false", Sort.BOOL);
        }
        Term mutatedKey = host.box(mutation.arguments.get(0));
        Term previous = associativeHas(mutation.receiver, key, host);
        if (mutatedKey == null || previous == null) return null;
        String sameKey = "(= " + key.text + " " + mutatedKey.text + ")";
        if ("PUT".equals(mutation.operation)) {
            return new Term("(or " + sameKey + " " + previous.text + ")",
                    Sort.BOOL);
        }
        if ("REMOVE_IF".equals(mutation.operation)) {
            // The key is present unless the guard fired for exactly this key.
            String guard = conditionalGuard(mutation, sameKey, host);
            if (guard == null) return null;
            return new Term("(and (not " + guard + ") " + previous.text
                    + ")", Sort.BOOL);
        }
        return new Term("(and (not " + sameKey + ") " + previous.text + ")",
                Sort.BOOL);
    }

    /** {@code guard AND key==removedKey}: the condition under which a
     *  {@code REMOVE_IF} deletes the key being read.  The guard is the
     *  recorded symbolic branch predicate, lowered as a boolean. */
    private static String conditionalGuard(Mutation mutation, String sameKey,
                                           Host host) {
        Term guard = host.operand(mutation.guard, Sort.BOOL);
        if (guard == null) return null;
        return "(and " + guard.text + " " + sameKey + ")";
    }

    private static Term associativeRead(
            JsonElement expression, Term key, Host host) {
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            return state == null ? null
                    : new Term("(ite (assoc_has " + state.text + " "
                    + key.text + ") (assoc_read " + state.text + " "
                    + key.text + ") (VRef nullRef))", Sort.VALUE);
        }
        if (emptiesState(mutation.operation)) {
            return new Term("(VRef nullRef)", Sort.VALUE);
        }
        Term mutatedKey = host.box(mutation.arguments.get(0));
        Term previous = associativeRead(mutation.receiver, key, host);
        if (mutatedKey == null || previous == null) return null;
        String sameKey = "(= " + key.text + " " + mutatedKey.text + ")";
        Term mutatedValue = "PUT".equals(mutation.operation)
                ? host.box(mutation.arguments.get(1))
                : new Term("(VRef nullRef)", Sort.VALUE);
        if (mutatedValue == null) return null;
        // A conditional remove deletes the read key only when its recorded
        // guard holds; flipping the guard (z3's choice) turns a present key
        // into null -- the removeExpiredKeys removal story.
        String condition = "REMOVE_IF".equals(mutation.operation)
                ? conditionalGuard(mutation, sameKey, host) : sameKey;
        if (condition == null) return null;
        return new Term("(ite " + condition + " " + mutatedValue.text + " "
                + previous.text + ")", Sort.VALUE);
    }

    /**
     * Positional container projections are Java operations, not total SMT
     * functions, so membership is required rather than assumed.
     */
    private static void requireIndexedMember(
            Term state, Term index, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (indexed_size s))))");
    }

    private static void requireAssociativeMember(
            Term state, Term index, Host host) {
        host.require(associativeMemberRequirement(state, index));
    }

    private static String associativeMemberRequirement(
            Term state, Term index) {
        return "(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (assoc_size s))"
                + " (assoc_has s (assoc_key_at s i))))";
    }

    static List<AssociativeRemovalEffect> associativeRemovalEffects(
            JsonElement expression, Host host) {
        List<AssociativeRemovalEffect> result = new java.util.ArrayList<>();
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(relation, "_type"))
                    || !"ASSOCIATIVE".equals(string(relation, "shape"))) {
                break;
            }
            String operation = string(relation, "operation");
            JsonArray arguments = array(relation, "arguments");
            JsonElement receiverIr = relation.get("receiver");
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                Term present = key == null ? null
                        : associativeHas(receiverIr, key, host);
                if (present != null) {
                    result.add(new AssociativeRemovalEffect(
                            key, present.text));
                }
            } else if ("REMOVE_IF".equals(operation)
                    && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                Term guard = host.operand(relation.get("guard"), Sort.BOOL);
                Term present = key == null ? null
                        : associativeHas(receiverIr, key, host);
                if (present != null && guard != null) {
                    result.add(new AssociativeRemovalEffect(key,
                            "(and " + guard.text + " "
                                    + present.text + ")"));
                }
            } else if ("REMOVE_AT".equals(operation)
                    && arguments.size() == 1) {
                Term state = host.operand(receiverIr, Sort.ASSOCIATIVE);
                Term index = host.operand(arguments.get(0), Sort.INT);
                if (state != null && index != null) {
                    result.add(new AssociativeRemovalEffect(new Term(
                            "(assoc_key_at " + state.text + " "
                                    + index.text + ")", Sort.VALUE),
                            associativeMemberRequirement(state, index)));
                }
            }
            if (!("PUT".equals(operation)
                    || "REMOVE".equals(operation)
                    || "REMOVE_IF".equals(operation)
                    || "REMOVE_AT".equals(operation))) {
                break;
            }
            cursor = receiverIr;
        }
        return result;
    }

    /**
     * One Java container size.  {@code array.length} and
     * {@code Collection.size()} are both {@code int} (JLS 10.7, 15.14), so
     * the value carries that computational type; and a size is never negative
     * and never exceeds {@code Integer.MAX_VALUE}, which the state the size is
     * read from must satisfy for that type to be the one the JVM computed in.
     */
    private static Term javaContainerSize(String text, Host host) {
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType("I");
        host.require("(and (<= 0 " + text + ") (<= " + text + " "
                + domain.upper + "))");
        return new Term(text, Sort.INT, IntegralWidth.JAVA_INT);
    }

    private static Term associativeSize(JsonElement expression, Host host) {
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            return state == null ? null
                    : javaContainerSize("(assoc_size " + state.text + ")",
                    host);
        }
        if (emptiesState(mutation.operation)) {
            return new Term("0", Sort.INT, IntegralWidth.JAVA_INT);
        }
        Term key = host.box(mutation.arguments.get(0));
        Term previousSize = associativeSize(mutation.receiver, host);
        Term previouslyPresent = key == null ? null
                : associativeHas(mutation.receiver, key, host);
        if (previousSize == null || previouslyPresent == null) return null;
        String changedSize = "PUT".equals(mutation.operation)
                ? "(+ " + previousSize.text + " 1)"
                : "(- " + previousSize.text + " 1)";
        return new Term("(ite " + previouslyPresent.text + " "
                + ("PUT".equals(mutation.operation)
                ? previousSize.text : changedSize) + " "
                + ("PUT".equals(mutation.operation)
                ? changedSize : previousSize.text) + ")", Sort.INT,
                IntegralWidth.JAVA_INT);
    }

    private static Mutation associativeMutation(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject relation = expression.getAsJsonObject();
        if (!EXPRESSION_TYPE.equals(string(relation, "_type"))
                || !"ASSOCIATIVE".equals(string(relation, "shape"))) {
            return null;
        }
        String operation = string(relation, "operation");
        JsonArray arguments = array(relation, "arguments");
        int arity = emptiesState(operation) ? 0
                : "REMOVE".equals(operation) ? 1
                : "REMOVE_IF".equals(operation) ? 1
                : "PUT".equals(operation) ? 2 : -1;
        if (arity < 0 || arguments.size() != arity) return null;
        // A conditional remove must state its guard; without it the op is
        // malformed and the codec refuses it rather than dropping the guard.
        JsonElement guard = "REMOVE_IF".equals(operation)
                ? relation.get("guard") : null;
        if ("REMOVE_IF".equals(operation)
                && (guard == null || guard.isJsonNull())) {
            return null;
        }
        return new Mutation(operation, relation.get("receiver"), arguments,
                guard);
    }

    private static Entry entry(JsonElement expression, Host host) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject next = expression.getAsJsonObject();
        if (!EXPRESSION_TYPE.equals(string(next, "_type"))
                || !"NEXT".equals(string(next, "operation"))) return null;
        JsonArray positions = array(next, "arguments");
        if (positions.size() != 1) return null;
        Term index = host.operand(positions.get(0), Sort.INT);
        JsonElement cursor = next.get("receiver");
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject view = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(view, "_type"))) break;
            String operation = string(view, "operation");
            if ("ITERATOR".equals(operation)
                    || "ENTRY_VIEW".equals(operation)) {
                cursor = view.get("receiver");
                continue;
            }
            break;
        }
        Term state = associativeState(cursor, host);
        return state == null || index == null ? null
                : new Entry(state, index);
    }

    private static View view(JsonElement expression, Host host) {
        JsonElement cursor = expression;
        String kind = "";
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject operation = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(operation, "_type"))) break;
            String name = string(operation, "operation");
            if ("ENTRY_VIEW".equals(name) || "KEY_VIEW".equals(name)
                    || "VALUE_VIEW".equals(name)) {
                kind = name;
                cursor = operation.get("receiver");
                break;
            }
            if (!"ITERATOR".equals(name)) break;
            cursor = operation.get("receiver");
        }
        if (kind.isEmpty()) kind = selectedReadViewKind(cursor);
        Term state = associativeState(cursor, host);
        return kind.isEmpty() || state == null ? null : new View(kind, state);
    }

    /** Lowers the selected map state beneath iterator/view wrappers. */
    private static Term associativeState(JsonElement expression, Host host) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(relation, "_type"))) break;
            String operation = string(relation, "operation");
            if (!"ITERATOR".equals(operation)
                    && !"ENTRY_VIEW".equals(operation)
                    && !"KEY_VIEW".equals(operation)
                    && !"VALUE_VIEW".equals(operation)) {
                break;
            }
            cursor = relation.get("receiver");
        }
        if (cursor != null && cursor.isJsonObject()
                && "ReadFromExpression".equals(string(
                cursor.getAsJsonObject(), "_type"))) {
            String kind = selectedReadViewKind(cursor);
            if (!kind.isEmpty()) {
                cursor = selectedReadViewState(
                        cursor.getAsJsonObject(), kind);
            }
        }
        Term state = host.operand(cursor, Sort.ASSOCIATIVE);
        if (state != null && state.sort != Sort.ASSOCIATIVE) {
            host.unsupported("ContainerRelation:ASSOCIATIVE:state-sort="
                    + state.sort);
            return null;
        }
        return state;
    }

    /**
     * Recovers the view operation at a version-selected map read.
     *
     * <p>The VM keeps the exact {@code VALUE_VIEW}/{@code KEY_VIEW} operation
     * in every known writer arm of a {@code ReadFromExpression}.  The wrapper
     * itself is the selector over those arms, so an iterator sees the wrapper
     * rather than the view node directly.  The projection remains exact when
     * every known arm agrees; an unknown-writer arm still belongs to this same
     * call-site view and is lowered through the wrapper's selected state.</p>
     */
    private static String selectedReadViewKind(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if (EXPRESSION_TYPE.equals(string(object, "_type"))) {
            String operation = string(object, "operation");
            if ("ENTRY_VIEW".equals(operation)
                    || "KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) {
                return operation;
            }
            return "ITERATOR".equals(operation)
                    ? selectedReadViewKind(object.get("receiver")) : "";
        }
        if (!"ReadFromExpression".equals(string(object, "_type"))) {
            return "";
        }
        String selected = "";
        for (JsonElement element : array(object, "candidates")) {
            if (!element.isJsonObject()) continue;
            JsonObject arm = element.getAsJsonObject();
            if (bool(arm, "unknown", false)) continue;
            String candidate = selectedReadViewKind(arm.get("expression"));
            if (candidate.isEmpty()) return "";
            if (!selected.isEmpty() && !selected.equals(candidate)) {
                return "";
            }
            selected = candidate;
        }
        return selected;
    }

    /**
     * Moves a common view outside a read-from choice so every selector arm
     * denotes an {@code AssocState}, including the unknown-writer arm.
     */
    private static JsonObject selectedReadViewState(
            JsonObject read, String kind) {
        JsonObject normalized = read.deepCopy();
        normalized.addProperty("_java_type", "java/util/Map");
        for (JsonElement element : array(normalized, "candidates")) {
            if (!element.isJsonObject()) return null;
            JsonObject arm = element.getAsJsonObject();
            JsonElement expression = arm.get("expression");
            if (bool(arm, "unknown", false)) {
                JsonObject state = new JsonObject();
                state.addProperty("_type", EXPRESSION_TYPE);
                state.addProperty("shape", "ASSOCIATIVE");
                state.addProperty("operation", "STATE");
                state.addProperty("_java_type", "java/util/Map");
                state.add("receiver", expression == null
                        ? null : expression.deepCopy());
                state.add("arguments", new JsonArray());
                arm.add("expression", state);
                continue;
            }
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject view = expression.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(string(view, "_type"))
                    || !kind.equals(string(view, "operation"))
                    || view.get("receiver") == null) {
                return null;
            }
            arm.add("expression", view.get("receiver").deepCopy());
        }
        JsonArray normalizedCandidates = array(normalized, "candidates");
        if (normalizedCandidates.size() == 0) return null;
        JsonElement selection = normalizedCandidates
                .get(normalizedCandidates.size() - 1)
                .getAsJsonObject().get("expression").deepCopy();
        for (int index = normalizedCandidates.size() - 2;
             index >= 0; index--) {
            JsonObject arm = normalizedCandidates.get(index)
                    .getAsJsonObject();
            String selector = string(arm, "selector");
            if (selector.isEmpty()) return null;
            JsonObject ite = new JsonObject();
            ite.addProperty("_type", "IteExpression");
            ite.addProperty("selector", selector);
            ite.add("then", arm.get("expression").deepCopy());
            ite.add("else", selection);
            selection = ite;
        }
        normalized.add("ite", selection);
        return normalized;
    }

    /**
     * Canonical map-state form for eager read-from cataloguing.
     *
     * <p>The composer catalogs recorded reads before it sees their iterator
     * use.  Exposing the same normalization used by {@link #associativeState}
     * prevents that eager pass from memoizing a common map view as a plain
     * Java reference.</p>
     */
    static JsonObject selectedReadViewState(JsonObject read) {
        String kind = selectedReadViewKind(read);
        return kind.isEmpty() ? null : selectedReadViewState(read, kind);
    }

    /**
     * The one lowering of a boxed container {@code Value} back to the Java
     * sort it holds.  The caller resolves the Java type to {@code cellSort}
     * because the two encoders answer that question differently.
     */
    static Term unboxValue(Term value, String javaType, Sort cellSort,
                           Host host) {
        if (value == null || value.sort != Sort.VALUE) return value;
        String kind = valueKind(javaType);
        if (!kind.isEmpty()) {
            host.require("((_ is " + kind + ") " + value.text + ")");
        }
        String integralValue = unboxIntegral(value.text, javaType);
        if (!integralValue.isEmpty()) {
            return new Term(integralValue, Sort.INT,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
        }
        if (cellSort == Sort.BOOL) {
            return new Term("(valueBool " + value.text + ")", Sort.BOOL);
        }
        if (cellSort == Sort.REF) {
            return new Term("(valueRef " + value.text + ")", Sort.REF);
        }
        if (cellSort == Sort.FLOAT32) {
            return new Term("(valueFloat " + value.text + ")", Sort.FLOAT32);
        }
        if (cellSort == Sort.FLOAT64) {
            return new Term("(valueDouble " + value.text + ")",
                    Sort.FLOAT64);
        }
        if (cellSort == Sort.STRING) {
            return new Term("(valueString " + value.text + ")", Sort.STRING);
        }
        return value;
    }

    public interface Host {
        Term state(JsonElement identity, Sort shape);

        Term operand(JsonElement expression, Sort expected);

        /**
         * Whether an externally evidenced container identity must survive
         * local select-over-store simplification.
         */
        default boolean preserveContainerIdentity(JsonElement expression,
                                                  Sort expected) {
            return false;
        }

        Term box(JsonElement expression);

        Term unbox(Term value, String javaType);

        void require(String predicate);

        Term field(Term owner, String ownerClass, int fieldOffset,
                   String javaType);

        void unsupported(String reason);
    }

    public enum Sort {
        BOOL, INT, FLOAT32, FLOAT64, STRING, REF, VALUE,
        INDEXED, ASSOCIATIVE
    }

    public static final class Term {
        public final String text;
        public final Sort sort;
        final IntegralWidth integralWidth;

        public Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE);
        }

        Term(String text, Sort sort, IntegralWidth integralWidth) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT
                    && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
        }
    }

    private static final class Entry {
        private final Term state;
        private final Term index;

        private Entry(Term state, Term index) {
            this.state = state;
            this.index = index;
        }
    }

    private static final class View {
        private final String kind;
        private final Term state;

        private View(String kind, Term state) {
            this.kind = kind;
            this.state = state;
        }
    }

    private static final class Mutation {
        private final String operation;
        private final JsonElement receiver;
        private final JsonArray arguments;
        /** The symbolic branch predicate a conditional remove fired under,
         *  or {@code null} for an unconditional PUT/REMOVE.  Only
         *  {@code REMOVE_IF} carries one: the recorded {@code expiry < now}
         *  guard of a {@code removeExpiredKeys} {@code it.remove()}. */
        private final JsonElement guard;

        private Mutation(String operation, JsonElement receiver,
                         JsonArray arguments, JsonElement guard) {
            this.operation = operation;
            this.receiver = receiver;
            this.arguments = arguments;
            this.guard = guard;
        }
    }

    static final class AssociativeRemovalEffect {
        final Term removedKey;
        final String precondition;

        private AssociativeRemovalEffect(Term removedKey,
                                         String precondition) {
            this.removedKey = removedKey;
            this.precondition = precondition;
        }
    }
}
