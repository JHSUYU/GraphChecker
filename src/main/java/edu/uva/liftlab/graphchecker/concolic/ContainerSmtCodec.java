package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The single SMT lowering for VM container operations.
 *
 * <p>Scalar expression decoding stays with the host solver.  This codec owns
 * only container algebra, so path solving and final composition cannot drift
 * into different select/store/size semantics.</p>
 */
public final class ContainerSmtCodec {
    public static final String EXPRESSION_TYPE = "ContainerRelation";

    private ContainerSmtCodec() {
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

    /**
     * Integral scalars share SMT {@code Int}; only their container {@code
     * Value} representation is tagged with the Java primitive kind.
     */
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

    /**
     * Requires the host to declare {@code Ref}, {@code nullRef} and the
     * canonical {@code Value} datatype.
     */
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
                "(define-fun assoc_remove ((s AssocState) (k Value))"
                        + " AssocState"
                        + " (ite (assoc_has s k)"
                        + " (let ((p (select (assoc_position s) k)))"
                        + " (mkAssocState"
                        + " (- (assoc_size s) 1)"
                        + " (store (assoc_present s) k false)"
                        + " (assoc_values s)"
                        + " (lambda ((q Int))"
                        + " (ite (and (<= p q)"
                        + " (< q (- (assoc_size s) 1)))"
                        + " (select (assoc_order s) (+ q 1))"
                        + " (select (assoc_order s) q)))"
                        + " (lambda ((key Value))"
                        + " (ite (= key k) (- 1)"
                        + " (ite (and (assoc_has s key)"
                        + " (> (select (assoc_position s) key) p))"
                        + " (- (select (assoc_position s) key) 1)"
                        + " (select (assoc_position s) key))))))"
                        + " s))"
        ));
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

    /**
     * VM array access contributes concrete bounds and symbolic read/size
     * relations to the PC.  They constrain a source branch but are not
     * branches themselves.
     */
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

    /**
     * Rewrites an indexed read to the element it provably selects.
     *
     * <p>Structural readers - the java.lang codec proofs above all - inspect
     * the recorded expression rather than the lowered term, so they need the
     * same select-over-store identity {@link #term} applies.  An expression
     * that decides nothing is returned unchanged.</p>
     */
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

    /**
     * Resolves {@code READ(WRITE(s, j, v), i)} to the stored {@code v}.
     *
     * <p>This is the ordinary select-over-store identity, decided only on
     * exact integer literals: {@code i == j} selects the written value, and
     * a literally different {@code j} cannot have written index {@code i},
     * so the search continues into that write's receiver.  An index that is
     * not an exact literal on either side decides nothing, so the ordinary
     * select-over-store encoding is kept and the solver reasons about it.</p>
     *
     * <p>Resolving here rather than after lowering also keeps the write
     * chain's unrelated element expressions out of the formula entirely,
     * which is what {@code (store ... )} means: they cannot be observed
     * through this read.</p>
     */
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

    /**
     * Skips the writes a size query cannot observe.
     *
     * <p>{@code indexed_write} rebuilds the state with {@code (indexed_size
     * s)} unchanged, so a size taken over a write chain is the size of the
     * state underneath it.  Only {@code WRITE} is size preserving; append,
     * insert, and remove all change the size and stop the walk.</p>
     */
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
            Term state = host.operand(expression.get("receiver"), stateSort);
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
        if ("CLEAR".equals(operation)) {
            if (arguments.size() != 0) {
                host.unsupported("ContainerRelation:" + shape
                        + ":CLEAR:arity=" + arguments.size());
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
            if ("READ".equals(operation) && arguments.size() == 1) {
                JsonElement stored = storedIndexedWrite(receiverIr,
                        arguments.get(0));
                if (stored != null) {
                    return host.unbox(host.box(stored), javaType);
                }
            }
            if ("SIZE".equals(operation)) {
                receiverIr = sizePreservingIndexedReceiver(receiverIr);
            }
            Term receiver = host.operand(receiverIr, Sort.INDEXED);
            if (receiver == null) return null;
            if ("ITERATOR".equals(operation)) return receiver;
            if ("SIZE".equals(operation)) {
                return new Term("(indexed_size " + receiver.text + ")",
                        Sort.INT);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                Term index = host.operand(arguments.get(0), Sort.INT);
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
            Term receiver = host.operand(expression.get("receiver"),
                    Sort.ASSOCIATIVE);
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
                return index == null ? null
                        : new Term("(assoc_remove " + receiver.text
                        + " (assoc_key_at " + receiver.text + " "
                        + index.text + "))", Sort.ASSOCIATIVE);
            }
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : new Term("(assoc_remove " + receiver.text + " "
                        + key.text + ")", Sort.ASSOCIATIVE);
            }
        }
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
    }

    /**
     * Projects order-independent observations through associative mutations.
     * Iterator operations still consume the full {@link AssocState}, including
     * order and position, but a keyed lookup does not need either component.
     */
    private static Term associativeHas(
            JsonElement expression, Term key, Host host) {
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            return state == null ? null
                    : new Term("(assoc_has " + state.text + " "
                    + key.text + ")", Sort.BOOL);
        }
        if ("CLEAR".equals(mutation.operation)) {
            return new Term("false", Sort.BOOL);
        }
        Term mutatedKey = host.box(mutation.arguments.get(0));
        Term previous = associativeHas(mutation.receiver, key, host);
        if (mutatedKey == null || previous == null) return null;
        String sameKey = "(= " + key.text + " " + mutatedKey.text + ")";
        return "PUT".equals(mutation.operation)
                ? new Term("(or " + sameKey + " " + previous.text + ")",
                Sort.BOOL)
                : new Term("(and (not " + sameKey + ") "
                + previous.text + ")", Sort.BOOL);
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
        if ("CLEAR".equals(mutation.operation)) {
            return new Term("(VRef nullRef)", Sort.VALUE);
        }
        Term mutatedKey = host.box(mutation.arguments.get(0));
        Term previous = associativeRead(mutation.receiver, key, host);
        if (mutatedKey == null || previous == null) return null;
        Term mutatedValue = "PUT".equals(mutation.operation)
                ? host.box(mutation.arguments.get(1))
                : new Term("(VRef nullRef)", Sort.VALUE);
        return mutatedValue == null ? null : new Term(
                "(ite (= " + key.text + " " + mutatedKey.text + ") "
                        + mutatedValue.text + " " + previous.text + ")",
                Sort.VALUE);
    }

    private static Term associativeSize(JsonElement expression, Host host) {
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            return state == null ? null
                    : new Term("(assoc_size " + state.text + ")", Sort.INT);
        }
        if ("CLEAR".equals(mutation.operation)) {
            return new Term("0", Sort.INT);
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
                ? changedSize : previousSize.text) + ")", Sort.INT);
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
        int arity = "CLEAR".equals(operation) ? 0
                : "REMOVE".equals(operation) ? 1
                : "PUT".equals(operation) ? 2 : -1;
        return arity >= 0 && arguments.size() == arity
                ? new Mutation(operation, relation.get("receiver"), arguments)
                : null;
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
        Term state = host.operand(cursor, Sort.ASSOCIATIVE);
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
        Term state = host.operand(cursor, Sort.ASSOCIATIVE);
        return kind.isEmpty() || state == null ? null : new View(kind, state);
    }

    public interface Host {
        Term state(JsonElement identity, Sort shape);

        Term operand(JsonElement expression, Sort expected);

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

        private Mutation(String operation, JsonElement receiver,
                         JsonArray arguments) {
            this.operation = operation;
            this.receiver = receiver;
            this.arguments = arguments;
        }
    }
}
