package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** The single SMT lowering for VM container operations. */
public final class ContainerSmtCodec {
    public static final String EXPRESSION_TYPE = "ContainerRelation";
    /** Process-local projection nodes; never emitted by the VM or persisted. */
    private static final String SCALAR_ASSOC_MEMBER =
            "__SCALAR_ASSOC_MEMBER";
    private static final String SCALAR_ASSOC_NEXT = "__SCALAR_ASSOC_NEXT";
    private static final String SCALAR_ASSOC_HAS = "__SCALAR_ASSOC_HAS";
    private static final String SCALAR_ASSOC_READ = "__SCALAR_ASSOC_READ";
    private static final String SCALAR_ASSOC_SIZE = "__SCALAR_ASSOC_SIZE";

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
        return "(define-fun assoc_remove ((s AssocState) (k Value))"
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
                + " (lambda ((q Value))"
                + " (ite (= q k) (- 1)"
                + " (ite (and (assoc_has s q)"
                + " (> (select (assoc_position s) q) p))"
                + " (- (select (assoc_position s) q) 1)"
                + " (select (assoc_position s) q))))))"
                + " s))";
    }

    public static boolean handles(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && EXPRESSION_TYPE.equals(
                optionalString(expression.getAsJsonObject(), "_type"));
    }

    public static boolean handlesField(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                && "FieldAccessExpression".equals(
                optionalString(expression.getAsJsonObject(), "_type"));
    }

    public static boolean handlesFieldBinding(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject binary = expression.getAsJsonObject();
        String position = optionalString(binary, "_code_position");
        if (!"BinaryExpression".equals(optionalString(binary, "_type"))
                || !"==".equals(optionalString(binary, "_op"))
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
        if (!"BinaryExpression".equals(optionalString(binary, "_type"))) {
            return false;
        }
        JsonElement left = binary.get("_left");
        JsonElement right = binary.get("_right");
        return handles(left) || handles(right)
                || constant(left) && constant(right);
    }

    /** The VM's three constant-payload node kinds, stated once. */
    public static boolean constant(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        return constantKind(
                optionalString(expression.getAsJsonObject(), "_type"));
    }

    /** Whether one already-read {@code _type} names a constant payload. */
    public static boolean constantKind(String type) {
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
                optionalString(expression.getAsJsonObject(), "_type"));
    }

    public static Term field(JsonObject expression, Host host) {
        Term owner = host.operand(expression.get("owner"), Sort.REF);
        if (owner == null) return null;
        String ownerClass = optionalString(expression, "ownerClass");
        String javaType = optionalString(expression, "_java_type");
        if (boxedPrimitiveValue(owner, ownerClass, javaType)) {
            return owner;
        }
        return host.field(owner, ownerClass,
                JsonFields.optionalInteger(expression, "fieldOffset", -1), javaType);
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
     * Whether one container receiver carries identity that runtime evidence,
     * not this encoder, is the authority for.
     *
     * <p>Select-over-store and the size-preserving receiver skip are exact
     * on a state term this encoder built itself.  Applied to an evidenced
     * carrier they are still exact in value, but they drop the published
     * version chain out of the formula: the selected read then stands alone,
     * constrained by no writer and by none of the carrier's state axioms.
     * A host answers true here to keep the carrier's own state term - and so
     * its read-from arms - in the formula the solver sees.</p>
     */
    public static boolean evidencedContainerIdentity(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        if (SharedStateEvidence.GUARDED_READ_TYPE.equals(
                optionalString(node, "_type"))
                || VmExpressionIr.isConsumerBoundary(node)
                || VmExpressionIr.isConsumerBoundaryReference(node)
                || VmExpressionIr.isCanonicalMapStateReference(
                optionalString(node, "_exp"))) {
            return true;
        }
        // A local mutation inherits the identity of the state it rests on.
        return EXPRESSION_TYPE.equals(optionalString(node, "_type"))
                && evidencedContainerIdentity(node.get("receiver"));
    }

    /** Rewrites an indexed read to the element it provably selects. */
    static JsonElement selectedIndexedElement(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            return expression;
        }
        JsonObject object = expression.getAsJsonObject();
        JsonArray arguments = array(object, "arguments");
        if (!EXPRESSION_TYPE.equals(optionalString(object, "_type"))
                || !"INDEXED".equals(optionalString(object, "shape"))
                || !"READ".equals(optionalString(object, "operation"))
                || arguments.size() != 1) {
            return expression;
        }
        JsonElement stored = storedIndexedWrite(object.get("receiver"),
                arguments.get(0), optionalString(object, "_java_type"));
        return stored == null ? expression : selectedIndexedElement(stored);
    }

    /** Resolves {@code READ(WRITE(s, j, v), i)} to the stored {@code v}. */
    private static JsonElement storedIndexedWrite(JsonElement receiver,
                                                  JsonElement index,
                                                  String selectedJavaType) {
        Integer wanted = exactIndexLiteral(index);
        if (wanted == null) return null;
        return storedIndexedWrite(receiver, wanted, selectedJavaType);
    }

    /**
     * Projects one literal indexed read through value-propagation wrappers.
     * The wrapper is retained because its selector and dynamic event remain
     * the authority for the value even when select-over-store is exact.
     */
    private static JsonElement storedIndexedWrite(JsonElement receiver,
                                                  int wanted,
                                                  String selectedJavaType) {
        if (receiver == null || !receiver.isJsonObject()) return null;
        JsonObject root = receiver.getAsJsonObject();
        if (VmExpressionIr.isConsumerBoundary(root)
                || VmExpressionIr.isConsumerBoundaryReference(root)) {
            JsonElement selected = storedIndexedWrite(
                    root.get(VmExpressionIr.EXPRESSION), wanted,
                    selectedJavaType);
            if (selected == null) return null;
            JsonObject projected = copyWithout(root,
                    VmExpressionIr.EXPRESSION);
            projected.addProperty("_java_type", selectedJavaType);
            projected.add(VmExpressionIr.EXPRESSION, selected);
            return projected;
        }
        String type = optionalString(root, "_type");
        String armsField = SymbolicPropagationClosure.ITE_TYPE.equals(type)
                ? "arms" : SharedStateEvidence.GUARDED_READ_TYPE.equals(type)
                ? "candidates" : "";
        if (!armsField.isEmpty()) {
            JsonArray arms = array(root, armsField);
            if (arms.size() == 0) return null;
            JsonObject projected = copyWithout(root, armsField);
            projected.addProperty("_java_type", selectedJavaType);
            JsonArray projectedArms = new JsonArray();
            for (JsonElement element : arms) {
                if (!element.isJsonObject()) return null;
                JsonObject arm = element.getAsJsonObject();
                if (optionalString(arm, "selector").isEmpty()
                        || arm.get("expression") == null) {
                    return null;
                }
                JsonElement selected = storedIndexedWrite(
                        arm.get("expression"), wanted, selectedJavaType);
                if (selected == null) return null;
                JsonObject projectedArm = copyWithout(arm, "expression");
                projectedArm.add("expression", selected);
                projectedArms.add(projectedArm);
            }
            projected.add(armsField, projectedArms);
            return projected;
        }
        JsonElement cursor = receiver;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject node = cursor.getAsJsonObject();
            JsonArray arguments = array(node, "arguments");
            if (!EXPRESSION_TYPE.equals(optionalString(node, "_type"))
                    || !"INDEXED".equals(optionalString(node, "shape"))
                    || !"WRITE".equals(optionalString(node, "operation"))) {
                break;
            }
            if (arguments.size() != 2) return null;
            Integer written = exactIndexLiteral(arguments.get(0));
            if (written == null) return null;
            if (written.intValue() == wanted) {
                return arguments.get(1).deepCopy();
            }
            cursor = node.get("receiver");
        }
        // A local WRITE prefix may itself rest on a propagated array family.
        return cursor == receiver ? null
                : storedIndexedWrite(cursor, wanted, selectedJavaType);
    }

    /** Copies wrapper metadata without first cloning its large payload. */
    private static JsonObject copyWithout(JsonObject source, String omitted) {
        JsonObject result = new JsonObject();
        for (java.util.Map.Entry<String, JsonElement> entry
                : source.entrySet()) {
            if (!omitted.equals(entry.getKey())) {
                result.add(entry.getKey(), entry.getValue().deepCopy());
            }
        }
        return result;
    }

    /** Skips the writes a size query cannot observe. */
    private static JsonElement sizePreservingIndexedReceiver(
            JsonElement receiver) {
        JsonElement cursor = receiver;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject node = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(optionalString(node, "_type"))
                    || !"INDEXED".equals(optionalString(node, "shape"))
                    || !"WRITE".equals(optionalString(node, "operation"))
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
        String type = optionalString(object, "_type");
        if (!"ConstExpr".equals(type) && !"ConSymbolExp".equals(type)) {
            return null;
        }
        String javaType = optionalString(object, "_java_type");
        if (!"I".equals(javaType) && !"int".equals(javaType)) return null;
        String payload = optionalString(object, "_exp");
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
        ProjectionMemo memo = new ProjectionMemo();
        String shape = optionalString(expression, "shape");
        String operation = optionalString(expression, "operation");
        String javaType = optionalString(expression, "_java_type");
        if ("ASSOCIATIVE".equals(shape)
                && (SCALAR_ASSOC_MEMBER.equals(operation)
                || SCALAR_ASSOC_NEXT.equals(operation)
                || SCALAR_ASSOC_HAS.equals(operation)
                || SCALAR_ASSOC_READ.equals(operation)
                || SCALAR_ASSOC_SIZE.equals(operation))) {
            JsonArray positions = array(expression, "arguments");
            JsonElement state = expression.get("receiver");
            int arity = SCALAR_ASSOC_SIZE.equals(operation) ? 0 : 1;
            if (positions.size() != arity || !scalarAssociativeLeaf(state)) {
                host.unsupported("ContainerRelation:ASSOCIATIVE:"
                        + operation);
                return null;
            }
            if (SCALAR_ASSOC_SIZE.equals(operation)) {
                return associativeSize(state, host, memo);
            }
            if (SCALAR_ASSOC_HAS.equals(operation)
                    || SCALAR_ASSOC_READ.equals(operation)) {
                Term key = host.box(positions.get(0));
                if (key == null) return null;
                return SCALAR_ASSOC_HAS.equals(operation)
                        ? associativeHas(state, key, host, memo)
                        : host.unbox(associativeRead(state, key, host, memo),
                        javaType);
            }
            Term index = host.operand(positions.get(0), Sort.INT);
            if (index == null) return null;
            if (SCALAR_ASSOC_MEMBER.equals(operation)) {
                return associativeMemberAt(state, index, host, memo);
            }
            String viewKind = optionalString(expression, "viewKind");
            Term value = associativeElementAt(state, index, viewKind, host,
                    memo);
            return value == null ? null : host.unbox(value, javaType);
        }
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
            Entry entry = entry(expression.get("receiver"));
            if (entry == null) {
                host.unsupported("ContainerRelation:malformed-entry:"
                        + operation);
                return null;
            }
            Term value = associativeEntryValue(entry,
                    "KEY".equals(operation) ? "KEY_VIEW" : "VALUE_VIEW",
                    javaType, host, memo);
            return value == null ? null : host.unbox(value, javaType);
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
            View view = view(expression.get("receiver"));
            JsonArray positions = array(expression, "arguments");
            if (view == null || positions.size() != 1
                    || "ENTRY_VIEW".equals(view.kind)) {
                host.unsupported(
                        "ContainerRelation:ASSOCIATIVE:NEXT:view");
                return null;
            }
            Term value = associativeEntryValue(new Entry(
                    view.stateExpression, positions.get(0)), view.kind,
                    javaType, host, memo);
            return value == null ? null : host.unbox(value, javaType);
        }
        if ("OBSERVE_KEY".equals(operation)
                || "OBSERVE_VALUE".equals(operation)) {
            Entry entry = entry(expression.get("receiver"));
            JsonArray observed = array(expression, "arguments");
            if (entry == null || observed.size() != 1) {
                host.unsupported("ContainerRelation:malformed-observation:"
                        + operation);
                return null;
            }
            Term value = host.box(observed.get(0));
            if (value == null) return null;
            String observedJavaType = expressionJavaType(observed.get(0));
            Term selected = associativeEntryValue(entry,
                    "OBSERVE_KEY".equals(operation)
                            ? "KEY_VIEW" : "VALUE_VIEW",
                    observedJavaType, host, memo);
            if (selected == null) return null;
            return new Term("(= " + selected.text + " " + value.text + ")",
                    Sort.BOOL);
        }
        if ("HAS_NEXT".equals(operation)) {
            Sort stateSort = "INDEXED".equals(shape)
                    ? Sort.INDEXED : Sort.ASSOCIATIVE;
            JsonArray positions = array(expression, "arguments");
            Term position = positions.size() == 1
                    ? host.operand(positions.get(0), Sort.INT) : null;
            JsonElement stateExpression = stateSort == Sort.ASSOCIATIVE
                    ? associativeStateExpression(expression.get("receiver"))
                    : expression.get("receiver");
            Term state = stateSort == Sort.INDEXED
                    ? host.operand(stateExpression, stateSort) : null;
            Term size = stateSort == Sort.ASSOCIATIVE
                    ? projectedAssociativeObservation(stateExpression, null,
                    "I", SCALAR_ASSOC_SIZE, Sort.INT, host) : null;
            if (size == null && stateSort == Sort.ASSOCIATIVE) {
                size = associativeSize(stateExpression, host, memo);
            }
            if (position == null || stateSort == Sort.INDEXED && state == null
                    || stateSort == Sort.ASSOCIATIVE && size == null) {
                host.unsupported("ContainerRelation:" + shape
                        + ":HAS_NEXT");
                return null;
            }
            String sizeText = stateSort == Sort.INDEXED
                    ? "(indexed_size " + state.text + ")"
                    : size.text;
            return new Term("(and (<= 0 " + position.text + ") (< "
                    + position.text + " " + sizeText + "))", Sort.BOOL);
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
                        arguments.get(0), javaType);
                if (stored != null) {
                    return host.unbox(host.box(stored), javaType);
                }
            }
            if ("SIZE".equals(operation) && !preserveReceiver) {
                receiverIr = sizePreservingIndexedReceiver(receiverIr);
            }
            Term receiver = host.operand(receiverIr, Sort.INDEXED);
            if (receiver == null) return null;
            receiver = shared(receiver, host);
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
            JsonElement receiverIr = associativeStateExpression(
                    expression.get("receiver"));
            if ("SIZE".equals(operation)) {
                Term projected = projectedAssociativeObservation(receiverIr,
                        null, "I", SCALAR_ASSOC_SIZE, Sort.INT, host);
                return projected == null
                        ? associativeSize(receiverIr, host, memo) : projected;
            }
            if ("CONTAINS".equals(operation) && arguments.size() == 1) {
                Term projected = projectedAssociativeObservation(receiverIr,
                        arguments.get(0), "Z", SCALAR_ASSOC_HAS, Sort.BOOL,
                        host);
                if (projected != null) return projected;
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : associativeHas(receiverIr, key, host, memo);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                JsonElement projected = projectedAssociativeExpression(
                        receiverIr, arguments.get(0), javaType,
                        SCALAR_ASSOC_READ);
                if (projected != null) {
                    Term value = host.box(projected);
                    return value == null ? null
                            : host.unbox(value, javaType);
                }
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : host.unbox(associativeRead(
                        receiverIr, key, host, memo),
                        javaType);
            }
            if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
                Term size = projectedAssociativeObservation(receiverIr, null,
                        "I", SCALAR_ASSOC_SIZE, Sort.INT, host);
                if (size == null) {
                    size = associativeSize(receiverIr, host, memo);
                }
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
                return new Term("(let ((s " + receiver.text
                        + ")) (assoc_remove s (assoc_key_at s "
                        + index.text + ")))", Sort.ASSOCIATIVE);
            }
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : new Term("(assoc_remove " + receiver.text + " "
                        + key.text + ")", Sort.ASSOCIATIVE);
            }
            if ("REMOVE_IF".equals(operation) && arguments.size() == 1) {
                // A conditional remove drops the key when its guard holds and
                // otherwise preserves the map. Read/has short-circuit this via
                // the mutation walk; this form handles a nested receiver.
                Term key = host.box(arguments.get(0));
                Term guard = host.operand(expression.get("guard"), Sort.BOOL);
                return key == null || guard == null ? null
                        : new Term("(let ((s " + receiver.text + ")) (ite "
                        + guard.text + " (assoc_remove s " + key.text
                        + ") s))", Sort.ASSOCIATIVE);
            }
        }
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
    }

    /** Lowers one scalar observation through a complete propagation choice. */
    private static Term projectedAssociativeObservation(
            JsonElement state, JsonElement argument, String javaType,
            String projection, Sort expected, Host host) {
        JsonElement projected = projectedAssociativeExpression(state,
                argument, javaType, projection);
        return projected == null ? null : host.operand(projected, expected);
    }

    private static JsonElement projectedAssociativeExpression(
            JsonElement state, JsonElement argument, String javaType,
            String projection) {
        return propagationWrapper(state)
                ? projectAssociativeChoice(state, argument, "", javaType,
                projection) : null;
    }

    /** One positional key/value observation, retaining every choice guard. */
    private static Term associativeEntryValue(Entry entry, String viewKind,
                                              String javaType, Host host,
                                              ProjectionMemo memo) {
        if (propagationWrapper(entry.stateExpression)
                && javaType != null && !javaType.isEmpty()) {
            JsonElement member = projectAssociativeChoice(
                    entry.stateExpression, entry.indexExpression, viewKind,
                    javaType, SCALAR_ASSOC_MEMBER);
            JsonElement selected = projectAssociativeChoice(
                    entry.stateExpression, entry.indexExpression, viewKind,
                    javaType, SCALAR_ASSOC_NEXT);
            if (member != null && selected != null) {
                Term admitted = host.operand(member, Sort.BOOL);
                Term value = host.box(selected);
                if (admitted != null) host.require(admitted.text);
                return admitted == null ? null : value;
            }
        } else if (scalarAssociativeLeaf(entry.stateExpression)) {
            Term index = host.operand(entry.indexExpression, Sort.INT);
            Term admitted = index == null ? null : associativeMemberAt(
                    entry.stateExpression, index, host, memo);
            Term value = index == null ? null : associativeElementAt(
                    entry.stateExpression, index, viewKind, host, memo);
            if (admitted != null) host.require(admitted.text);
            return admitted == null ? null : value;
        }
        // An unfamiliar choice remains exact through the whole-state model.
        Term state = associativeState(entry.stateExpression, host);
        Term index = host.operand(entry.indexExpression, Sort.INT);
        if (state == null || index == null) return null;
        requireAssociativeMember(state, index, host);
        return new Term(("KEY_VIEW".equals(viewKind)
                ? "(assoc_key_at " : "(assoc_value_at ") + state.text + " "
                + index.text + ")", Sort.VALUE);
    }

    private static String expressionJavaType(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                ? optionalString(expression.getAsJsonObject(), "_java_type") : "";
    }

    private static Term associativeHas(
            JsonElement expression, Term key, Host host,
            ProjectionMemo memo) {
        Term cached = memo.get(memo.has, expression, key.text);
        if (cached != null) return cached;
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            if (state == null || state.sort != Sort.ASSOCIATIVE) {
                host.unsupported("ContainerRelation:ASSOCIATIVE:key-state");
                return null;
            }
            state = shared(state, host);
            Term result = state == null ? null : shared(new Term(
                    "(assoc_has " + state.text + " " + key.text + ")",
                    Sort.BOOL), host);
            return memo.put(memo.has, expression, key.text, result);
        }
        if (emptiesState(mutation.operation)) {
            return memo.put(memo.has, expression, key.text,
                    new Term("false", Sort.BOOL));
        }
        Term mutatedKey = memo.box(mutation.arguments.get(0), host);
        Term previous = associativeHas(mutation.receiver, key, host, memo);
        if (mutatedKey == null || previous == null) return null;
        String sameKey = "(= " + key.text + " " + mutatedKey.text + ")";
        Term result;
        if ("PUT".equals(mutation.operation)) {
            result = shared(new Term("(or " + sameKey + " "
                    + previous.text + ")", Sort.BOOL), host);
        } else if ("REMOVE_IF".equals(mutation.operation)) {
            // The key is present unless the guard fired for exactly this key.
            String guard = conditionalGuard(mutation, sameKey, host, memo);
            if (guard == null) return null;
            result = shared(new Term("(and (not " + guard + ") "
                    + previous.text + ")", Sort.BOOL), host);
        } else {
            result = shared(new Term("(and (not " + sameKey + ") "
                    + previous.text + ")", Sort.BOOL), host);
        }
        return memo.put(memo.has, expression, key.text, result);
    }

    /** Membership of one positional associative access without building the
     * intermediate map states. */
    private static Term associativeMemberAt(JsonElement expression,
                                            Term index, Host host,
                                            ProjectionMemo memo) {
        Term key = associativeKeyAt(expression, index, host, memo);
        Term size = associativeSize(expression, host, memo);
        Term present = key == null ? null
                : associativeHas(expression, key, host, memo);
        if (key == null || size == null || present == null) return null;
        return shared(new Term("(and (<= 0 " + index.text + ") (< "
                + index.text + " " + size.text + ") " + present.text
                + ")", Sort.BOOL), host);
    }

    /** One key/value view element after the exact mutation sequence. */
    private static Term associativeElementAt(JsonElement expression,
                                             Term index, String viewKind,
                                             Host host,
                                             ProjectionMemo memo) {
        Term key = associativeKeyAt(expression, index, host, memo);
        if (key == null) return null;
        if ("KEY_VIEW".equals(viewKind)) return key;
        return "VALUE_VIEW".equals(viewKind)
                ? associativeRead(expression, key, host, memo) : null;
    }

    /**
     * Resolves the key at an index through PUT/REMOVE/REMOVE_IF.  Removal
     * shifts a later key left by one; PUT appends only when the key was not
     * already present.  Arrays remain only at the recorded base state.
     */
    private static Term associativeKeyAt(JsonElement expression, Term index,
                                         Host host, ProjectionMemo memo) {
        Term cached = memo.get(memo.keys, expression, index.text);
        if (cached != null) return cached;
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            if (state == null || state.sort != Sort.ASSOCIATIVE) {
                host.unsupported(
                        "ContainerRelation:ASSOCIATIVE:position-state");
                return null;
            }
            state = shared(state, host);
            Term result = state == null ? null : shared(new Term(
                    "(assoc_key_at " + state.text + " " + index.text + ")",
                    Sort.VALUE), host);
            return memo.put(memo.keys, expression, index.text, result);
        }
        if (emptiesState(mutation.operation)) {
            return memo.put(memo.keys, expression, index.text,
                    new Term("(VRef nullRef)", Sort.VALUE));
        }
        Term mutatedKey = memo.box(mutation.arguments.get(0), host);
        Term previous = associativeKeyAt(mutation.receiver, index, host,
                memo);
        if (mutatedKey == null || previous == null) return null;
        Term result;
        if ("PUT".equals(mutation.operation)) {
            Term present = associativeHas(mutation.receiver, mutatedKey, host,
                    memo);
            Term size = associativeSize(mutation.receiver, host, memo);
            if (present == null || size == null) return null;
            String appended = "(and (not " + present.text + ") (= "
                    + index.text + " " + size.text + "))";
            result = shared(new Term("(ite " + appended + " "
                    + mutatedKey.text + " " + previous.text + ")",
                    Sort.VALUE), host);
            return memo.put(memo.keys, expression, index.text, result);
        }
        Term removedPosition = associativePosition(mutation.receiver,
                mutatedKey, host, memo);
        Term happens = associativeRemovalHappens(mutation, mutatedKey, host,
                memo);
        Term shifted = associativeKeyAt(mutation.receiver,
                new Term("(+ " + index.text + " 1)", Sort.INT), host,
                memo);
        if (removedPosition == null || happens == null || shifted == null) {
            return null;
        }
        String shifts = "(and " + happens.text + " (<= "
                + removedPosition.text + " " + index.text + "))";
        result = shared(new Term("(ite " + shifts + " " + shifted.text
                + " " + previous.text + ")", Sort.VALUE), host);
        return memo.put(memo.keys, expression, index.text, result);
    }

    /** Exact position of one key after the recorded mutation sequence. */
    private static Term associativePosition(JsonElement expression, Term key,
                                            Host host,
                                            ProjectionMemo memo) {
        Term cached = memo.get(memo.positions, expression, key.text);
        if (cached != null) return cached;
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            if (state == null) return null;
            state = shared(state, host);
            Term result = state == null ? null : shared(new Term(
                    "(select (assoc_position " + state.text + ") "
                            + key.text + ")", Sort.INT), host);
            return memo.put(memo.positions, expression, key.text, result);
        }
        if (emptiesState(mutation.operation)) {
            return memo.put(memo.positions, expression, key.text,
                    new Term("(- 1)", Sort.INT));
        }
        Term mutatedKey = memo.box(mutation.arguments.get(0), host);
        Term previous = associativePosition(mutation.receiver, key, host,
                memo);
        if (mutatedKey == null || previous == null) return null;
        String same = "(= " + key.text + " " + mutatedKey.text + ")";
        Term result;
        if ("PUT".equals(mutation.operation)) {
            Term present = associativeHas(mutation.receiver, mutatedKey, host,
                    memo);
            Term size = associativeSize(mutation.receiver, host, memo);
            if (present == null || size == null) return null;
            result = shared(new Term("(ite " + same + " (ite "
                    + present.text + " " + previous.text + " "
                    + size.text + ") " + previous.text + ")", Sort.INT),
                    host);
            return memo.put(memo.positions, expression, key.text, result);
        }
        Term removedPosition = associativePosition(mutation.receiver,
                mutatedKey, host, memo);
        Term happens = associativeRemovalHappens(mutation, mutatedKey, host,
                memo);
        Term keyPresent = associativeHas(mutation.receiver, key, host, memo);
        if (removedPosition == null || happens == null
                || keyPresent == null) return null;
        String moves = "(and " + keyPresent.text + " (> "
                + previous.text + " " + removedPosition.text + "))";
        String after = "(ite " + same + " (- 1) (ite " + moves
                + " (- " + previous.text + " 1) " + previous.text + "))";
        result = shared(new Term("(ite " + happens.text + " " + after
                + " " + previous.text + ")", Sort.INT), host);
        return memo.put(memo.positions, expression, key.text, result);
    }

    /** Whether this REMOVE/REMOVE_IF changes its receiver state. */
    private static Term associativeRemovalHappens(Mutation mutation,
                                                  Term mutatedKey,
                                                  Host host,
                                                  ProjectionMemo memo) {
        Term cached = memo.get(memo.removals, mutation.source,
                mutatedKey.text);
        if (cached != null) return cached;
        Term present = associativeHas(mutation.receiver, mutatedKey, host,
                memo);
        if (present == null) return null;
        Term result = present;
        if ("REMOVE_IF".equals(mutation.operation)) {
            Term guard = memo.operand(mutation.guard, Sort.BOOL, host);
            result = guard == null ? null : shared(new Term("(and "
                    + guard.text + " " + present.text + ")", Sort.BOOL),
                    host);
        }
        return memo.put(memo.removals, mutation.source, mutatedKey.text,
                result);
    }

    /** {@code guard AND key==removedKey}: the condition under which a
     *  {@code REMOVE_IF} deletes the key being read.  The guard is the
     *  recorded symbolic branch predicate, lowered as a boolean. */
    private static String conditionalGuard(Mutation mutation, String sameKey,
                                           Host host,
                                           ProjectionMemo memo) {
        Term guard = memo.operand(mutation.guard, Sort.BOOL, host);
        if (guard == null) return null;
        return "(and " + guard.text + " " + sameKey + ")";
    }

    private static Term associativeRead(
            JsonElement expression, Term key, Host host,
            ProjectionMemo memo) {
        Term cached = memo.get(memo.reads, expression, key.text);
        if (cached != null) return cached;
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            if (state == null) return null;
            state = shared(state, host);
            Term result = state == null ? null : shared(new Term(
                    "(let ((s " + state.text + ")) (ite (assoc_has s "
                            + key.text + ") (assoc_read s " + key.text
                            + ") (VRef nullRef)))", Sort.VALUE), host);
            return memo.put(memo.reads, expression, key.text, result);
        }
        if (emptiesState(mutation.operation)) {
            return memo.put(memo.reads, expression, key.text,
                    new Term("(VRef nullRef)", Sort.VALUE));
        }
        Term mutatedKey = memo.box(mutation.arguments.get(0), host);
        Term previous = associativeRead(mutation.receiver, key, host, memo);
        if (mutatedKey == null || previous == null) return null;
        String sameKey = "(= " + key.text + " " + mutatedKey.text + ")";
        Term mutatedValue = "PUT".equals(mutation.operation)
                ? memo.box(mutation.arguments.get(1), host)
                : new Term("(VRef nullRef)", Sort.VALUE);
        if (mutatedValue == null) return null;
        // A conditional remove deletes the read key only when its recorded
        // guard holds; flipping that guard can restore or remove the key.
        String condition = "REMOVE_IF".equals(mutation.operation)
                ? conditionalGuard(mutation, sameKey, host, memo) : sameKey;
        if (condition == null) return null;
        Term result = shared(new Term("(ite " + condition + " "
                + mutatedValue.text + " " + previous.text + ")",
                Sort.VALUE), host);
        return memo.put(memo.reads, expression, key.text, result);
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
        Term size = shared(new Term(text, Sort.INT,
                IntegralWidth.JAVA_INT), host);
        if (size == null) return null;
        host.require("(and (<= 0 " + size.text + ") (<= " + size.text + " "
                + domain.upper + "))");
        return size;
    }

    private static Term associativeSize(JsonElement expression, Host host,
                                        ProjectionMemo memo) {
        Term cached = memo.sizes.get(expression);
        if (cached != null) return cached;
        Mutation mutation = associativeMutation(expression);
        if (mutation == null) {
            Term state = host.operand(expression, Sort.ASSOCIATIVE);
            Term result = state == null ? null
                    : javaContainerSize("(assoc_size " + state.text + ")",
                    host);
            return memo.putSize(expression, result);
        }
        if (emptiesState(mutation.operation)) {
            return memo.putSize(expression,
                    new Term("0", Sort.INT, IntegralWidth.JAVA_INT));
        }
        Term key = memo.box(mutation.arguments.get(0), host);
        Term previousSize = associativeSize(mutation.receiver, host, memo);
        Term previouslyPresent = key == null ? null
                : associativeHas(mutation.receiver, key, host, memo);
        if (previousSize == null || previouslyPresent == null) return null;
        Term changes = "REMOVE_IF".equals(mutation.operation)
                ? associativeRemovalHappens(mutation, key, host, memo)
                : previouslyPresent;
        if (changes == null) return null;
        previousSize = shared(previousSize, host);
        changes = shared(changes, host);
        if (previousSize == null || changes == null) return null;
        String changedSize = "PUT".equals(mutation.operation)
                ? "(+ previous_size 1)" : "(- previous_size 1)";
        String value = "(let ((previous_size " + previousSize.text
                + ")) (ite " + changes.text + " "
                + ("PUT".equals(mutation.operation)
                ? "previous_size" : changedSize) + " "
                + ("PUT".equals(mutation.operation)
                ? changedSize : "previous_size") + "))";
        return memo.putSize(expression,
                new Term(value, Sort.INT, IntegralWidth.JAVA_INT));
    }

    private static Mutation associativeMutation(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject relation = expression.getAsJsonObject();
        if (!EXPRESSION_TYPE.equals(optionalString(relation, "_type"))
                || !"ASSOCIATIVE".equals(optionalString(relation, "shape"))) {
            return null;
        }
        String operation = optionalString(relation, "operation");
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
        return new Mutation(expression, operation, relation.get("receiver"),
                arguments, guard);
    }

    private static Entry entry(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject next = expression.getAsJsonObject();
        if (!EXPRESSION_TYPE.equals(optionalString(next, "_type"))
                || !"NEXT".equals(optionalString(next, "operation"))) return null;
        JsonArray positions = array(next, "arguments");
        if (positions.size() != 1) return null;
        JsonElement cursor = next.get("receiver");
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject view = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(optionalString(view, "_type"))) break;
            String operation = optionalString(view, "operation");
            if ("ITERATOR".equals(operation)
                    || "ENTRY_VIEW".equals(operation)) {
                cursor = view.get("receiver");
                continue;
            }
            break;
        }
        cursor = associativeStateExpression(cursor);
        return cursor == null ? null : new Entry(cursor, positions.get(0));
    }

    private static View view(JsonElement expression) {
        JsonElement cursor = expression;
        String kind = "";
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject operation = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(optionalString(operation, "_type"))) break;
            String name = optionalString(operation, "operation");
            if ("ENTRY_VIEW".equals(name) || "KEY_VIEW".equals(name)
                    || "VALUE_VIEW".equals(name)) {
                kind = name;
                cursor = operation.get("receiver");
                break;
            }
            if (!"ITERATOR".equals(name)) break;
            cursor = operation.get("receiver");
        }
        if (kind.isEmpty()) {
            kind = selectedReadViewKind(cursor);
            if (kind.isEmpty()) return null;
            cursor = selectedViewState(cursor, kind);
            if (cursor == null) return null;
        }
        return new View(kind, cursor);
    }

    /** True only for propagation choices whose metadata must survive a
     * scalar projection. */
    private static boolean propagationWrapper(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        String type = optionalString(object, "_type");
        return VmExpressionIr.isConsumerBoundary(object)
                || VmExpressionIr.isConsumerBoundaryReference(object)
                || SymbolicPropagationClosure.ITE_TYPE.equals(type)
                || SharedStateEvidence.GUARDED_READ_TYPE.equals(type);
    }

    /**
     * Rebuilds a propagation choice with a scalar map projection at every
     * leaf.  Success is all-or-nothing so no writer arm or selector can be
     * silently discarded.
     */
    private static JsonElement projectAssociativeChoice(
            JsonElement expression, JsonElement index, String viewKind,
            String selectedJavaType, String projection) {
        // A scalar String Term cannot carry the separate Java nullness bit
        // used by both hosts.  Keep String reads in the existing boxed
        // whole-state path until the codec Term can preserve that pair.
        if ((SCALAR_ASSOC_READ.equals(projection)
                || SCALAR_ASSOC_NEXT.equals(projection))
                && "VString".equals(valueKind(selectedJavaType))) {
            return null;
        }
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject root = expression.getAsJsonObject();
        String projectedJavaType = SCALAR_ASSOC_MEMBER.equals(projection)
                || SCALAR_ASSOC_HAS.equals(projection) ? "Z"
                : SCALAR_ASSOC_SIZE.equals(projection) ? "I"
                : selectedJavaType;
        if (VmExpressionIr.isConsumerBoundary(root)
                || VmExpressionIr.isConsumerBoundaryReference(root)) {
            JsonElement payload = projectAssociativeChoice(
                    root.get(VmExpressionIr.EXPRESSION), index, viewKind,
                    selectedJavaType, projection);
            if (payload == null) return null;
            JsonObject projected = copyWithout(root,
                    VmExpressionIr.EXPRESSION);
            projected.addProperty("_java_type", projectedJavaType);
            projected.add(VmExpressionIr.EXPRESSION, payload);
            return projected;
        }
        String type = optionalString(root, "_type");
        String armsField = SymbolicPropagationClosure.ITE_TYPE.equals(type)
                ? "arms" : SharedStateEvidence.GUARDED_READ_TYPE.equals(type)
                ? "candidates" : "";
        if (!armsField.isEmpty()) {
            JsonArray arms = array(root, armsField);
            if (arms.size() == 0) return null;
            JsonObject projected = copyWithout(root, armsField);
            projected.addProperty("_java_type", projectedJavaType);
            JsonArray projectedArms = new JsonArray();
            for (JsonElement element : arms) {
                if (!element.isJsonObject()) return null;
                JsonObject arm = element.getAsJsonObject();
                if (optionalString(arm, "selector").isEmpty()
                        || arm.get("expression") == null) return null;
                JsonElement payload = projectAssociativeChoice(
                        arm.get("expression"), index, viewKind,
                        selectedJavaType, projection);
                if (payload == null) return null;
                JsonObject projectedArm = copyWithout(arm, "expression");
                projectedArm.add("expression", payload);
                projectedArms.add(projectedArm);
            }
            projected.add(armsField, projectedArms);
            return projected;
        }
        if (!scalarAssociativeLeaf(root)) return null;
        JsonObject projected = new JsonObject();
        projected.addProperty("_type", EXPRESSION_TYPE);
        projected.addProperty("_java_type", projectedJavaType);
        projected.addProperty("shape", "ASSOCIATIVE");
        projected.addProperty("operation", projection);
        projected.addProperty("viewKind", viewKind);
        projected.add("receiver", root);
        JsonArray positions = new JsonArray();
        if (index != null) positions.add(index.deepCopy());
        projected.add("arguments", positions);
        return projected;
    }

    /** The exact mutation subset supported by scalar positional lowering. */
    private static boolean scalarAssociativeLeaf(JsonElement expression) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            if (propagationWrapper(cursor)) return false;
            Mutation mutation = associativeMutation(cursor);
            if (mutation != null) {
                if (emptiesState(mutation.operation)) return true;
                cursor = mutation.receiver;
                continue;
            }
            JsonObject object = cursor.getAsJsonObject();
            if (EXPRESSION_TYPE.equals(optionalString(object, "_type"))
                    && "ASSOCIATIVE".equals(optionalString(object, "shape"))) {
                return "STATE".equals(optionalString(object, "operation"))
                        && object.get("receiver") != null
                        && !propagationWrapper(object.get("receiver"));
            }
            // An arbitrary Java expression might lower as an Int/Ref.  Let
            // the exact whole-state path validate it instead of assuming it
            // is a map state for the scalar fast path.
            return false;
        }
        return false;
    }

    /** Lowers the selected map state beneath iterator/view wrappers. */
    private static Term associativeState(JsonElement expression, Host host) {
        JsonElement cursor = associativeStateExpression(expression);
        Term state = host.operand(cursor, Sort.ASSOCIATIVE);
        if (state != null && state.sort != Sort.ASSOCIATIVE) {
            host.unsupported("ContainerRelation:ASSOCIATIVE:state-sort="
                    + state.sort);
            return null;
        }
        return shared(state, host);
    }

    /** Retains the JSON state so scalar observations can cross its choices. */
    private static JsonElement associativeStateExpression(
            JsonElement expression) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject relation = cursor.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(optionalString(relation, "_type"))) break;
            String operation = optionalString(relation, "operation");
            if (!"ITERATOR".equals(operation)
                    && !"ENTRY_VIEW".equals(operation)
                    && !"KEY_VIEW".equals(operation)
                    && !"VALUE_VIEW".equals(operation)) {
                break;
            }
            cursor = relation.get("receiver");
        }
        String kind = selectedReadViewKind(cursor);
        if (!kind.isEmpty()) {
            cursor = selectedViewState(cursor, kind);
            if (cursor == null) return null;
        }
        return cursor;
    }

    /** Names a pure subterm when the host supports DAG sharing. */
    private static Term shared(Term value, Host host) {
        if (value == null) return null;
        Term result = host.share(value);
        if (result == null || result.sort != value.sort) {
            host.unsupported("ContainerRelation:shared-term-sort");
            return null;
        }
        return result;
    }

    /**
     * Recovers one common map view through propagation wrappers.
     *
     * <p>The VM keeps the exact {@code VALUE_VIEW}/{@code KEY_VIEW} operation
     * in every writer arm of a {@code ReadFromExpression}.  Consumer
     * boundaries and case merges preserve that choice structure, so an
     * iterator may see several wrappers rather than the view node directly.
     * The projection remains exact only when every recorded arm agrees.</p>
     */
    private static String selectedReadViewKind(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if (VmExpressionIr.isConsumerBoundary(object)
                || VmExpressionIr.isConsumerBoundaryReference(object)) {
            JsonElement payload = object.get(VmExpressionIr.EXPRESSION);
            return payload == null || !payload.isJsonObject() ? ""
                    : selectedReadViewKind(payload);
        }
        if (EXPRESSION_TYPE.equals(optionalString(object, "_type"))) {
            String operation = optionalString(object, "operation");
            if ("ENTRY_VIEW".equals(operation)
                    || "KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) {
                return operation;
            }
            return "ITERATOR".equals(operation)
                    ? selectedReadViewKind(object.get("receiver")) : "";
        }
        String type = optionalString(object, "_type");
        JsonArray arms;
        if (SymbolicPropagationClosure.ITE_TYPE.equals(type)) {
            arms = array(object, "arms");
        } else if ("ReadFromExpression".equals(type)) {
            arms = array(object, "candidates");
        } else {
            return "";
        }
        if (arms.size() == 0) return "";
        String selected = "";
        for (JsonElement element : arms) {
            if (!element.isJsonObject()) return "";
            JsonObject arm = element.getAsJsonObject();
            if (optionalString(arm, "selector").isEmpty()) return "";
            JsonElement armExpression = arm.get("expression");
            if (armExpression == null || !armExpression.isJsonObject()) {
                return "";
            }
            String candidate = selectedReadViewKind(armExpression);
            if (candidate.isEmpty()) return "";
            if (!selected.isEmpty() && !selected.equals(candidate)) {
                return "";
            }
            selected = candidate;
        }
        return selected;
    }

    /**
     * Projects one common view through the wrappers that preserve a selected
     * value.  Each returned arm or boundary payload denotes the underlying
     * {@code AssocState}; selectors and provenance stay on their original
     * wrappers.
     */
    private static JsonElement selectedViewState(
            JsonElement expression, String kind) {
        return selectedViewState(expression, kind,
                new IdentityHashMap<JsonElement, JsonElement>());
    }

    /** Copy-on-write projection over one decoder-owned expression DAG. */
    private static JsonElement selectedViewState(
            JsonElement expression, String kind,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (expression == null || !expression.isJsonObject()
                || kind == null || kind.isEmpty()) {
            return null;
        }
        if (memo.containsKey(expression)) {
            return memo.get(expression);
        }
        JsonObject object = expression.getAsJsonObject();
        if (VmExpressionIr.isConsumerBoundary(object)
                || VmExpressionIr.isConsumerBoundaryReference(object)) {
            JsonElement payload = selectedViewState(
                    object.get(VmExpressionIr.EXPRESSION), kind, memo);
            if (payload == null) return null;
            JsonObject normalized = JsonFields.shallowCopy(object);
            normalized.addProperty("_java_type", "java/util/Map");
            normalized.add(VmExpressionIr.EXPRESSION, payload);
            memo.put(expression, normalized);
            return normalized;
        }
        if (EXPRESSION_TYPE.equals(optionalString(object, "_type"))) {
            String operation = optionalString(object, "operation");
            if (kind.equals(operation)) {
                JsonElement receiver = object.get("receiver");
                if (receiver == null || !receiver.isJsonObject()) return null;
                memo.put(expression, receiver);
                return receiver;
            }
            if (!"ITERATOR".equals(operation)) return null;
            JsonElement result = selectedViewState(object.get("receiver"),
                    kind, memo);
            if (result != null) memo.put(expression, result);
            return result;
        }
        String type = optionalString(object, "_type");
        String armsField;
        if (SymbolicPropagationClosure.ITE_TYPE.equals(type)) {
            armsField = "arms";
        } else if ("ReadFromExpression".equals(type)) {
            armsField = "candidates";
        } else {
            return null;
        }
        JsonArray arms = array(object, armsField);
        if (arms.size() == 0) return null;
        JsonObject normalized = JsonFields.shallowCopy(object);
        normalized.addProperty("_java_type", "java/util/Map");
        JsonArray normalizedArms = new JsonArray();
        for (JsonElement element : arms) {
            if (!element.isJsonObject()) return null;
            JsonObject arm = element.getAsJsonObject();
            if (optionalString(arm, "selector").isEmpty()) return null;
            JsonElement projectedArm = selectedViewState(
                    arm.get("expression"), kind, memo);
            if (projectedArm == null) return null;
            JsonObject normalizedArm = JsonFields.shallowCopy(arm);
            normalizedArm.add("expression", projectedArm);
            normalizedArms.add(normalizedArm);
        }
        normalized.add(armsField, normalizedArms);
        memo.put(expression, normalized);
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
        JsonElement normalized = kind.isEmpty()
                ? null : selectedViewState(read, kind);
        return normalized == null || !normalized.isJsonObject()
                ? null : normalized.getAsJsonObject();
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

        /**
         * Returns an equivalent name for a pure term when the encoder keeps
         * a definitional DAG.  The identity default preserves hosts that
         * already bound large container terms at their operand boundary.
         */
        default Term share(Term value) {
            return value;
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
        private final JsonElement stateExpression;
        private final JsonElement indexExpression;

        private Entry(JsonElement stateExpression, JsonElement indexExpression) {
            this.stateExpression = stateExpression;
            this.indexExpression = indexExpression;
        }
    }

    private static final class View {
        private final String kind;
        private final JsonElement stateExpression;

        private View(String kind, JsonElement stateExpression) {
            this.kind = kind;
            this.stateExpression = stateExpression;
        }
    }

    /**
     * Dynamic programming table for one scalar projection.
     *
     * <p>A removal asks for both {@code keyAt(s, i)} and
     * {@code keyAt(s, i + 1)}, while computing either one asks for positions,
     * membership and size over the same state prefixes.  Without memoizing
     * those pure subproblems, a chain of removals revisits the same prefix
     * exponentially.  The table is deliberately scoped to one call to
     * {@link #term}: host side effects such as required assertions and symbol
     * collection therefore happen in their original constraint context.</p>
     */
    private static final class ProjectionMemo {
        private final IdentityHashMap<JsonElement, Map<String, Term>> has =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Map<String, Term>> keys =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Map<String, Term>> positions =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Map<String, Term>> removals =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Map<String, Term>> reads =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Term> sizes =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Term> boxed =
                new IdentityHashMap<>();
        private final IdentityHashMap<JsonElement, Term> booleanOperands =
                new IdentityHashMap<>();

        private Term get(
                IdentityHashMap<JsonElement, Map<String, Term>> table,
                JsonElement expression, String argument) {
            Map<String, Term> row = table.get(expression);
            return row == null ? null : row.get(argument);
        }

        private Term put(
                IdentityHashMap<JsonElement, Map<String, Term>> table,
                JsonElement expression, String argument, Term result) {
            if (result == null) return null;
            Map<String, Term> row = table.get(expression);
            if (row == null) {
                row = new LinkedHashMap<>();
                table.put(expression, row);
            }
            Term held = row.putIfAbsent(argument, result);
            return held == null ? result : held;
        }

        private Term putSize(JsonElement expression, Term result) {
            if (result == null) return null;
            Term held = sizes.put(expression, result);
            return held == null ? result : held;
        }

        private Term box(JsonElement expression, Host host) {
            Term held = boxed.get(expression);
            if (held != null) return held;
            Term result = host.box(expression);
            if (result != null) boxed.put(expression, result);
            return result;
        }

        private Term operand(JsonElement expression, Sort expected,
                             Host host) {
            if (expected != Sort.BOOL) return host.operand(expression,
                    expected);
            Term held = booleanOperands.get(expression);
            if (held != null) return held;
            Term result = host.operand(expression, expected);
            if (result != null) booleanOperands.put(expression, result);
            return result;
        }
    }

    private static final class Mutation {
        private final JsonElement source;
        private final String operation;
        private final JsonElement receiver;
        private final JsonArray arguments;
        /** The branch predicate controlling a conditional removal, or
         *  {@code null} for an unconditional PUT/REMOVE. */
        private final JsonElement guard;

        private Mutation(JsonElement source, String operation,
                         JsonElement receiver,
                         JsonArray arguments, JsonElement guard) {
            this.source = source;
            this.operation = operation;
            this.receiver = receiver;
            this.arguments = arguments;
            this.guard = guard;
        }
    }

}
