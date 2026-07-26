package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;

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
                "(define-fun indexed_clear ((s IndexedState)) IndexedState"
                        + " (mkIndexedState 0 (indexed_elements s)))",
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
                        + " s))",
                "(define-fun assoc_clear ((s AssocState)) AssocState"
                        + " (mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " (assoc_values s) (assoc_order s)"
                        + " ((as const (Array Value Int)) (- 1))))"
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
                || position.indexOf("java.lang.System.symbolizeField(") < 0) {
            return false;
        }
        return handlesField(binary.get("_left"))
                && symbol(binary.get("_right"))
                || handlesField(binary.get("_right"))
                && symbol(binary.get("_left"));
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
        Term receiver = host.operand(expression.get("receiver"),
                "INDEXED".equals(shape) ? Sort.INDEXED : Sort.ASSOCIATIVE);
        JsonArray arguments = array(expression, "arguments");
        if (receiver == null) return null;

        if ("INDEXED".equals(shape)) {
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
            if ("CLEAR".equals(operation) && arguments.size() == 0) {
                return new Term("(indexed_clear " + receiver.text + ")",
                        Sort.INDEXED);
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
            if ("ITERATOR".equals(operation)
                    || "ENTRY_VIEW".equals(operation)
                    || "KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) return receiver;
            if ("SIZE".equals(operation)) {
                return new Term("(assoc_size " + receiver.text + ")",
                        Sort.INT);
            }
            if ("CONTAINS".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : new Term("(assoc_has " + receiver.text + " "
                        + key.text + ")", Sort.BOOL);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : host.unbox(new Term("(ite (assoc_has "
                        + receiver.text + " "
                        + key.text + ") (assoc_read " + receiver.text + " "
                        + key.text + ") (VRef nullRef))", Sort.VALUE),
                        javaType);
            }
            if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
                return new Term("(= (assoc_size " + receiver.text + ") 0)",
                        Sort.BOOL);
            }
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
            if ("CLEAR".equals(operation) && arguments.size() == 0) {
                return new Term("(assoc_clear " + receiver.text + ")",
                        Sort.ASSOCIATIVE);
            }
        }
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
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
}
