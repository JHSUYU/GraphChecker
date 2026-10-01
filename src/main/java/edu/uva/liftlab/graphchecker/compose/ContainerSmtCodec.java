package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;

import static edu.uva.liftlab.graphchecker.compose.ContainerStateModel.NULL_CELL;
import static edu.uva.liftlab.graphchecker.compose.ContainerStateModel.emptiesState;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** The single SMT lowering for VM container operations. */
public final class ContainerSmtCodec {
    private static final String EXPRESSION_TYPE = "ContainerRelation";
    private ContainerSmtCodec() {
    }

    /**
     * The version a read node observed (a read inside one replay has one
     * answer), or null when it states none.
     */
    private static JsonObject observedVersion(JsonObject read) {
        if (!VmRows.joinable(read)) return null;
        JsonObject observed = JsonFields.object(read,
                VmRows.OBSERVED_VERSION);
        return observed.size() == 0 ? null : observed;
    }

    /**
     * The read with its observed version's expression replaced and its Java
     * type restated; the rest is shared, never cloned (nobody writes it).
     */
    private static JsonObject projectedRead(JsonObject read,
                                            JsonObject observed,
                                            JsonElement expression,
                                            String javaType) {
        JsonObject version = JsonFields.shallowCopy(observed);
        version.add(VmExpressionIr.EXPRESSION, expression);
        JsonObject projected = JsonFields.shallowCopy(read);
        projected.addProperty("_java_type", javaType);
        projected.add(VmRows.OBSERVED_VERSION, version);
        return projected;
    }

    public static boolean handles(JsonElement expression) {
        return EXPRESSION_TYPE.equals(VmExpressionIr.typeOf(expression));
    }

    public static boolean handlesField(JsonElement expression) {
        return "FieldAccessExpression".equals(
                VmExpressionIr.typeOf(expression));
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
        return VmExpressionIr.SYMBOL_TYPE.equals(
                VmExpressionIr.typeOf(expression));
    }

    /** The one refusal for a projection no evidence values. */
    private static final String UNSTATED_FIELD_PROJECTION =
            "UNSTATED_FIELD_PROJECTION:";

    /**
     * One field projection, by the one rule both queries lower it under:
     * JOIN, then PIN, then REFUSE by name.
     *
     * <p>JOIN: the read's {@code observedVersion}; {@code concreteValue} of a
     * primitive read is the read node itself, so the guarded-read lowering
     * carries a root or handoff value through the object it was stored in.
     * PIN: with no version logged, the stated pair {@code concreteOwner} /
     * {@code concreteValue} (rid spelling, {@code "N"} for null), so a read's
     * reference and another read's owner mint the same identity name; a
     * value the host refuses is refused, never re-guessed.  REFUSE: anything
     * else -- a free accessor over an uninterpreted Ref lets a model hold by
     * a value no execution produced.</p>
     *
     * <p>The pair states the run's own object; the host answers what the
     * projection is where a family may re-point its owner to another
     * ({@link Host#projection}).</p>
     */
    public static Term field(JsonObject expression, Host host) {
        String ownerClass = optionalString(expression, "ownerClass");
        String javaType = optionalString(expression, "_java_type");
        // The owner term is lowered only for a boxed payload: lowering it
        // otherwise drags in the owner's read chain and its refusals.
        Sort boxed = boxedPayloadSort(ownerClass, javaType);
        if (boxed != null) {
            Term owner = host.operand(expression.get("owner"), Sort.REF);
            if (owner == null) return null;
            if (owner.sort == boxed) return owner;
        }
        // The VM writes both members or neither; a half pair is refused.
        JsonElement concreteOwner = expression.get("concreteOwner");
        JsonElement concreteValue = expression.get("concreteValue");
        if (stated(concreteOwner) && stated(concreteValue)) {
            // No expectation: the host's table decides the value's sort.
            Term cell = host.operand(concreteValue, null);
            return cell == null ? null : host.projection(expression, cell);
        }
        host.unsupported(UNSTATED_FIELD_PROJECTION + ownerClass + "@"
                + JsonFields.optionalInteger(expression, "fieldOffset", -1)
                + ":" + javaType);
        return null;
    }

    /** Whether the VM wrote this member at all. */
    private static boolean stated(JsonElement member) {
        return member != null && !member.isJsonNull();
    }

    /**
     * The sort a boxed primitive's payload field holds, or null: a read of
     * {@code Integer.value} IS the owner term, which must already have that
     * sort.
     */
    private static Sort boxedPayloadSort(String ownerClass, String javaType) {
        if ("java/lang/Boolean".equals(ownerClass)) {
            return "Z".equals(javaType) ? Sort.BOOL : null;
        }
        if ("java/lang/Float".equals(ownerClass)) {
            return "F".equals(javaType) ? Sort.FLOAT32 : null;
        }
        if ("java/lang/Double".equals(ownerClass)) {
            return "D".equals(javaType) ? Sort.FLOAT64 : null;
        }
        boolean integral = "java/lang/Byte".equals(ownerClass)
                && "B".equals(javaType)
                || "java/lang/Character".equals(ownerClass)
                && "C".equals(javaType)
                || "java/lang/Short".equals(ownerClass)
                && "S".equals(javaType)
                || "java/lang/Integer".equals(ownerClass)
                && "I".equals(javaType)
                || "java/lang/Long".equals(ownerClass)
                && "J".equals(javaType);
        return integral ? Sort.INT : null;
    }

    /**
     * Whether a container receiver's identity is evidenced at runtime, not
     * built by this encoder.  Select-over-store and the size receiver skip
     * are exact in value but would drop the published version chain (and its
     * read-from arms) out of the formula, so such a carrier is kept.
     */
    private static boolean evidencedContainerIdentity(JsonElement expression) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject node = cursor.getAsJsonObject();
            if (VmRows.GUARDED_READ_TYPE.equals(
                    optionalString(node, "_type"))
                    || VmExpressionIr.consumerBoundary(node)
                    || VmExpressionIr.isCanonicalMapStateReference(
                    optionalString(node, "_exp"))) {
                return true;
            }
            // A local mutation inherits the identity of the state it rests
            // on, however long the chain of them.
            if (!EXPRESSION_TYPE.equals(optionalString(node, "_type"))) {
                return false;
            }
            cursor = node.get("receiver");
        }
        return false;
    }

    /**
     * Resolves {@code READ(WRITE(s, j, v), i)} to the stored {@code v},
     * projected through the value-propagation wrappers above it.
     */
    private static JsonElement storedIndexedWrite(JsonElement receiver,
                                                  JsonElement index,
                                                  String selectedJavaType) {
        Integer wanted = exactIndexLiteral(index);
        if (wanted == null) return null;
        List<JsonObject> wrappers = new ArrayList<JsonObject>();
        JsonElement cursor = receiver;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject root = cursor.getAsJsonObject();
            if (wrapper(root)) {
                wrappers.add(root);
                cursor = wrapped(root);
                continue;
            }
            JsonElement below = cursor;
            while (below != null && below.isJsonObject()) {
                JsonObject node = below.getAsJsonObject();
                JsonArray arguments = array(node, "arguments");
                if (!EXPRESSION_TYPE.equals(optionalString(node, "_type"))
                        || !"INDEXED".equals(optionalString(node, "shape"))
                        || !"WRITE".equals(
                        optionalString(node, "operation"))) {
                    break;
                }
                if (arguments.size() != 2) return null;
                Integer written = exactIndexLiteral(arguments.get(0));
                if (written == null) return null;
                if (written.intValue() == wanted) {
                    // The stored value is an immutable propagated graph.
                    return rewrapped(wrappers, arguments.get(1),
                            selectedJavaType);
                }
                below = node.get("receiver");
            }
            // A local WRITE prefix may itself rest on a propagated array
            // family.
            if (below == cursor) return null;
            cursor = below;
        }
        return null;
    }

    /**
     * Whether a container value sits beneath a value-propagation wrapper: a
     * consumer boundary, or a guarded read of the version it observed.  The
     * walks down such chains are loops: a container's history is one
     * guarded read per version, and a recursion along it was as deep.
     */
    private static boolean wrapper(JsonObject node) {
        return VmExpressionIr.consumerBoundary(node)
                || VmRows.GUARDED_READ_TYPE.equals(
                optionalString(node, "_type"));
    }

    /** The value one {@link #wrapper} carries, or null. */
    private static JsonElement wrapped(JsonObject wrapper) {
        if (VmExpressionIr.consumerBoundary(wrapper)) {
            return wrapper.get(VmExpressionIr.EXPRESSION);
        }
        JsonObject observed = observedVersion(wrapper);
        return observed == null ? null
                : observed.get(VmExpressionIr.EXPRESSION);
    }

    /**
     * {@code value} put back beneath the wrappers it was found under (listed
     * outermost first), each restated at {@code javaType}: their selector
     * and event stay the value's authority.
     */
    private static JsonElement rewrapped(List<JsonObject> wrappers,
                                         JsonElement value,
                                         String javaType) {
        JsonElement projected = value;
        for (int index = wrappers.size() - 1; index >= 0; index--) {
            JsonObject wrapper = wrappers.get(index);
            if (VmExpressionIr.consumerBoundary(wrapper)) {
                JsonObject boundary = JsonFields.shallowCopy(wrapper);
                boundary.addProperty("_java_type", javaType);
                boundary.add(VmExpressionIr.EXPRESSION, projected);
                projected = boundary;
            } else {
                projected = projectedRead(wrapper, observedVersion(wrapper),
                        projected, javaType);
            }
        }
        return projected;
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
        if (!VmExpressionIr.isPrimitiveIntExpression(object)) return null;
        String value = VmExpressionIr.constantPayload(
                optionalString(object, "_exp"));
        if (!value.matches("-?[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    /**
     * One {@code ContainerRelation} node, or null once refused by name.  An
     * answer asked through a reference ({@code owner}, a read a STATE family
     * may re-point) is the host's to answer per object
     * ({@link Host#query}); a state is never selected by one, since an
     * array-valued choice over lambda terms is outside what z3 decides.
     */
    public static Term term(JsonObject expression, Host host) {
        Term answer = relation(expression, host);
        return answer == null || !expression.has("owner")
                || answer.sort == Sort.INDEXED
                || answer.sort == Sort.ASSOCIATIVE
                ? answer : host.query(expression, answer);
    }

    private static Term relation(JsonObject expression, Host host) {
        // The view states whose bijection this call already stated.
        Map<JsonElement, ViewOrder> views =
                new IdentityHashMap<JsonElement, ViewOrder>();
        String shape = optionalString(expression, "shape");
        String operation = optionalString(expression, "operation");
        String javaType = optionalString(expression, "_java_type");
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
                return unmodeled("INDEXED", operation, arguments, host);
            }
            Term size = integer(arguments.get(0), host);
            return size == null ? null : new Term(
                    "(mkIndexedState " + size.text
                            + " (indexed_elements " + state.text + "))",
                    Sort.INDEXED, IntegralWidth.NONE, literal(size.text));
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
                    javaType, host, views);
            return value == null ? null : host.unbox(value, javaType);
        }
        if ("INDEXED".equals(shape) && "NEXT".equals(operation)) {
            JsonArray positions = array(expression, "arguments");
            if (positions.size() != 1) {
                return unmodeled(shape, operation, positions, host);
            }
            // The element a traversal reads: an indexed ITERATOR is the
            // identity on its state.
            Term index = integer(positions.get(0), host);
            Term cursor = host.operand(expression.get("receiver"),
                    Sort.INDEXED);
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
                    javaType, host, views);
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
            String observedJavaType = VmTermLowering.expressionJavaType(observed.get(0));
            Term selected = associativeEntryValue(entry,
                    "OBSERVE_KEY".equals(operation)
                            ? "KEY_VIEW" : "VALUE_VIEW",
                    observedJavaType, host, views);
            if (selected == null) return null;
            return new Term("(= " + selected.text + " " + value.text + ")",
                    Sort.BOOL);
        }
        if ("HAS_NEXT".equals(operation)) {
            Sort stateSort = "INDEXED".equals(shape)
                    ? Sort.INDEXED : Sort.ASSOCIATIVE;
            JsonArray positions = array(expression, "arguments");
            Term position = positions.size() == 1
                    ? integer(positions.get(0), host) : null;
            Term state = stateSort == Sort.ASSOCIATIVE
                    ? associativeState(expression.get("receiver"), host)
                    : host.operand(expression.get("receiver"), stateSort);
            Term size = state == null ? null
                    : stateSort == Sort.ASSOCIATIVE
                    ? associativeSize(state, host)
                    : indexedSize(expression.get("receiver"), state, host);
            if (position == null || size == null) {
                host.unsupported("ContainerRelation:" + shape
                        + ":HAS_NEXT");
                return null;
            }
            return new Term("(and (<= 0 " + position.text + ") (< "
                    + position.text + " " + size.text + "))", Sort.BOOL);
        }
        JsonArray arguments = array(expression, "arguments");
        if (emptiesState(operation)) {
            if (arguments.size() != 0) {
                return unmodeled(shape, operation, arguments, host);
            }
            if ("INDEXED".equals(shape)) {
                return new Term("(mkIndexedState 0"
                        + " ((as const (Array Int Value))"
                        + " " + NULL_CELL + "))", Sort.INDEXED,
                        IntegralWidth.NONE, 0L);
            }
            if ("ASSOCIATIVE".equals(shape)) {
                return new Term("(mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " ((as const (Array Value Value))"
                        + " " + NULL_CELL + ")"
                        + " ((as const (Array Int Value))"
                        + " " + NULL_CELL + ")"
                        + " ((as const (Array Value Int)) (- 1)))",
                        Sort.ASSOCIATIVE);
            }
        }
        if ("INDEXED".equals(shape)) {
            return indexed(expression, operation, arguments, javaType, host);
        }
        if ("ASSOCIATIVE".equals(shape)) {
            return associative(expression, operation, arguments, javaType,
                    host, views);
        }
        return unmodeled(shape, operation, arguments, host);
    }

    /** One operation on a list, array or queue state. */
    private static Term indexed(JsonObject expression, String operation,
                                JsonArray arguments, String javaType,
                                Host host) {
        JsonElement receiverIr = expression.get("receiver");
        boolean preserveReceiver = evidencedContainerIdentity(receiverIr);
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
        Term receiver = shared(host.operand(receiverIr, Sort.INDEXED),
                host);
        if (receiver == null) return null;
        if ("ITERATOR".equals(operation)) return receiver;
        if ("SIZE".equals(operation)) {
            return indexedSize(receiverIr, receiver, host);
        }
        if ("READ".equals(operation) && arguments.size() == 1) {
            Term index = integer(arguments.get(0), host);
            if (index != null) {
                requireIndexedMember(receiver, index, host);
            }
            return index == null ? null
                    : host.unbox(new Term("(indexed_read "
                    + receiver.text + " " + index.text + ")",
                    Sort.VALUE), javaType);
        }
        if ("WRITE".equals(operation) && arguments.size() == 2) {
            Term index = integer(arguments.get(0), host);
            Term value = host.box(arguments.get(1));
            if (index == null || value == null) return null;
            // A set() or an array store throws outside its receiver, as a
            // get() does.  In place: the size is the receiver's (dropped,
            // Lucene's deleteCommits compaction left its REMOVE no size to
            // shift by).
            requireIndexedMember(receiver, index, host);
            return new Term("(indexed_write " + receiver.text + " "
                    + index.text + " " + value.text + ")",
                    Sort.INDEXED, IntegralWidth.NONE, receiver.indexedSize);
        }
        if ("APPEND".equals(operation) && arguments.size() == 1) {
            Term value = host.box(arguments.get(0));
            return value == null ? null
                    : new Term("(indexed_append " + receiver.text + " "
                    + value.text + ")", Sort.INDEXED,
                    IntegralWidth.NONE, grown(receiver, 1L));
        }
        if ("INSERT".equals(operation) && arguments.size() == 2) {
            Term index = integer(arguments.get(0), host);
            Term value = host.box(arguments.get(1));
            if (index == null || value == null) return null;
            return shift(receiver, index, value, host);
        }
        if ("REMOVE".equals(operation) && arguments.size() == 1) {
            Term index = integer(arguments.get(0), host);
            if (index == null) return null;
            return shift(receiver, index, null, host);
        }
        // CONTAINS over an indexed container is REFUSED by name: its
        // only spelling is a quantifier over the element array, outside
        // the fragment z3 decides ("incomplete quantifiers").
        if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
            return new Term("(= (indexed_size " + receiver.text + ") 0)",
                    Sort.BOOL);
        }
        return unmodeled("INDEXED", operation, arguments, host);
    }

    /** One operation on a map or set state. */
    private static Term associative(JsonObject expression, String operation,
                                    JsonArray arguments, String javaType,
                                    Host host,
                                    Map<JsonElement, ViewOrder> views) {
        JsonElement receiverIr = associativeStateExpression(
                expression.get("receiver"));
        if (("READ".equals(operation) || "CONTAINS".equals(operation))
                && arguments.size() == 1
                || "READ_OR_DEFAULT".equals(operation)
                && arguments.size() == 2) {
            return associativeLookup(receiverIr, operation, arguments,
                    javaType, host);
        }
        Term receiver = associativeState(expression.get("receiver"),
                host);
        if (receiver == null) return null;
        if ("SIZE".equals(operation)) {
            return associativeSize(receiver, host);
        }
        if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
            return new Term("(= " + associativeSize(receiver, host).text
                    + " 0)", Sort.BOOL);
        }
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
            Term index = integer(arguments.get(0), host);
            if (index == null) return null;
            // Removing AT a position is a walk of the same view: which
            // key the position names is the bijection's to say.
            ViewOrder order = requireAssociativeViewBijection(receiverIr,
                    receiver, host, views);
            if (order == null) return null;
            requireAssociativeMember(receiver, index, order, host);
            return new Term("(let ((s " + receiver.text
                    + ")) (assoc_remove s (" + order.keyAt + " s "
                    + index.text + ")))", Sort.ASSOCIATIVE);
        }
        if ("REMOVE".equals(operation) && arguments.size() == 1) {
            Term key = host.box(arguments.get(0));
            return key == null ? null
                    : new Term("(assoc_remove " + receiver.text + " "
                    + key.text + ")", Sort.ASSOCIATIVE);
        }
        if ("PUT_ALL".equals(operation) && arguments.size() == 1) {
            return putAll(receiver, arguments.get(0), host);
        }
        if ("REMOVE_IF".equals(operation) && arguments.size() == 1) {
            // Drops the key when the guard holds; read/has short-circuit
            // this via the mutation walk, this handles a nested receiver.
            Term key = host.box(arguments.get(0));
            Term guard = host.operand(expression.get("guard"), Sort.BOOL);
            return key == null || guard == null ? null
                    : new Term("(assoc_remove_if " + receiver.text + " "
                    + key.text + " " + guard.text + ")",
                    Sort.ASSOCIATIVE);
        }
        return unmodeled("ASSOCIATIVE", operation, arguments, host);
    }

    /**
     * {@code putAll(m)}: each key m's chain names, in the order it put
     * them, put where m holds it ({@code assoc_put_if}, its guard inside
     * each component as {@code assoc_remove_if}'s).  The keys are the puts
     * above m's exact empty base; a source whose chain ends anywhere else,
     * or runs past {@link #VIEW_CHAIN_LIMIT}, bounds nothing and is refused
     * by name.
     */
    private static Term putAll(Term receiver, JsonElement source, Host host) {
        List<JsonElement> keys = associativeViewKeys(source,
                host);
        Term from = associativeState(source, host);
        if (keys == null || from == null) {
            host.unsupported("ContainerRelation:ASSOCIATIVE:PUT_ALL:"
                    + "source-keys-unstated");
            return null;
        }
        Term state = receiver;
        for (JsonElement each : keys) {
            Term key = host.box(each);
            if (key == null) return null;
            state = shared(new Term("(assoc_put_if " + state.text + " "
                    + key.text + " (assoc_read " + from.text + " " + key.text
                    + ") (assoc_has " + from.text + " " + key.text + "))",
                    Sort.ASSOCIATIVE), host);
        }
        return state;
    }

    /**
     * A read, a read with a default ({@code getOrDefault}: the default where
     * the key is absent) or a membership test at one key.  With a literal
     * key, the chain's
     * mutations at other literal keys cannot touch it and are passed in the
     * IR, never lowered: a map the recording rebuilt from a store's bytes
     * (Solr's cluster state, one per notification) is a put per entry, and
     * lowering every one of them was millions of container terms for a query
     * that reads one key.  The walk stops at the first mutation at the key
     * (its answer), at a key that is not a literal, or at the chain's base,
     * never at a depth (512 lowered the rest of a longer map whole); what
     * remains is lowered as the whole state was.  Never an absent-key
     * default over the passed puts: only literal keys are compared, and two
     * distinct literals are distinct values.
     */
    private static Term associativeLookup(JsonElement receiverIr,
                                          String operation,
                                          JsonArray arguments,
                                          String javaType, Host host) {
        JsonElement key = arguments.get(0);
        Term wanted = host.box(key);
        if (wanted == null) return null;
        boolean read = !"CONTAINS".equals(operation);
        Term absent = arguments.size() == 2 ? host.box(arguments.get(1))
                : new Term(NULL_CELL, Sort.VALUE);
        if (absent == null) return null;
        JsonElement state = receiverIr;
        String literal = literalKey(key);
        if (literal != null) {
            while (true) {
                Mutation mutation = associativeMutation(state);
                if (mutation == null || !("PUT".equals(mutation.operation)
                        || "REMOVE".equals(mutation.operation))) {
                    break;
                }
                String at = literalKey(mutation.arguments.get(0));
                if (at == null) break;
                if (at.equals(literal)) {
                    boolean removed = "REMOVE".equals(mutation.operation);
                    if (!read) {
                        return new Term(removed ? "false" : "true",
                                Sort.BOOL);
                    }
                    Term value = removed ? absent
                            : host.box(mutation.arguments.get(1));
                    return value == null ? null : host.unbox(value, javaType);
                }
                state = mutation.receiver;
            }
        }
        Term receiver = associativeState(state, host);
        if (receiver == null) return null;
        if (!read) return associativeHas(receiver, wanted, host);
        requireStatedContainerBase(state, wanted, host);
        return host.unbox(associativeRead(receiver, wanted, absent, host),
                javaType);
    }

    /**
     * A key the VM stated as one constant -- a string or a number, no symbol
     * inside -- as its Java type and payload, or null.  Two keys are equal
     * Java keys exactly when these agree (an Integer is no Long's key).
     */
    private static String literalKey(JsonElement key) {
        String type = VmExpressionIr.typeOf(key);
        if (!("ConstExpr".equals(type) || "ConStringSymbolExp".equals(type))
                || VmExpressionIr.carriesPropagatedValue(key)) {
            return null;
        }
        JsonObject constant = key.getAsJsonObject();
        return optionalString(constant, "_java_type") + "|"
                + VmExpressionIr.constantPayload(
                optionalString(constant, "_exp"));
    }

    /**
     * One int operand (a position or a size), or null once refused by name.
     * A refused leaf keeps its own node's sort, which need not be Int, and
     * a membership require over it was ill-sorted SMT: z3 answered the
     * whole composition with an error.
     */
    private static Term integer(JsonElement expression, Host host) {
        Term value = host.operand(expression, Sort.INT);
        if (value == null || value.sort == Sort.INT) return value;
        host.unsupported("ContainerRelation:int-operand-sort=" + value.sort);
        return null;
    }

    /** An operation this codec has no relation for, refused by name. */
    private static Term unmodeled(String shape, String operation,
                                  JsonArray arguments, Host host) {
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
    }

    /** One positional key/value observation of a view's whole state. */
    private static Term associativeEntryValue(
            Entry entry, String viewKind, String javaType, Host host,
            Map<JsonElement, ViewOrder> views) {
        Term state = associativeState(entry.stateExpression, host);
        Term index = integer(entry.indexExpression, host);
        if (state == null || index == null) return null;
        // Only where the recording bounds the view's positions.
        ViewOrder order = requireAssociativeViewBijection(
                entry.stateExpression, state, host, views);
        if (order == null) return null;
        requireAssociativeMember(state, index, order, host);
        String key = "(" + order.keyAt + " " + state.text + " "
                + index.text + ")";
        return new Term("KEY_VIEW".equals(viewKind) ? key
                : "(assoc_read " + state.text + " " + key + ")",
                Sort.VALUE);
    }

    /**
     * Refuses a read whose container chain does not end at a base the VM
     * walked: an INITIAL's {@code SNAPSHOT_BASE} or a program {@code CLEAR}.
     * Membership itself is the assoc model's ({@code assoc_put} /
     * {@code assoc_remove}), decided by z3 for symbolic keys too.
     *
     * <p>Trap: never replace this with an "absent-key default" over the
     * chain's constant PUT keys -- a symbolic PUT key makes that default
     * contradict the chain.  Walked to its end: stopped at depth 512, a
     * longer chain passed unrefused whatever its base.</p>
     */
    private static void requireStatedContainerBase(
            JsonElement expression, Term key, Host host) {
        JsonElement chain = expression;
        while (true) {
            Mutation mutation = associativeMutation(host.chain(chain));
            if (mutation == null) {
                host.unsupported(VmRows.CONTAINER_BASE_UNSTATED + ":"
                        + key.text);
                return;
            }
            if (emptiesState(mutation.operation)) return;
            chain = mutation.receiver;
        }
    }

    /** The value at one key, or {@code absent} where the key is. */
    private static Term associativeRead(Term state, Term key, Term absent,
                                        Host host) {
        return shared(new Term("(let ((s " + state.text + ")) (ite "
                + "(assoc_has s " + key.text + ") (assoc_read s " + key.text
                + ") " + absent.text + "))", Sort.VALUE), host);
    }

    private static Term associativeHas(Term state, Term key, Host host) {
        return shared(new Term("(assoc_has " + state.text + " " + key.text
                + ")", Sort.BOOL), host);
    }

    private static Term associativeSize(Term state, Host host) {
        return javaContainerSize("(assoc_size " + state.text + ")", host);
    }

    /** An indexed size: the length an array STATE records, else the model's. */
    private static Term indexedSize(JsonElement stateIr, Term state,
                                    Host host) {
        if (stateIr != null && stateIr.isJsonObject()) {
            JsonObject object = stateIr.getAsJsonObject();
            JsonArray arguments = array(object, "arguments");
            if (EXPRESSION_TYPE.equals(optionalString(object, "_type"))
                    && "STATE".equals(optionalString(object, "operation"))
                    && arguments.size() == 1) {
                return integer(arguments.get(0), host);
            }
        }
        return javaContainerSize("(indexed_size " + state.text + ")", host);
    }

    /** Positional projections are partial Java ops: require membership. */
    private static void requireIndexedMember(
            Term state, Term index, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (indexed_size s))))");
    }

    private static void requireAssociativeMember(
            Term state, Term index, ViewOrder order, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (assoc_size s))"
                + " (assoc_has s (" + order.keyAt + " s i))))");
    }

    /** Refusal subject for a view whose map size nothing bounds. */
    public static final String ASSOC_VIEW_SIZE_UNSTATED =
            "UNSTATED_VALUE:AssociativeViewSize";

    /**
     * What a view's position is read through.  {@code STATED}: the chain's
     * order ({@code assoc_key_at}, {@code assoc_position}), where it is the
     * order the map's class iterates in ({@link #ordered}).  {@code FREE}:
     * a bijection between the positions and the state's keys and nothing
     * more ({@code assoc_view_key}, {@code assoc_view_position},
     * {@code ContainerStateModel}), where it is not: the formula then names
     * no order the run did not have, and a consumer that reads the view as
     * a set (hdfs-11741's exported block keys) keeps every key.
     */
    enum ViewOrder {
        STATED("assoc_key_at"), FREE("assoc_view_key");

        final String keyAt;

        ViewOrder(String keyAt) {
            this.keyAt = keyAt;
        }

        /** The position this order holds one key at. */
        Term position(Term state, Term key, Host host) {
            return shared(new Term(this == STATED
                    ? "(select (assoc_position " + state.text + ") "
                    + key.text + ")"
                    : "(assoc_view_position " + state.text + " "
                    + key.text + ")", Sort.INT), host);
        }
    }

    /**
     * AN INDEXED VIEW OF AN ASSOCIATIVE STATE IS A BIJECTION between
     * positions {@code [0, n)} and the keys the state holds.
     * {@code values()}, {@code keySet()}, {@code entrySet()}, {@code toArray}
     * and ITERATOR/NEXT all name each entry once at one position.  Stating
     * only "this position names a present key" lets z3 repeat one key and
     * drop another (hdfs-11741's exported block keys).
     *
     * <pre>
     *   (=&gt; (&lt; p n) (and (has k_p) (= (position k_p) p)))     p in [0, m)
     *   (=&gt; (has K) (and (&lt;= 0 (position K)) (&lt; (position K) n)
     *                   (= k_(position K) K)))                 K a put key
     * </pre>
     *
     * <p>Two positions name two keys: a key has one position.  {@code m},
     * the chain's put count, bounds {@code n} (from an empty base the keys
     * are exactly the ones put), so the facts are written at CONCRETE
     * positions with no quantifier, linear in the chain.  {@code k_p} and
     * {@code position} are the chain's order where the chain states the
     * class's iteration order, else free ({@link ViewOrder}).  A state with
     * no bounding chain is refused ({@link #ASSOC_VIEW_SIZE_UNSTATED}).</p>
     *
     * @return how the view's positions are read, or null when refused
     */
    private static ViewOrder requireAssociativeViewBijection(
            JsonElement stateIr, Term state, Host host,
            Map<JsonElement, ViewOrder> views) {
        if (stateIr != null && views.containsKey(stateIr)) {
            return views.get(stateIr);
        }
        List<JsonElement> put = associativeViewKeys(stateIr, host);
        if (put == null) {
            host.unsupported(ASSOC_VIEW_SIZE_UNSTATED + ":"
                    + associativeStateSubject(stateIr));
            return null;
        }
        ViewOrder order = ordered(stateIr, host, put)
                ? ViewOrder.STATED : ViewOrder.FREE;
        Term size = associativeSize(state, host);
        for (int position = 0; position < put.size(); position++) {
            Term key = shared(new Term("(" + order.keyAt + " " + state.text
                    + " " + position + ")", Sort.VALUE), host);
            host.require("(=> (< " + position + " " + size.text
                    + ") (and " + associativeHas(state, key, host).text
                    + " (= " + order.position(state, key, host).text + " "
                    + position + ")))");
        }
        for (JsonElement each : put) {
            Term key = host.box(each);
            if (key == null) return null;
            Term where = order.position(state, key, host);
            host.require("(=> " + associativeHas(state, key, host).text
                    + " (and (<= 0 " + where.text + ") (< " + where.text
                    + " " + size.text + ") (= (" + order.keyAt + " "
                    + state.text + " " + where.text + ") " + key.text
                    + ")))");
        }
        views.put(stateIr, order);
        return order;
    }

    /**
     * Whether the chain's order is the order Java iterates this state in.
     * A position is the run's iteration count; the model's is the chain's
     * order (a put appends a new key, a removal closes the gap).  The VM
     * states the members a snapshot read in their class's iteration order,
     * and how many of the relations above the base they are ({@code
     * SNAPSHOT_BASE}'s {@code order} and {@code members}).  An {@code
     * INSERTION} class (LinkedHashMap, LinkedHashSet) then iterates in the
     * chain's order, a {@code putAll} in its source's.  A {@code HASH} class
     * (HashMap, HashSet, ConcurrentHashMap, Hashtable) keeps its snapshot's
     * order through removals and updates of a key it holds, while a put of
     * any other key may rebin or resize its table.  A base stating no order
     * is a recording older than that; a program {@code CLEAR} empties the
     * state and keeps its class.  One key has one order.
     */
    private static boolean ordered(JsonElement state, Host host,
                                   List<JsonElement> put) {
        Set<String> distinct = new HashSet<String>();
        for (JsonElement key : put) distinct.add(String.valueOf(key));
        if (distinct.size() <= 1) return true;
        List<Mutation> above = new ArrayList<Mutation>();
        JsonElement chain = state;
        JsonObject base = null;
        int members = 0;
        for (int depth = 0; depth < VIEW_CHAIN_LIMIT && base == null;
             depth++) {
            JsonElement node = host.chain(chain);
            Mutation mutation = associativeMutation(node);
            if (mutation == null) return false;
            if ("SNAPSHOT_BASE".equals(mutation.operation)) {
                base = node.getAsJsonObject();
                members = JsonFields.optionalInteger(base, "members", -1);
            } else if ("CLEAR".equals(mutation.operation)) {
                base = snapshotBase(mutation.receiver, host);
                if (base == null) return false;
            } else {
                above.add(mutation);
                chain = mutation.receiver;
            }
        }
        String order = base == null ? "" : optionalString(base, "order");
        boolean hash = "HASH".equals(order);
        if (!hash && !"INSERTION".equals(order) || members < 0
                || members > above.size()) {
            return false;
        }
        Set<String> present = new HashSet<String>();
        for (int index = above.size() - 1; index >= 0; index--) {
            Mutation mutation = above.get(index);
            boolean member = index >= above.size() - members;
            String key = mutation.arguments.size() == 0 ? null
                    : literalKey(mutation.arguments.get(0));
            if ("PUT_ALL".equals(mutation.operation)) {
                if (hash) return false;
                JsonElement from = mutation.arguments.get(0);
                List<JsonElement> source = associativeViewKeys(from, host);
                if (source == null || !ordered(from, host, source)) {
                    return false;
                }
            } else if ("PUT".equals(mutation.operation)) {
                if (!member && hash
                        && (key == null || !present.contains(key))) {
                    return false;
                }
                if (key != null) present.add(key);
            } else if (key == null) {
                present.clear();
            } else {
                present.remove(key);
            }
        }
        return true;
    }

    /** The snapshot base beneath a program {@code CLEAR}, or null. */
    private static JsonObject snapshotBase(JsonElement state, Host host) {
        JsonElement chain = state;
        for (int depth = 0; depth < VIEW_CHAIN_LIMIT; depth++) {
            JsonElement node = host.chain(chain);
            Mutation mutation = associativeMutation(node);
            if (mutation == null) return null;
            if ("SNAPSHOT_BASE".equals(mutation.operation)) {
                return node.getAsJsonObject();
            }
            chain = mutation.receiver;
        }
        return null;
    }

    /**
     * The keys a view's state was put with above an exact empty base, in
     * the order put ({@code PUT_ALL}: its source's, at its place), or null
     * when the chain ends anywhere else and so bounds nothing -- or runs
     * past {@link #VIEW_CHAIN_LIMIT}.  Each state of the chain is the one
     * it stands for ({@link Host#chain}): a view reached through a read
     * (a map's {@code values()} a region iterates) is its read's version.
     */
    private static List<JsonElement> associativeViewKeys(
            JsonElement state, Host host) {
        List<JsonElement> keys = new ArrayList<JsonElement>();
        JsonElement chain = state;
        for (int depth = 0; depth < VIEW_CHAIN_LIMIT; depth++) {
            Mutation mutation = associativeMutation(host.chain(chain));
            if (mutation == null) return null;
            if (emptiesState(mutation.operation)) {
                Collections.reverse(keys);
                return keys;
            }
            if ("PUT".equals(mutation.operation)) {
                keys.add(mutation.arguments.get(0));
            } else if ("PUT_ALL".equals(mutation.operation)) {
                List<JsonElement> added = associativeViewKeys(
                        mutation.arguments.get(0), host);
                if (added == null) return null;
                for (int index = added.size() - 1; index >= 0; index--) {
                    keys.add(added.get(index));
                }
            }
            chain = mutation.receiver;
        }
        return null;
    }

    /**
     * The longest chain a view's bijection is stated over: its facts grow
     * with the square of the puts, and a longer chain is refused by name
     * ({@link #ASSOC_VIEW_SIZE_UNSTATED}), never cut.
     */
    private static final int VIEW_CHAIN_LIMIT = 512;

    /** What a refused view names itself by: its own top operation. */
    private static String associativeStateSubject(JsonElement state) {
        if (state == null || !state.isJsonObject()) return "no-state";
        JsonObject object = state.getAsJsonObject();
        String operation = optionalString(object, "operation");
        return operation.isEmpty() ? optionalString(object, "_type")
                : operation;
    }

    /**
     * One Java container size: an {@code int} (JLS 10.7, 15.14) in
     * {@code [0, Integer.MAX_VALUE]}.
     */
    private static Term javaContainerSize(String text, Host host) {
        JavaPrimitiveSmtSemantics.IntegralDomain domain =
                JavaPrimitiveSmtSemantics.domainOfJavaType("I");
        Term size = shared(new Term(text, Sort.INT,
                IntegralWidth.JAVA_INT), host);
        host.require(VmTermLowering.integralRange("0", size.text,
                domain.upper));
        return size;
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
                : "PUT_ALL".equals(operation) ? 1
                : "PUT".equals(operation) ? 2 : -1;
        if (arity < 0 || arguments.size() != arity) return null;
        // REMOVE_IF without a guard is malformed: refused, never dropped.
        JsonElement guard = "REMOVE_IF".equals(operation)
                ? relation.get("guard") : null;
        if ("REMOVE_IF".equals(operation)
                && (guard == null || guard.isJsonNull())) {
            return null;
        }
        return new Mutation(operation, relation.get("receiver"), arguments);
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

    /** The map state beneath iterator and view wrappers, as JSON. */
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

    /**
     * One list insertion or removal, shifted WITHOUT a quantifier.  A
     * whole-state {@code lambda} shift leaves z3 undecided ("incomplete
     * quantifiers"); with the recorded size it is a finite store chain at
     * CONCRETE indices, the index {@code i} kept symbolic:
     *
     * <pre>
     *   insert: a[k] = ite(k &lt; i, s[k], ite(k = i, v, s[k-1]))  k in [0, n]
     *   remove: a[k] = ite(k &lt; i, s[k], s[k+1])                 k in [0, n-2]
     * </pre>
     *
     * <p>Definedness is required beside it ({@code 0 <= i <= n} for insert,
     * {@code < n} for remove): an out-of-range index throws, so it is not a
     * path that reached the anchor.  With no stated size the quantified
     * form is kept and refused by name.</p>
     *
     * @param value the element to insert, or null for a removal
     */
    private static Term shift(Term receiver, Term index, Term value,
                              Host host) {
        long size = receiver.indexedSize;
        boolean insert = value != null;
        if (size < 0L) {
            // No stated size: the quantified relation, refused by name.
            host.unsupported("ContainerRelation:INDEXED:"
                    + (insert ? "INSERT" : "REMOVE")
                    + ":unstated-size");
            return new Term("(indexed_" + (insert ? "insert" : "remove")
                    + " " + receiver.text + " " + index.text
                    + (insert ? " " + value.text : "") + ")",
                    Sort.INDEXED);
        }
        if (!insert && size == 0L) {
            host.unsupported("ContainerRelation:INDEXED:REMOVE:empty");
            return null;
        }
        long result = insert ? size + 1L : size - 1L;
        // What the execution's own semantics require of the index.
        host.require("(and (<= 0 " + index.text + ") ("
                + (insert ? "<=" : "<") + " " + index.text + " " + size
                + "))");
        StringBuilder array = new StringBuilder("(indexed_elements ")
                .append(receiver.text).append(')');
        for (long slot = 0L; slot < result; slot++) {
            String held = "(indexed_read " + receiver.text + " " + slot
                    + ")";
            String cell;
            if (insert) {
                String before = slot == 0L ? held
                        : "(indexed_read " + receiver.text + " "
                        + (slot - 1L) + ")";
                cell = "(ite (< " + slot + " " + index.text + ") " + held
                        + " (ite (= " + slot + " " + index.text + ") "
                        + value.text + " " + before + "))";
            } else {
                cell = "(ite (< " + slot + " " + index.text + ") " + held
                        + " (indexed_read " + receiver.text + " "
                        + (slot + 1L) + "))";
            }
            array = new StringBuilder("(store ").append(array).append(' ')
                    .append(slot).append(' ').append(cell).append(')');
        }
        return new Term("(mkIndexedState " + result + " " + array + ")",
                Sort.INDEXED, IntegralWidth.NONE, result);
    }

    /** One decimal size the recording stated, or -1. */
    private static long literal(String text) {
        String value = text == null ? "" : text.trim();
        if (value.isEmpty()) return -1L;
        for (int index = 0; index < value.length(); index++) {
            if (!Character.isDigit(value.charAt(index))) return -1L;
        }
        try {
            return Long.parseLong(value);
        } catch (NumberFormatException tooLarge) {
            return -1L;
        }
    }

    /** This state's size plus one more element, or -1. */
    private static long grown(Term receiver, long by) {
        return receiver == null || receiver.indexedSize < 0L ? -1L
                : receiver.indexedSize + by;
    }

    /** Names a pure subterm when the host supports DAG sharing. */
    private static Term shared(Term value, Host host) {
        return value == null ? null : host.share(value);
    }

    /** The view a read selects beneath iterators and {@link #wrapper}s. */
    private static String selectedReadViewKind(JsonElement expression) {
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject object = cursor.getAsJsonObject();
            if (wrapper(object)) {
                cursor = wrapped(object);
                continue;
            }
            if (!EXPRESSION_TYPE.equals(optionalString(object, "_type"))) {
                return "";
            }
            String operation = optionalString(object, "operation");
            if ("ENTRY_VIEW".equals(operation)
                    || "KEY_VIEW".equals(operation)
                    || "VALUE_VIEW".equals(operation)) {
                return operation;
            }
            if (!"ITERATOR".equals(operation)) return "";
            cursor = object.get("receiver");
        }
        return "";
    }

    /**
     * Projects a view through value-preserving wrappers down to its
     * {@code AssocState}; selectors and provenance stay on the wrappers
     * ({@link #rewrapped}).
     */
    private static JsonElement selectedViewState(
            JsonElement expression, String kind) {
        if (kind == null || kind.isEmpty()) return null;
        List<JsonObject> wrappers = new ArrayList<JsonObject>();
        JsonElement cursor = expression;
        while (cursor != null && cursor.isJsonObject()) {
            JsonObject object = cursor.getAsJsonObject();
            if (wrapper(object)) {
                wrappers.add(object);
                cursor = wrapped(object);
                continue;
            }
            if (!EXPRESSION_TYPE.equals(optionalString(object, "_type"))) {
                return null;
            }
            String operation = optionalString(object, "operation");
            JsonElement receiver = object.get("receiver");
            if (kind.equals(operation)) {
                return receiver == null || !receiver.isJsonObject() ? null
                        : rewrapped(wrappers, receiver, "java/util/Map");
            }
            if (!"ITERATOR".equals(operation)) return null;
            cursor = receiver;
        }
        return null;
    }


    /**
     * The encoder a codec call lowers operands, boxes and requirements
     * through; each encoder resolves Java types to sorts its own way.
     */
    public interface Host {
        Term state(JsonElement identity, Sort shape);

        Term operand(JsonElement expression, Sort expected);

        /** The pure term, or an equivalent name of the same sort for it. */
        Term share(Term value);

        Term box(JsonElement expression);

        Term unbox(Term value, String javaType);

        /**
         * One field projection, given the {@code cell} the run's own object
         * held there: that cell, unless the owner may be another object.
         */
        Term projection(JsonObject fieldAccess, Term cell);

        /**
         * One query's answer, given the {@code answer} it has over the run's
         * own object's state: that answer, unless its owner may be another
         * object.
         */
        Term query(JsonObject relation, Term answer);

        /** The chain of mutations a container state stands for: a read's
         *  joined version, else the node itself. */
        JsonElement chain(JsonElement state);

        void require(String predicate);

        void unsupported(String reason);

    }

    public enum Sort {
        BOOL, INT, FLOAT32, FLOAT64, STRING, REF, VALUE,
        INDEXED, ASSOCIATIVE
    }

    public static final class Term {
        public final String text;
        public final Sort sort;
        public final IntegralWidth integralWidth;
        /**
         * How many elements this INDEXED state holds, counted along a chain
         * from an empty or literal-size base, or {@code -1}: never guessed.
         * It lets a shift be a finite store chain instead of a lambda.
         */
        public final long indexedSize;
        /** Whether a String answer is null, as a Bool, or {@code ""} when
         *  it is no String taken from a cell. */
        public final String nullness;

        public Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE);
        }

        public Term(String text, Sort sort, IntegralWidth integralWidth) {
            this(text, sort, integralWidth, -1L);
        }

        public Term(String text, Sort sort, IntegralWidth integralWidth,
                    long indexedSize) {
            this(text, sort, integralWidth, indexedSize, "");
        }

        private Term(String text, Sort sort, IntegralWidth integralWidth,
                     long indexedSize, String nullness) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT
                    && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.indexedSize = sort == Sort.INDEXED ? indexedSize : -1L;
            this.nullness = nullness;
        }

        /** A String answer a cell holds, null where {@code nullness}. */
        public static Term string(String text, String nullness) {
            return new Term(text, Sort.STRING, IntegralWidth.NONE, -1L,
                    nullness);
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
