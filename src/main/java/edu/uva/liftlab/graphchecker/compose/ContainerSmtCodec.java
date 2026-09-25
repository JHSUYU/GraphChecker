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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.IntegralWidth;

import static edu.uva.liftlab.graphchecker.compose.ContainerStateModel.NULL_CELL;
import static edu.uva.liftlab.graphchecker.compose.ContainerStateModel.emptiesState;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** The single SMT lowering for VM container operations. */
public final class ContainerSmtCodec {
    public static final String EXPRESSION_TYPE = "ContainerRelation";
    private ContainerSmtCodec() {
    }

    /**
     * The version a read node observed (a read inside one replay has one
     * answer), or null when it states none.
     */
    private static JsonObject observedVersion(JsonObject read) {
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

    /** The one refusal for a projection no evidence values. */
    public static final String UNSTATED_FIELD_PROJECTION =
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
            return host.operand(concreteValue, null);
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
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        if (VmRows.GUARDED_READ_TYPE.equals(
                optionalString(node, "_type"))
                || VmExpressionIr.consumerBoundary(node)
                || VmExpressionIr.isCanonicalMapStateReference(
                optionalString(node, "_exp"))) {
            return true;
        }
        // A local mutation inherits the identity of the state it rests on.
        return EXPRESSION_TYPE.equals(optionalString(node, "_type"))
                && evidencedContainerIdentity(node.get("receiver"));
    }

    /** Resolves {@code READ(WRITE(s, j, v), i)} to the stored {@code v}. */
    private static JsonElement storedIndexedWrite(JsonElement receiver,
                                                  JsonElement index,
                                                  String selectedJavaType) {
        Integer wanted = exactIndexLiteral(index);
        if (wanted == null) return null;
        return storedIndexedWrite(receiver, wanted, selectedJavaType,
                new IdentityHashMap<JsonElement, JsonElement>());
    }

    /**
     * Projects one literal indexed read through value-propagation wrappers,
     * which are kept: their selector and event stay the value's authority.
     */
    private static JsonElement storedIndexedWrite(
            JsonElement receiver, int wanted, String selectedJavaType,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (receiver == null || !receiver.isJsonObject()) return null;
        // A pure function of a decoder-owned DAG: memoize per node.
        if (memo.containsKey(receiver)) return memo.get(receiver);
        JsonElement answer = storedIndexedWriteUncached(receiver, wanted,
                selectedJavaType, memo);
        memo.put(receiver, answer);
        return answer;
    }

    private static JsonElement storedIndexedWriteUncached(
            JsonElement receiver, int wanted, String selectedJavaType,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        JsonObject root = receiver.getAsJsonObject();
        if (VmExpressionIr.consumerBoundary(root)) {
            JsonElement selected = storedIndexedWrite(
                    root.get(VmExpressionIr.EXPRESSION), wanted,
                    selectedJavaType, memo);
            if (selected == null) return null;
            JsonObject projected = JsonFields.shallowCopy(root);
            projected.addProperty("_java_type", selectedJavaType);
            projected.add(VmExpressionIr.EXPRESSION, selected);
            return projected;
        }
        if (VmRows.GUARDED_READ_TYPE.equals(optionalString(root, "_type"))) {
            JsonObject observed = observedVersion(root);
            JsonElement written = observed == null ? null
                    : observed.get(VmExpressionIr.EXPRESSION);
            if (written == null) return null;
            JsonElement selected = storedIndexedWrite(written, wanted,
                    selectedJavaType, memo);
            return selected == null ? null : projectedRead(root, observed,
                    selected, selectedJavaType);
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
                // The stored value is an immutable propagated graph.
                return arguments.get(1);
            }
            cursor = node.get("receiver");
        }
        // A local WRITE prefix may itself rest on a propagated array family.
        return cursor == receiver ? null
                : storedIndexedWrite(cursor, wanted, selectedJavaType, memo);
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
        // The view states whose bijection this call already stated.
        Set<JsonElement> views = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
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
                host.unsupported("ContainerRelation:INDEXED:STATE:arity="
                        + arguments.size());
                return null;
            }
            Term size = host.operand(arguments.get(0), Sort.INT);
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
                host.unsupported("ContainerRelation:INDEXED:NEXT:arity="
                        + positions.size());
                return null;
            }
            // The element a traversal reads: an indexed ITERATOR is the
            // identity on its state.
            Term index = host.operand(positions.get(0), Sort.INT);
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
                    ? host.operand(positions.get(0), Sort.INT) : null;
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
                host.unsupported("ContainerRelation:" + shape + ":"
                        + operation + ":arity=" + arguments.size());
                return null;
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
            Term receiver = host.operand(receiverIr, Sort.INDEXED);
            if (receiver == null) return null;
            receiver = shared(receiver, host);
            if (receiver == null) return null;
            if ("ITERATOR".equals(operation)) return receiver;
            if ("SIZE".equals(operation)) {
                return indexedSize(receiverIr, receiver, host);
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
                        + value.text + ")", Sort.INDEXED,
                        IntegralWidth.NONE, grown(receiver, 1L));
            }
            if ("INSERT".equals(operation) && arguments.size() == 2) {
                Term index = host.operand(arguments.get(0), Sort.INT);
                Term value = host.box(arguments.get(1));
                if (index == null || value == null) return null;
                return shift(receiver, index, value, host);
            }
            if ("REMOVE".equals(operation) && arguments.size() == 1) {
                Term index = host.operand(arguments.get(0), Sort.INT);
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
        } else if ("ASSOCIATIVE".equals(shape)) {
            JsonElement receiverIr = associativeStateExpression(
                    expression.get("receiver"));
            Term receiver = associativeState(expression.get("receiver"),
                    host);
            if (receiver == null) return null;
            if ("SIZE".equals(operation)) {
                return associativeSize(receiver, host);
            }
            if ("CONTAINS".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                return key == null ? null
                        : associativeHas(receiver, key, host);
            }
            if ("READ".equals(operation) && arguments.size() == 1) {
                Term key = host.box(arguments.get(0));
                if (key == null) return null;
                requireStatedContainerBase(receiverIr, key, host);
                return host.unbox(associativeRead(receiver, key, host),
                        javaType);
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
                Term index = host.operand(arguments.get(0), Sort.INT);
                if (index == null) return null;
                // Removing AT a position is a walk of the same view: which
                // key the position names is the bijection's to say.
                if (!requireAssociativeViewBijection(receiverIr, receiver,
                        host, views)) {
                    return null;
                }
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
                // Drops the key when the guard holds; read/has short-circuit
                // this via the mutation walk, this handles a nested receiver.
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

    /** One positional key/value observation of a view's whole state. */
    private static Term associativeEntryValue(Entry entry, String viewKind,
                                              String javaType, Host host,
                                              Set<JsonElement> views) {
        Term state = associativeState(entry.stateExpression, host);
        Term index = host.operand(entry.indexExpression, Sort.INT);
        if (state == null || index == null) return null;
        // Only where the recording bounds the view's positions.
        if (!requireAssociativeViewBijection(entry.stateExpression, state,
                host, views)) {
            return null;
        }
        requireAssociativeMember(state, index, host);
        return new Term(("KEY_VIEW".equals(viewKind)
                ? "(assoc_key_at " : "(assoc_value_at ") + state.text + " "
                + index.text + ")", Sort.VALUE);
    }

    /**
     * Refuses a read whose container chain does not end at a base the VM
     * walked: an INITIAL's {@code SNAPSHOT_BASE} or a program {@code CLEAR}.
     * Membership itself is the assoc model's ({@code assoc_put} /
     * {@code assoc_remove}), decided by z3 for symbolic keys too.
     *
     * <p>Trap: never replace this with an "absent-key default" over the
     * chain's constant PUT keys -- a symbolic PUT key makes that default
     * contradict the chain.</p>
     */
    private static void requireStatedContainerBase(
            JsonElement expression, Term key, Host host) {
        JsonElement chain = expression;
        for (int depth = 0; depth < CONTAINER_CHAIN_LIMIT; depth++) {
            Mutation mutation = associativeMutation(chain);
            if (mutation == null) {
                host.unsupported(CONTAINER_BASE_UNSTATED + ":" + key.text);
                return;
            }
            if (emptiesState(mutation.operation)) return;
            chain = mutation.receiver;
        }
    }

    private static final int CONTAINER_CHAIN_LIMIT = 512;

    /** Refusal subject for an unwalked base; same name as the VM rows use. */
    public static final String CONTAINER_BASE_UNSTATED =
            VmRows.CONTAINER_BASE_UNSTATED;

    /** The value at one key, or the null cell where the key is absent. */
    private static Term associativeRead(Term state, Term key, Host host) {
        return shared(new Term("(let ((s " + state.text + ")) (ite "
                + "(assoc_has s " + key.text + ") (assoc_read s " + key.text
                + ") " + NULL_CELL + "))", Sort.VALUE), host);
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
                return host.operand(arguments.get(0), Sort.INT);
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
            Term state, Term index, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (assoc_size s))"
                + " (assoc_has s (assoc_key_at s i))))");
    }

    /** Refusal subject for a view whose map size nothing bounds. */
    public static final String ASSOC_VIEW_SIZE_UNSTATED =
            "UNSTATED_VALUE:AssociativeViewSize";

    /**
     * AN INDEXED VIEW OF AN ASSOCIATIVE STATE IS A BIJECTION between
     * positions {@code [0, n)} and the keys the state holds.
     * {@code values()}, {@code keySet()}, {@code entrySet()}, {@code toArray}
     * and ITERATOR/NEXT all name each entry once at one position.  Stating
     * only "this position names a present key" lets z3 repeat one key and
     * drop another (hdfs-11741's exported block keys).
     *
     * <pre>
     *   (=&gt; (&lt; p n) (and (has k_p) (= (position k_p) p)))   p in [0, m)
     *   (=&gt; (&lt; q n) (not (= k_p k_q)))                      p &lt; q &lt; m
     *   (=&gt; (has K) (or_{p &lt; m} (and (&lt; p n) (= k_p K))))   K a put key
     * </pre>
     *
     * <p>{@code m}, the chain's put count, bounds {@code n} (from an empty
     * base the keys are exactly the ones put), so the facts are written at
     * CONCRETE positions with no quantifier.  Java's iteration ORDER is not
     * stated: the recording does not state it.  A state with no bounding
     * chain is refused ({@link #ASSOC_VIEW_SIZE_UNSTATED}).</p>
     *
     * @return whether the view's positions are stated
     */
    private static boolean requireAssociativeViewBijection(
            JsonElement stateIr, Term state, Host host,
            Set<JsonElement> views) {
        if (stateIr != null && views.contains(stateIr)) return true;
        List<JsonElement> put = associativeViewKeys(stateIr);
        if (put == null) {
            host.unsupported(ASSOC_VIEW_SIZE_UNSTATED + ":"
                    + associativeStateSubject(stateIr));
            return false;
        }
        Term size = associativeSize(state, host);
        int bound = put.size();
        Term[] at = new Term[bound];
        for (int position = 0; position < bound; position++) {
            Term key = shared(new Term("(assoc_key_at " + state.text + " "
                    + position + ")", Sort.VALUE), host);
            Term present = associativeHas(state, key, host);
            Term where = shared(new Term("(select (assoc_position "
                    + state.text + ") " + key.text + ")", Sort.INT), host);
            at[position] = key;
            host.require("(=> (< " + position + " " + size.text
                    + ") (and " + present.text + " (= " + where.text + " "
                    + position + ")))");
        }
        for (int later = 1; later < bound; later++) {
            for (int earlier = 0; earlier < later; earlier++) {
                host.require("(=> (< " + later + " " + size.text
                        + ") (not (= " + at[earlier].text + " "
                        + at[later].text + ")))");
            }
        }
        for (JsonElement each : put) {
            Term key = host.box(each);
            if (key == null) return false;
            Term present = associativeHas(state, key, host);
            StringBuilder somewhere = new StringBuilder("(or");
            for (int position = 0; position < bound; position++) {
                somewhere.append(" (and (< ").append(position).append(' ')
                        .append(size.text).append(") (= ")
                        .append(at[position].text).append(' ')
                        .append(key.text).append("))");
            }
            host.require("(=> " + present.text + " "
                    + somewhere.append(')') + ")");
        }
        views.add(stateIr);
        return true;
    }

    /**
     * The keys a view's state was put with above an exact empty base, or
     * null when the chain ends anywhere else and so bounds nothing.
     */
    private static List<JsonElement> associativeViewKeys(
            JsonElement state) {
        List<JsonElement> keys = new ArrayList<JsonElement>();
        JsonElement chain = state;
        for (int depth = 0; depth < CONTAINER_CHAIN_LIMIT; depth++) {
            Mutation mutation = associativeMutation(chain);
            if (mutation == null) return null;
            if (emptiesState(mutation.operation)) {
                Collections.reverse(keys);
                return keys;
            }
            if ("PUT".equals(mutation.operation)) {
                keys.add(mutation.arguments.get(0));
            }
            chain = mutation.receiver;
        }
        return null;
    }

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

    private static String selectedReadViewKind(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        if (VmExpressionIr.consumerBoundary(object)) {
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
        if (!VmRows.GUARDED_READ_TYPE.equals(optionalString(object, "_type"))) {
            return "";
        }
        JsonObject observed = observedVersion(object);
        JsonElement written = observed == null ? null
                : observed.get(VmExpressionIr.EXPRESSION);
        return written == null || !written.isJsonObject() ? ""
                : selectedReadViewKind(written);
    }

    /**
     * Projects a view through value-preserving wrappers down to its
     * {@code AssocState}; selectors and provenance stay on the wrappers.
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
        if (VmExpressionIr.consumerBoundary(object)) {
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
        if (!VmRows.GUARDED_READ_TYPE.equals(optionalString(object, "_type"))) {
            return null;
        }
        JsonObject observed = observedVersion(object);
        JsonElement written = observed == null ? null
                : observed.get(VmExpressionIr.EXPRESSION);
        if (written == null) return null;
        JsonElement state = selectedViewState(written, kind, memo);
        if (state == null) return null;
        JsonObject normalized = projectedRead(object, observed, state,
                "java/util/Map");
        memo.put(expression, normalized);
        return normalized;
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

        public Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE);
        }

        public Term(String text, Sort sort, IntegralWidth integralWidth) {
            this(text, sort, integralWidth, -1L);
        }

        public Term(String text, Sort sort, IntegralWidth integralWidth,
                    long indexedSize) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT
                    && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.indexedSize = sort == Sort.INDEXED ? indexedSize : -1L;
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
