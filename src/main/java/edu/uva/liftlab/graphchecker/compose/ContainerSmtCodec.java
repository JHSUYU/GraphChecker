package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

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
    /** Member holding one arm's or candidate's value. */
    private static final String EXPRESSION_MEMBER = "expression";
    private ContainerSmtCodec() {
    }

    /**
     * The version a read node observed, as the one-element list the codec
     * projects through.
     *
     * <p>A read names the version it saw and nothing about the versions it
     * did not.  It used to name every version retained at it and leave the
     * choice to a solver; that candidate set was the stitcher's, and the
     * list here is one long because a read inside one replay has one
     * answer.</p>
     */
    private static JsonArray readVersions(JsonObject read) {
        JsonObject observed = JsonFields.object(read,
                VmRows.OBSERVED_VERSION);
        JsonArray versions = new JsonArray();
        if (observed.size() > 0) versions.add(observed);
        return versions;
    }

    /**
     * Writes the projected version back onto the read node.
     *
     * <p>A read names the one version it observed, so there is one to write
     * back.  The member used to be chosen -- {@code observedVersion} for a
     * node on this schema, {@code candidates} for one still carrying the
     * alternatives -- and during the changeover both shapes were read.  The
     * VM does not publish the older shape any more, so there is one member
     * and no choice to make.</p>
     */
    private static void putVersions(JsonObject projected,
                                    JsonArray versions) {
        projected.add(VmRows.OBSERVED_VERSION,
                versions.get(0));
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
     * <p>JOIN is the read's own {@code observedVersion}, and the VM
     * publishes it ON the value it states: {@code concreteValue} for a
     * primitive read is the read node itself, so the guarded-read lowering
     * joins it to the version's expression -- which is what carries a value
     * from a root, or from a handoff variable, through the object it was
     * stored in and on to the branch that reads it.</p>
     *
     * <p>PIN is what that pair states when the log covers no version: the
     * object read from and what its field then held.  A reference-typed
     * read states the same pair as a primitive one -- {@code concreteOwner}
     * and {@code concreteValue} in the VM's rid spelling, or {@code "N"} for
     * null -- so the host mints the SAME identity name for the object read
     * as it does for an owner of that identity, and one read's reference can
     * be equated with another read's owner.  There is one step: a value the
     * host refuses is refused, never replaced by a second guess.</p>
     *
     * <p>REFUSE is the rest.  Neither query may leave a projection free: an
     * accessor over an uninterpreted Ref is a function the solver may define
     * however it likes, which lets a model hold by a value no execution
     * produced -- a composed query answered that way names no cause, and a
     * flip model answered that way is not materializable.  So a projection
     * with no stated value is refused by name, in the composition and in the
     * flip query alike.</p>
     */
    public static Term field(JsonObject expression, Host host) {
        String ownerClass = optionalString(expression, "ownerClass");
        String javaType = optionalString(expression, "_java_type");
        // The owner term is the projection in exactly one case, and is
        // asked for in no other: lowering it would lower the whole read
        // chain the owner came out of, and a refusal anywhere inside that
        // chain refuses a projection this node states exactly.
        Sort boxed = boxedPayloadSort(ownerClass, javaType);
        if (boxed != null) {
            Term owner = host.operand(expression.get("owner"), Sort.REF);
            if (owner == null) return null;
            if (owner.sort == boxed) return owner;
        }
        // Both members are written together by the VM or not at all; a
        // half-present pair is a payload this codec does not recognise and
        // is refused rather than guessed at.
        JsonElement concreteOwner = expression.get("concreteOwner");
        JsonElement concreteValue = expression.get("concreteValue");
        if (stated(concreteOwner) && stated(concreteValue)) {
            // No expectation: the observed value carries its own Java type
            // and the host's own table is the authority on its sort.
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
     * The sort a boxed primitive's payload field holds, or null.
     *
     * <p>{@code Integer.value} IS the int the box holds, so a read of it is
     * the owner term itself -- the one field whose projection is the object
     * it was read from.  The sort answered here is the sort that owner must
     * already have lowered to; anything else is not that box.</p>
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
        if (VmRows.GUARDED_READ_TYPE.equals(
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
     * Projects one literal indexed read through value-propagation wrappers.
     * The wrapper is retained because its selector and dynamic event remain
     * the authority for the value even when select-over-store is exact.
     */
    private static JsonElement storedIndexedWrite(
            JsonElement receiver, int wanted, String selectedJavaType,
            IdentityHashMap<JsonElement, JsonElement> memo) {
        if (receiver == null || !receiver.isJsonObject()) return null;
        // The receiver is a decoder-owned DAG and this projection is a pure
        // function of it once the wanted index and selected type are fixed,
        // so one answer per node settles every path that reaches it.
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
        if (VmExpressionIr.isConsumerBoundary(root)
                || VmExpressionIr.isConsumerBoundaryReference(root)) {
            JsonElement selected = storedIndexedWrite(
                    root.get(VmExpressionIr.EXPRESSION), wanted,
                    selectedJavaType, memo);
            if (selected == null) return null;
            JsonObject projected = copyWithout(root,
                    VmExpressionIr.EXPRESSION);
            projected.addProperty("_java_type", selectedJavaType);
            projected.add(VmExpressionIr.EXPRESSION, selected);
            return projected;
        }
        String type = optionalString(root, "_type");
        boolean read = VmRows.GUARDED_READ_TYPE.equals(type);
        if (read) {
            JsonArray arms = readVersions(root);
            if (arms.size() == 0) return null;
            JsonObject projected = copyWithout(root, VmRows.OBSERVED_VERSION);
            projected.addProperty("_java_type", selectedJavaType);
            JsonArray projectedArms = new JsonArray();
            for (JsonElement element : arms) {
                if (!element.isJsonObject()) return null;
                JsonObject arm = element.getAsJsonObject();
                if (arm.get("expression") == null) {
                    return null;
                }
                JsonElement selected = storedIndexedWrite(
                        arm.get("expression"), wanted, selectedJavaType,
                        memo);
                if (selected == null) return null;
                JsonObject projectedArm = copyWithout(arm, "expression");
                projectedArm.add("expression", selected);
                projectedArms.add(projectedArm);
            }
            putVersions(projected, projectedArms);
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
                // The stored value is an immutable propagated graph.
                return arguments.get(1);
            }
            cursor = node.get("receiver");
        }
        // A local WRITE prefix may itself rest on a propagated array family.
        return cursor == receiver ? null
                : storedIndexedWrite(cursor, wanted, selectedJavaType, memo);
    }

    /**
     * A fresh wrapper over one node's metadata, minus the payload member the
     * caller is about to replace.
     *
     * <p>The retained members are decoder-owned expression graphs and nobody
     * writes through them.  Cloning them restated each shared subtree once
     * per arm and per path through the choice, which is the same defect
     * {@link CanonicalJson#copy} used to have.</p>
     */
    private static JsonObject copyWithout(JsonObject source, String omitted) {
        JsonObject result = new JsonObject();
        for (java.util.Map.Entry<String, JsonElement> entry
                : source.entrySet()) {
            if (!omitted.equals(entry.getKey())) {
                result.add(entry.getKey(), entry.getValue());
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
            // CONTAINS over an indexed container is REFUSED, by name.
            // There was one way to say it -- "(exists ((i Int)) ... (=
            // (indexed_read s i) v))" -- and a quantifier over an element
            // array is outside the fragment z3 decides: 17960's moved
            // valuation sat for 141 s and came back "(incomplete
            // quantifiers)", which states what the lowering wrote and
            // nothing about the recording.  It is a gap the composition
            // names.
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
                Term read = associativeRead(receiver, key, host);
                return read == null ? null : host.unbox(read, javaType);
            }
            if ("IS_EMPTY".equals(operation) && arguments.size() == 0) {
                Term size = associativeSize(receiver, host);
                return size == null ? null
                        : new Term("(= " + size.text + " 0)", Sort.BOOL);
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
     * Refuses a read whose container the recording never walked.
     *
     * <p>Membership is not decided here.  The assoc model decides it: the
     * chain lowers to {@code assoc_put}/{@code assoc_remove} over the base,
     * a key is present exactly when the store says so, and z3 answers that
     * for a symbolic key as readily as for a constant one.  What this walk
     * checks is the one thing the model cannot: that the chain ends at a
     * base the VM actually walked -- an INITIAL's {@code SNAPSHOT_BASE},
     * which is the exact empty container the PUTs above it refill, or a
     * {@code CLEAR} the program itself did.  A chain that ends on an opaque
     * state states no membership at all, and leaving that to the solver is
     * leaving it to the witness.</p>
     *
     * <p>This used to publish an "absent-key default" instead: a Boolean
     * defined by a syntactic list of the chain's CONSTANT PUT keys.  On bug3
     * the PUT that stores key 119982 has a symbolic key -- the received
     * BlockKey's id -- so the list said 119982 was absent while the chain,
     * under the model, holds it, and seven recorded executions became
     * unstatable.  A default that decides a value the propagation already
     * states is the thing this design does not do.</p>
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

    /**
     * Refusal subject for a membership no recording decides: the same name
     * the shared-state evidence gives an INITIAL that states no base.
     */
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

    /**
     * An indexed state's size: the length an array STATE records, else
     * the model's.
     */
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
     * Refusal subject for an indexed view whose size the recording does not
     * state.  A view of a map whose size nothing states leaves the
     * positions free, and free positions are the thing this states about.
     */
    public static final String ASSOC_VIEW_SIZE_UNSTATED =
            "UNSTATED_VALUE:AssociativeViewSize";

    /**
     * AN INDEXED VIEW OF AN ASSOCIATIVE STATE IS A BIJECTION between the
     * positions {@code [0, n)} and the keys that state holds.
     *
     * <p>{@code values()}, {@code keySet()}, {@code entrySet()},
     * {@code toArray} and an ITERATOR/NEXT walk are all one thing: the
     * map's entries, each named once, at one position each.  Stated
     * position by position -- "this position names a key that is present"
     * -- and nothing more, a formula lets the solver answer every position
     * with the SAME present key and leave another present key at no
     * position at all.  That is how hdfs-11741's composed query delivered
     * the four exported block-key ids 182906, 182908, 182908, 182907 out of
     * a NameNode whose export really held 182905, 182906, 182907, 182908:
     * one id twice, and the id the target looks up nowhere -- a formula
     * stating "the exported set lacks G" with no producer decision having
     * removed G.</p>
     *
     * <p>So the three facts, over the positions the recording bounds and
     * under the size {@code n} the codec derives from the operations:</p>
     *
     * <pre>
     *   (=&gt; (&lt; p n) (and (has k_p) (= (position k_p) p)))   p in [0, m)
     *   (=&gt; (&lt; q n) (not (= k_p k_q)))                      p &lt; q &lt; m
     *   (=&gt; (has K) (or_{p &lt; m} (and (&lt; p n) (= k_p K))))   K a put key
     * </pre>
     *
     * <p>The first two say every live position names a present key, at
     * that position, and that two positions never name one key; the third
     * says no present key sits at no position -- from an empty base the
     * keys a map can hold are exactly the ones put into it, so the
     * disjunction over the chain's put keys is the whole of "every present
     * key".  {@code m} is the number of puts the chain states, which
     * bounds {@code n}: the recording says how many entries were added,
     * so the facts are written out at CONCRETE positions and no quantifier
     * is introduced -- the fragment z3 answers {@code (incomplete
     * quantifiers)} on is the one the container lowering stays out of.</p>
     *
     * <p>What this does NOT state is Java's HashMap ITERATION ORDER.  A
     * recording states which entries a map held, not that a traversal
     * hands them back in ascending key order; the bijection is what
     * soundness needs and the order is not a fact the recording states.</p>
     *
     * <p>A view whose state is not a chain the recording bounds -- an
     * opaque {@code AssocState} the execution never built here, or a
     * choice this codec cannot push the observation through -- has no
     * {@code m} to write the facts out at, and is refused by name
     * ({@link #ASSOC_VIEW_SIZE_UNSTATED}) rather than left with free
     * positions.</p>
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
        if (size == null) return false;
        int bound = put.size();
        Term[] at = new Term[bound];
        for (int position = 0; position < bound; position++) {
            Term key = shared(new Term("(assoc_key_at " + state.text + " "
                    + position + ")", Sort.VALUE), host);
            Term present = key == null ? null
                    : associativeHas(state, key, host);
            Term where = key == null ? null : shared(new Term(
                    "(select (assoc_position " + state.text + ") "
                            + key.text + ")", Sort.INT), host);
            if (key == null || present == null || where == null) {
                return false;
            }
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
            Term present = key == null ? null
                    : associativeHas(state, key, host);
            if (present == null) return false;
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
     * The keys one view's state was built from, or null when the recording
     * bounds no such set.
     *
     * <p>A chain that ends at the exact empty container holds exactly the
     * keys put into it above that base, so the puts bound both how many
     * entries the view can have and which keys they can be.  A chain that
     * ends anywhere else -- an opaque state, a choice, a Java expression
     * this codec does not read as a map -- bounds neither.</p>
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
     * One list insertion or removal, shifted WITHOUT a quantifier.
     *
     * <p>A whole-state insert or remove would state the shift as a
     * {@code lambda} over every index, which puts the query in a fragment
     * z3 answers {@code (incomplete quantifiers)}: 17960's moved valuation
     * came back undecided after 141 s while the same query with the two
     * lambdas gone was decided in 0.07 s.  The shift itself is finite --
     * the recording states how many elements the list held -- so where the
     * size is stated the result is written out as that many
     * {@code store}s, each at a CONCRETE index:</p>
     *
     * <pre>
     *   insert: a[k] = ite(k &lt; i, s[k], ite(k = i, v, s[k-1]))  k in [0, n]
     *   remove: a[k] = ite(k &lt; i, s[k], s[k+1])                 k in [0, n-2]
     * </pre>
     *
     * <p>Exact, not approximate: every index the list has is written, and
     * the index {@code i} stays symbolic -- no case split on it, so the
     * term is linear in the size the recording stated.  The cells past the
     * new size are not written because they are not in the list; the size
     * is what says which they are.</p>
     *
     * <p>The operation's own DEFINEDNESS is stated beside it, as the
     * division lowering states a non-zero divisor: {@code List.add(i, v)}
     * requires {@code 0 <= i <= n} and {@code remove(i)} requires
     * {@code 0 <= i < n}, and an index outside that throws rather than
     * producing a list.  The recording shows the operation HAPPENED, so
     * this is that execution's own fact, and no witness is lost by it: an
     * out-of-range index is an execution that threw, which is not a path
     * that reached the anchor.</p>
     *
     * <p>A state whose size the recording does not state keeps the
     * quantified definition -- there is nothing here to invent a size
     * from -- and an {@code unknown} the quantifiers leave behind is named
     * by {@link Solver} rather than passed off as a verdict.</p>
     *
     * @param value the element to insert, or null for a removal
     */
    private static Term shift(Term receiver, Term index, Term value,
                              Host host) {
        long size = receiver.indexedSize;
        boolean insert = value != null;
        if (size < 0L) {
            // No stated size: the shift stays the quantified relation it
            // was, and the refusal is the solver's to name.
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
        if (value == null) return null;
        Term result = host.share(value);
        if (result == null || result.sort != value.sort) {
            host.unsupported("ContainerRelation:shared-term-sort");
            return null;
        }
        return result;
    }

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
        if (!"ReadFromExpression".equals(type)) return "";
        JsonArray arms = readVersions(object);
        if (arms.size() == 0) return "";
        String selected = "";
        for (JsonElement element : arms) {
            if (!element.isJsonObject()) return "";
            JsonObject arm = element.getAsJsonObject();
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
        if (!"ReadFromExpression".equals(type)) return null;
        JsonArray arms = readVersions(object);
        if (arms.size() == 0) return null;
        JsonObject normalized = JsonFields.shallowCopy(object);
        normalized.addProperty("_java_type", "java/util/Map");
        JsonArray normalizedArms = new JsonArray();
        for (JsonElement element : arms) {
            if (!element.isJsonObject()) return null;
            JsonObject arm = element.getAsJsonObject();
            if (arm.get("expression") == null) return null;
            JsonElement projectedArm = selectedViewState(
                    arm.get("expression"), kind, memo);
            if (projectedArm == null) return null;
            JsonObject normalizedArm = JsonFields.shallowCopy(arm);
            normalizedArm.add("expression", projectedArm);
            normalizedArms.add(normalizedArm);
        }
        putVersions(normalized, normalizedArms);
        memo.put(expression, normalized);
        return normalized;
    }


    /**
     * The one lowering of a boxed container {@code Value} back to the Java
     * sort it holds.  The caller resolves the Java type to {@code cellSort}
     * because the two encoders answer that question differently.
     */
    public interface Host {
        Term state(JsonElement identity, Sort shape);

        Term operand(JsonElement expression, Sort expected);

        /**
         * Whether an externally evidenced container identity must survive
         * local select-over-store simplification.
         */
        boolean preserveContainerIdentity(JsonElement expression,
                                                  Sort expected);

        /**
         * Returns an equivalent name for a pure term when the encoder keeps
         * a definitional DAG.  The identity default preserves hosts that
         * already bound large container terms at their operand boundary.
         */
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
         * How many elements this INDEXED state holds, or {@code -1}.
         *
         * <p>The RECORDING states it: a container the execution built from
         * an empty one, or from a snapshot whose size the VM published as a
         * literal, has a size this lowering can count along the chain of
         * operations it is lowering.  It is what lets a shift be written as
         * a finite store chain instead of a {@code lambda} -- the whole
         * reason 17960's moved valuation came back
         * {@code (incomplete quantifiers)} -- and it is never guessed: a
         * state whose size the recording does not state carries
         * {@code -1}.</p>
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
