package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
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
    /**
     * The relations that carry a {@code guard}: the conditional mutations,
     * which state both arms of it (REMOVE_IF, PUT_IF, APPEND_IF), and PIN,
     * which requires it.
     */
    private static final Set<String> GUARDED = Collections.unmodifiableSet(
            new HashSet<String>(java.util.Arrays.asList("REMOVE_IF",
                    "PUT_IF", "APPEND_IF", "PIN")));

    /** Whether a relation's {@code guard} is a decision it states both ways. */
    public static boolean conditionalMutation(String operation) {
        return GUARDED.contains(operation) && !"PIN".equals(operation);
    }
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

    /**
     * What {@link #field} lowers of one projection: the owner of a boxed
     * payload, and the cell of a stated pair.  Never {@code concreteOwner},
     * which only spells the run's object, nor otherwise the owner, whose
     * read chain no lowering asks.  Null for a projection {@link #field}
     * refuses, which rests on all it names.
     */
    public static List<JsonElement> fieldOperands(JsonObject expression) {
        List<JsonElement> operands = new ArrayList<JsonElement>();
        if (boxedPayloadSort(optionalString(expression, "ownerClass"),
                optionalString(expression, "_java_type")) != null) {
            operands.add(expression.get("owner"));
        }
        if (stated(expression.get("concreteOwner"))
                && stated(expression.get("concreteValue"))) {
            operands.add(expression.get("concreteValue"));
        }
        return operands.isEmpty() ? null : operands;
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
        // A query the chain cannot decide answers what its call stated it
        // returned, where the host pins that ({@link Host#answered}).
        if (expression.has(ANSWER) && expression.has("concreteValue")
                && !statedBase(expression.get("receiver"), host)) {
            Term pinned = host.answered(expression);
            if (pinned != null) return pinned;
        }
        Term answer = relation(expression, host);
        return answer == null || !expression.has("owner")
                || answer.sort == Sort.INDEXED
                || answer.sort == Sort.ASSOCIATIVE
                ? answer : host.query(expression, answer);
    }

    /**
     * The member a query states its session-unique answer id in, beside the
     * {@code concreteValue} its call returned (ContainerExpression's
     * {@code state_returned}): only a query whose chain may not decide it;
     * and the id that names an {@code UNKNOWN} cell.
     */
    public static final String ANSWER = "answer";

    /**
     * Whether a state's chain ends at a base the VM walked -- a
     * {@code SNAPSHOT_BASE} or a program {@code CLEAR} -- through every
     * relation under it (views, iterators, entries, mutations, pins): then
     * it decides a query over it.  A {@code STATE} root, or anything no
     * relation, is opaque.  Each state is the one it stands for
     * ({@link Host#chain}), and the host remembers every answer
     * ({@link Host#statedBase}), so a long chain is walked once.
     */
    private static boolean statedBase(JsonElement state, Host host) {
        List<JsonElement> walked = new ArrayList<JsonElement>();
        JsonElement cursor = state;
        Boolean stated = null;
        while (stated == null) {
            JsonElement node = host.chain(cursor);
            stated = node == null ? Boolean.FALSE : host.statedBase(node);
            if (stated != null) break;
            walked.add(node);
            String operation = handles(node)
                    ? optionalString(node.getAsJsonObject(), "operation")
                    : "STATE";
            if (emptiesState(operation)) {
                stated = Boolean.TRUE;
            } else if ("STATE".equals(operation)) {
                stated = Boolean.FALSE;
            } else {
                cursor = node.getAsJsonObject().get("receiver");
            }
        }
        for (JsonElement node : walked) host.statedBase(node, stated);
        return stated.booleanValue();
    }

    /**
     * One relation node lowered by its rule ({@link #RULES}): the rule of
     * its (shape, operation), else of its operation on any shape, where its
     * argument count is the rule's.  With no rule there, the operation is
     * refused by name -- a list's or map's after its receiver state is
     * lowered, so a receiver that does not lower is the refusal named.
     */
    private static Term relation(JsonObject expression, Host host) {
        Call call = new Call(expression, host);
        Rule rule = RULES.get(call.shape + " " + call.operation);
        if (rule == null) rule = RULES.get(ANY_SHAPE + " " + call.operation);
        if (rule != null && (rule.arity == ANY_ARITY
                || rule.arity == call.arguments.size())) {
            return rule.lowering.lower(call);
        }
        if (("INDEXED".equals(call.shape)
                || "ASSOCIATIVE".equals(call.shape))
                && call.receiver() == null) {
            return null;
        }
        return unmodeled(call.shape, call.operation, call.arguments, host);
    }

    /** One relation node being lowered, with what its rule reads of it. */
    private static final class Call {
        final JsonObject expression;
        final Host host;
        final String shape;
        final String operation;
        final String javaType;
        final JsonArray arguments;
        /** The view states whose bijection this call already stated. */
        final Map<JsonElement, ViewOrder> views =
                new IdentityHashMap<JsonElement, ViewOrder>();

        Call(JsonObject expression, Host host) {
            this.expression = expression;
            this.host = host;
            this.shape = optionalString(expression, "shape");
            this.operation = optionalString(expression, "operation");
            this.javaType = optionalString(expression, "_java_type");
            this.arguments = array(expression, "arguments");
        }

        JsonElement receiverIr() {
            return expression.get("receiver");
        }

        /** The state the operation is on: a list's, shared, or a map's. */
        Term receiver() {
            return "INDEXED".equals(shape)
                    ? shared(host.operand(receiverIr(), Sort.INDEXED), host)
                    : associativeState(receiverIr(), host);
        }

        JsonElement argument(int index) {
            return arguments.get(index);
        }

        Term unboxed(Term value) {
            return value == null ? null : host.unbox(value, javaType);
        }
    }

    /** How one relation lowers ({@link #RULES}). */
    private interface Lowering {
        Term lower(Call call);
    }

    /** One operation on its receiver state, lowered once it is. */
    private interface OnState {
        Term lower(Call call, Term receiver);
    }

    /** A rule's lowering of a relation on its receiver state: none where
     *  the receiver does not lower. */
    private static Lowering onState(OnState lowering) {
        return call -> {
            Term receiver = call.receiver();
            return receiver == null ? null : lowering.lower(call, receiver);
        };
    }

    /** The argument count of a rule that takes any. */
    private static final int ANY_ARITY = -1;
    /** The shape of a rule for an operation on any shape. */
    private static final String ANY_SHAPE = "*";

    private static final class Rule {
        final int arity;
        final Lowering lowering;

        Rule(int arity, Lowering lowering) {
            this.arity = arity;
            this.lowering = lowering;
        }
    }

    /**
     * Every relation's lowering, keyed {@code "<shape> <operation>"} (shape
     * {@link #ANY_SHAPE}: any), with the argument count it takes.
     */
    private static final Map<String, Rule> RULES =
            new HashMap<String, Rule>();

    private static void rule(String shape, String operation, int arity,
                             Lowering lowering) {
        RULES.put(shape + " " + operation, new Rule(arity, lowering));
    }

    static {
        // What a callback the run never ran would have stored.
        rule(ANY_SHAPE, "UNKNOWN", ANY_ARITY,
                call -> call.host.unknown(call.expression));
        rule(ANY_SHAPE, "STATE", ANY_ARITY, ContainerSmtCodec::stateRoot);
        rule(ANY_SHAPE, "KEY", ANY_ARITY, ContainerSmtCodec::entryPart);
        rule(ANY_SHAPE, "VALUE", ANY_ARITY, ContainerSmtCodec::entryPart);
        rule(ANY_SHAPE, "HAS_NEXT", ANY_ARITY, ContainerSmtCodec::hasNext);
        rule(ANY_SHAPE, "CLEAR", ANY_ARITY, ContainerSmtCodec::emptied);
        rule(ANY_SHAPE, "SNAPSHOT_BASE", ANY_ARITY,
                ContainerSmtCodec::emptied);

        // A list, array or queue state.
        rule("INDEXED", "NEXT", ANY_ARITY, ContainerSmtCodec::indexedNext);
        rule("INDEXED", "READ", 1, ContainerSmtCodec::indexedRead);
        rule("INDEXED", "ITERATOR", ANY_ARITY,
                onState((call, receiver) -> receiver));
        rule("INDEXED", "SIZE", ANY_ARITY, onState((call, receiver) ->
                indexedSize(call.receiverIr(), receiver, call.host)));
        rule("INDEXED", "WRITE", 2, onState((call, receiver) -> {
            Term index = integer(call.argument(0), call.host);
            Term value = call.host.box(call.argument(1));
            if (index == null || value == null) return null;
            // A set() or an array store throws outside its receiver, as a
            // get() does.  In place: the size is the receiver's (dropped,
            // Lucene's deleteCommits compaction left its REMOVE no size to
            // shift by).
            requireIndexedMember(receiver, index, call.host);
            return new Term("(indexed_write " + receiver.text + " "
                    + index.text + " " + value.text + ")",
                    Sort.INDEXED, IntegralWidth.NONE, receiver.indexedSize);
        }));
        rule("INDEXED", "APPEND", 1, onState((call, receiver) -> {
            Term value = call.host.box(call.argument(0));
            return value == null ? null
                    : new Term("(indexed_append " + receiver.text + " "
                    + value.text + ")", Sort.INDEXED,
                    IntegralWidth.NONE, grown(receiver, 1L));
        }));
        // A stream's member under the decisions that let it through.
        rule("INDEXED", "APPEND_IF", 1, onState((call, receiver) -> {
            Term value = call.host.box(call.argument(0));
            Term guard = call.host.operand(call.expression.get("guard"),
                    Sort.BOOL);
            return value == null || guard == null ? null
                    : new Term("(indexed_append_if " + receiver.text + " "
                    + value.text + " " + guard.text + ")", Sort.INDEXED);
        }));
        rule("INDEXED", "PIN", 0, onState((call, receiver) ->
                pinned(receiver, call.expression, call.host)));
        rule("INDEXED", "CONTAINS", 1, onState((call, receiver) ->
                indexedContains(call.receiverIr(), receiver,
                        call.argument(0), call.host)));
        rule("INDEXED", "INSERT", 2, onState((call, receiver) -> {
            Term index = integer(call.argument(0), call.host);
            Term value = call.host.box(call.argument(1));
            if (index == null || value == null) return null;
            return shift(receiver, index, value, call.host);
        }));
        rule("INDEXED", "REMOVE", 1, onState((call, receiver) -> {
            Term index = integer(call.argument(0), call.host);
            return index == null ? null
                    : shift(receiver, index, null, call.host);
        }));
        rule("INDEXED", "IS_EMPTY", 0, onState((call, receiver) ->
                new Term("(= (indexed_size " + receiver.text + ") 0)",
                        Sort.BOOL)));
        // A queue's head, or null where it is empty: no member required.
        rule("INDEXED", "PEEK", 0, onState((call, receiver) -> {
            long size = receiver.indexedSize;
            String head = "(indexed_read " + receiver.text + " 0)";
            return call.unboxed(new Term(size == 0L ? NULL_CELL
                    : size > 0L ? head
                    : "(ite (= (indexed_size " + receiver.text + ") 0) "
                    + NULL_CELL + " " + head + ")", Sort.VALUE));
        }));
        // Without its head where it has one: whether it does is the op's
        // own test, which a stated size decides; with none, as a removal,
        // it is refused by name.
        rule("INDEXED", "POLL", 0, onState((call, receiver) -> {
            if (receiver.indexedSize == 0L) return receiver;
            if (receiver.indexedSize < 0L) {
                call.host.unsupported("ContainerRelation:INDEXED:POLL:"
                        + "unstated-size");
                return null;
            }
            return shift(receiver, new Term("0", Sort.INT), null,
                    call.host);
        }));

        // A map or set state.
        rule("ASSOCIATIVE", "NEXT", ANY_ARITY,
                ContainerSmtCodec::associativeNext);
        rule("ASSOCIATIVE", "READ", 1, ContainerSmtCodec::lookup);
        rule("ASSOCIATIVE", "CONTAINS", 1, ContainerSmtCodec::lookup);
        rule("ASSOCIATIVE", "READ_OR_DEFAULT", 2, ContainerSmtCodec::lookup);
        rule("ASSOCIATIVE", "MATCHES", 2, ContainerSmtCodec::lookup);
        rule("ASSOCIATIVE", "SIZE", ANY_ARITY, onState((call, receiver) ->
                associativeSize(receiver, call.host)));
        rule("ASSOCIATIVE", "IS_EMPTY", 0, onState((call, receiver) ->
                new Term("(= " + associativeSize(receiver, call.host).text
                        + " 0)", Sort.BOOL)));
        for (String view : new String[]{"ITERATOR", "ENTRY_VIEW",
                "KEY_VIEW", "VALUE_VIEW"}) {
            rule("ASSOCIATIVE", view, ANY_ARITY,
                    onState((call, receiver) -> receiver));
        }
        rule("ASSOCIATIVE", "PUT", 2, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            Term value = call.host.box(call.argument(1));
            return key == null || value == null ? null
                    : new Term("(assoc_put " + receiver.text + " "
                    + key.text + " " + value.text + ")",
                    Sort.ASSOCIATIVE);
        }));
        // Removing AT a position is a walk of the same view: which key the
        // position names is the bijection's to say.
        rule("ASSOCIATIVE", "REMOVE_AT", 1, onState((call, receiver) -> {
            Term index = integer(call.argument(0), call.host);
            if (index == null) return null;
            ViewOrder order = requireAssociativeViewBijection(
                    associativeStateExpression(call.receiverIr()), receiver,
                    call.host, call.views);
            if (order == null) return null;
            requireAssociativeMember(receiver, index, order, call.host);
            return new Term("(let ((s " + receiver.text
                    + ")) (assoc_remove s (" + order.keyAt + " s "
                    + index.text + ")))", Sort.ASSOCIATIVE);
        }));
        rule("ASSOCIATIVE", "REMOVE", 1, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            return key == null ? null
                    : new Term("(assoc_remove " + receiver.text + " "
                    + key.text + ")", Sort.ASSOCIATIVE);
        }));
        rule("ASSOCIATIVE", "PUT_ALL", 1, onState((call, receiver) ->
                putAll(receiver, call.argument(0), call.host)));
        // Drops the key when the guard holds; read/has short-circuit this
        // via the mutation walk, this handles a nested receiver.
        rule("ASSOCIATIVE", "REMOVE_IF", 1, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            Term guard = call.host.operand(call.expression.get("guard"),
                    Sort.BOOL);
            return key == null || guard == null ? null
                    : new Term("(assoc_remove_if " + receiver.text + " "
                    + key.text + " " + guard.text + ")",
                    Sort.ASSOCIATIVE);
        }));
        // A stream's member collected to a set where the guard holds.
        rule("ASSOCIATIVE", "PUT_IF", 2, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            Term value = call.host.box(call.argument(1));
            Term guard = call.host.operand(call.expression.get("guard"),
                    Sort.BOOL);
            return key == null || value == null || guard == null ? null
                    : new Term("(assoc_put_if " + receiver.text + " "
                    + key.text + " " + value.text + " " + guard.text + ")",
                    Sort.ASSOCIATIVE);
        }));
        rule("ASSOCIATIVE", "PIN", 0, onState((call, receiver) ->
                pinned(receiver, call.expression, call.host)));
    }

    /** A STATE root, of a list sized by its one argument where it states
     *  one. */
    private static Term stateRoot(Call call) {
        Sort stateSort = "INDEXED".equals(call.shape)
                ? Sort.INDEXED : Sort.ASSOCIATIVE;
        Term state = call.host.state(call.receiverIr(), stateSort);
        if (state == null || stateSort != Sort.INDEXED
                || call.arguments.size() == 0) {
            return state;
        }
        if (call.arguments.size() != 1) {
            return unmodeled("INDEXED", call.operation, call.arguments,
                    call.host);
        }
        Term size = integer(call.argument(0), call.host);
        return size == null ? null : new Term(
                "(mkIndexedState " + size.text
                        + " (indexed_elements " + state.text + "))",
                Sort.INDEXED, IntegralWidth.NONE, literal(size.text));
    }

    /** A map entry's key or value, by its view's position. */
    private static Term entryPart(Call call) {
        Entry entry = entry(call.receiverIr());
        if (entry == null) {
            call.host.unsupported("ContainerRelation:malformed-entry:"
                    + call.operation);
            return null;
        }
        return call.unboxed(associativeEntryValue(entry,
                "KEY".equals(call.operation) ? "KEY_VIEW" : "VALUE_VIEW",
                call.javaType, call.host, call.views));
    }

    /** Whether a traversal's position is below its state's size. */
    private static Term hasNext(Call call) {
        Sort stateSort = "INDEXED".equals(call.shape)
                ? Sort.INDEXED : Sort.ASSOCIATIVE;
        Term position = call.arguments.size() == 1
                ? integer(call.argument(0), call.host) : null;
        Term state = stateSort == Sort.ASSOCIATIVE
                ? associativeState(call.receiverIr(), call.host)
                : call.host.operand(call.receiverIr(), stateSort);
        Term size = state == null ? null
                : stateSort == Sort.ASSOCIATIVE
                ? associativeSize(state, call.host)
                : indexedSize(call.receiverIr(), state, call.host);
        if (position == null || size == null) {
            call.host.unsupported("ContainerRelation:" + call.shape
                    + ":HAS_NEXT");
            return null;
        }
        return new Term("(and (<= 0 " + position.text + ") (< "
                + position.text + " " + size.text + "))", Sort.BOOL);
    }

    /** A state emptied: a program {@code CLEAR} or a snapshot's base. */
    private static Term emptied(Call call) {
        if (call.arguments.size() != 0) {
            return unmodeled(call.shape, call.operation, call.arguments,
                    call.host);
        }
        if ("INDEXED".equals(call.shape)) {
            return new Term("(mkIndexedState 0"
                    + " ((as const (Array Int Value))"
                    + " " + NULL_CELL + "))", Sort.INDEXED,
                    IntegralWidth.NONE, 0L);
        }
        if ("ASSOCIATIVE".equals(call.shape)) {
            return new Term("(mkAssocState 0"
                    + " ((as const (Array Value Bool)) false)"
                    + " ((as const (Array Value Value))"
                    + " " + NULL_CELL + ")"
                    + " ((as const (Array Int Value))"
                    + " " + NULL_CELL + ")"
                    + " ((as const (Array Value Int)) (- 1)))",
                    Sort.ASSOCIATIVE);
        }
        return unmodeled(call.shape, call.operation, call.arguments,
                call.host);
    }

    /** The element a list traversal reads: an indexed ITERATOR is the
     *  identity on its state. */
    private static Term indexedNext(Call call) {
        if (call.arguments.size() != 1) {
            return unmodeled(call.shape, call.operation, call.arguments,
                    call.host);
        }
        Term index = integer(call.argument(0), call.host);
        Term cursor = call.host.operand(call.receiverIr(), Sort.INDEXED);
        if (cursor != null && index != null) {
            requireIndexedMember(cursor, index, call.host);
        }
        return cursor == null || index == null ? null
                : call.unboxed(new Term("(indexed_read " + cursor.text
                + " " + index.text + ")", Sort.VALUE));
    }

    /** The key or value a map view's traversal reads at its position. */
    private static Term associativeNext(Call call) {
        View view = view(call.receiverIr());
        if (view == null || call.arguments.size() != 1
                || "ENTRY_VIEW".equals(view.kind)) {
            call.host.unsupported("ContainerRelation:ASSOCIATIVE:NEXT:view");
            return null;
        }
        return call.unboxed(associativeEntryValue(new Entry(
                view.stateExpression, call.argument(0)), view.kind,
                call.javaType, call.host, call.views));
    }

    /**
     * A list's element: the value stored by the write it reads where the
     * receiver's chain names it and no evidenced identity must be kept,
     * else the element at its index of the receiver state.
     */
    private static Term indexedRead(Call call) {
        if (!evidencedContainerIdentity(call.receiverIr())) {
            JsonElement stored = storedIndexedWrite(call.receiverIr(),
                    call.argument(0), call.javaType);
            if (stored != null) {
                return call.host.unbox(call.host.box(stored), call.javaType);
            }
        }
        Term receiver = call.receiver();
        if (receiver == null) return null;
        Term index = integer(call.argument(0), call.host);
        if (index != null) {
            requireIndexedMember(receiver, index, call.host);
        }
        return index == null ? null
                : call.unboxed(new Term("(indexed_read " + receiver.text
                + " " + index.text + ")", Sort.VALUE));
    }

    /** A map lookup: read, contains, read-or-default or a key match. */
    private static Term lookup(Call call) {
        return associativeLookup(associativeStateExpression(
                call.receiverIr()), call.operation, call.arguments,
                call.javaType, call.host);
    }

    /**
     * A state that holds only where the run's own decision does: the
     * {@code guard} of a PIN (what a stream pulled no further, or dropped
     * before anything relations follow) is required wherever the state is
     * used, and the state is its receiver's.
     */
    private static Term pinned(Term receiver, JsonObject expression,
                               Host host) {
        Term guard = host.operand(expression.get("guard"), Sort.BOOL);
        if (guard == null) return null;
        host.require(guard.text);
        return receiver;
    }

    /**
     * {@code contains(x)} on a list: some position below its size holds
     * {@code x}, a disjunction over the positions its chain can fill -- the
     * appends and insertions above an exact base ({@link #indexedBound}),
     * as {@link #putAll} unrolls its source's keys.  Its quantified form
     * is outside what z3 decides ("incomplete quantifiers"), so a chain
     * with no exact base within {@link #VIEW_CHAIN_LIMIT} is refused by
     * name.
     */
    private static Term indexedContains(JsonElement receiverIr,
                                        Term receiver, JsonElement wanted,
                                        Host host) {
        Integer bound = indexedBound(receiverIr, host);
        if (bound == null) {
            host.unsupported("ContainerRelation:INDEXED:CONTAINS:"
                    + "unbounded-chain");
            return null;
        }
        Term value = host.box(wanted);
        if (value == null) return null;
        StringBuilder any = new StringBuilder("(let ((s ")
                .append(receiver.text).append(") (x ").append(value.text)
                .append(")) (or false");
        for (int position = 0; position < bound; position++) {
            any.append(" (and (< ").append(position)
                    .append(" (indexed_size s)) (= (indexed_read s ")
                    .append(position).append(") x))");
        }
        return shared(new Term(any.append("))").toString(), Sort.BOOL),
                host);
    }

    /**
     * How many positions an INDEXED chain can fill: its appends and
     * insertions, guarded or not, down to an exact base (a stated
     * {@code SNAPSHOT_BASE}, whose members are appends above it, or a
     * {@code CLEAR}); writes, removals, polls and pins fill none.  Null for a
     * chain with no such base within {@link #VIEW_CHAIN_LIMIT}.  Each
     * state is the one it stands for ({@link Host#chain}).
     */
    private static Integer indexedBound(JsonElement state, Host host) {
        int filled = 0;
        JsonElement chain = state;
        for (int depth = 0; depth < VIEW_CHAIN_LIMIT; depth++) {
            JsonElement node = host.chain(chain);
            if (node == null || !node.isJsonObject()) return null;
            JsonObject relation = node.getAsJsonObject();
            if (!EXPRESSION_TYPE.equals(optionalString(relation, "_type"))
                    || !"INDEXED".equals(optionalString(relation, "shape"))) {
                return null;
            }
            String operation = optionalString(relation, "operation");
            if (emptiesState(operation)) return filled;
            if ("APPEND".equals(operation) || "APPEND_IF".equals(operation)
                    || "INSERT".equals(operation)) {
                filled++;
            } else if (!"WRITE".equals(operation)
                    && !"REMOVE".equals(operation)
                    && !"POLL".equals(operation)
                    && !"PIN".equals(operation)) {
                return null;
            }
            chain = relation.get("receiver");
        }
        return null;
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
     * the key is absent), a membership test, or a match ({@code MATCHES}:
     * whether the read, null where the key is absent, is the expected cell
     * -- the test a muted body made of the value there) at one key.  With a
     * literal key, the chain's
     * mutations at other literal keys, guarded or not, cannot touch it and
     * are passed in the IR, never lowered: a map the recording rebuilt from a
     * store's bytes (Solr's cluster state, one per notification) is a put per
     * entry, and lowering every one of them was millions of container terms
     * for a query that reads one key.  The walk stops at the first mutation
     * at the key (its answer; a guarded one's answer is the lowered whole),
     * at a key that is not a literal, at a pin, or at the chain's base,
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
        boolean match = "MATCHES".equals(operation);
        Term absent = arguments.size() == 2 && !match
                ? host.box(arguments.get(1)) : new Term(NULL_CELL, Sort.VALUE);
        Term expected = match ? host.box(arguments.get(1)) : null;
        if (absent == null || match && expected == null) return null;
        JsonElement state = receiverIr;
        String literal = literalKey(key);
        if (literal != null) {
            while (true) {
                Mutation mutation = associativeMutation(state);
                boolean guarded = mutation != null
                        && ("PUT_IF".equals(mutation.operation)
                        || "REMOVE_IF".equals(mutation.operation));
                if (mutation == null || !guarded
                        && !"PUT".equals(mutation.operation)
                        && !"REMOVE".equals(mutation.operation)) {
                    break;
                }
                String at = literalKey(mutation.arguments.get(0));
                if (at == null) break;
                // A guarded mutation at the key may not have fired: from it
                // on, the chain is lowered whole.
                if (guarded && at.equals(literal)) break;
                if (at.equals(literal)) {
                    boolean removed = "REMOVE".equals(mutation.operation);
                    if (!read) {
                        return new Term(removed ? "false" : "true",
                                Sort.BOOL);
                    }
                    Term value = removed ? absent
                            : host.box(mutation.arguments.get(1));
                    return value == null ? null : match
                            ? matched(value, expected)
                            : host.unbox(value, javaType);
                }
                state = mutation.receiver;
            }
        }
        Term receiver = associativeState(state, host);
        if (receiver == null) return null;
        if (!read) return associativeHas(receiver, wanted, host);
        Term cell = associativeRead(receiver, wanted, absent, host);
        if (match) return matched(cell, expected);
        requireStatedContainerBase(state, wanted, host);
        return host.unbox(cell, javaType);
    }

    /** Whether one cell is another: a Java value's equality, by its tag. */
    private static Term matched(Term cell, Term expected) {
        return new Term("(= " + cell.text + " " + expected.text + ")",
                Sort.BOOL);
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
     * order ({@code assoc_key_at}, {@code assoc_position_of}), where it is the
     * order the map's class iterates in ({@link #unordered}).  {@code FREE}:
     * a bijection between the positions and the state's keys and nothing
     * more ({@code assoc_view_key}, {@code assoc_view_position},
     * {@code ContainerStateModel}), where it is not: the formula then names
     * no order the run did not have, and a consumer that reads the view as
     * a set (hdfs-11741's exported block keys) keeps every key.
     */
    enum ViewOrder {
        STATED("assoc_key_at", "assoc_position_of"),
        FREE("assoc_view_key", "assoc_view_position");

        final String keyAt;
        private final String positionOf;

        ViewOrder(String keyAt, String positionOf) {
            this.keyAt = keyAt;
            this.positionOf = positionOf;
        }

        /** The position this order holds one key at. */
        Term position(Term state, Term key, Host host) {
            return shared(new Term("(" + positionOf + " " + state.text + " "
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
        String unordered = unordered(stateIr, host, put);
        ViewOrder order = unordered.isEmpty() ? ViewOrder.STATED
                : ViewOrder.FREE;
        if (order == ViewOrder.FREE) {
            host.diagnostic(ASSOC_VIEW_UNORDERED + ":" + unordered + ":"
                    + mapNamed(stateIr, host), "a view of this map reads "
                    + "positions its chain does not order (UNRECORDED: its "
                    + "snapshot states no iteration order; HASH_INSERT: a "
                    + "put of another key into a hash-ordered map may rebin "
                    + "its table), so they are a bijection with its keys in "
                    + "no order (assoc_view_key)");
        }
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

    /** The DIAGNOSTIC naming a view whose positions are FREE. */
    public static final String ASSOC_VIEW_UNORDERED = "ASSOC_VIEW_UNORDERED";

    /**
     * Why the chain's order is not the order Java iterates this state in
     * ({@code UNRECORDED}, {@code HASH_INSERT}, {@code CHAIN},
     * {@code PUT_ALL:}<i>its source's</i>), or {@code ""} when it is.
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
    private static String unordered(JsonElement state, Host host,
                                    List<JsonElement> put) {
        if (oneKey(put)) return "";
        List<Mutation> above = new ArrayList<Mutation>();
        JsonElement chain = state;
        JsonObject base = null;
        int members = 0;
        for (int depth = 0; depth < VIEW_CHAIN_LIMIT && base == null;
             depth++) {
            JsonElement node = host.chain(chain);
            Mutation mutation = associativeMutation(node);
            if (mutation == null) return "CHAIN";
            if ("SNAPSHOT_BASE".equals(mutation.operation)) {
                base = node.getAsJsonObject();
                members = JsonFields.optionalInteger(base, "members", -1);
            } else if ("CLEAR".equals(mutation.operation)) {
                base = snapshotBase(mutation.receiver, host);
                if (base == null) return "CHAIN";
            } else {
                above.add(mutation);
                chain = mutation.receiver;
            }
        }
        String order = base == null ? "" : optionalString(base, "order");
        boolean hash = "HASH".equals(order);
        if (!hash && !"INSERTION".equals(order) || members < 0
                || members > above.size()) {
            return "UNRECORDED";
        }
        Set<String> present = new HashSet<String>();
        for (int index = above.size() - 1; index >= 0; index--) {
            Mutation mutation = above.get(index);
            boolean member = index >= above.size() - members;
            String key = mutation.arguments.size() == 0 ? null
                    : literalKey(mutation.arguments.get(0));
            if ("PUT_ALL".equals(mutation.operation)) {
                if (hash) return "HASH_INSERT";
                JsonElement from = mutation.arguments.get(0);
                List<JsonElement> source = associativeViewKeys(from, host);
                String why = source == null ? "CHAIN"
                        : unordered(from, host, source);
                if (!why.isEmpty()) return "PUT_ALL:" + why;
            } else if ("PUT".equals(mutation.operation)
                    || "PUT_IF".equals(mutation.operation)) {
                if (!member && hash
                        && (key == null || !present.contains(key))) {
                    return "HASH_INSERT";
                }
                if (key != null) present.add(key);
            } else if ("PIN".equals(mutation.operation)) {
                continue;
            } else if (key == null) {
                present.clear();
            } else {
                present.remove(key);
            }
        }
        return "";
    }

    /**
     * Whether every key a view puts is one key: one text.  Compared, never
     * spelled: a key is a recorded expression, whose text spells each shared
     * subterm once per path through it (hdfs-11741 i1: spelling every key
     * of every view lowered was 45 s of a 4-minute composition).
     */
    private static boolean oneKey(List<JsonElement> put) {
        Map<JsonElement, Set<JsonElement>> same =
                new IdentityHashMap<JsonElement, Set<JsonElement>>();
        for (JsonElement key : put) {
            if (!sameText(put.get(0), key, same)) return false;
        }
        return true;
    }

    /**
     * Whether two JSON values print one text ({@code String.valueOf}), each
     * pair of nodes compared once ({@code same}: the pairs found equal).
     */
    static boolean sameText(JsonElement left, JsonElement right,
                            Map<JsonElement, Set<JsonElement>> same) {
        JsonElement x = left == null ? JsonNull.INSTANCE : left;
        JsonElement y = right == null ? JsonNull.INSTANCE : right;
        if (x == y) return true;
        if (x.isJsonNull() || y.isJsonNull()) {
            return x.isJsonNull() && y.isJsonNull();
        }
        if (x.isJsonPrimitive() || y.isJsonPrimitive()) {
            if (!x.isJsonPrimitive() || !y.isJsonPrimitive()) return false;
            JsonPrimitive one = x.getAsJsonPrimitive();
            JsonPrimitive other = y.getAsJsonPrimitive();
            return one.isString() == other.isString()
                    && one.isBoolean() == other.isBoolean()
                    && one.getAsString().equals(other.getAsString());
        }
        Set<JsonElement> known = same.get(x);
        if (known != null && known.contains(y)) return true;
        boolean equal;
        if (x.isJsonArray() && y.isJsonArray()) {
            JsonArray one = x.getAsJsonArray();
            JsonArray other = y.getAsJsonArray();
            equal = one.size() == other.size();
            for (int at = 0; equal && at < one.size(); at++) {
                equal = sameText(one.get(at), other.get(at), same);
            }
        } else if (x.isJsonObject() && y.isJsonObject()) {
            JsonObject one = x.getAsJsonObject();
            JsonObject other = y.getAsJsonObject();
            equal = one.size() == other.size();
            Iterator<Map.Entry<String, JsonElement>> those =
                    other.entrySet().iterator();
            for (Map.Entry<String, JsonElement> member : one.entrySet()) {
                if (!equal) break;
                Map.Entry<String, JsonElement> that = those.next();
                equal = member.getKey().equals(that.getKey())
                        && sameText(member.getValue(), that.getValue(), same);
            }
        } else {
            equal = false;
        }
        if (equal) {
            same.computeIfAbsent(x, key -> Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>())).add(y);
        }
        return equal;
    }

    /**
     * The map a state is a version of, as the recording names it: the
     * symbol of its root with its Java class, else the location its state
     * was read from.
     */
    private static String mapNamed(JsonElement state, Host host) {
        JsonObject base = snapshotBase(state, host);
        JsonElement root = base == null ? null : base.get("receiver");
        if (root != null && root.isJsonObject() && "STATE".equals(
                optionalString(root.getAsJsonObject(), "operation"))) {
            root = root.getAsJsonObject().get("receiver");
        }
        // A consumer boundary wraps the read that named the map.
        while (root != null && root.isJsonObject()
                && root.getAsJsonObject().has("expression")
                && !root.getAsJsonObject().has("location")) {
            root = root.getAsJsonObject().get("expression");
        }
        if (root == null || !root.isJsonObject()) return "unnamed";
        JsonObject named = root.getAsJsonObject();
        String symbol = optionalString(named, "_exp");
        if (!symbol.isEmpty()) {
            return symbol + " (" + optionalString(named, "_java_type") + ")";
        }
        JsonElement read = named.get("location");
        if (read == null || !read.isJsonObject()) return "unnamed";
        JsonObject location = read.getAsJsonObject();
        return optionalString(location, "locationKind") + "/"
                + JsonFields.optionalLongInteger(location, "ownerSymRid", -1L)
                + "#" + JsonFields.optionalLongInteger(location, "slot", 0L);
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
            if ("PUT".equals(mutation.operation)
                    || "PUT_IF".equals(mutation.operation)) {
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
        int arity = emptiesState(operation) || "PIN".equals(operation) ? 0
                : "REMOVE".equals(operation) ? 1
                : "REMOVE_IF".equals(operation) ? 1
                : "PUT_ALL".equals(operation) ? 1
                : "PUT".equals(operation) || "PUT_IF".equals(operation)
                ? 2 : -1;
        if (arity < 0 || arguments.size() != arity) return null;
        // A guarded node without its guard is malformed: refused, never
        // dropped.
        if (GUARDED.contains(operation)) {
            JsonElement guard = relation.get("guard");
            if (guard == null || guard.isJsonNull()) return null;
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

        /**
         * THE PIN of a query its chain cannot decide: the answer its call
         * stated it returned, or null where the host lets the relation
         * stand (something it rests on can move).
         */
        Term answered(JsonObject query);

        /**
         * What a callback the run never ran would have stored: a free cell,
         * one name per {@code UNKNOWN} node.
         */
        Term unknown(JsonObject cell);

        /** What {@link #statedBase} found of one chain node, or null. */
        Boolean statedBase(JsonElement node);

        /** Remembers it. */
        void statedBase(JsonElement node, Boolean stated);

        void require(String predicate);

        /** Names, refusing nothing, what the lowering states only in part:
         *  a DIAGNOSTIC gap {@code subject} (the encoder adds its session),
         *  with why. */
        void diagnostic(String subject, String detail);

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
