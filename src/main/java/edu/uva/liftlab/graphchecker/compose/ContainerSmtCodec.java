package edu.uva.liftlab.graphchecker.compose;

import edu.uva.liftlab.graphchecker.contract.Digests;
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

public final class ContainerSmtCodec {
    private static final String EXPRESSION_TYPE = "ContainerRelation";
    private static final Set<String> GUARDED = Collections.unmodifiableSet(
            new HashSet<String>(java.util.Arrays.asList("REMOVE_IF",
                    "PUT_IF", "APPEND_IF", "PIN")));

    public static boolean conditionalMutation(String operation) {
        return GUARDED.contains(operation) && !"PIN".equals(operation);
    }
    private ContainerSmtCodec() {
    }

    private static JsonObject observedVersion(JsonObject read) {
        if (!VmRows.joinable(read)) return null;
        JsonObject observed = JsonFields.object(read,
                VmRows.OBSERVED_VERSION);
        return observed.size() == 0 ? null : observed;
    }

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

    private static final String UNSTATED_FIELD_PROJECTION =
            "UNSTATED_FIELD_PROJECTION:";

    public static Term field(JsonObject expression, Host host) {
        String ownerClass = optionalString(expression, "ownerClass");
        String javaType = optionalString(expression, "_java_type");
        Sort boxed = boxedPayloadSort(ownerClass, javaType);
        if (boxed != null) {
            Term owner = host.operand(expression.get("owner"), Sort.REF);
            if (owner == null) return null;
            if (owner.sort == boxed) return owner;
        }
        JsonElement concreteOwner = expression.get("concreteOwner");
        JsonElement concreteValue = expression.get("concreteValue");
        if (stated(concreteOwner) && stated(concreteValue)) {
            Term cell = host.operand(concreteValue, null);
            return cell == null ? null : host.projection(expression, cell);
        }
        host.unsupported(UNSTATED_FIELD_PROJECTION + ownerClass + "@"
                + JsonFields.optionalInteger(expression, "fieldOffset", -1)
                + ":" + javaType);
        return null;
    }

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

    private static boolean stated(JsonElement member) {
        return member != null && !member.isJsonNull();
    }

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
            if (!EXPRESSION_TYPE.equals(optionalString(node, "_type"))) {
                return false;
            }
            cursor = node.get("receiver");
        }
        return false;
    }

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
                    return rewrapped(wrappers, arguments.get(1),
                            selectedJavaType);
                }
                below = node.get("receiver");
            }
            if (below == cursor) return null;
            cursor = below;
        }
        return null;
    }

    private static boolean wrapper(JsonObject node) {
        return VmExpressionIr.consumerBoundary(node)
                || VmRows.GUARDED_READ_TYPE.equals(
                optionalString(node, "_type"));
    }

    private static JsonElement wrapped(JsonObject wrapper) {
        if (VmExpressionIr.consumerBoundary(wrapper)) {
            return wrapper.get(VmExpressionIr.EXPRESSION);
        }
        JsonObject observed = observedVersion(wrapper);
        return observed == null ? null
                : observed.get(VmExpressionIr.EXPRESSION);
    }

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

    public static Term term(JsonObject expression, Host host) {
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

    public static final String ANSWER = "answer";

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

    private static final class Call {
        final JsonObject expression;
        final Host host;
        final String shape;
        final String operation;
        final String javaType;
        final JsonArray arguments;
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

    private interface Lowering {
        Term lower(Call call);
    }

    private interface OnState {
        Term lower(Call call, Term receiver);
    }

    private static Lowering onState(OnState lowering) {
        return call -> {
            Term receiver = call.receiver();
            return receiver == null ? null : lowering.lower(call, receiver);
        };
    }

    private static final int ANY_ARITY = -1;
    private static final String ANY_SHAPE = "*";

    private static final class Rule {
        final int arity;
        final Lowering lowering;

        Rule(int arity, Lowering lowering) {
            this.arity = arity;
            this.lowering = lowering;
        }
    }

    private static final Map<String, Rule> RULES =
            new HashMap<String, Rule>();

    private static void rule(String shape, String operation, int arity,
                             Lowering lowering) {
        RULES.put(shape + " " + operation, new Rule(arity, lowering));
    }

    static {
        rule(ANY_SHAPE, "UNKNOWN", ANY_ARITY,
                call -> call.host.unknown(call.expression));
        rule(ANY_SHAPE, "STATE", ANY_ARITY, ContainerSmtCodec::stateRoot);
        rule(ANY_SHAPE, "KEY", ANY_ARITY, ContainerSmtCodec::entryPart);
        rule(ANY_SHAPE, "VALUE", ANY_ARITY, ContainerSmtCodec::entryPart);
        rule(ANY_SHAPE, "HAS_NEXT", ANY_ARITY, ContainerSmtCodec::hasNext);
        rule(ANY_SHAPE, "CLEAR", ANY_ARITY, ContainerSmtCodec::emptied);
        rule(ANY_SHAPE, "SNAPSHOT_BASE", ANY_ARITY,
                ContainerSmtCodec::emptied);

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
        rule("INDEXED", "PEEK", 0, onState((call, receiver) -> {
            long size = receiver.indexedSize;
            String head = "(indexed_read " + receiver.text + " 0)";
            return call.unboxed(new Term(size == 0L ? NULL_CELL
                    : size > 0L ? head
                    : "(ite (= (indexed_size " + receiver.text + ") 0) "
                    + NULL_CELL + " " + head + ")", Sort.VALUE));
        }));
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
        rule("ASSOCIATIVE", "REMOVE_AT", 1, onState((call, receiver) -> {
            Term index = integer(call.argument(0), call.host);
            if (index == null) return null;
            ViewOrder order = requireAssociativeViewBijection(
                    associativeStateExpression(call.receiverIr()), receiver,
                    call.host, call.views);
            if (order == null) return null;
            requireAssociativeMember(receiver, index, order, call.host);
            return new Term("(let ((s " + receiver.text
                    + ")) (assoc_remove s " + order.keyAt(receiver, "s",
                    index.text) + "))", Sort.ASSOCIATIVE);
        }));
        rule("ASSOCIATIVE", "REMOVE", 1, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            return key == null ? null
                    : new Term("(assoc_remove " + receiver.text + " "
                    + key.text + ")", Sort.ASSOCIATIVE);
        }));
        rule("ASSOCIATIVE", "PUT_ALL", 1, onState((call, receiver) ->
                putAll(receiver, call.argument(0), call.host)));
        rule("ASSOCIATIVE", "REMOVE_IF", 1, onState((call, receiver) -> {
            Term key = call.host.box(call.argument(0));
            Term guard = call.host.operand(call.expression.get("guard"),
                    Sort.BOOL);
            return key == null || guard == null ? null
                    : new Term("(assoc_remove_if " + receiver.text + " "
                    + key.text + " " + guard.text + ")",
                    Sort.ASSOCIATIVE);
        }));
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

    private static Term lookup(Call call) {
        return associativeLookup(associativeStateExpression(
                call.receiverIr()), call.operation, call.arguments,
                call.javaType, call.host);
    }

    private static Term pinned(Term receiver, JsonObject expression,
                               Host host) {
        Term guard = host.operand(expression.get("guard"), Sort.BOOL);
        if (guard == null) return null;
        host.require(guard.text);
        return receiver;
    }

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

    private static Term matched(Term cell, Term expected) {
        return new Term("(= " + cell.text + " " + expected.text + ")",
                Sort.BOOL);
    }

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

    private static Term integer(JsonElement expression, Host host) {
        Term value = host.operand(expression, Sort.INT);
        if (value == null || value.sort == Sort.INT) return value;
        host.unsupported("ContainerRelation:int-operand-sort=" + value.sort);
        return null;
    }

    private static Term unmodeled(String shape, String operation,
                                  JsonArray arguments, Host host) {
        host.unsupported("ContainerRelation:" + shape + ":"
                + operation + ":arity=" + arguments.size());
        return null;
    }

    private static Term associativeEntryValue(
            Entry entry, String viewKind, String javaType, Host host,
            Map<JsonElement, ViewOrder> views) {
        Term state = associativeState(entry.stateExpression, host);
        Term index = integer(entry.indexExpression, host);
        if (state == null || index == null) return null;
        ViewOrder order = requireAssociativeViewBijection(
                entry.stateExpression, state, host, views);
        if (order == null) return null;
        requireAssociativeMember(state, index, order, host);
        String key = order.keyAt(state, state.text, index.text);
        return new Term("KEY_VIEW".equals(viewKind) ? key
                : "(assoc_read " + state.text + " " + key + ")",
                Sort.VALUE);
    }

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

    private static void requireIndexedMember(
            Term state, Term index, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (indexed_size s))))");
    }

    private static void requireAssociativeMember(
            Term state, Term index, ViewOrder order, Host host) {
        host.require("(let ((s " + state.text + ") (i " + index.text
                + ")) (and (<= 0 i) (< i (assoc_size s))"
                + " (assoc_has s " + order.keyAt(state, "s", "i") + ")))");
    }

    public static final String ASSOC_VIEW_SIZE_UNSTATED =
            "UNSTATED_VALUE:AssociativeViewSize";

    enum ViewOrder {
        STATED("assoc_key_at", "assoc_position_of"),
        FREE("assoc_view_key", "assoc_view_position");

        private final String keyAt;
        private final String positionOf;

        ViewOrder(String keyAt, String positionOf) {
            this.keyAt = keyAt;
            this.positionOf = positionOf;
        }

        String keyAt(Term state, String as, String index) {
            return "(" + keyAt + " " + argument(state, as) + " " + index
                    + ")";
        }

        Term position(Term state, Term key, Host host) {
            return shared(new Term("(" + positionOf + " "
                    + argument(state, state.text) + " " + key.text + ")",
                    Sort.INT), host);
        }

        private String argument(Term state, String as) {
            return this == FREE
                    ? tag(state) + " (assoc_size " + as + ")" : as;
        }
    }

    static String tag(Term state) {
        return Long.toString(Long.parseLong(
                Digests.digest(state.text, 15), 16));
    }

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
            Term key = shared(new Term(order.keyAt(state, state.text,
                    String.valueOf(position)), Sort.VALUE), host);
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
                    + " " + size.text + ") (= " + order.keyAt(state,
                    state.text, where.text) + " " + key.text + ")))");
        }
        views.put(stateIr, order);
        return order;
    }

    public static final String ASSOC_VIEW_UNORDERED = "ASSOC_VIEW_UNORDERED";

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

    private static boolean oneKey(List<JsonElement> put) {
        Map<JsonElement, Set<JsonElement>> same =
                new IdentityHashMap<JsonElement, Set<JsonElement>>();
        for (JsonElement key : put) {
            if (!sameText(put.get(0), key, same)) return false;
        }
        return true;
    }

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

    private static String mapNamed(JsonElement state, Host host) {
        JsonObject base = snapshotBase(state, host);
        JsonElement root = base == null ? null : base.get("receiver");
        if (root != null && root.isJsonObject() && "STATE".equals(
                optionalString(root.getAsJsonObject(), "operation"))) {
            root = root.getAsJsonObject().get("receiver");
        }
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

    private static final int VIEW_CHAIN_LIMIT = 512;

    private static String associativeStateSubject(JsonElement state) {
        if (state == null || !state.isJsonObject()) return "no-state";
        JsonObject object = state.getAsJsonObject();
        String operation = optionalString(object, "operation");
        return operation.isEmpty() ? optionalString(object, "_type")
                : operation;
    }

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

    private static Term shift(Term receiver, Term index, Term value,
                              Host host) {
        long size = receiver.indexedSize;
        boolean insert = value != null;
        if (size < 0L) {
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

    private static long grown(Term receiver, long by) {
        return receiver == null || receiver.indexedSize < 0L ? -1L
                : receiver.indexedSize + by;
    }

    private static Term shared(Term value, Host host) {
        return value == null ? null : host.share(value);
    }

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


    public interface Host {
        Term state(JsonElement identity, Sort shape);

        Term operand(JsonElement expression, Sort expected);

        Term share(Term value);

        Term box(JsonElement expression);

        Term unbox(Term value, String javaType);

        Term projection(JsonObject fieldAccess, Term cell);

        Term query(JsonObject relation, Term answer);

        JsonElement chain(JsonElement state);

        Term answered(JsonObject query);

        Term unknown(JsonObject cell);

        Boolean statedBase(JsonElement node);

        void statedBase(JsonElement node, Boolean stated);

        void require(String predicate);

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
        public final long indexedSize;
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
