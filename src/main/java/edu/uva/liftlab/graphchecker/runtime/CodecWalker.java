package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.Hole;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations.Shape;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations.View;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations.ViewForm;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Predicate;

/**
 * One codec's reading of a message graph (WIRE-CODEC §4.2): at an encode,
 * the leaves of demanded ports, each with its key path and the slot that
 * holds it; at a decode, the slot at one key path.  Pure Java, run with
 * observation paused; a view's accessor is the one piece of application code
 * it calls.
 *
 * <p>A key path's components are a map key ({@code key.toString()}, as JSON
 * writes it), a list or array index, a NamedList name ({@code name#k} for its
 * k-th repeat) or a generated message's field name.  A leaf's port is the key
 * above it: in a TREE codec's space the last key on its path, in {@code pb}
 * {@code <Message>.<field>}, in a LEAF codec's space the codec's name.</p>
 *
 * <p>Nothing is walked field by field but a generated message: an
 * application object a TREE walk meets with no view is named ({@link
 * Walk#viewMissing}), never guessed.  Every bound is named with the first
 * path it left unvisited.</p>
 */
final class CodecWalker {
    /** Nodes one walk visits. */
    static final int MAX_NODES = 4096;
    /** Components on one path. */
    static final int MAX_DEPTH = 32;
    /** Leaves one message exports. */
    static final int MAX_LEAVES = 256;

    /** How a leaf's holder holds it. */
    enum Holding {
        /** An instance field of a generated message. */
        FIELD,
        /** An array element. */
        ELEMENT,
        /** A map entry, by its key object. */
        ENTRY,
        /** A position of an ordered collection. */
        POSITION,
        /** The graph itself. */
        ROOT,
        /** What a view's accessor rendered: no slot to write. */
        VIEW
    }

    private final String codec;
    private final Shape shape;
    private final String space;
    private final List<View> views;
    private final Predicate<String> demanded;
    /** Per generated message class: whether a demanded port is reachable
     *  from it.  Walks run on every thread. */
    private final Map<Class<?>, Boolean> reaches = new ConcurrentHashMap<>();

    CodecWalker(WireDeclarations.Codec codec, List<View> views,
                Predicate<String> demanded) {
        this.codec = codec.name();
        this.shape = codec.shape();
        this.space = codec.space();
        List<View> own = new ArrayList<>();
        for (View view : views) {
            if (view.codec().equals(codec.name())
                    || WireDeclarations.EVERY_CODEC.equals(view.codec())) {
                own.add(view);
            }
        }
        this.views = own;
        this.demanded = demanded;
    }

    String codec() {
        return codec;
    }

    /** The port a key of this codec's space names. */
    String port(String key) {
        return CommunicationCatalogContract.codecPortId(space, key);
    }

    // ---- the encoding side --------------------------------------------------

    /** Every leaf of a demanded port in {@code graph}, in walk order. */
    Walk leaves(Object graph) {
        Walk walk = new Walk();
        if (graph == null) return walk;
        if (shape == Shape.LEAF) {
            if (leafValue(graph) && demanded.test(port(codec))) {
                walk.leaves.add(new Leaf(Collections.emptyList(), codec,
                        graph, null, Holding.ROOT, null));
            }
            return walk;
        }
        if (shape == Shape.PROTOBUF && !reaches(graph.getClass())) {
            return walk;
        }
        visit(walk, graph, new ArrayList<Object>(), "",
                new IdentityHashMap<Object, Boolean>());
        return walk;
    }

    /**
     * Visits one container or message at {@code path}; {@code key} is the
     * key above it, which an index below it keeps.
     */
    private void visit(Walk walk, Object node, List<Object> path, String key,
                       Map<Object, Boolean> onPath) {
        if (++walk.nodes > MAX_NODES || path.size() > MAX_DEPTH) {
            walk.bound = (walk.nodes > MAX_NODES ? "the walk visited "
                    + MAX_NODES + " nodes" : "the path is " + MAX_DEPTH
                    + " components deep") + "; first unvisited: "
                    + text(path);
            return;
        }
        // A graph that reaches itself is walked once along each path.
        if (onPath.put(node, Boolean.TRUE) != null) return;
        try {
            for (Child child : children(walk, node)) {
                List<Object> at = new ArrayList<>(path);
                at.add(child.component);
                String childKey = child.key == null ? key : child.key;
                Object value = child.value;
                Holding holding = child.holding;
                View rendered = value == null || leafValue(value) ? null
                        : view(value.getClass());
                if (rendered != null && rendered.form() == ViewForm.LEAF) {
                    // One leaf: what its accessor renders, no slot of its own.
                    value = access(value, rendered.accessor());
                    holding = holding == null ? null : Holding.VIEW;
                }
                boolean port = !childKey.isEmpty()
                        && demanded.test(port(childKey));
                if (value == null) {
                    if (port) walk.nullLeaves.add(text(at));
                    continue;
                }
                if (!leafValue(value)) {
                    visit(walk, value, at, childKey, onPath);
                    if (!walk.bound.isEmpty()) return;
                    continue;
                }
                if (!port) continue;
                if (holding == null) {
                    walk.unaddressable.add(text(at));
                    continue;
                }
                if (walk.leaves.size() >= MAX_LEAVES) {
                    walk.bound = "the message holds " + MAX_LEAVES
                            + " leaves; first unvisited: " + text(at);
                    return;
                }
                walk.leaves.add(new Leaf(at, childKey, value, child.holder,
                        holding, holding == Holding.VIEW ? null
                        : child.slot));
            }
        } finally {
            onPath.remove(node);
        }
    }

    // ---- the decoding side --------------------------------------------------

    /**
     * The leaf at {@code path} in a decoded graph, or null when the path is
     * absent (the entry's view does not see this graph).  A present path
     * holding null is a leaf whose value is null.
     */
    Leaf resolve(Object graph, List<Object> path) {
        if (graph == null) return null;
        if (path.isEmpty()) {
            return new Leaf(path, shape == Shape.LEAF ? codec : "", graph,
                    null, Holding.ROOT, null);
        }
        Object node = graph;
        Walk scratch = new Walk();
        String key = "";
        for (int index = 0; index < path.size(); index++) {
            Child found = null;
            for (Child child : children(scratch, node)) {
                if (child.component.equals(path.get(index))) {
                    found = child;
                    break;
                }
            }
            if (found == null) return null;
            key = found.key == null ? key : found.key;
            if (index == path.size() - 1) {
                return found.holding == null ? null : new Leaf(path, key,
                        found.value, found.holder, found.holding, found.slot);
            }
            if (found.value == null || leafValue(found.value)) return null;
            node = found.value;
        }
        return null;
    }

    // ---- children -----------------------------------------------------------

    /** One child of a node: how its parent holds it and the key it adds. */
    private static final class Child {
        final Object component;
        /** The key this child adds (a map key, a name, Message.field), or
         *  null for an index, which keeps the key above it. */
        final String key;
        final Object value;
        final Object holder;
        /** Null: the child has no slot (an element of a Set). */
        final Holding holding;
        final Object slot;

        Child(Object component, String key, Object value, Object holder,
              Holding holding, Object slot) {
            this.component = component;
            this.key = key;
            this.value = value;
            this.holder = holder;
            this.holding = holding;
            this.slot = slot;
        }
    }

    private List<Child> children(Walk walk, Object node) {
        if (shape == Shape.PROTOBUF && generatedMessage(node.getClass())) {
            return messageFields(walk, node);
        }
        View view = view(node.getClass());
        if (view != null) return viewed(walk, node, view);
        return containerChildren(walk, node);
    }

    private List<Child> containerChildren(Walk walk, Object node) {
        List<Child> children = new ArrayList<>();
        if (node instanceof Map) {
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) node).entrySet()) {
                String key = String.valueOf(entry.getKey());
                children.add(new Child(key, key, entry.getValue(), node,
                        Holding.ENTRY, entry.getKey()));
            }
            return children;
        }
        if (node.getClass().isArray()) {
            int length = Array.getLength(node);
            for (int index = 0; index < length; index++) {
                children.add(new Child(index, null, Array.get(node, index),
                        node, Holding.ELEMENT, index));
            }
            return children;
        }
        if (node instanceof Collection) {
            // A List or a Deque is ordered; a Set is not addressed.
            boolean ordered = node instanceof List || node instanceof Deque;
            int index = 0;
            for (Object element : (Collection<?>) node) {
                children.add(new Child(index, null, element, node,
                        ordered ? Holding.POSITION : null, index));
                index++;
            }
            return children;
        }
        walk.viewMissing.add(node.getClass().getName());
        return children;
    }

    /** The node as its view sees it: its own map (and extra keys), or its
     *  flat name/value list. */
    private List<Child> viewed(Walk walk, Object node, View view) {
        List<Child> children = new ArrayList<>();
        if (view.form() == ViewForm.LEAF) {
            // A leaf, which its parent's walk renders.
            return children;
        }
        Object seen = access(node, view.accessor());
        if (view.form() == ViewForm.PAIRS) {
            if (!(seen instanceof List)) return children;
            List<?> pairs = (List<?>) seen;
            Map<String, Integer> repeats = new HashMap<>();
            for (int index = 0; index + 1 < pairs.size(); index += 2) {
                String name = String.valueOf(pairs.get(index));
                int repeat = repeats.merge(name, 1, Integer::sum) - 1;
                children.add(new Child(repeat == 0 ? name
                        : name + "#" + repeat, name, pairs.get(index + 1),
                        pairs, Holding.POSITION, index + 1));
            }
            return children;
        }
        if (seen != null) children.addAll(containerChildren(walk, seen));
        for (Map.Entry<String, String> extra : view.put().entrySet()) {
            children.add(new Child(extra.getKey(), extra.getKey(),
                    access(node, extra.getValue()), node, Holding.VIEW,
                    null));
        }
        return children;
    }

    /** The most specific view of this codec for {@code type}, or null. */
    private View view(Class<?> type) {
        for (Class<?> at = type; at != null; at = at.getSuperclass()) {
            for (View view : views) {
                if (view.type().equals(at.getName())) return view;
            }
        }
        return null;
    }

    /** What a view's accessor answers: a no-argument method or a field. */
    private static Object access(Object node, String accessor) {
        boolean method = accessor.endsWith("()");
        String name = method ? accessor.substring(0, accessor.length() - 2)
                : accessor;
        for (Class<?> at = node.getClass(); at != null;
             at = at.getSuperclass()) {
            try {
                if (method) {
                    Method getter = at.getDeclaredMethod(name);
                    getter.setAccessible(true);
                    return getter.invoke(node);
                }
                Field field = at.getDeclaredField(name);
                field.setAccessible(true);
                return field.get(node);
            } catch (NoSuchMethodException | NoSuchFieldException absent) {
                // Declared higher up.
            } catch (ReflectiveOperationException | RuntimeException failed) {
                return null;
            }
        }
        return null;
    }

    /**
     * A generated message's fields: its instance fields named {@code *_},
     * but its bookkeeping ({@code bitField*_}, {@code memoized*},
     * {@code unknownFields}).  A String field a parse left as bytes is
     * materialized by its getter once (protobuf-java caches valid UTF-8); a
     * field no single leaf holds (bytes, a repeated primitive) is named when
     * its port is demanded.
     */
    private List<Child> messageFields(Walk walk, Object message) {
        List<Child> children = new ArrayList<>();
        for (Field field : messageFields(message.getClass())) {
            String name = field.getName().substring(0,
                    field.getName().length() - 1);
            String key = message.getClass().getSimpleName() + "." + name;
            boolean port = demanded.test(port(key));
            Object value = read(field, message);
            if (port && value != null && !field.getType().isPrimitive()
                    && !leafValue(value) && !(value instanceof List)
                    && !generatedMessage(value.getClass())) {
                materialize(message, name);
                value = read(field, message);
            }
            boolean repeatedPrimitive = value instanceof List
                    && !((List<?>) value).isEmpty()
                    && leafValue(((List<?>) value).get(0))
                    && !(((List<?>) value).get(0) instanceof String);
            if (value == null || field.getType().isPrimitive()
                    || leafValue(value)
                    || generatedMessage(value.getClass())) {
                children.add(new Child(name, key, value, message,
                        Holding.FIELD, field));
            } else if (value instanceof List && !repeatedPrimitive) {
                children.add(new Child(name, key, value, message,
                        Holding.VIEW, null));
            } else if (port) {
                walk.unsupported.add(key + " holds a "
                        + value.getClass().getName());
            }
        }
        return children;
    }

    private static Object read(Field field, Object owner) {
        try {
            return field.get(owner);
        } catch (IllegalAccessException | RuntimeException unreadable) {
            return null;
        }
    }

    /** Calls a message's getter of {@code name} once. */
    private static void materialize(Object message, String name) {
        try {
            Method getter = message.getClass().getMethod("get"
                    + Character.toUpperCase(name.charAt(0))
                    + name.substring(1));
            getter.invoke(message);
        } catch (ReflectiveOperationException | RuntimeException absent) {
            // The field stays what it was; the walk names it.
        }
    }

    private static final Map<Class<?>, List<Field>> FIELDS =
            Collections.synchronizedMap(new HashMap<Class<?>, List<Field>>());

    private static List<Field> messageFields(Class<?> type) {
        List<Field> known = FIELDS.get(type);
        if (known != null) return known;
        List<Field> fields = new ArrayList<>();
        for (Field field : type.getDeclaredFields()) {
            String name = field.getName();
            if (Modifier.isStatic(field.getModifiers())
                    || !name.endsWith("_") || name.length() < 2
                    || name.startsWith("bitField")
                    || name.startsWith("memoized")
                    || name.equals("unknownFields")) {
                continue;
            }
            try {
                field.setAccessible(true);
            } catch (RuntimeException sealed) {
                continue;
            }
            fields.add(field);
        }
        FIELDS.put(type, fields);
        return fields;
    }

    /**
     * Whether a demanded port is reachable from a generated message class,
     * through its message-typed fields and its lists' element types; a
     * payload that reaches none is skipped whole.
     */
    private boolean reaches(Class<?> type) {
        if (!generatedMessage(type)) return false;
        Boolean known = reaches.get(type);
        if (known != null) return known;
        // The whole closure first, so nothing half-known is ever cached: a
        // walk on another thread must never read a class as reaching none
        // while this one is still looking.
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> open = new ArrayDeque<>();
        open.add(type);
        boolean found = false;
        while (!open.isEmpty() && !found) {
            Class<?> at = open.poll();
            if (!seen.add(at)) continue;
            for (Field field : messageFields(at)) {
                String name = field.getName().substring(0,
                        field.getName().length() - 1);
                if (demanded.test(port(at.getSimpleName() + "." + name))) {
                    found = true;
                    break;
                }
                Class<?> nested = List.class.isAssignableFrom(field.getType())
                        ? elementType(field) : field.getType();
                if (nested != null && generatedMessage(nested)) {
                    open.add(nested);
                }
            }
        }
        reaches.put(type, found);
        return found;
    }

    private static Class<?> elementType(Field field) {
        Type generic = field.getGenericType();
        if (!(generic instanceof ParameterizedType)) return null;
        Type[] arguments = ((ParameterizedType) generic)
                .getActualTypeArguments();
        return arguments.length == 1 && arguments[0] instanceof Class
                ? (Class<?>) arguments[0] : null;
    }

    /** A protobuf-java generated message: a subclass of its runtime's
     *  {@code GeneratedMessage*}, whatever package shades it. */
    static boolean generatedMessage(Class<?> type) {
        for (Class<?> at = type.getSuperclass(); at != null;
             at = at.getSuperclass()) {
            if (at.getSimpleName().startsWith("GeneratedMessage")) return true;
        }
        return false;
    }

    /** A String, a box or an enum constant: one leaf. */
    static boolean leafValue(Object value) {
        return value instanceof String || value instanceof Number
                || value instanceof Boolean || value instanceof Character
                || value instanceof Enum;
    }

    /** A path's text form ({@link Hole#path}). */
    static String text(List<Object> path) {
        return Hole.of("W", path, 0).path();
    }

    // ---- results ------------------------------------------------------------

    /** One leaf and the slot holding it. */
    static final class Leaf {
        final List<Object> path;
        /** The port's key within the codec's space. */
        final String key;
        final Object value;
        /** The map, list, array or message holding it; null at the root. */
        final Object holder;
        final Holding holding;
        /** The Field, index or key object; null at the root or a view. */
        final Object slot;

        Leaf(List<Object> path, String key, Object value, Object holder,
             Holding holding, Object slot) {
            this.path = Collections.unmodifiableList(new ArrayList<>(path));
            this.key = key;
            this.value = value;
            this.holder = holder;
            this.holding = holding;
            this.slot = slot;
        }

        /**
         * Stores {@code fresh} where this leaf is, through its holder's own
         * API.  False where there is no slot to write (a view's rendering,
         * the root, a Deque's position) or the holder refuses (an immutable
         * one).
         */
        @SuppressWarnings({"unchecked", "rawtypes"})
        boolean store(Object fresh) {
            try {
                switch (holding) {
                    case FIELD:
                        ((Field) slot).set(holder, fresh);
                        return true;
                    case ELEMENT:
                        Array.set(holder, (Integer) slot, fresh);
                        return true;
                    case ENTRY:
                        ((Map) holder).put(slot, fresh);
                        return true;
                    case POSITION:
                        if (!(holder instanceof List)) return false;
                        ((List) holder).set((Integer) slot, fresh);
                        return true;
                    default:
                        return false;
                }
            } catch (RuntimeException | IllegalAccessException refused) {
                return false;
            }
        }
    }

    /** What one walk found, and what it could not address. */
    static final class Walk {
        final List<Leaf> leaves = new ArrayList<>();
        /** Classes a TREE walk met with no view. */
        final Set<String> viewMissing = new LinkedHashSet<>();
        /** Paths of demanded leaves in a Set. */
        final List<String> unaddressable = new ArrayList<>();
        /** Demanded message fields no single leaf holds. */
        final List<String> unsupported = new ArrayList<>();
        /** Paths of demanded keys holding null. */
        final List<String> nullLeaves = new ArrayList<>();
        /** The bound hit, with the first unvisited path; "" for none. */
        String bound = "";
        int nodes;
    }
}
