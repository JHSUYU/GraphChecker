package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.pauseObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resumeObservation;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;

import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A door's walk of the protobuf message it carries (SYMBOL-SCOPE §6.3).
 *
 * <p>A message field's port (a derived port: {@code StaticScopeMap}'s
 * {@code EXPORT_SITE} row states the field as its cell) crosses with its
 * message, not at the builder's setter.  The outbound door walks the message
 * ({@link #send}): each port field is exported from the message itself, or,
 * in a message this JVM decoded, its decoded element is staged again under
 * its ORIGINAL producer -- a relay hands on what it received (hdfs-adhoc-07:
 * the QJM client hands jn1's prepareRecovery segment to jn0's
 * acceptRecovery).  After the parse the receiving side walks the message it
 * decoded ({@link #receive}) and binds each element to the message object it
 * was decoded into, with the message it arrived in; a getter's attach takes
 * the element of the message it is called on ({@link #bound}), whatever its
 * thread serves by then.</p>
 *
 * <p>Both sides walk alike: depth first, each message's port fields, then
 * its message-valued fields -- a nested message, each element of a repeated
 * one, a {@code oneof}'s message -- every class's fields by name.  The k-th
 * port field the walk meets is the port's k-th element on the wire, staged
 * or not.  A class's default instance (JVM-wide) is never walked.</p>
 */
final class MessageCodec {
    private MessageCodec() {
    }

    /** Message class name -> its port fields; empty outside a concolic
     *  session, so a door walks nothing. */
    private static volatile Map<String, List<PortField>> ports =
            Collections.emptyMap();
    /** Per runtime class, what a walk visits in it. */
    private static final Map<Class<?>, Plan> PLANS =
            new ConcurrentHashMap<Class<?>, Plan>();
    private static final Bindings BINDINGS = new Bindings();

    /** One port a message field carries. */
    private static final class PortField {
        private final String portId;
        private final String field;
        private final String descriptor;

        private PortField(String portId, String field, String descriptor) {
            this.portId = portId;
            this.field = field;
            this.descriptor = descriptor;
        }
    }

    /**
     * Installs the session's port fields from its scope map's rows: every
     * {@code EXPORT_SITE} whose cell is a message field.
     */
    static void install(List<JsonObject> rows) {
        Map<String, Map<String, PortField>> found =
                new LinkedHashMap<String, Map<String, PortField>>();
        for (JsonObject row : rows) {
            if (!StaticScopeMap.SITE_KIND.equals(member(row, "kind"))
                    || !StaticScopeMap.EXPORT_SITE.equals(
                            member(row, "role"))) {
                continue;
            }
            FieldPathSpec.DeclaredField cell = FieldPathSpec.declaredField(
                    member(row, "cell"));
            String portId = member(row, "portId");
            if (cell == null || portId.isEmpty()) continue;
            found.computeIfAbsent(cell.owner(),
                    owner -> new LinkedHashMap<String, PortField>())
                    .putIfAbsent(cell.name(), new PortField(portId,
                            cell.name(), javaTypeDescriptor(cell.type())));
        }
        Map<String, List<PortField>> table =
                new HashMap<String, List<PortField>>();
        for (Map.Entry<String, Map<String, PortField>> message
                : found.entrySet()) {
            table.put(message.getKey(), Collections.unmodifiableList(
                    new ArrayList<PortField>(message.getValue().values())));
        }
        PLANS.clear();
        BINDINGS.clear();
        ports = Collections.unmodifiableMap(table);
    }

    /**
     * The outbound door's walk of {@code message}: every port field staged
     * on the message this thread sends next -- a decoded element under its
     * original producer, one the decode carried none for counted empty, any
     * other exported from the field itself.
     */
    static void send(Object message) {
        if (message == null || ports.isEmpty()) return;
        walk(message, (holder, owner, port) -> {
            Element decoded = BINDINGS.get(holder, port.portId);
            if (decoded == null) {
                WireExport.export(port.portId, new WireExport.Leaf(holder,
                        owner, port.field, port.descriptor));
            } else if (decoded.handle == SymbolicMessageEnvelope.ABSENT) {
                SymbolicMessageEnvelope.skip(port.portId);
            } else {
                WireExport.relay(port.portId, decoded);
            }
        });
    }

    /**
     * The walk of a message decoded on this thread, inside the exchange it
     * arrived in: each port field's element, taken from that message's
     * envelope, is bound to the message object it was decoded into.
     */
    static void receive(Object message) {
        if (message == null || ports.isEmpty()) return;
        walk(message, (holder, owner, port) -> BINDINGS.put(holder,
                port.portId, Element.received(SymbolicMessageEnvelope.take(
                        port.portId))));
    }

    /**
     * The element a message field's port has in {@code message}, the one
     * its getter was called on: the one its decode bound, else none
     * ({@link SymbolicMessageEnvelope#ABSENT}: a message this JVM built, or
     * a class's default instance, which no decode binds).
     */
    static Element bound(Object message, String portId) {
        Element element = message == null ? null
                : BINDINGS.get(message, portId);
        return element == null ? Element.NONE : element;
    }

    /** One decoded element: its handle, and the message it arrived in. */
    static final class Element {
        private static final Element NONE = new Element(
                SymbolicMessageEnvelope.ABSENT, "", "");
        final long handle;
        final String correlationId;
        final String half;

        private Element(long handle, String correlationId, String half) {
            this.handle = handle;
            this.correlationId = correlationId;
            this.half = half;
        }

        /** {@code handle}, taken from the message this thread received. */
        static Element received(long handle) {
            MessageDoors.Inbound inbound = MessageDoors.current();
            return new Element(handle,
                    inbound == null ? "" : Text.safe(inbound.correlationId),
                    inbound == null ? "" : Text.safe(inbound.half));
        }
    }

    // ------------------------------------------------------------------
    // The walk
    // ------------------------------------------------------------------

    private interface Visit {
        void port(Object holder, String owner, PortField port);
    }

    /** Walks {@code message} depth first, observation paused: the walk is
     *  the engine's, its reflective reads no event of the program's. */
    private static void walk(Object message, Visit visit) {
        pauseObservation();
        try {
            walk(message, visit,
                    Collections.newSetFromMap(
                            new IdentityHashMap<Object, Boolean>()));
        } finally {
            resumeObservation();
        }
    }

    private static void walk(Object message, Visit visit, Set<Object> seen) {
        Plan plan = plan(message.getClass());
        if (plan == null || plan.defaultInstance == message
                || !seen.add(message)) {
            return;
        }
        for (Map.Entry<Field, PortField> port : plan.ports.entrySet()) {
            visit.port(message, plan.owner, port.getValue());
        }
        for (Field child : plan.children) {
            Object value;
            try {
                value = child.get(message);
            } catch (IllegalAccessException unreadable) {
                continue;
            }
            if (value instanceof Collection) {
                for (Object element : (Collection<?>) value) {
                    if (element != null) walk(element, visit, seen);
                }
            } else if (value != null) {
                walk(value, visit, seen);
            }
        }
    }

    /** What a walk visits in one generated message class: its port fields,
     *  and the fields that may hold a message. */
    private static final class Plan {
        private final String owner;
        private final Object defaultInstance;
        private final Map<Field, PortField> ports;
        private final List<Field> children;

        private Plan(String owner, Object defaultInstance,
                     Map<Field, PortField> ports, List<Field> children) {
            this.owner = owner;
            this.defaultInstance = defaultInstance;
            this.ports = ports;
            this.children = children;
        }
    }

    /** No plan: a value that is no generated message. */
    private static final Plan NONE = new Plan("", null,
            Collections.<Field, PortField>emptyMap(),
            Collections.<Field>emptyList());

    private static Plan plan(Class<?> type) {
        Plan plan = PLANS.get(type);
        if (plan == null) {
            plan = EnginePlumbing.generatedMessage(type) ? planOf(type) : NONE;
            PLANS.put(type, plan);
        }
        return plan == NONE ? null : plan;
    }

    private static Plan planOf(Class<?> type) {
        Map<String, PortField> declared = new HashMap<String, PortField>();
        for (PortField port : ports.getOrDefault(type.getName(),
                Collections.<PortField>emptyList())) {
            declared.put(port.field, port);
        }
        List<Field> fields = new ArrayList<Field>();
        for (Field field : type.getDeclaredFields()) {
            if (!Modifier.isStatic(field.getModifiers())) fields.add(field);
        }
        fields.sort(Comparator.comparing(Field::getName));
        Map<Field, PortField> ports = new LinkedHashMap<Field, PortField>();
        List<Field> children = new ArrayList<Field>();
        for (Field field : fields) {
            PortField port = declared.get(field.getName());
            if (port == null && !mayHoldMessage(field)) continue;
            try {
                field.setAccessible(true);
            } catch (RuntimeException sealed) {
                continue;
            }
            if (port != null) ports.put(field, port);
            else children.add(field);
        }
        return new Plan(type.getName(), defaultInstance(type),
                Collections.unmodifiableMap(ports),
                Collections.unmodifiableList(children));
    }

    /**
     * Whether a field may hold a message: a message field, a repeated one
     * (a {@code List} of a message class, never a repeated scalar's boxes),
     * or a {@code oneof}'s {@code Object}.
     */
    private static boolean mayHoldMessage(Field field) {
        Class<?> held = field.getType();
        if (held == Object.class || EnginePlumbing.generatedMessage(held)) {
            return true;
        }
        if (!Collection.class.isAssignableFrom(held)
                || !(field.getGenericType() instanceof ParameterizedType)) {
            return false;
        }
        Type[] elements = ((ParameterizedType) field.getGenericType())
                .getActualTypeArguments();
        return elements.length == 1 && elements[0] instanceof Class
                && EnginePlumbing.generatedMessage((Class<?>) elements[0]);
    }

    /** The class's JVM-wide default instance ({@code getDefaultInstance}),
     *  or null. */
    private static Object defaultInstance(Class<?> type) {
        try {
            return type.getMethod("getDefaultInstance").invoke(null);
        } catch (ReflectiveOperationException | RuntimeException none) {
            return null;
        }
    }

    private static String member(JsonObject row, String name) {
        JsonElement value = row.get(name);
        return value == null || !value.isJsonPrimitive() ? ""
                : value.getAsString();
    }

    // ------------------------------------------------------------------
    // Bindings: by message identity, held weakly
    // ------------------------------------------------------------------

    /**
     * Each decoded message's elements, by port, keyed by the message's
     * identity and held only as long as the message lives: a message's
     * {@code equals} is its value, and two equal messages were two
     * decodes.
     */
    private static final class Bindings {
        private final ReferenceQueue<Object> dropped =
                new ReferenceQueue<Object>();
        private final Map<Identity, Map<String, Element>> held =
                new HashMap<Identity, Map<String, Element>>();

        synchronized void put(Object message, String portId,
                              Element element) {
            expunge();
            held.computeIfAbsent(new Identity(message, dropped),
                    key -> new HashMap<String, Element>())
                    .put(portId, element);
        }

        synchronized Element get(Object message, String portId) {
            Map<String, Element> elements =
                    held.get(new Identity(message, null));
            return elements == null ? null : elements.get(portId);
        }

        synchronized void clear() {
            held.clear();
            while (dropped.poll() != null) {
                // Drained: their entries went with the map.
            }
        }

        private void expunge() {
            for (Object gone; (gone = dropped.poll()) != null; ) {
                held.remove(gone);
            }
        }
    }

    /** A message by identity, weakly. */
    private static final class Identity extends WeakReference<Object> {
        private final int hash;

        private Identity(Object message, ReferenceQueue<Object> dropped) {
            super(message, dropped);
            hash = System.identityHashCode(message);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof Identity)) return false;
            Object referent = get();
            return referent != null && referent == ((Identity) other).get();
        }
    }
}
