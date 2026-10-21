package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.pauseObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resumeObservation;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.primitiveString;

final class MessageCodec {
    private MessageCodec() {
    }

    private static volatile Map<String, List<PortField>> ports =
            Collections.emptyMap();
    private static final Map<Class<?>, Plan> PLANS =
            new ConcurrentHashMap<Class<?>, Plan>();
    private static final Bindings BINDINGS = new Bindings();

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

    static void install(List<JsonObject> rows) {
        Map<String, Map<String, PortField>> found =
                new LinkedHashMap<String, Map<String, PortField>>();
        for (JsonObject row : rows) {
            if (!StaticScopeMap.SITE_KIND.equals(primitiveString(row, "kind"))
                    || !StaticScopeMap.EXPORT_SITE.equals(
                            primitiveString(row, "role"))) {
                continue;
            }
            FieldPathSpec.DeclaredField cell = FieldPathSpec.declaredField(
                    primitiveString(row, "cell"));
            String portId = primitiveString(row, "portId");
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

    static void send(Object message) {
        if (message == null || ports.isEmpty()) return;
        walk(message, (holder, owner, port) -> {
            Element element = BINDINGS.get(holder, port.portId);
            if (element == null) {
                WireExport.export(port.portId, new WireExport.Leaf(holder,
                        owner, port.field, port.descriptor));
            } else if (element.handle == SymbolicMessageEnvelope.ABSENT) {
                SymbolicMessageEnvelope.skip(port.portId);
            } else if (element.built) {
                WireExport.stage(port.portId, element.handle,
                        element.producer);
            } else {
                WireExport.relay(port.portId, element);
            }
        });
    }

    static void set(Object builder, String portId, long handle,
                    Endpoint producer) {
        if (builder != null && !ports.isEmpty()) {
            BINDINGS.put(builder, portId, new Element(handle, producer));
        }
    }

    static void built(Object builder, Object message) {
        if (builder != null && message != null && !ports.isEmpty()) {
            BINDINGS.copy(builder, message);
        }
    }

    static void receive(Object message) {
        if (message == null || ports.isEmpty()) return;
        walk(message, (holder, owner, port) -> {
            Element element = Element.received(SymbolicMessageEnvelope.take(
                    port.portId));
            if (holder != plan(holder.getClass()).defaultInstance) {
                BINDINGS.put(holder, port.portId, element);
            }
        });
    }

    static Element bound(Object message, String portId) {
        if (message == null || !BINDINGS.decoded(message)) return null;
        Element element = BINDINGS.get(message, portId);
        return element == null ? Element.NONE : element;
    }

    static final class Element {
        private static final Element NONE = new Element(
                SymbolicMessageEnvelope.ABSENT, "", "");
        final long handle;
        final String correlationId;
        final String half;
        final boolean built;
        final Endpoint producer;

        private Element(long handle, String correlationId, String half) {
            this.handle = handle;
            this.correlationId = correlationId;
            this.half = half;
            this.built = false;
            this.producer = null;
        }

        private Element(long handle, Endpoint producer) {
            this.handle = handle;
            this.correlationId = "";
            this.half = "";
            this.built = true;
            this.producer = producer;
        }

        static Element received(long handle) {
            MessageDoors.Inbound inbound = MessageDoors.current();
            return new Element(handle,
                    inbound == null ? "" : trimmed(inbound.correlationId),
                    inbound == null ? "" : trimmed(inbound.half));
        }
    }


    private interface Visit {
        void port(Object holder, String owner, PortField port);
    }

    private static void walk(Object message, Visit visit) {
        pauseObservation();
        try {
            visit(message, visit);
        } finally {
            resumeObservation();
        }
    }

    private static void visit(Object message, Visit visit) {
        Plan plan = plan(message.getClass());
        if (plan == null) return;
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
                    if (element != null) visit(element, visit);
                }
            } else if (value != null) {
                visit(value, visit);
            }
        }
    }

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

    private static final Plan NONE = new Plan("", null,
            Collections.<Field, PortField>emptyMap(),
            Collections.<Field>emptyList());

    private static Plan plan(Class<?> type) {
        Plan plan = PLANS.get(type);
        if (plan == null) {
            plan = EnginePlumbing.wireMessage(type) ? planOf(type) : NONE;
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

    private static boolean mayHoldMessage(Field field) {
        Class<?> held = field.getType();
        if (held == Object.class || EnginePlumbing.wireMessage(held)) {
            return true;
        }
        if (!Collection.class.isAssignableFrom(held)
                || !(field.getGenericType() instanceof ParameterizedType)) {
            return false;
        }
        Type[] elements = ((ParameterizedType) field.getGenericType())
                .getActualTypeArguments();
        return elements.length == 1 && elements[0] instanceof Class
                && EnginePlumbing.wireMessage((Class<?>) elements[0]);
    }

    private static Object defaultInstance(Class<?> type) {
        try {
            return type.getMethod("getDefaultInstance").invoke(null);
        } catch (ReflectiveOperationException | RuntimeException none) {
            return null;
        }
    }


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

        synchronized boolean decoded(Object message) {
            Map<String, Element> elements =
                    held.get(new Identity(message, null));
            return elements != null && !elements.isEmpty()
                    && !elements.values().iterator().next().built;
        }

        synchronized void copy(Object from, Object to) {
            Map<String, Element> elements =
                    held.get(new Identity(from, null));
            if (elements == null) return;
            expunge();
            held.computeIfAbsent(new Identity(to, dropped),
                    key -> new HashMap<String, Element>())
                    .putAll(elements);
        }

        synchronized void clear() {
            held.clear();
            while (dropped.poll() != null) {
            }
        }

        private void expunge() {
            for (Object gone; (gone = dropped.poll()) != null; ) {
                held.remove(gone);
            }
        }
    }

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
