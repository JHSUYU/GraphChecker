package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Which version of a shared store each decoded object was parsed from
 * (IDENTITY §7.2): a node holds what it fetched as the objects it parsed it
 * into (Solr's {@code ClusterState}, {@code DocCollection}s, {@code Slice}s,
 * {@code Replica}s, {@code Aliases}), and a guard that reads a field of one
 * of them reads that version, wherever and whenever it runs.  The adapter
 * hands each decode's product to {@link MessageDoors#decoded}; its object
 * graph is walked once and every application object in it is registered
 * with the version, the first decode that reaches an object keeping it (a
 * later product holding an older object shares it, it does not re-make it).
 *
 * <p>The walk follows instance fields of application objects and the
 * contents of maps, collections and object arrays, registering no JDK
 * object, no value (a String, a box, an enum), no lambda or synthetic class
 * and no engine object, and never an inner object's outer one; it
 * runs with the VM's propagation paused: it is the engine's bookkeeping,
 * never the program's reads.  It is bounded, by name: past {@link
 * #MAX_OBJECTS} objects or {@link #MAX_DEPTH} hops a decode registers no
 * more, counted in {@link #summary} and stated as a DIAGNOSTIC row.</p>
 */
final class Provenance {
    /** The most objects one decode's walk visits. */
    static final int MAX_OBJECTS = 4096;
    /** The most hops from the product the walk goes. */
    static final int MAX_DEPTH = 16;

    /** One version of one store location. */
    static final class Version {
        final LocationId location;
        final long version;

        Version(LocationId location, long version) {
            this.location = location;
            this.version = version;
        }

        @Override
        public String toString() {
            return location.owner() + " " + location.slot() + "@" + version;
        }
    }

    private static final WeakIdentityMap<Version> DECODED =
            new WeakIdentityMap<Version>();
    /** Per class, its instance reference fields and its superclasses'. */
    private static final Map<Class<?>, Field[]> FIELDS =
            new ConcurrentHashMap<Class<?>, Field[]>();
    private static final Field[] NONE = new Field[0];

    private static final AtomicLong DECODES = new AtomicLong();
    private static final AtomicLong OBJECTS = new AtomicLong();
    private static final AtomicLong NANOS = new AtomicLong();
    private static final AtomicLong MAX_NANOS = new AtomicLong();
    private static final AtomicLong BOUNDED = new AtomicLong();

    private Provenance() {
    }

    /** The version {@code value} was decoded from, or null. */
    static Version of(Object value) {
        return value == null ? null : DECODED.get(value);
    }

    /**
     * Registers every application object of {@code product}'s graph not yet
     * registered with {@code version}.
     *
     * @return the objects registered, in walk order
     */
    static List<Object> register(Version version, Object product) {
        List<Object> registered = new ArrayList<Object>();
        if (product == null || version == null) return registered;
        long started = System.nanoTime();
        boolean paused = ConcolicVmBroker.pauseEngineWork();
        boolean bounded = false;
        try {
            bounded = walk(version, product, registered);
        } finally {
            if (paused) ConcolicVmBroker.resumeEngineWork();
        }
        long took = System.nanoTime() - started;
        DECODES.incrementAndGet();
        OBJECTS.addAndGet(registered.size());
        NANOS.addAndGet(took);
        MAX_NANOS.accumulateAndGet(took, Math::max);
        if (bounded) {
            BOUNDED.incrementAndGet();
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    version.toString(), "the decoded walk stopped at its bound ("
                            + MAX_OBJECTS + " objects, " + MAX_DEPTH
                            + " hops): an object past it states no version,"
                            + " and a guard reading it reads no store");
        }
        return registered;
    }

    /** @return whether the walk stopped at its bound */
    private static boolean walk(Version version, Object product,
                                List<Object> registered) {
        IdentityHashMap<Object, Boolean> seen =
                new IdentityHashMap<Object, Boolean>();
        Deque<Object[]> queue = new ArrayDeque<Object[]>();
        queue.add(new Object[] {product, 0});
        boolean bounded = false;
        while (!queue.isEmpty()) {
            Object[] next = queue.removeFirst();
            Object value = next[0];
            int depth = (Integer) next[1];
            if (value == null || seen.put(value, Boolean.TRUE) != null) {
                continue;
            }
            if (seen.size() > MAX_OBJECTS) {
                bounded = true;
                break;
            }
            if (depth > MAX_DEPTH) {
                bounded = true;
                continue;
            }
            Class<?> type = value.getClass();
            if (valueLike(type)) continue;
            try {
                if (type.isArray()) {
                    if (type.getComponentType().isPrimitive()) continue;
                    for (Object element : (Object[]) value) {
                        queue.add(new Object[] {element, depth + 1});
                    }
                    continue;
                }
                if (value instanceof Map) {
                    for (Object element : ((Map<?, ?>) value).values()) {
                        queue.add(new Object[] {element, depth + 1});
                    }
                    continue;
                }
                if (value instanceof Collection) {
                    for (Object element : (Collection<?>) value) {
                        queue.add(new Object[] {element, depth + 1});
                    }
                    continue;
                }
                // A lambda or a synthetic class is code the product holds
                // (a supplier capturing the store's client), no data of it.
                if (jdk(type.getName()) || type.isSynthetic()
                        || type.getName().contains("$$Lambda$")
                        || EnginePlumbing.site(type.getName())) {
                    continue;
                }
                // An object an earlier decode made is that decode's, and so
                // is what it holds.
                if (DECODED.putIfAbsent(value, version) != null) continue;
                registered.add(value);
                for (Field field : fields(type)) {
                    queue.add(new Object[] {field.get(value), depth + 1});
                }
            } catch (ReflectiveOperationException | RuntimeException
                    unreadable) {
                // A member it cannot read (a concurrent map moving under a
                // shared object) registers nothing below it.
            }
        }
        return bounded;
    }

    /** A value is no holder of decoded state: its identity carries none. */
    private static boolean valueLike(Class<?> type) {
        return type.isPrimitive() || type.isEnum() || type == String.class
                || Number.class.isAssignableFrom(type)
                || type == Boolean.class || type == Character.class
                || type == Class.class
                || type.getSuperclass() != null
                && type.getSuperclass().isEnum();
    }

    private static boolean jdk(String name) {
        return name.startsWith("java.") || name.startsWith("javax.")
                || name.startsWith("sun.") || name.startsWith("jdk.")
                || name.startsWith("com.sun.");
    }

    /** The instance reference fields of {@code type} and its non-JDK
     *  superclasses, once per class. */
    private static Field[] fields(Class<?> type) {
        Field[] known = FIELDS.get(type);
        if (known != null) return known;
        List<Field> found = new ArrayList<Field>();
        for (Class<?> at = type; at != null && !jdk(at.getName());
             at = at.getSuperclass()) {
            for (Field field : at.getDeclaredFields()) {
                // An inner class's outer instance ({@code this$0}) is the
                // code that made it, no member of the product.
                if (Modifier.isStatic(field.getModifiers())
                        || field.getType().isPrimitive()
                        || field.isSynthetic()) {
                    continue;
                }
                try {
                    field.setAccessible(true);
                    found.add(field);
                } catch (RuntimeException inaccessible) {
                    // Not walked.
                }
            }
        }
        known = found.isEmpty() ? NONE : found.toArray(new Field[0]);
        FIELDS.put(type, known);
        return known;
    }

    /** The walk's cost so far, for the run's log: decodes, objects
     *  registered, total and longest walk, walks stopped at the bound. */
    static String summary() {
        long decodes = DECODES.get();
        return decodes + " decode(s), " + OBJECTS.get() + " object(s), "
                + String.format("%.1f", NANOS.get() / 1e6) + " ms in all, "
                + String.format("%.2f", decodes == 0L ? 0.0
                : NANOS.get() / 1e6 / decodes) + " ms each, longest "
                + String.format("%.2f", MAX_NANOS.get() / 1e6) + " ms, "
                + BOUNDED.get() + " at the bound";
    }

    /** Whether any decode was walked (the summary says something). */
    static boolean walked() {
        return DECODES.get() > 0L;
    }

    static void resetForTests() {
        DECODED.clear();
        DECODES.set(0L);
        OBJECTS.set(0L);
        NANOS.set(0L);
        MAX_NANOS.set(0L);
        BOUNDED.set(0L);
    }
}
