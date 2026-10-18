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
 * later product holding an older object shares it, it does not re-make it:
 * stated, never a silent re-pin, as a DIAGNOSTIC row and in {@link
 * #summary}, as are a holder built from two decodes, a member the walk
 * could not read, and every object it skips as no product of the decode).  What a decode reaches but did not make is no product of it:
 * a class's constant (an object a static field of its own class holds,
 * Solr's {@code DocRouter.DEFAULT} behind every collection's router) and
 * what a supplier holds (code that makes state on demand, Solr's {@code
 * PrsSupplier} with the per-replica states of child znodes).
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
        /** The path as this run spells it: the recording's rows'. */
        final String path;
        final long version;

        Version(LocationId location, String path, long version) {
            this.location = location;
            this.path = path;
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
    private static final AtomicLong SHARED = new AtomicLong();
    private static final AtomicLong UNREGISTERED = new AtomicLong();
    private static final AtomicLong SKIPPED = new AtomicLong();
    /** Provenance sites whose read of an unregistered object is stated. */
    private static final java.util.Set<String> UNREGISTERED_SITES =
            ConcurrentHashMap.newKeySet();
    /** Class, holding version and reaching version of each shared object
     *  stated: one row each. */
    private static final java.util.Set<String> STATED =
            ConcurrentHashMap.newKeySet();
    /** Per class, its static reference fields. */
    private static final Map<Class<?>, Field[]> STATICS =
            new ConcurrentHashMap<Class<?>, Field[]>();

    private Provenance() {
    }

    /** The version {@code value} was decoded from, or null. */
    static Version of(Object value) {
        return value == null ? null : DECODED.get(value);
    }

    /**
     * A provenance site's read of {@code receiver} (SYMBOL-SCOPE §5.7): the
     * version it holds, or null; a {@code holder} -- the object a
     * constructor is building from what it reads -- holds that version from
     * then on, unless it already holds one ({@code derived} says whether it
     * took it now), so a guard reading the holder's copy reads the version
     * (a processor's {@code readOnlyCollection}, copied from its
     * collection's).
     */
    static Version observe(Object receiver, Object holder, boolean[] derived) {
        Version version = of(receiver);
        if (version != null && holder != null && holder != receiver) {
            Version held = DECODED.putIfAbsent(holder, version);
            derived[0] = held == null;
            // Built from two decodes: it keeps the first, stated.
            if (held != null && !same(held, version)) {
                state(holder.getClass(), held, version, "a "
                        + holder.getClass().getName() + " built from the"
                        + " decodes of " + held + " and " + version
                        + " keeps the first, so a guard reading it reads "
                        + held);
            }
        }
        return version;
    }

    /** Whether two versions name one location's one version. */
    private static boolean same(Version one, Version other) {
        return one.location.equals(other.location)
                && one.version == other.version;
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
                // A supplier (state made on demand: PrsSupplier's per-replica
                // states) and a class's constant are no product of this
                // decode: skipped, and stated with all they hold.
                String skipped = value instanceof java.util.function.Supplier
                        ? "a supplier, which makes its state on demand"
                        : constant(value) ? "a constant its class holds"
                        : "";
                if (!skipped.isEmpty()) {
                    SKIPPED.incrementAndGet();
                    stateOnce(type, version, version, "the decode reached a "
                            + type.getName() + ", " + skipped + ": no"
                            + " decode makes it, so it and what it holds"
                            + " hold no version");
                    continue;
                }
                // An object an earlier decode made is that decode's, and so
                // is what it holds; another version's is stated.
                Version held = DECODED.putIfAbsent(value, version);
                if (held != null) {
                    if (!same(held, version)) {
                        state(type, held, version, "the decode reached a "
                                + type.getName() + " that the decode of "
                                + held + " registered: it keeps that version,"
                                + " so a guard reading it reads " + held
                                + ", not this decode's");
                    }
                    continue;
                }
                registered.add(value);
                for (Field field : fields(type)) {
                    queue.add(new Object[] {field.get(value), depth + 1});
                }
            } catch (ReflectiveOperationException | RuntimeException
                    unreadable) {
                // A member it cannot read (a concurrent map moving under a
                // shared object) registers nothing below it: stated.
                state(type, version, version, "the decoded walk could not"
                        + " read a " + type.getName() + " (" + unreadable
                        .getClass().getSimpleName() + "): nothing below it"
                        + " holds " + version);
            }
        }
        return bounded;
    }

    /**
     * What a decode left unregistered or registered under another version
     * (a shared object, a holder built from two decodes, an unreadable
     * member): counted, stated once per class, pair and kind (DIAGNOSTIC),
     * never a silent re-pin or skip.
     */
    private static void state(Class<?> type, Version held, Version version,
                              String detail) {
        SHARED.incrementAndGet();
        stateOnce(type, held, version, detail);
    }

    /** One DIAGNOSTIC row per class, pair and kind of what a decode left. */
    private static void stateOnce(Class<?> type, Version held,
                                  Version version, String detail) {
        if (!STATED.add(type.getName() + "|" + held + "|" + version + "|"
                + detail.substring(0, Math.min(24, detail.length())))) {
            return;
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                version.toString(), detail);
    }

    /** Whether a static field of {@code value}'s own class or one of its
     *  application superclasses holds it, itself or as an element of a
     *  map, collection or array it holds: a class's constant (Solr's
     *  {@code DocRouter.DEFAULT}, and the routers {@code DocRouter.routerMap}
     *  holds as values). */
    private static boolean constant(Object value) {
        for (Class<?> at = value.getClass(); at != null
                && !jdk(at.getName()); at = at.getSuperclass()) {
            for (Field field : statics(at)) {
                try {
                    if (holds(field.get(null), value)) return true;
                } catch (ReflectiveOperationException | RuntimeException
                        unreadable) {
                    // Not one it can read.
                }
            }
        }
        return false;
    }

    /** Whether {@code held} is {@code value}, or a map's value, a
     *  collection's or an array's element that is, among its first
     *  {@link #MAX_CONSTANTS}. */
    private static boolean holds(Object held, Object value) {
        if (held == value) return true;
        Iterable<?> elements = held instanceof Map ? ((Map<?, ?>) held)
                .values() : held instanceof Collection ? (Collection<?>) held
                : held instanceof Object[] ? java.util.Arrays.asList(
                (Object[]) held) : null;
        if (elements == null) return false;
        int seen = 0;
        for (Object element : elements) {
            if (element == value) return true;
            if (++seen >= MAX_CONSTANTS) break;
        }
        return false;
    }

    /** The most elements of one static container a constant is looked for
     *  among: a class's table of constants, not a cache. */
    private static final int MAX_CONSTANTS = 1024;

    /** The static reference fields of {@code type}, once per class. */
    private static Field[] statics(Class<?> type) {
        Field[] known = STATICS.get(type);
        if (known != null) return known;
        List<Field> found = new ArrayList<Field>();
        for (Field field : type.getDeclaredFields()) {
            if (!Modifier.isStatic(field.getModifiers())
                    || field.getType().isPrimitive()) {
                continue;
            }
            try {
                field.setAccessible(true);
                found.add(field);
            } catch (RuntimeException inaccessible) {
                // Not read.
            }
        }
        known = found.isEmpty() ? NONE : found.toArray(new Field[0]);
        STATICS.put(type, known);
        return known;
    }

    /**
     * A provenance site in a region read an object no decode registered: its
     * guard reads no store version, so no closure crosses to a writer of
     * one.  Counted, stated once per site (DIAGNOSTIC), never silent.
     */
    static void unregistered(String siteId, Object receiver) {
        if (receiver == null) return;
        UNREGISTERED.incrementAndGet();
        if (!UNREGISTERED_SITES.add(siteId)) return;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, siteId,
                "this provenance site read a " + receiver.getClass().getName()
                        + " no decode registered, so its guard reads no store"
                        + " version and no closure crosses to a writer of one");
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
                + BOUNDED.get() + " at the bound, " + SHARED.get()
                + " object(s) another version holds or unreadable, "
                + SKIPPED.get() + " skipped as no decode's (a constant, a"
                + " supplier), "
                + UNREGISTERED.get() + " provenance read(s) of an object no"
                + " decode registered";
    }

    /** Whether any decode was walked (the summary says something). */
    static boolean walked() {
        return DECODES.get() > 0L;
    }

    /** Objects a decode reached that another version holds, holders built
     *  from two decodes, members it could not read (tests). */
    static long shared() {
        return SHARED.get();
    }
}
