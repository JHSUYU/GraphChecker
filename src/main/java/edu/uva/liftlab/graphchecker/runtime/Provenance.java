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

final class Provenance {
    static final int MAX_OBJECTS = 4096;
    static final int MAX_DEPTH = 16;

    static final class Version {
        final LocationId location;
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
    private static final java.util.Set<String> UNREGISTERED_SITES =
            ConcurrentHashMap.newKeySet();
    private static final java.util.Set<String> STATED =
            ConcurrentHashMap.newKeySet();
    private static final Map<Class<?>, Field[]> STATICS =
            new ConcurrentHashMap<Class<?>, Field[]>();

    private Provenance() {
    }

    static Version of(Object value) {
        return value == null ? null : DECODED.get(value);
    }

    static Version observe(Object receiver, Object holder, boolean[] derived) {
        Version version = of(receiver);
        if (version != null && holder != null && holder != receiver) {
            Version held = DECODED.putIfAbsent(holder, version);
            derived[0] = held == null;
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

    private static boolean same(Version one, Version other) {
        return one.location.equals(other.location)
                && one.version == other.version;
    }

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
                if (jdk(type.getName()) || type.isSynthetic()
                        || type.getName().contains("$$Lambda$")
                        || EnginePlumbing.site(type.getName())) {
                    continue;
                }
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
                state(type, version, version, "the decoded walk could not"
                        + " read a " + type.getName() + " (" + unreadable
                        .getClass().getSimpleName() + "): nothing below it"
                        + " holds " + version);
            }
        }
        return bounded;
    }

    private static void state(Class<?> type, Version held, Version version,
                              String detail) {
        SHARED.incrementAndGet();
        stateOnce(type, held, version, detail);
    }

    private static void stateOnce(Class<?> type, Version held,
                                  Version version, String detail) {
        if (!STATED.add(type.getName() + "|" + held + "|" + version + "|"
                + detail.substring(0, Math.min(24, detail.length())))) {
            return;
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                version.toString(), detail);
    }

    private static boolean constant(Object value) {
        for (Class<?> at = value.getClass(); at != null
                && !jdk(at.getName()); at = at.getSuperclass()) {
            for (Field field : statics(at)) {
                try {
                    if (holds(field.get(null), value)) return true;
                } catch (ReflectiveOperationException | RuntimeException
                        unreadable) {
                }
            }
        }
        return false;
    }

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

    private static final int MAX_CONSTANTS = 1024;

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
            }
        }
        known = found.isEmpty() ? NONE : found.toArray(new Field[0]);
        STATICS.put(type, known);
        return known;
    }

    static void unregistered(String siteId, Object receiver) {
        if (receiver == null) return;
        UNREGISTERED.incrementAndGet();
        if (!UNREGISTERED_SITES.add(siteId)) return;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, siteId,
                "this provenance site read a " + receiver.getClass().getName()
                        + " no decode registered, so its guard reads no store"
                        + " version and no closure crosses to a writer of one");
    }

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

    private static Field[] fields(Class<?> type) {
        Field[] known = FIELDS.get(type);
        if (known != null) return known;
        List<Field> found = new ArrayList<Field>();
        for (Class<?> at = type; at != null && !jdk(at.getName());
             at = at.getSuperclass()) {
            for (Field field : at.getDeclaredFields()) {
                if (Modifier.isStatic(field.getModifiers())
                        || field.getType().isPrimitive()
                        || field.isSynthetic()) {
                    continue;
                }
                try {
                    field.setAccessible(true);
                    found.add(field);
                } catch (RuntimeException inaccessible) {
                }
            }
        }
        known = found.isEmpty() ? NONE : found.toArray(new Field[0]);
        FIELDS.put(type, known);
        return known;
    }

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

    static boolean walked() {
        return DECODES.get() > 0L;
    }

    static long shared() {
        return SHARED.get();
    }
}
