package edu.uva.liftlab.graphchecker.runtime;

import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

final class WeakIdentityMap<V> {
    private final Map<Object, V> entries = new ConcurrentHashMap<>();
    private final ReferenceQueue<Object> collected = new ReferenceQueue<>();

    V get(Object key) {
        sweep();
        return key == null ? null : entries.get(new Probe(key));
    }

    V put(Object key, V value) {
        sweep();
        return entries.put(new Key(require(key), collected), value);
    }

    V putIfAbsent(Object key, V value) {
        sweep();
        return entries.putIfAbsent(new Key(require(key), collected), value);
    }

    V remove(Object key) {
        sweep();
        return key == null ? null : entries.remove(new Probe(key));
    }

    boolean remove(Object key, V value) {
        sweep();
        return key != null && value != null
                && entries.remove(new Probe(key), value);
    }

    boolean isEmpty() {
        return entries.isEmpty();
    }

    void clear() {
        entries.clear();
        while (collected.poll() != null) {
        }
    }

    private void sweep() {
        for (Reference<?> dead = collected.poll(); dead != null;
                dead = collected.poll()) {
            entries.remove(dead);
        }
    }

    private static Object require(Object key) {
        if (key == null) {
            throw new IllegalArgumentException("a weak identity key is null");
        }
        return key;
    }

    private static final class Key extends WeakReference<Object> {
        private final int identity;

        private Key(Object value, ReferenceQueue<Object> queue) {
            super(value, queue);
            this.identity = System.identityHashCode(value);
        }

        @Override
        public int hashCode() {
            return identity;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            Object held = get();
            if (held == null) return false;
            return other instanceof Key ? held == ((Key) other).get()
                    : other instanceof Probe && held == ((Probe) other).value;
        }
    }

    private static final class Probe {
        private final Object value;

        private Probe(Object value) {
            this.value = value;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(value);
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Key && ((Key) other).get() == value;
        }
    }
}
