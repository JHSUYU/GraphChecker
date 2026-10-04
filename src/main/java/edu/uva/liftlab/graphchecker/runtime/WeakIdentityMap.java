package edu.uva.liftlab.graphchecker.runtime;

import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A map keyed by object identity that holds its keys weakly: an entry goes
 * once its key is collected, so no table of the runtime keeps an
 * application object alive.  An object nothing references any more is never
 * asked about again, so dropping its entry changes no answer.
 *
 * <p>hdfs-adhoc-49 (TestSnapshot, 36 MiniDFSClusters one after another):
 * the recorder's object ids and the registered sources, with the HDFS
 * adapter's own registry, kept every NameNode and DataNode the test had shut
 * down alive -- 1.8 GB of the recording's 4 GB heap -- and the recording
 * collected for minutes on end.  Thread-safe; each operation first drops the
 * entries of collected keys.</p>
 */
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

    boolean isEmpty() {
        return entries.isEmpty();
    }

    void clear() {
        entries.clear();
        while (collected.poll() != null) {
            // Their entries went with the table.
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

    /** A stored key: weak, by identity.  Once collected it equals only
     *  itself, which is how {@link #sweep} removes it. */
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

    /** A lookup: the object itself, matched by identity, never stored. */
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
