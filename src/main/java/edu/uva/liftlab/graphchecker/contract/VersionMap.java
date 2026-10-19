package edu.uva.liftlab.graphchecker.contract;

import java.util.function.Function;

public final class VersionMap<V> {
    private String[] keys = new String[8];
    private long[] versions = new long[8];
    private Object[] values = new Object[8];
    private int size;

    @SuppressWarnings("unchecked")
    public V get(String key, long version) {
        if (key == null) return null;
        int mask = keys.length - 1;
        for (int at = hash(key, version) & mask; ; at = (at + 1) & mask) {
            String held = keys[at];
            if (held == null) return null;
            if (versions[at] == version && held.equals(key)) {
                return (V) values[at];
            }
        }
    }

    public void put(String key, long version, V value) {
        slot(key, version, value);
    }

    public V computeIfAbsent(String key, long version,
                             Function<String, V> make) {
        V held = get(key, version);
        if (held != null) return held;
        V made = make.apply(key);
        slot(key, version, made);
        return made;
    }

    @SuppressWarnings("unchecked")
    public void replaceAll(Function<V, V> replace) {
        for (int at = 0; at < keys.length; at++) {
            if (keys[at] != null) values[at] = replace.apply((V) values[at]);
        }
    }

    private void slot(String key, long version, Object value) {
        if (key == null || value == null) {
            throw new NullPointerException(key + "#" + version);
        }
        if (2 * (size + 1) > keys.length) grow();
        int mask = keys.length - 1;
        for (int at = hash(key, version) & mask; ; at = (at + 1) & mask) {
            String held = keys[at];
            if (held == null) {
                keys[at] = key;
                versions[at] = version;
                values[at] = value;
                size++;
                return;
            }
            if (versions[at] == version && held.equals(key)) {
                values[at] = value;
                return;
            }
        }
    }

    private void grow() {
        String[] oldKeys = keys;
        long[] oldVersions = versions;
        Object[] oldValues = values;
        keys = new String[2 * oldKeys.length];
        versions = new long[2 * oldKeys.length];
        values = new Object[2 * oldKeys.length];
        size = 0;
        for (int at = 0; at < oldKeys.length; at++) {
            if (oldKeys[at] != null) {
                slot(oldKeys[at], oldVersions[at], oldValues[at]);
            }
        }
    }

    private static int hash(String key, long version) {
        return OpenSet.spread(31 * key.hashCode()
                + (int) (version ^ (version >>> 32)));
    }
}
