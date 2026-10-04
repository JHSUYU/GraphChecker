package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;

import java.lang.ref.WeakReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/** The runtime's weak identity tables: keyed by identity, never keeping a
 *  key alive. */
public class WeakIdentityMapTest {

    @Test
    public void keysAreObjectsNotValues() {
        WeakIdentityMap<Integer> map = new WeakIdentityMap<>();
        String one = new String("node");
        String other = new String("node");
        assertNull(map.put(one, 1));
        assertNull(map.putIfAbsent(other, 2));
        assertEquals(Integer.valueOf(1), map.putIfAbsent(one, 3));
        assertEquals(Integer.valueOf(1), map.get(one));
        assertEquals(Integer.valueOf(2), map.get(other));
        assertEquals(Integer.valueOf(1), map.put(one, 4));
        assertEquals(Integer.valueOf(4), map.remove(one));
        assertNull(map.get(one));
        assertNull(map.get(null));
        assertFalse(map.isEmpty());
        map.clear();
        assertTrue(map.isEmpty());
    }

    @Test
    public void aCollectedKeysEntryGoes() {
        WeakIdentityMap<Integer> map = new WeakIdentityMap<>();
        WeakReference<Object> watched = putUnreferenced(map);
        for (int attempt = 0; attempt < 50 && watched.get() != null;
                attempt++) {
            System.gc();
            byte[][] pressure = new byte[16][];
            for (int index = 0; index < pressure.length; index++) {
                pressure[index] = new byte[1 << 20];
            }
        }
        assertNull("the key was never collected", watched.get());
        Object probe = new Object();
        for (int attempt = 0; attempt < 50 && !map.isEmpty(); attempt++) {
            map.get(probe);
            Thread.yield();
        }
        assertTrue(map.isEmpty());
    }

    private static WeakReference<Object> putUnreferenced(
            WeakIdentityMap<Integer> map) {
        Object key = new Object();
        map.put(key, 7);
        return new WeakReference<>(key);
    }
}
