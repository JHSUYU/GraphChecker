package edu.uva.liftlab.graphchecker.contract;

import java.util.AbstractSet;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A HASH SET AS ONE ARRAY of its elements (open addressing, linear
 * probing): a reference a slot at most half full, where a {@code HashSet}
 * holds a 32-byte node and a table slot per element (a closure walk's named
 * symbols, 17 M of them in SGF8-adhoc-05 round 5's planner, 640 MB).  Its
 * order is its table's (null, where held, first), as a {@code HashSet}'s is
 * its own: only where no order is read.  No element is removed.  One thread
 * changes it; it is read while no thread does.
 */
public final class OpenSet<E> extends AbstractSet<E> {
    private Object[] slots;
    /** The non-null elements. */
    private int size;
    private boolean holdsNull;

    public OpenSet() {
        slots = new Object[8];
    }

    @Override
    public boolean contains(Object element) {
        if (element == null) return holdsNull;
        int mask = slots.length - 1;
        for (int at = spread(element.hashCode()) & mask; ;
             at = (at + 1) & mask) {
            Object held = slots[at];
            if (held == null) return false;
            if (held.equals(element)) return true;
        }
    }

    @Override
    public boolean add(E element) {
        if (element == null) {
            boolean added = !holdsNull;
            holdsNull = true;
            return added;
        }
        if (2 * (size + 1) > slots.length) grow();
        if (!put(slots, element)) return false;
        size++;
        return true;
    }

    @Override
    public int size() {
        return holdsNull ? size + 1 : size;
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<E>() {
            private boolean nullLeft = holdsNull;
            private int at = advance(0);

            private int advance(int from) {
                while (from < slots.length && slots[from] == null) from++;
                return from;
            }

            @Override
            public boolean hasNext() {
                return nullLeft || at < slots.length;
            }

            @Override
            @SuppressWarnings("unchecked")
            public E next() {
                if (nullLeft) {
                    nullLeft = false;
                    return null;
                }
                if (at >= slots.length) throw new NoSuchElementException();
                E element = (E) slots[at];
                at = advance(at + 1);
                return element;
            }
        };
    }

    private static boolean put(Object[] slots, Object element) {
        int mask = slots.length - 1;
        for (int at = spread(element.hashCode()) & mask; ;
             at = (at + 1) & mask) {
            Object held = slots[at];
            if (held == null) {
                slots[at] = element;
                return true;
            }
            if (held.equals(element)) return false;
        }
    }

    private void grow() {
        Object[] larger = new Object[2 * slots.length];
        for (Object held : slots) {
            if (held != null) put(larger, held);
        }
        slots = larger;
    }

    /** murmur3's 32-bit finalizer: a String's hash is weak in its low bits
     *  for keys that differ at their end. */
    static int spread(int h) {
        h ^= h >>> 16;
        h *= 0x85ebca6b;
        h ^= h >>> 13;
        h *= 0xc2b2ae35;
        h ^= h >>> 16;
        return h;
    }
}
