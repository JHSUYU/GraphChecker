package edu.uva.liftlab.graphchecker.contract;

import java.util.AbstractSet;
import java.util.Iterator;
import java.util.NoSuchElementException;

public final class IdentitySet<E> extends AbstractSet<E> {
    private Object[] slots;
    private int size;

    public IdentitySet(int expected) {
        int capacity = 2;
        while (capacity < 2 * expected) capacity <<= 1;
        slots = new Object[capacity];
    }

    @Override
    public boolean contains(Object element) {
        if (element == null) return false;
        int mask = slots.length - 1;
        for (int at = OpenSet.spread(System.identityHashCode(element))
                & mask; ; at = (at + 1) & mask) {
            Object held = slots[at];
            if (held == null) return false;
            if (held == element) return true;
        }
    }

    @Override
    public boolean add(E element) {
        if (element == null) throw new NullPointerException();
        if (2 * (size + 1) > slots.length) grow();
        if (!put(slots, element)) return false;
        size++;
        return true;
    }

    @Override
    public int size() {
        return size;
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<E>() {
            private int at = advance(0);

            private int advance(int from) {
                while (from < slots.length && slots[from] == null) from++;
                return from;
            }

            @Override
            public boolean hasNext() {
                return at < slots.length;
            }

            @Override
            @SuppressWarnings("unchecked")
            public E next() {
                if (at >= slots.length) throw new NoSuchElementException();
                E element = (E) slots[at];
                at = advance(at + 1);
                return element;
            }
        };
    }

    private static boolean put(Object[] slots, Object element) {
        int mask = slots.length - 1;
        for (int at = OpenSet.spread(System.identityHashCode(element))
                & mask; ; at = (at + 1) & mask) {
            Object held = slots[at];
            if (held == null) {
                slots[at] = element;
                return true;
            }
            if (held == element) return false;
        }
    }

    private void grow() {
        Object[] larger = new Object[2 * slots.length];
        for (Object held : slots) {
            if (held != null) put(larger, held);
        }
        slots = larger;
    }
}
