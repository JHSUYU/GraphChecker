package edu.uva.liftlab.graphchecker.contract;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

public final class FrozenSet<E> extends AbstractSet<E> {
    private static final int SCANNED = 8;
    private static final FrozenSet<Object> EMPTY =
            new FrozenSet<Object>(new Object[0]);

    private final Object[] elements;
    private volatile int[] index;

    private FrozenSet(Object[] elements) {
        this.elements = elements;
    }

    private int[] index() {
        int[] built = index;
        if (built != null) return built;
        int capacity = 16;
        while (capacity < 2 * elements.length) capacity <<= 1;
        built = new int[capacity];
        int mask = capacity - 1;
        for (int place = 0; place < elements.length; place++) {
            if (elements[place] == null) continue;
            int at = OpenSet.spread(elements[place].hashCode()) & mask;
            while (built[at] != 0) at = (at + 1) & mask;
            built[at] = place + 1;
        }
        index = built;
        return built;
    }

    @SuppressWarnings("unchecked")
    public static <E> Set<E> of(Set<? extends E> elements) {
        if (elements instanceof FrozenSet) return (Set<E>) elements;
        if (elements.isEmpty()) return (Set<E>) EMPTY;
        return new FrozenSet<E>(elements.toArray());
    }

    @Override
    public boolean contains(Object element) {
        if (element == null || elements.length <= SCANNED) {
            for (Object held : elements) {
                if (held == null ? element == null : held.equals(element)) {
                    return true;
                }
            }
            return false;
        }
        int[] index = index();
        int mask = index.length - 1;
        for (int at = OpenSet.spread(element.hashCode()) & mask; ;
             at = (at + 1) & mask) {
            int place = index[at];
            if (place == 0) return false;
            if (elements[place - 1].equals(element)) return true;
        }
    }

    @Override
    public int size() {
        return elements.length;
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<E>() {
            private int at;

            @Override
            public boolean hasNext() {
                return at < elements.length;
            }

            @Override
            @SuppressWarnings("unchecked")
            public E next() {
                if (at >= elements.length) {
                    throw new NoSuchElementException();
                }
                return (E) elements[at++];
            }
        };
    }

    @Override
    public Object[] toArray() {
        return Arrays.copyOf(elements, elements.length);
    }
}
