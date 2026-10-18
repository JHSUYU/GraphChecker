package edu.uva.liftlab.graphchecker.contract;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A SET HELD FOR GOOD, in the order it was made: its elements in one array,
 * and past {@link #SCANNED} of them an index of their places (open
 * addressing), where a {@code LinkedHashSet} holds a 40-byte entry and a
 * table slot per element (what a delivery rests on, SGF8-adhoc-05 round 5's
 * planner: 18 M symbols in 53 K sets, 912 MB).  Unmodifiable; null may be
 * one of its elements, as of a {@code LinkedHashSet}.
 */
public final class FrozenSet<E> extends AbstractSet<E> {
    /** Up to this many elements are found by a scan, with no index. */
    private static final int SCANNED = 8;
    private static final FrozenSet<Object> EMPTY =
            new FrozenSet<Object>(new Object[0]);

    private final Object[] elements;
    /** Each element's place plus one, by its hash; null when scanned. */
    private final int[] index;

    private FrozenSet(Object[] elements) {
        this.elements = elements;
        if (elements.length <= SCANNED) {
            index = null;
            return;
        }
        int capacity = 16;
        while (capacity < 2 * elements.length) capacity <<= 1;
        index = new int[capacity];
        int mask = capacity - 1;
        for (int place = 0; place < elements.length; place++) {
            if (elements[place] == null) continue;
            int at = OpenSet.spread(elements[place].hashCode()) & mask;
            while (index[at] != 0) at = (at + 1) & mask;
            index[at] = place + 1;
        }
    }

    /** The set {@code elements} is, in its order: itself where it is one
     *  already.  Its elements are distinct (a set's). */
    @SuppressWarnings("unchecked")
    public static <E> Set<E> of(Set<? extends E> elements) {
        if (elements instanceof FrozenSet) return (Set<E>) elements;
        if (elements.isEmpty()) return (Set<E>) EMPTY;
        return new FrozenSet<E>(elements.toArray());
    }

    /** The distinct elements of {@code elements}, in their first order. */
    public static <E> Set<E> distinct(Collection<? extends E> elements) {
        if (elements instanceof Set) return of((Set<? extends E>) elements);
        return of(new java.util.LinkedHashSet<E>(elements));
    }

    @Override
    public boolean contains(Object element) {
        if (element == null || index == null) {
            for (Object held : elements) {
                if (held == null ? element == null : held.equals(element)) {
                    return true;
                }
            }
            return false;
        }
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

    /** The empty one. */
    @SuppressWarnings("unchecked")
    public static <E> Set<E> empty() {
        return (Set<E>) EMPTY;
    }
}
