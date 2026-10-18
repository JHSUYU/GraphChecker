package edu.uva.liftlab.graphchecker.contract;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A SET HELD FOR GOOD, in the order it was made: its elements in one array,
 * where a {@code LinkedHashSet} holds a 40-byte entry and a table slot per
 * element (what a delivery rests on, SGF8-adhoc-05 round 5's planner: 18 M
 * symbols in 53 K sets, 912 MB).  Most are only iterated: past {@link
 * #SCANNED} elements, an index of their places (open addressing) is built
 * the first time it is asked whether it holds one (its arrays were 300 MB
 * of that planner's, every set indexed).  Unmodifiable; null may be one of
 * its elements, as of a {@code LinkedHashSet}.
 */
public final class FrozenSet<E> extends AbstractSet<E> {
    /** Up to this many elements are found by a scan, with no index. */
    private static final int SCANNED = 8;
    private static final FrozenSet<Object> EMPTY =
            new FrozenSet<Object>(new Object[0]);

    private final Object[] elements;
    /** Each element's place plus one, by its hash; null until asked, and
     *  for a set scanned.  Any thread may build it; each builds the same. */
    private volatile int[] index;

    private FrozenSet(Object[] elements) {
        this.elements = elements;
    }

    /** {@link #index}, built where none is. */
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

    /** The set {@code elements} is, in its order: itself where it is one
     *  already.  Its elements are distinct (a set's). */
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
