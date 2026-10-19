package edu.uva.liftlab.graphchecker.contract;

public final class PairSet {
    private Object[] slots = new Object[2 * 8];
    private int size;

    public boolean contains(Object first, Object second) {
        int mask = slots.length / 2 - 1;
        for (int at = hash(first, second) & mask; ; at = (at + 1) & mask) {
            Object held = slots[2 * at];
            if (held == null) return false;
            if (held.equals(first) && slots[2 * at + 1].equals(second)) {
                return true;
            }
        }
    }

    public boolean add(Object first, Object second) {
        if (first == null || second == null) {
            throw new NullPointerException("a pair of " + first + " and "
                    + second);
        }
        if (2 * (size + 1) > slots.length / 2) grow();
        if (!put(slots, first, second)) return false;
        size++;
        return true;
    }

    public void addAll(PairSet other) {
        for (int at = 0; at < other.slots.length; at += 2) {
            if (other.slots[at] != null) {
                add(other.slots[at], other.slots[at + 1]);
            }
        }
    }

    private static boolean put(Object[] slots, Object first, Object second) {
        int mask = slots.length / 2 - 1;
        for (int at = hash(first, second) & mask; ; at = (at + 1) & mask) {
            Object held = slots[2 * at];
            if (held == null) {
                slots[2 * at] = first;
                slots[2 * at + 1] = second;
                return true;
            }
            if (held.equals(first) && slots[2 * at + 1].equals(second)) {
                return false;
            }
        }
    }

    private void grow() {
        Object[] larger = new Object[2 * slots.length];
        for (int at = 0; at < slots.length; at += 2) {
            if (slots[at] != null) put(larger, slots[at], slots[at + 1]);
        }
        slots = larger;
    }

    private static int hash(Object first, Object second) {
        return OpenSet.spread(31 * first.hashCode() + second.hashCode());
    }
}
