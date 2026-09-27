/** A read at a symbolic index names an array and writes nothing: a scan at
 *  concrete indices afterwards (length included) reads what the heap holds,
 *  while an element written symbolically stays symbolic. */
public final class RegionSymbolicIndexScanSmoke {
    private static final class Input {
        int value = 5;
    }

    private static final class Entry {
        final int weight;

        Entry(int weight) {
            this.weight = weight;
        }
    }

    private static volatile int sink;

    public static void main(String[] args) {
        Entry[] entries = new Entry[1024];
        int[] counts = new int[1024];
        for (int i = 0; i < entries.length; i++) entries[i] = new Entry(i);
        Input input = new Input();
        require(System.startConcolicRegion("REGION.symbolic-index-scan",
                "TASK.symbolic-index-scan") == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "INDEX_SOURCE");
        Entry named = entries[input.value & 1023];
        int counted = counts[input.value & 1023];

        String before = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        for (int i = 0; i < entries.length; i++) {
            if (entries[i].weight > 2000) sink++;
            if (counts[i] > 0) sink++;
        }
        String after = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        // At most the one element the symbolic read itself returned (its
        // object carries that read); every other slot is the heap's.  The
        // VM this replaces added ~800 characters per slot.
        require(after.length() - before.length() < 4096, "a scan of a named "
                + "array constrained the path by "
                + (after.length() - before.length()) + " characters");

        counts[3] = input.value;
        boolean decision = counts[3] > 0;
        String written = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        System.finishConcolicRegion();
        require(decision && named != null && counted == 0
                        && written.length() > after.length()
                        && written.contains("INDEX_SOURCE"),
                "a symbolic element lost its source: " + written);
        System.out.println("CAUSYNTH_SYMBOLIC_INDEX_SCAN_SMOKE_OK");
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
