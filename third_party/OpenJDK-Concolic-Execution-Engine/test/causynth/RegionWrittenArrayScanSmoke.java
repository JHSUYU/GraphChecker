/** A scan over a large array that a region stored into under symbolic guards
 *  reads every bucket no recorded write touched as the heap holds it -- no
 *  READ node, no condition -- and a written bucket as the value its write
 *  stored.  Both ways an array gets its shadow are covered: `entries` is
 *  named by a read at a symbolic index (LightWeightGSet.get), `counts` by the
 *  store of a symbolic value.  hdfs-17960's FSImageSaver scanned the
 *  NameNode's ~2M-bucket inode map this way and built a READ and an
 *  `== null` condition per bucket until its replay JVM passed 24 GB. */
public final class RegionWrittenArrayScanSmoke {
    private static final class Input {
        int value = 5;
    }

    private static final class Entry {
        final int key;

        Entry(int key) {
            this.key = key;
        }
    }

    private static final class Sink {
        int value;
    }

    private static final int BUCKETS = 1 << 20;
    private static final String REFERENCE =
            "\"expression\":{\"_type\":\"VmExpressionReference\",";

    public static void main(String[] args) {
        Entry[] entries = new Entry[BUCKETS];
        int[] counts = new int[BUCKETS];
        Input input = new Input();
        Sink sink = new Sink();
        require(System.startConcolicRegion("REGION.written-array-scan",
                "TASK.written-array-scan") == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "WRITE_SOURCE");
        Entry named = entries[input.value & (BUCKETS - 1)];
        if (input.value > 0) {
            entries[7] = new Entry(input.value);
            counts[7] = input.value;
        }
        if (input.value > 1) entries[BUCKETS - 3] = new Entry(3);

        String before = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        long first = freshExpressionId(sink, input);
        int found = 0;
        int nonzero = 0;
        for (int i = 0; i < entries.length; i++) {
            if (entries[i] != null) found++;
            if (counts[i] != 0) nonzero++;
        }
        long last = freshExpressionId(sink, input);
        String after = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);

        sink.value = counts[7];
        String written = field(sink);
        // A field no symbolic value reached, so what it states is the load's.
        Sink plain = new Sink();
        plain.value = counts[5];
        String untouched = field(plain);
        System.finishConcolicRegion();

        require(named == null && found == 2 && nonzero == 1,
                "the scan read the wrong heap: " + found + "/" + nonzero);
        // Two probes and the three written buckets' conditions; the VM this
        // replaces built a READ and an index constant per bucket.
        require(last - first < 64, "the scan built " + (last - first)
                + " expressions over " + BUCKETS + " buckets");
        require(after.length() - before.length() < 4096, "the scan "
                + "constrained the path by " + (after.length()
                - before.length()) + " characters");
        require(written.contains("WRITE_SOURCE")
                        && !written.contains("\"operation\":\"READ\""),
                "a written bucket does not read its stored value: "
                        + written);
        require(untouched.contains("\"symbolic\":false"),
                "an untouched bucket reads symbolically: " + untouched);
        System.out.println("CAUSYNTH_WRITTEN_ARRAY_SCAN_SMOKE_OK");
    }

    // The id of an expression built now: ids come from one session counter,
    // so two of them bound how many nodes were built in between.
    private static long freshExpressionId(Sink sink, Input input) {
        sink.value = input.value + 1;
        String stated = field(sink);
        int at = stated.indexOf(REFERENCE);
        require(at >= 0, "no fresh expression: " + stated);
        String id = "\"expressionId\":";
        int start = stated.indexOf(id, at) + id.length();
        int end = start;
        while (Character.isDigit(stated.charAt(end))) end++;
        return Long.parseLong(stated.substring(start, end));
    }

    private static String field(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
