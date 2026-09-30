/**
 * Every read states whether it is exact: the word it loaded is the word its
 * observed version stored.
 *
 * <p>writerSetComplete says whether the location's writer set is whole; it
 * used to decide a read's joinability too, so one lost version left every
 * later read of the location unjoined.  observedExact is the read's own
 * verification: a read that returned exactly its version's word joins it at
 * an incomplete location.  unnamedWriter is what removes alternative writers:
 * a writer the log never named reached the location.  The version bound is
 * not one -- every retained version is still a real writer -- so a hot field
 * past it keeps its alternatives.  A reference loads no comparable word, and
 * is never exact.</p>
 */
public final class RegionReadExactnessSmoke {
    private static final class Input {
        String name = "abc";
    }

    private static final class Holder {
        int value;
        String name;
    }

    private static final class Sink {
        int i;
        String name;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.exactness",
                "TASK.exactness") == 0L, "region start rejected");
        Holder holder = new Holder();
        System.observeExactPrimitiveField(holder, Holder.class.getName(),
                "value", "I");
        Sink sink = new Sink();

        sink.i = holder.value;
        String first = field(sink, "i", "I", Integer.valueOf(sink.i));
        require(first.contains("\"observedExact\":true")
                        && first.contains("\"writerSetComplete\":true")
                        && first.contains("\"versionKind\":\"INITIAL\""),
                "a read of the INITIAL is not exact: " + first);

        // Past the version bound the writer set is not whole; each read
        // still verifies itself.
        for (int index = 1; index <= 70; index++) {
            holder.value = index;
        }
        sink.i = holder.value;
        String bounded = field(sink, "i", "I", Integer.valueOf(sink.i));
        String log = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "value", "I");
        require(bounded.contains("\"observedExact\":true")
                        && bounded.contains("\"writerSetComplete\":false")
                        && !bounded.contains("\"unnamedWriter\""),
                "a read past the bound is not exact, or lost its"
                        + " alternatives: " + bounded);
        require(log.contains("\"incompleteReasons\":[\"VERSION_BOUND\"]")
                        && log.contains("\"unnamedWriter\":false"),
                "the bound is not named, or names an unnamed writer: "
                        + log);

        // A reference states no word.
        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "name",
                "Ljava/lang/String;", "EXACT.NAME");
        holder.name = input.name;
        sink.name = holder.name;
        String reference = field(sink, "name", "Ljava/lang/String;",
                sink.name);
        require(reference.contains("\"_type\":\"ReadFromExpression\"")
                        && reference.contains("\"observedExact\":false"),
                "a reference read claims a word: " + reference);

        System.endConcolic();
        System.out.println("RegionReadExactnessSmoke OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
