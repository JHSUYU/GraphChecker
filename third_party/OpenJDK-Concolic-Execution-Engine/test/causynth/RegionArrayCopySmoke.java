import java.util.Arrays;

/**
 * System.arraycopy and Arrays.copyOf move element shadows and versions.
 *
 * <p>No bytecode runs for a copy, so no element hook saw it: a destination
 * kept whatever shadow it had and a tracked element kept its old version,
 * and the next reader found a word no version stored.  CharArrayBuffer's
 * growth was 1,136 of the 1,139 UNOBSERVED reads of one Solr session.  The
 * copy now carries each source element's value into the destination's
 * state, versions each tracked destination element in the same critical
 * section as the copy, and keeps overlapping ranges right.  A store no hook
 * sees makes a recorded write stale; the read then states the heap's word,
 * concrete, instead of the stale value.</p>
 */
public final class RegionArrayCopySmoke {
    private static final class Input {
        char c = 'x';
        int n = 7;
        boolean flag = true;
    }

    private static final class Sink {
        char c;
        int i;
        boolean z;
        byte b;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.array-copy",
                "TASK.array-copy") == 0L, "region start rejected");
        Input in = new Input();
        System.symbolizeExactField(in, Input.class.getName(), "c", "C",
                "COPY.C");
        System.symbolizeExactField(in, Input.class.getName(), "n", "I",
                "COPY.N");
        System.symbolizeExactField(in, Input.class.getName(), "flag", "Z",
                "COPY.FLAG");
        Sink sink = new Sink();

        // A symbolic element moved by System.arraycopy keeps its value.
        char[] source = new char[4];
        source[1] = in.c;
        char[] destination = new char[8];
        System.arraycopy(source, 0, destination, 2, 4);
        sink.c = destination[3];
        String moved = field(sink, "c", "C", Character.valueOf(sink.c));
        require(moved.contains("COPY.C"), "the copy lost its value: " + moved);
        sink.c = destination[2];
        require(!field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("COPY.C"),
                "a concrete element read back symbolic");

        // Arrays.copyOf, the growth of every buffer, is the same copy.
        char[] grown = Arrays.copyOf(source, 16);
        sink.c = grown[1];
        require(field(sink, "c", "C", Character.valueOf(sink.c))
                        .contains("COPY.C"), "copyOf lost the value");

        // A tracked destination element: versioned by the copy, joined.
        int[] cells = new int[2];
        cells[0] = in.n;
        int[] replacement = {5, 6};
        System.arraycopy(replacement, 0, cells, 0, 2);
        sink.i = cells[0];
        String joined = field(sink, "i", "I", Integer.valueOf(sink.i));
        String element = System.getSharedElementVersions(cells, 0);
        require(sink.i == 5 && joined.contains("\"observedExact\":true")
                        && joined.contains("\"writerSetComplete\":true")
                        && !joined.contains("UNOBSERVED"),
                "the copied-over element read is not its copy: " + joined);
        require(count(element, "\"writerContextId\"") == 2
                        && !element.contains("UNOBSERVED")
                        && element.contains("\"writerSetComplete\":true"),
                "the copy published no version: " + element);

        // Overlapping ranges read the source before it is overwritten.
        int[] shift = new int[4];
        shift[1] = in.n;
        System.arraycopy(shift, 1, shift, 0, 3);
        sink.i = shift[0];
        require(field(sink, "i", "I", Integer.valueOf(sink.i))
                        .contains("COPY.N"), "the shift lost its value");

        // boolean[] and byte[] written symbolically read back as written.
        boolean[] flags = new boolean[2];
        flags[0] = in.flag;
        sink.z = flags[0];
        String flag = field(sink, "z", "Z", Boolean.valueOf(sink.z));
        require(flag.contains("COPY.FLAG") && flag.contains("\"_java_type\":\"Z\""),
                "the boolean element did not round-trip: " + flag);
        byte[] bytes = new byte[2];
        bytes[0] = (byte) in.n;
        sink.b = bytes[0];
        require(field(sink, "b", "B", Byte.valueOf(sink.b)).contains("COPY.N"),
                "the byte element did not round-trip");

        // A store no hook sees: the recorded write is stale, the read is
        // the heap's word.
        char[] stale = new char[2];
        stale[0] = in.c;
        System.pauseConcolicPathCondition();
        stale[0] = 'q';
        System.resumeConcolicPathCondition();
        sink.c = stale[0];
        require(sink.c == 'q' && !field(sink, "c", "C",
                        Character.valueOf(sink.c)).contains("COPY.C"),
                "a stale recorded write was read back");

        System.endConcolic();
        System.out.println("RegionArrayCopySmoke OK");
    }

    private static String field(Sink sink, String name, String descriptor,
                                Object value) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                name, descriptor, value);
    }

    private static int count(String value, String needle) {
        int result = 0;
        int offset = 0;
        while ((offset = value.indexOf(needle, offset)) >= 0) {
            result++;
            offset += needle.length();
        }
        return result;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
