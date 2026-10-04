import java.util.ArrayList;
import java.util.List;

/** An INDEXED SIZE is built over the nearest state that is not an element
 *  set (ContainerExpression::size_source): an array store or a set()
 *  replaces an element and never changes a size, so `a.length` and
 *  `list.size()` skip it; an APPEND, INSERT, REMOVE, POLL or CLEAR changes
 *  it and is kept.  hdfs-adhoc-03's packet buffer, whose length is no
 *  constant, took a checksum per chunk, and its `buf.length` carried every
 *  checksum ever written into it to each branch on it. */
public final class RegionIndexedSizeSmoke {
    private static final class Input {
        int value = 5;
        List<Integer> list = new ArrayList<Integer>();

        Input() {
            list.add(Integer.valueOf(13));
            list.add(Integer.valueOf(17));
        }
    }

    private static final class Sink {
        int value;
    }

    private static final String SIZE = "\"operation\":\"SIZE\"";
    private static final String WRITE = "\"operation\":\"WRITE\"";

    public static void main(String[] args) {
        Input input = new Input();
        Sink sink = new Sink();
        require(System.startConcolicRegion("REGION.indexed-size",
                "TASK.indexed-size") == 0L, "region start rejected");
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "SIZE_SOURCE");
        System.symbolizeField(input, "list", "size_list");

        // An array of no constant length, its elements written symbolically.
        byte[] buf = new byte[input.value + 16];
        for (int i = 0; i < 8; i++) buf[i] = (byte) (input.value + i);
        sink.value = buf.length;
        String length = field(sink);
        boolean fits = 4 + 8 <= buf.length;

        // A set() over an append: the size is the append's.
        input.list.add(Integer.valueOf(19));
        input.list.set(0, Integer.valueOf(input.value));
        sink.value = input.list.size();
        String appended = field(sink);

        // A set() over a removal: the size is the removal's.
        input.list.remove(1);
        input.list.set(1, Integer.valueOf(input.value + 1));
        sink.value = input.list.size();
        String removed = field(sink);
        System.finishConcolicRegion();

        require(fits && buf.length == 21, "the array is not the one built");
        require(length.contains(SIZE) && length.contains("SIZE_SOURCE")
                        && length.contains("\"operation\":\"STATE\"")
                        && !length.contains(WRITE),
                "an array's length is not its STATE root's: " + length);
        require(appended.contains(SIZE)
                        && appended.contains("\"operation\":\"APPEND\"")
                        && !appended.contains(WRITE),
                "a list's size skips no set() or skips its append: "
                        + appended);
        require(removed.contains(SIZE)
                        && removed.contains("\"operation\":\"REMOVE\"")
                        && removed.contains("\"operation\":\"APPEND\"")
                        && count(removed, WRITE) == 1,
                "a list's size is not its removal's: " + removed);
        System.out.println("CAUSYNTH_REGION_INDEXED_SIZE_SMOKE_OK");
    }

    private static String field(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + needle.length())) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
