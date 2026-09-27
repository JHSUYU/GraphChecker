/**
 * Writers_W(l) at the recording: a thread outside every region writes
 * tracked state too (an HDFS IPC handler's updatePipeline rewrites a block's
 * generation stamp no region wrote).  Unversioned, a region's later read
 * resolved to the last version a region wrote -- a value the heap no longer
 * held.  The write is a concrete version with no writer attribution, and the
 * read resolves to it.
 */
public final class RegionUnattributedWriterSmoke {
    private static final class Block {
        long generationStamp = 1L;
    }

    private static final class Input {
        int value = 7;
    }

    private static final class Sink {
        long value;
        int slot;
    }

    public static void main(String[] args) throws Exception {
        final Block block = new Block();
        final int[] slots = new int[4];
        Input input = new Input();
        require(System.startConcolicRegion("REGION.unattributed-writer",
                "TASK.unattributed-writer") == 0L, "region start rejected");
        System.observeExactPrimitiveField(block, Block.class.getName(),
                "generationStamp", "J");
        block.generationStamp = 2L;
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "UNATTRIBUTED_SOURCE");
        // The first symbolic store shadows the array; the second, into a
        // shadowed array, starts slot 2's version log.
        slots[0] = input.value;
        slots[2] = input.value;

        Thread outside = new Thread(new Runnable() {
            @Override
            public void run() {
                block.generationStamp = 3L;
                slots[2] = 9;
            }
        });
        outside.start();
        outside.join();

        String versions = System.getSharedFieldVersions(block,
                Block.class.getName(), "generationStamp", "J");
        require(count(versions, "\"versionKind\":\"WRITE\"") == 2, versions);
        Sink read = new Sink();
        read.value = block.generationStamp;
        read.slot = slots[2];
        String field = System.getSymbolicFieldExpression(read,
                Sink.class.getName(), "value", "J", Long.valueOf(read.value));
        String slot = System.getSymbolicFieldExpression(read,
                Sink.class.getName(), "slot", "I", Integer.valueOf(read.slot));
        System.endConcolic();
        require(read.value == 3L && read.slot == 9,
                "the outside stores did not run");
        require(field.contains("\"Y_J_3\""),
                "the field read names no outside write: " + field);
        require(slot.contains("\"Y_I_9\""),
                "the slot read names no outside write: " + slot);
        System.out.println("RegionUnattributedWriterSmoke OK");
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
