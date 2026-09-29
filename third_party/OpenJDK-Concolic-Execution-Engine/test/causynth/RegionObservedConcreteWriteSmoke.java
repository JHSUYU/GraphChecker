/**
 * Contract smoke for an observed concrete store of a plain integral field.
 *
 * <p>A woven write site of a tracked field (SYMBOL-SCOPE F2) calls {@code
 * observeExactPrimitiveField} just before its store.  The value it stores is
 * concrete, and a concrete store is versioned only where a log exists, so the
 * observation is what starts the log: INITIAL, the value from before the
 * window, then the store as a WRITE.  A later read resolves over the log and
 * names that WRITE, which is what lets a reader in another occurrence join
 * the writer.  A field of the same object no write site observed stays
 * untracked.  A flag is observed as a counter is: a commit point's
 * {@code deleted}, set where a deletion policy let it go.</p>
 */
public final class RegionObservedConcreteWriteSmoke {
    private static final class Block {
        long generationStamp = 1L;
        long numBytes = 7L;
        boolean deleted;
    }

    private static final class Sink {
        long value;
        boolean flag;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion("REGION.observed-write",
                "TASK.observed-write") == 0L, "region start rejected");

        Block block = new Block();
        System.observeExactPrimitiveField(block, Block.class.getName(),
                "generationStamp", "J");
        block.generationStamp = 2L;
        block.numBytes = 8L;
        // A read site observes too; a log that stands is left alone.
        System.observeExactPrimitiveField(block, Block.class.getName(),
                "generationStamp", "J");
        Sink sink = new Sink();
        sink.value = block.generationStamp;
        require(sink.value == 2L, "the store did not run concretely");

        String evidence = System.getSharedFieldVersions(block,
                Block.class.getName(), "generationStamp", "J");
        require(evidence.contains("\"selected\":true"), evidence);
        require(evidence.contains("\"versionKind\":\"INITIAL\""), evidence);
        require(evidence.contains("\"versionKind\":\"WRITE\""), evidence);
        require(count(evidence, "\"versionKind\":\"INITIAL\"") == 1,
                evidence);
        require(count(evidence, "\"readerContextId\"") == 1, evidence);

        String read = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "value", "J", Long.valueOf(sink.value));
        require(read.contains(
                "\"expressionAuthority\":\"VM_GUARDED_READ_FROM_V1\""), read);
        require(read.contains("\"versionKind\":\"WRITE\""), read);

        System.observeExactPrimitiveField(block, Block.class.getName(),
                "deleted", "Z");
        block.deleted = true;
        sink.flag = block.deleted;
        require(sink.flag, "the flag's store did not run concretely");
        String flagged = System.getSharedFieldVersions(block,
                Block.class.getName(), "deleted", "Z");
        require(flagged.contains("\"selected\":true"), flagged);
        require(flagged.contains("\"versionKind\":\"INITIAL\""), flagged);
        require(flagged.contains("\"versionKind\":\"WRITE\""), flagged);
        String flagRead = System.getSymbolicFieldExpression(sink,
                Sink.class.getName(), "flag", "Z", Boolean.valueOf(sink.flag));
        require(flagRead.contains(
                "\"expressionAuthority\":\"VM_GUARDED_READ_FROM_V1\""),
                flagRead);

        String untouched = System.getSharedFieldVersions(block,
                Block.class.getName(), "numBytes", "J");
        require(untouched.contains("\"selected\":false"), untouched);

        System.endConcolic();
        System.out.println("RegionObservedConcreteWriteSmoke OK");
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
