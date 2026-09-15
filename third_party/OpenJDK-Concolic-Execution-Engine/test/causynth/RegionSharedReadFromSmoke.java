/**
 * Contract smoke for bounded shared reads.
 *
 * <p>One concrete execution performs one real read, and at that instant the
 * location held exactly one version.  The read node names that version and
 * carries its value; the writers the run did not read are retained in the
 * location's log, where a later question can still find them, and are not
 * republished as arms of the read.  {@code writerSetComplete} stays separate
 * coverage metadata about that log.</p>
 */
public final class RegionSharedReadFromSmoke {
    private static final class Holder {
        int shared = 7;
        int unselected;
    }

    private static final class Input {
        int value = 3;
    }

    private static final class Sink {
        int value;
    }

    public static void main(String[] args) {
        require(System.startConcolicRegion(
                "REGION.read-from", "TASK.read-from") == 0L,
                "region start rejected");

        Holder holder = new Holder();
        System.symbolizeExactField(holder, Holder.class.getName(), "shared",
                "I", "READ.INIT");

        Input input = new Input();
        System.symbolizeExactField(input, Input.class.getName(), "value",
                "I", "READ.NEXT");
        require(System.markConcolicBranch("READ.WRITE", 1) > 0L,
                "branch marker rejected");
        if (input.value > 0) {
            holder.shared = input.value + 1;
        }

        long secondReceipt = System.armSharedPrimitiveFieldRead(holder,
                Holder.class.getName(), "shared", "I", 23L);
        require(secondReceipt > 0L, "multi-writer read was not armed");
        require(System.armSharedPrimitiveFieldRead(holder,
                Holder.class.getName(), "shared", "I", 24L) == -6L,
                "duplicate pending read was admitted");
        require(holder.unselected == 0,
                "unrelated getfield consumed the selected read receipt");
        Sink second = new Sink();
        second.value = holder.shared;
        require(second.value == 23, "multi-writer concrete override lost: "
                + second.value);
        require(System.confirmSharedPrimitiveFieldRead(secondReceipt) > 0L,
                "multi-writer read did not consume its receipt");
        String multiple = expression(second);
        require(multiple.contains(
                "\"expressionAuthority\":\"VM_GUARDED_READ_FROM_V1\""),
                multiple);
        require(multiple.contains("\"writerSetComplete\":true"), multiple);
        // The value the read carries is the writer it observed, computed from
        // READ.NEXT.  The mint it did not read is not in the read at all.
        require(multiple.contains("READ.NEXT"), multiple);
        require(!multiple.contains("READ.INIT"), multiple);

        String evidence = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
        require(evidence.contains("\"selected\":true"), evidence);
        require(evidence.contains("\"writerSetComplete\":true"), evidence);
        // Both writers stay in the log -- one version entry each, and only a
        // version entry carries a writerContextId.
        require(count(evidence, "\"writerContextId\"") == 2, evidence);
        require(evidence.contains("READ.INIT"), evidence);
        require(evidence.contains("READ.NEXT"), evidence);
        // The version the read named is the newest retained one, and the
        // older one is named by no read.
        require(namesVersion(multiple, versionId(evidence, true)),
                "the read did not name the newest retained writer: "
                        + multiple + " over " + evidence);
        require(!namesVersion(multiple, versionId(evidence, false)),
                "the read published a writer it did not observe: " + multiple);
        // One read of this location, and only a read entry carries a reader.
        require(count(evidence, "\"readerContextId\"") == 1, evidence);

        String unselected = System.getSharedFieldVersions(holder,
                Holder.class.getName(), "unselected", "I");
        require(unselected.contains("\"selected\":false"), unselected);

        System.endConcolic();
        System.out.println("RegionSharedReadFromSmoke OK");
    }

    private static String expression(Sink sink) {
        return System.getSymbolicFieldExpression(sink, Sink.class.getName(),
                "value", "I", Integer.valueOf(sink.value));
    }

    /** Whether any read node in `json` names `versionId` as its observed one. */
    private static boolean namesVersion(String json, long versionId) {
        return json.contains("\"observedVersion\":{\"fieldVersionId\":"
                + versionId + ",");
    }

    /**
     * The newest (or oldest) entry of the `versions` array, which ends where
     * the read log begins.  Read from the log rather than assumed, so the
     * comparison below is between two things the VM said.
     */
    private static long versionId(String json, boolean newest) {
        int end = json.indexOf("],\"readLogTruncated\"");
        require(end >= 0, "no version log in " + json);
        String key = "\"fieldVersionId\":";
        int at = newest ? json.lastIndexOf(key, end) : json.indexOf(key);
        require(at >= 0 && at < end, "no versions in " + json);
        int from = at + key.length();
        int to = from;
        while (to < json.length() && json.charAt(to) >= '0'
                && json.charAt(to) <= '9') {
            to++;
        }
        require(to > from, json);
        return Long.parseLong(json.substring(from, to));
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
