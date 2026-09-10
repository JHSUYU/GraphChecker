/**
 * Contract smoke for bounded shared reads: every retained writer remains an
 * SMT-selectable expression.
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
        require(System.selectSharedFieldCarrier(holder, Holder.class.getName(),
                "shared", "I") > 0L, "carrier selection rejected");
        require(System.selectSharedFieldCarrier(holder, Holder.class.getName(),
                "shared", "I") == 0L, "carrier selection is not idempotent");

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
        require(multiple.contains("\"exactlyOne\":[\"rf1\",\"rf2\"]"),
                multiple);
        require(multiple.contains("READ.INIT"), multiple);
        require(multiple.contains("READ.NEXT"), multiple);
        require(multiple.contains("\"pathGuard\":"), multiple);

        String evidence = System.getSharedFieldVersions(
                holder, Holder.class.getName(), "shared", "I");
        require(evidence.contains("\"writerSetComplete\":true"), evidence);
        require(count(evidence, "\"fieldVersionId\"") == 2, evidence);
        require(lastRead(evidence).contains("\"candidateCount\":2"), evidence);

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

    private static String lastRead(String json) {
        int at = json.lastIndexOf("\"readEventId\"");
        require(at >= 0, "no read was recorded: " + json);
        return json.substring(at);
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
