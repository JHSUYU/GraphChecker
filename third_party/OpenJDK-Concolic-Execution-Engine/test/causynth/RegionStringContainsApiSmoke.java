/**
 * Verifies that String.contains keeps the symbolic receiver and needle and
 * records both the taken and non-taken Java branch predicates.
 */
public final class RegionStringContainsApiSmoke {
    private static final class Input {
        private String text = new String("alpha-needle-omega");
    }

    public static void main(String[] args) {
        Input input = new Input();
        System.startConcolicRegion("REGION.string-contains",
                "ACT.string-contains");
        System.symbolizeField(input, "text", "string_contains_text");

        // Soot lowers the invoke into an assignment and inserts the marker at
        // the subsequent IfStmt.  Keep the smoke in the same shape: the VM
        // predicate is produced first, then claimed by the exact branch event.
        boolean positive = input.text.contains("needle");
        long positiveEvent = System.markConcolicBranch(
                "STRING.CONTAINS.POSITIVE", 1);
        if (positive) {
            // Record the positive contains predicate.
        }
        boolean negative = input.text.contains("absent");
        long negativeEvent = System.markConcolicBranch(
                "STRING.CONTAINS.NEGATIVE", 1);
        if (negative) {
            throw new AssertionError("unexpected concrete contains result");
        }

        // Computing a symbolic predicate is not itself a path decision.  If
        // the result is ignored, it must neither enter the path condition nor
        // become the condition of an unrelated later concrete branch.
        input.text.contains("ignored");
        long unrelatedEvent = System.markConcolicBranch(
                "STRING.CONTAINS.UNRELATED", 1);
        if (args.length >= 0) {
            // This branch deliberately has no symbolic input.
        }

        require(positiveEvent > 0L && negativeEvent > positiveEvent
                        && unrelatedEvent > negativeEvent,
                "contains branch markers were rejected");

        String events = System.getConcolicBranchEvents();
        require(exactCondition(events, "STRING.CONTAINS.POSITIVE", 1, 0),
                events);
        require(exactCondition(events, "STRING.CONTAINS.NEGATIVE", 1, 1),
                events);
        require(noCondition(events, "STRING.CONTAINS.UNRELATED", 1), events);
        require(count(events, "\"conditionCount\":1") == 2, events);
        require(count(events, "\"conditionCount\":0") == 1, events);

        String summary = System.finishConcolicRegion();
        require(summary.contains("\"regionId\":\"REGION.string-contains\""),
                summary);
        require(summary.contains("string_contains_text"), summary);
        require(count(summary, "\"_name\":\"contains\"") == 2, summary);
        require(summary.contains("\"_is_not\":false"), summary);
        require(summary.contains("\"_is_not\":true"), summary);
        require(summary.contains("Y_L'String'_needle"), summary);
        require(summary.contains("Y_L'String'_absent"), summary);
        require(!summary.contains("Y_L'String'_ignored"), summary);
        if (Boolean.getBoolean("causynth.smoke.dump")) {
            System.out.println(summary);
        }
        System.out.println("CAUSYNTH_REGION_STRING_CONTAINS_API_SMOKE_OK");
    }

    private static boolean exactCondition(String events, String site,
                                          int occurrence, int index) {
        String identity = "\"siteId\":\"" + site
                + "\",\"occurrence\":" + occurrence;
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return false;
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        if (start < 0 || end < start) return false;
        String event = events.substring(start, end + 1);
        return event.contains("\"conditionIndices\":[" + index + "]")
                && event.contains("\"conditionCount\":1");
    }

    private static boolean noCondition(String events, String site,
                                       int occurrence) {
        String identity = "\"siteId\":\"" + site
                + "\",\"occurrence\":" + occurrence;
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return false;
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        if (start < 0 || end < start) return false;
        String event = events.substring(start, end + 1);
        return event.contains("\"conditionIndices\":[]")
                && event.contains("\"conditionCount\":0");
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

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
