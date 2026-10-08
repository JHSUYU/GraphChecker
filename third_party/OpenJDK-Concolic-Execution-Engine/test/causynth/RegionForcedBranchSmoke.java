/**
 * System.forceNextConcolicBranch: the marked conditional takes the forced
 * arm whatever its operands decide, its event states {@code forced} and the
 * concrete answer it overrode, and the condition it records is the forced
 * arm's.  Only the marked branch of the marker's own frame is forced, once;
 * a refused marker drops the directive.
 */
public final class RegionForcedBranchSmoke {
    private static final class Input {
        int value = 1;
        int other = 10;
    }

    private static final int ARM = 1;
    private static final int CASE = 2;
    private static final int DEFAULT = 3;

    private static void check(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }

    /** The one event of {@code site} in a branch-event envelope. */
    private static String event(String events, String site) {
        int at = events.indexOf("\"siteId\":\"" + site + "\"");
        check(at >= 0, "no event at " + site + ": " + events);
        int start = events.lastIndexOf('{', at);
        int end = events.indexOf('}', at);
        return events.substring(start, end + 1);
    }

    /** A branch in a callee: no marker of its frame, so never forced. */
    private static boolean helper(int value) {
        if (value > 100) {
            return true;
        }
        return false;
    }

    public static void main(String[] args) throws Exception {
        Input input = new Input();
        check(System.startConcolicRegion("REGION.FORCED.SMOKE",
                "ACT.FORCED.SMOKE") == 0L, "region start rejected");
        System.symbolizeField(input, "value", "forced_value");
        System.symbolizeField(input, "other", "forced_other");

        // javac jumps over the then-block when value <= 100: the jump arm
        // is the healthy one here, so falling through (0) is forced.
        check(System.forceNextConcolicBranch(ARM, 0) == 0,
                "the forcing was refused");
        // The marked branch is the next one of this frame: nothing that
        // branches stands between a marker and it.
        long outer = System.markConcolicBranch("FORCED.OUTER", 1);
        long inner = 0L;
        boolean thrown = false;
        try {
            if (input.value > 100) {
                System.forceNextConcolicBranch(ARM, 0);
                inner = System.markConcolicBranch("FORCED.INNER", 1);
                if (input.value < -5) {
                    throw new IllegalStateException("forced throw");
                }
            }
        } catch (IllegalStateException expected) {
            thrown = true;
        }
        check(outer > 0L && inner > outer && thrown,
                "the forced path did not reach the throw");

        // Consumed by one marker: the next marked branch is the run's.
        long plain = System.markConcolicBranch("PLAIN", 1);
        boolean plainOutcome = input.value > 100;
        check(plain > 0L && !plainOutcome, "an unforced branch was forced");

        // A refused marker drops the directive it was asked of.
        check(System.forceNextConcolicBranch(ARM, 0) == 0, "refused");
        System.pauseConcolicPathCondition();
        check(System.markConcolicBranch("REFUSED", 1) == 0L,
                "a paused marker was taken");
        System.resumeConcolicPathCondition();
        long afterRefusal = System.markConcolicBranch("AFTER.REFUSAL", 1);
        boolean afterRefusalOutcome = input.value > 100;
        check(afterRefusal > 0L && !afterRefusalOutcome,
                "a refused marker's forcing reached a later branch");

        // A callee's branch is not the marker's: the helper decides as its
        // operands do, the marked branch after it is forced.
        check(System.forceNextConcolicBranch(ARM, 0) == 0, "refused");
        long framed = System.markConcolicBranch("FRAMED", 1);
        boolean helped = helper(input.value);
        boolean framedOutcome = false;
        if (input.value > 100) {
            framedOutcome = true;
        }
        check(framed > 0L && !helped && framedOutcome,
                "the forcing reached another frame's branch");

        // A tableswitch to a case, then to its default.
        check(System.forceNextConcolicBranch(CASE, 3) == 0, "refused");
        System.markConcolicBranch("TABLE.CASE", 1);
        String table;
        switch (input.value) {
            case 1: table = "one"; break;
            case 2: table = "two"; break;
            case 3: table = "three"; break;
            default: table = "other";
        }
        check("three".equals(table), "tableswitch not forced: " + table);
        check(System.forceNextConcolicBranch(DEFAULT, 0) == 0, "refused");
        System.markConcolicBranch("TABLE.DEFAULT", 1);
        switch (input.value) {
            case 1: table = "one"; break;
            case 2: table = "two"; break;
            case 3: table = "three"; break;
            default: table = "other";
        }
        check("other".equals(table), "tableswitch default: " + table);

        // A lookupswitch to a case, then to its default.
        check(System.forceNextConcolicBranch(CASE, 1000) == 0, "refused");
        System.markConcolicBranch("LOOKUP.CASE", 1);
        String lookup;
        switch (input.value) {
            case 10: lookup = "ten"; break;
            case 1000: lookup = "thousand"; break;
            default: lookup = "other";
        }
        check("thousand".equals(lookup), "lookupswitch: " + lookup);
        check(System.forceNextConcolicBranch(DEFAULT, 0) == 0, "refused");
        System.markConcolicBranch("LOOKUP.DEFAULT", 1);
        switch (input.other) {
            case 10: lookup = "ten"; break;
            case 1000: lookup = "thousand"; break;
            default: lookup = "other";
        }
        check("other".equals(lookup), "lookupswitch default: " + lookup);
        check(System.forceNextConcolicBranch(9, 0) == -2,
                "an unknown kind was taken");

        String events = System.getConcolicBranchEvents();
        String outerEvent = event(events, "FORCED.OUTER");
        check(outerEvent.contains("\"outcome\":false")
                        && outerEvent.contains("\"forced\":true")
                        && outerEvent.contains("\"concrete\":1")
                        && outerEvent.contains("\"conditionCount\":1"),
                "the forced event: " + outerEvent);
        check(event(events, "FORCED.INNER").contains("\"forced\":true"),
                "the nested forced event: " + events);
        for (String site : new String[] {"PLAIN", "AFTER.REFUSAL"}) {
            check(!event(events, site).contains("forced"),
                    site + " states a forcing: " + events);
        }
        check(!events.contains("REFUSED"), "a refused marker left an event");
        check(event(events, "FRAMED").contains("\"forced\":true")
                        && event(events, "FRAMED").contains("\"concrete\":1"),
                "the framed event: " + events);
        check(event(events, "TABLE.CASE").contains("\"forced\":true")
                        && event(events, "TABLE.CASE")
                        .contains("\"concrete\":1"),
                "the table case event: " + events);
        check(event(events, "TABLE.DEFAULT").contains("\"forced\":true")
                        && event(events, "TABLE.DEFAULT")
                        .contains("\"outcome\":false"),
                "the table default event: " + events);
        check(event(events, "LOOKUP.CASE").contains("\"forced\":true")
                        && event(events, "LOOKUP.CASE")
                        .contains("\"outcome\":true"),
                "the lookup case event: " + events);
        check(event(events, "LOOKUP.DEFAULT").contains("\"forced\":true")
                        && event(events, "LOOKUP.DEFAULT")
                        .contains("\"concrete\":10"),
                "the lookup default event: " + events);

        // The forced arm's condition is the one recorded: value > 100 held
        // on the outer branch's path, though the run's value is 1.
        String path = System.getPathCondition();
        check(path.contains("forced_value"), "no condition recorded: " + path);
        System.finishConcolicRegion();
        System.out.println("RegionForcedBranchSmoke passed");
    }
}
