public final class RegionBranchEventApiSmoke {
    private static final class Input {
        int value = 1;
        long wide = 2L;
        boolean flag = true;
    }

    private static void check(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }

    private static int occurrences(String text, String needle) {
        int count = 0;
        int cursor = 0;
        while ((cursor = text.indexOf(needle, cursor)) >= 0) {
            count++;
            cursor += needle.length();
        }
        return count;
    }

    public static void main(String[] args) throws Exception {
        Input input = new Input();
        long status = System.startConcolicRegion(
                "REGION.BRANCH.SMOKE", "ACT.BRANCH.SMOKE");
        check(status == 0L, "region start rejected");
        System.symbolizeField(input, "value", "branch_value");
        System.symbolizeField(input, "wide", "branch_wide");
        System.symbolizeField(input, "flag", "branch_flag");

        Integer boxedInt = Integer.valueOf(input.value);
        Boolean boxedBoolean = Boolean.valueOf(input.flag);
        String intExpression = System.getSymbolicExpression(boxedInt);
        String booleanExpression = System.getSymbolicExpression(boxedBoolean);
        check(intExpression.contains("branch_value"),
                "boxed int lost its primitive shadow: " + intExpression);
        check(booleanExpression.contains("branch_flag"),
                "boxed boolean lost its primitive shadow: "
                        + booleanExpression);

        long first = System.markConcolicBranch("SAME_SHAPE.1", 1);
        boolean firstOutcome;
        if (input.value > 0) {
            firstOutcome = true;
        } else {
            firstOutcome = false;
        }
        check(first > 0L && firstOutcome, "first branch marker failed");

        long second = System.markConcolicBranch("SAME_SHAPE.2", 1);
        boolean secondOutcome;
        if (input.value > 0) {
            secondOutcome = true;
        } else {
            secondOutcome = false;
        }
        check(second > first && secondOutcome,
                "second same-shape branch marker failed");

        for (int occurrence = 1; occurrence <= 2; occurrence++) {
            long loopEvent = System.markConcolicBranch(
                    "LOOP.SAME.SITE", occurrence);
            boolean loopOutcome;
            if (input.value >= occurrence) {
                loopOutcome = true;
            } else {
                loopOutcome = false;
            }
            check(loopEvent > second,
                    "loop branch marker failed at " + occurrence);
            check(occurrence == 1 ? loopOutcome : !loopOutcome,
                    "loop branch outcome changed");
        }

        long wideEvent = System.markConcolicBranch("LCMP.BRANCH", 1);
        boolean wideOutcome;
        if (input.wide >= 0L) {
            wideOutcome = true;
        } else {
            wideOutcome = false;
        }
        check(wideEvent > second && wideOutcome,
                "lcmp branch marker failed");

        String beforePause = System.getConcolicBranchEvents();
        System.pauseConcolicPathCondition();
        long pausedEvent = System.markConcolicBranch("PAUSED.BRANCH", 1);
        if (input.value > 0) {
            input.value += 0;
        }
        System.resumeConcolicPathCondition();
        String afterPause = System.getConcolicBranchEvents();
        check(pausedEvent == 0L, "paused marker must be rejected");
        check(beforePause.equals(afterPause),
                "paused bookkeeping changed branch events");

        final String[] foreignEvents = new String[1];
        final long[] foreignMarker = new long[1];
        Thread foreign = new Thread(new Runnable() {
            @Override
            public void run() {
                foreignMarker[0] = System.markConcolicBranch(
                        "FOREIGN.BRANCH", 1);
                foreignEvents[0] = System.getConcolicBranchEvents();
            }
        }, "branch-event-foreign");
        foreign.start();
        foreign.join();
        check(foreignMarker[0] == 0L,
                "foreign thread acquired the owner marker");
        check(foreignEvents[0].contains("\"active\":false")
                        && foreignEvents[0].contains("\"events\":[]"),
                "foreign thread observed owner events: " + foreignEvents[0]);

        String events = System.getConcolicBranchEvents();
        check(events.contains("\"kind\":\"CONCOLIC_THREAD_BRANCH_EVENTS\""),
                "missing branch event envelope: " + events);
        check(events.contains("\"regionId\":\"REGION.BRANCH.SMOKE\""),
                "missing region ownership: " + events);
        check(events.contains("\"activationId\":\"ACT.BRANCH.SMOKE\""),
                "missing activation ownership: " + events);
        check(events.contains("\"siteId\":\"SAME_SHAPE.1\"")
                        && events.contains("\"siteId\":\"SAME_SHAPE.2\""),
                "same-shape sites were not distinguished: " + events);
        check(events.contains("\"siteId\":\"LOOP.SAME.SITE\","
                        + "\"occurrence\":1")
                        && events.contains("\"siteId\":\"LOOP.SAME.SITE\","
                        + "\"occurrence\":2"),
                "loop occurrences were not distinguished: " + events);
        check(events.contains("\"siteId\":\"LCMP.BRANCH\""),
                "lcmp event is absent: " + events);
        check(!events.contains("PAUSED.BRANCH")
                        && !events.contains("FOREIGN.BRANCH"),
                "non-owner/paused event leaked into owner context: " + events);
        check(occurrences(events,
                "\"authority\":\"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1\"")
                        == 5,
                "expected five exact branch events: " + events);
        check(occurrences(events, "\"conditionCount\":1") == 5,
                "every symbolic if must own one PC index: " + events);
        check(events.contains("\"conditionIndices\":[0]")
                        && events.contains("\"conditionIndices\":[1]")
                        && events.contains("\"conditionIndices\":[4]"),
                "PC indices are not exact/monotonic: " + events);

        String summary = System.finishConcolicRegion();
        check(summary.contains("\"threadContextId\":")
                        && summary.contains("\"branchEvents\":"),
                "final summary omitted thread branch context: " + summary);
        String afterFinish = System.getConcolicBranchEvents();
        check(afterFinish.contains("\"active\":false")
                        && afterFinish.contains("\"events\":[]"),
                "branch context survived finish: " + afterFinish);
        System.out.println("RegionBranchEventApiSmoke passed");
    }
}
