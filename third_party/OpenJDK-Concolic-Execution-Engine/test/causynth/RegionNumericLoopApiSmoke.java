/**
 * Exercises the exact VM branch-event ownership used by bounded numeric
 * path exploration.  The loop starts from a symbolic int so that the iinc
 * bytecode must preserve its shadow across the second iteration and exit.
 */
public final class RegionNumericLoopApiSmoke {
    private static final class Input {
        private long wide = 9L;
        private double ratio = 2.5D;
        private int loopStart = 1;
    }

    public static void main(String[] args) {
        Input input = new Input();
        require(!Double.isNaN(input.ratio)
                        && !Double.isInfinite(input.ratio),
                "the loop smoke intentionally uses an ordinary finite double");

        long status = System.startConcolicRegion("REGION.numeric-loop",
                "ACT.numeric-loop");
        require(status == 0L, "region start rejected");
        System.symbolizeField(input, "wide", "numeric_loop_wide");
        System.symbolizeField(input, "ratio", "numeric_loop_ratio");
        System.symbolizeField(input, "loopStart", "numeric_loop_start");

        long longEvent = System.markConcolicBranch("NUMERIC.LONG", 1);
        boolean longOutcome;
        if (input.wide >= 7L) {
            longOutcome = true;
        } else {
            longOutcome = false;
        }
        require(longEvent > 0L && longOutcome,
                "symbolic long branch was not taken");

        long doubleEvent = System.markConcolicBranch("NUMERIC.DOUBLE", 1);
        boolean doubleOutcome;
        if (input.ratio < 3.0D) {
            doubleOutcome = true;
        } else {
            doubleOutcome = false;
        }
        require(doubleEvent > longEvent && doubleOutcome,
                "finite symbolic double branch was not taken");

        int loopOccurrence = 0;
        int bodyCount = 0;
        for (int cursor = input.loopStart; ; cursor++) {
            loopOccurrence++;
            System.markConcolicBranch(
                    "NUMERIC.LOOP.GUARD", loopOccurrence);
            if (cursor >= 3) {
                break;
            }
            bodyCount++;
        }
        require(bodyCount == 2 && loopOccurrence == 3,
                "bounded loop did not expose two iterations plus its exit");

        // A concrete-only branch must remain visible as an event with no
        // condition index.  Import/worklist admission can then reject it
        // explicitly instead of accidentally reusing a previous witness.
        long concreteEvent = System.markConcolicBranch(
                "NUMERIC.UNMODELED.CONCRETE", 1);
        if (bodyCount != 2) {
            throw new AssertionError("unreachable concrete branch");
        }
        require(concreteEvent > doubleEvent,
                "concrete branch marker rejected");

        String events = System.getConcolicBranchEvents();
        require(exactCondition(events, "NUMERIC.LONG", 1, 0), events);
        require(exactCondition(events, "NUMERIC.DOUBLE", 1, 1), events);
        require(exactCondition(events, "NUMERIC.LOOP.GUARD", 1, 2), events);
        require(exactCondition(events, "NUMERIC.LOOP.GUARD", 2, 3), events);
        require(exactCondition(events, "NUMERIC.LOOP.GUARD", 3, 4), events);
        require(emptyCondition(events, "NUMERIC.UNMODELED.CONCRETE", 1),
                events);
        require(count(events, "\"conditionCount\":1") == 5, events);
        require(count(events, "\"conditionCount\":0") == 1, events);
        require(count(events, "VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1")
                        == 6,
                events);

        String summary = System.finishConcolicRegion();
        String longCondition = arrayObject(summary, "\"pathCondition\":[",
                0);
        String doubleCondition = arrayObject(summary,
                "\"pathCondition\":[", 1);
        String loopFirst = arrayObject(summary, "\"pathCondition\":[", 2);
        String loopSecond = arrayObject(summary, "\"pathCondition\":[", 3);
        String loopExit = arrayObject(summary, "\"pathCondition\":[", 4);

        require(longCondition.contains("numeric_loop_wide")
                        && longCondition.contains("\"_java_type\":\"J\""),
                "long condition lost its typed field symbol: "
                        + longCondition);
        require(doubleCondition.contains("numeric_loop_ratio")
                        && doubleCondition.contains(
                        "\"_java_type\":\"D\""),
                "double condition lost its typed field symbol: "
                        + doubleCondition);
        require(loopFirst.contains("numeric_loop_start"),
                "first loop guard lost its symbolic start: " + loopFirst);
        require(loopSecond.contains("numeric_loop_start")
                        && loopSecond.contains("Y_I_1"),
                "iinc did not propagate into the second loop guard: "
                        + loopSecond);
        require(loopExit.contains("numeric_loop_start")
                        && count(loopExit, "Y_I_1") >= 2,
                "iinc did not propagate through the loop exit: " + loopExit);
        require(summary.contains("\"siteId\":\"NUMERIC.LOOP.GUARD\","
                        + "\"occurrence\":3"),
                "final summary lost the loop exit occurrence: " + summary);
        require(summary.contains("\"siteId\":\"NUMERIC.UNMODELED.CONCRETE\"")
                        && summary.contains("\"conditionIndices\":[]"),
                "final summary did not preserve the fail-closed event: "
                        + summary);

        if (Boolean.getBoolean("causynth.smoke.dump")) {
            System.out.println(summary);
        }
        System.out.println("CAUSYNTH_REGION_NUMERIC_LOOP_API_SMOKE_OK");
    }

    private static boolean exactCondition(String events, String site,
                                          int occurrence, int index) {
        String event = event(events, site, occurrence);
        return event.contains("\"conditionIndices\":[" + index + "]")
                && event.contains("\"conditionCount\":1");
    }

    private static boolean emptyCondition(String events, String site,
                                          int occurrence) {
        String event = event(events, site, occurrence);
        return event.contains("\"conditionIndices\":[]")
                && event.contains("\"conditionCount\":0");
    }

    private static String event(String events, String site, int occurrence) {
        String identity = "\"siteId\":\"" + site + "\",\"occurrence\":"
                + occurrence;
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return "";
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        return start < 0 || end < start ? "" : events.substring(start,
                end + 1);
    }

    /** Returns one top-level object from a JSON array without test libraries. */
    private static String arrayObject(String json, String marker, int ordinal) {
        int markerOffset = json.indexOf(marker);
        if (markerOffset < 0) return "";
        int depth = 0;
        int current = -1;
        int start = -1;
        boolean quoted = false;
        boolean escaped = false;
        for (int index = markerOffset + marker.length(); index < json.length();
             index++) {
            char value = json.charAt(index);
            if (quoted) {
                if (escaped) {
                    escaped = false;
                } else if (value == '\\') {
                    escaped = true;
                } else if (value == '"') {
                    quoted = false;
                }
                continue;
            }
            if (value == '"') {
                quoted = true;
            } else if (value == '{') {
                if (depth == 0) {
                    current++;
                    start = index;
                }
                depth++;
            } else if (value == '}') {
                depth--;
                if (depth == 0 && current == ordinal) {
                    return json.substring(start, index + 1);
                }
            } else if (value == ']' && depth == 0) {
                break;
            }
        }
        return "";
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
