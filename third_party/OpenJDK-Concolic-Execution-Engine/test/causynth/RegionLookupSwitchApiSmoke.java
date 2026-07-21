/** Verifies sparse-switch arm semantics and multi-index default ownership. */
public final class RegionLookupSwitchApiSmoke {
    private static final class Input {
        private int value;

        Input(int value) {
            this.value = value;
        }
    }

    public static void main(String[] args) {
        Trace selected = execute(7, "lookup_selected");
        require(selected.result == 17, selected.summary);
        require(count(selected.summary,
                "\"_type\":\"BinaryExpression\"") == 1,
                selected.summary);
        require(selected.summary.contains("\"_op\":\"==\"")
                        && selected.summary.contains("Y_I_7"),
                selected.summary);
        requireExactEvent(selected.events, "LOOKUP.lookup_selected", true,
                1, "[0]");

        Trace defaultArm = execute(8, "lookup_default");
        require(defaultArm.result == 19, defaultArm.summary);
        require(count(defaultArm.summary,
                "\"_type\":\"BinaryExpression\"") == 3,
                defaultArm.summary);
        require(count(defaultArm.summary, "\"_op\":\"!=\"") == 3
                        && defaultArm.summary.contains("Y_I_-100")
                        && defaultArm.summary.contains("Y_I_7")
                        && defaultArm.summary.contains("Y_I_1000"),
                defaultArm.summary);
        requireExactEvent(defaultArm.events, "LOOKUP.lookup_default", false,
                3, "[0,1,2]");
        System.out.println("CAUSYNTH_REGION_LOOKUP_SWITCH_API_SMOKE_OK");
    }

    private static Trace execute(int value, String symbol) {
        Input input = new Input(value);
        long status = System.startConcolicRegion("REGION.lookup-switch",
                "ACT." + symbol);
        require(status == 0L, "region start rejected");
        System.symbolizeField(input, "value", symbol);
        long event = System.markConcolicBranch("LOOKUP." + symbol, 1);
        int result;
        switch (input.value) {
            case -100:
                result = 10;
                break;
            case 7:
                result = 17;
                break;
            case 1000:
                result = 18;
                break;
            default:
                result = 19;
                break;
        }
        require(event > 0L, "branch marker rejected");
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        require(summary.contains(symbol), summary);
        return new Trace(result, summary, events);
    }

    private static void requireExactEvent(String events, String site,
                                          boolean outcome, int count,
                                          String indices) {
        require(events.contains("\"siteId\":\"" + site + "\"")
                        && events.contains("\"occurrence\":1")
                        && events.contains("\"outcome\":" + outcome)
                        && events.contains("\"conditionIndices\":"
                        + indices)
                        && events.contains("\"conditionCount\":" + count),
                events);
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

    private static final class Trace {
        final int result;
        final String summary;
        final String events;

        Trace(int result, String summary, String events) {
            this.result = result;
            this.summary = summary;
            this.events = events;
        }
    }
}
