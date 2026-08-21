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
        require(selected.path.contains("\"_op\":\"==\"")
                        && selected.path.contains("Y_I_7"), selected.path);
        requireExactEvent(selected.events, "LOOKUP.lookup_selected", true,
                1);

        Trace defaultArm = execute(8, "lookup_default");
        require(defaultArm.result == 19, defaultArm.summary);
        require(count(defaultArm.path, "\"_op\":\"!=\"") == 3
                        && defaultArm.path.contains("Y_I_-100")
                        && defaultArm.path.contains("Y_I_7")
                        && defaultArm.path.contains("Y_I_1000"),
                defaultArm.path);
        requireExactEvent(defaultArm.events, "LOOKUP.lookup_default", false,
                3);
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
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        require(summary.contains(
                "\"pathConditionAuthority\":"
                        + "\"VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1\""),
                summary);
        return new Trace(result, summary, events, path);
    }

    private static void requireExactEvent(String events, String site,
                                          boolean outcome, int count) {
        require(events.contains("\"siteId\":\"" + site + "\"")
                        && events.contains("\"occurrence\":1")
                        && events.contains("\"outcome\":" + outcome)
                        && events.contains("\"conditionIndices\":[")
                        && !events.contains("\"conditionIndices\":[]")
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
        final String path;

        Trace(int result, String summary, String events, String path) {
            this.result = result;
            this.summary = summary;
            this.events = events;
            this.path = path;
        }
    }
}
