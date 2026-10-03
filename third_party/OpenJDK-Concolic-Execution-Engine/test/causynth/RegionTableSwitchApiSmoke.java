/** Verifies exact tableswitch path predicates and VM branch-event ownership. */
public final class RegionTableSwitchApiSmoke {
    private static final class Input {
        private int value;

        Input(int value) {
            this.value = value;
        }
    }

    public static void main(String[] args) {
        Trace below = execute(-1, "table_switch_below");
        require(count(below.path, "\"_op\":\"!=\"") == 3
                        && below.path.contains("Y_I_1")
                        && below.path.contains("Y_I_2")
                        && below.path.contains("Y_I_3"), below.path);
        requireExactEvent(below.events, "TABLE.table_switch_below", false,
                3);

        Trace above = execute(9, "table_switch_above");
        require(count(above.path, "\"_op\":\"!=\"") == 3
                        && above.path.contains("Y_I_1")
                        && above.path.contains("Y_I_2")
                        && above.path.contains("Y_I_3"), above.path);
        requireExactEvent(above.events, "TABLE.table_switch_above", false,
                3);

        Trace selected = execute(2, "table_switch_selected");
        require(selected.path.contains("\"_op\":\"==\"")
                        && selected.path.contains("Y_I_2"), selected.path);
        requireExactEvent(selected.events, "TABLE.table_switch_selected",
                true, 1);
        System.out.println("CAUSYNTH_REGION_TABLE_SWITCH_API_SMOKE_OK");
    }

    private static Trace execute(int value, String symbol) {
        Input input = new Input(value);
        long status = System.startConcolicRegion("REGION.table-switch",
                "ACT." + symbol);
        require(status == 0L, "region start rejected");
        System.symbolizeField(input, "value", symbol);
        long event = System.markConcolicBranch("TABLE." + symbol, 1);
        int result;
        switch (input.value) {
            case 1:
                result = 11;
                break;
            case 2:
                result = 12;
                break;
            case 3:
                result = 13;
                break;
            default:
                result = 19;
                break;
        }
        require(event > 0L, "branch marker rejected");
        require(result == (value == 1 ? 11 : value == 2 ? 12
                : value == 3 ? 13 : 19), "wrong tableswitch arm");
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();
        require(summary.contains(
                "\"pathConditionAuthority\":"
                        + "\"VM_SELECTED_BRANCHES_V2\""),
                summary);
        return new Trace(summary, events, path);
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

    private static final class Trace {
        final String summary;
        final String events;
        final String path;

        Trace(String summary, String events, String path) {
            this.summary = summary;
            this.events = events;
            this.path = path;
        }
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
