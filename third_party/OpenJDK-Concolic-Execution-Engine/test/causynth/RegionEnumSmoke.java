import java.util.Locale;

/**
 * The enum model (SymEnum): a constant Enum.valueOf chose by a symbolic
 * name is that name.  Solr's shape: a replica's state parsed from a String
 * (Replica.State.getState: valueOf of its upper case), then compared with a
 * constant (==, !=, equals), named (name(), an overridden toString() through
 * super.toString()), and switched on (javac's switch map read at its
 * ordinal).  Each decision's condition is over the name; a compare of two
 * objects no valueOf named stays a reference compare.
 */
public final class RegionEnumSmoke {
    enum State {
        ACTIVE, DOWN, RECOVERING;

        @Override
        public String toString() {
            return super.toString().toLowerCase(Locale.ROOT);
        }

        static State getState(String text) {
            return text == null ? null
                    : State.valueOf(text.toUpperCase(Locale.ROOT));
        }
    }

    private static final class Input {
        String state = new String("down");
    }

    private static final class Sink {
        State state;
    }

    public static void main(String[] args) {
        Input input = new Input();
        Sink sink = new Sink();
        require(System.startConcolicRegion("REGION.enum", "TASK.enum") == 0L,
                "region start rejected");
        System.symbolizeField(input, "state", "STATE");
        sink.state = State.getState(input.state);
        State state = sink.state;

        int compared = 0;
        if (state != State.ACTIVE) compared |= 1;
        if (state == State.DOWN) compared |= 2;
        if (state.equals(State.RECOVERING)) compared |= 4;
        String compares = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);

        String name = state.name();
        String text = state.toString();
        int ordinal = state.ordinal();
        int arm;
        switch (state) {
            case ACTIVE:
                arm = 1;
                break;
            case DOWN:
                arm = 2;
                break;
            default:
                arm = 3;
                break;
        }
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String summary = System.finishConcolicRegion();

        System.out.println("COMPARES " + compares);
        System.out.println("PATH " + path);
        require(compared == 3 && "DOWN".equals(name) && "down".equals(text)
                        && ordinal == 1 && arm == 2,
                "the model changed what the program computed");
        require(count(compares, "\"_name\":\"equals\"") >= 3
                        && compares.contains("java/lang/Enum valueOf")
                        && compares.contains("Y_L'String'_ACTIVE")
                        && compares.contains("Y_L'String'_DOWN")
                        && compares.contains("Y_L'String'_RECOVERING")
                        && compares.contains("STATE"),
                "a compare of a valueOf constant is no equals of names: "
                        + compares);
        require(path.contains("java/lang/Enum ordinal")
                        && path.contains("\"operation\":\"READ\"")
                        && path.contains("\"operation\":\"SNAPSHOT_BASE\""),
                "the switch is no read of its map at the ordinal: " + path);
        require(summary.length() > 0, "no summary");
        System.out.println("CAUSYNTH_REGION_ENUM_SMOKE_OK");
    }

    private static int count(String text, String needle) {
        int found = 0;
        for (int at = text.indexOf(needle); at >= 0;
             at = text.indexOf(needle, at + 1)) {
            found++;
        }
        return found;
    }

    private static void require(boolean condition, String message) {
        if (!condition) throw new AssertionError(message);
    }
}
