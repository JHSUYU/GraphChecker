import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/**
 * The enum model (SymEnum): an enum constant is its name.  Solr's shape: a
 * replica's state parsed from a String (Replica.State.getState: valueOf of
 * its upper case), then compared with a constant (==, !=, equals), named
 * (name(), an overridden toString() through super.toString()), switched on
 * (javac's switch map read at its ordinal), tested in an EnumSet (its bit at
 * the ordinal), and used as a key of a map and a set that hold constants the
 * program put there -- each by its name.  A compare with another enum class
 * is decided by the class, with null is a reference test, and through a
 * tracked field read is over the read -- also when the field's writer stored
 * a constant the program held, not one valueOf named (HBase's
 * RegionState.State: `state == State.OPEN`, `equals`).  An enum with a static
 * array of its own type still states its constants in ordinal order.
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

    enum Other { ACTIVE, DOWN }

    enum Phase {
        STOP, START, RUN;

        static final Phase[] TERMINAL = {RUN, STOP};
    }

    private static final class Input {
        String state = new String("down");
        String phase = new String("START");
    }

    private static final class Sink {
        State state;
    }

    private static final class Held {
        State state = State.DOWN;
    }

    public static void main(String[] args) {
        Input input = new Input();
        Sink sink = new Sink();
        Held held = new Held();
        // Held before the window: keys the program put, plain constants.
        Map<State, Integer> weights = new HashMap<State, Integer>();
        weights.put(State.ACTIVE, Integer.valueOf(1));
        weights.put(State.DOWN, Integer.valueOf(2));
        Set<State> seen = new HashSet<State>();
        seen.add(State.DOWN);
        EnumSet<State> live = EnumSet.of(State.ACTIVE, State.RECOVERING);
        State none = null;
        require(System.startConcolicRegion("REGION.enum", "TASK.enum") == 0L,
                "region start rejected");
        System.symbolizeField(input, "state", "STATE");
        System.symbolizeField(input, "phase", "PHASE");
        System.observeField(sink, Sink.class.getName(), "state",
                "L" + State.class.getName().replace('.', '/') + ";");
        System.observeField(held, Held.class.getName(), "state",
                "L" + State.class.getName().replace('.', '/') + ";");
        sink.state = State.getState(input.state);
        State state = sink.state;
        held.state = State.RECOVERING;
        State plain = held.state;
        int heldCompared = 0;
        if (plain == State.RECOVERING) heldCompared |= 1;
        if (plain.equals(State.ACTIVE)) heldCompared |= 2;

        int compared = 0;
        if (state != State.ACTIVE) compared |= 1;
        if (state == State.DOWN) compared |= 2;
        if (state.equals(State.RECOVERING)) compared |= 4;
        if (((Object) state) == Other.DOWN) compared |= 8;
        if (state == none) compared |= 16;
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
        boolean alive = live.contains(state);
        Integer weight = weights.get(state);
        boolean wasSeen = seen.contains(state);
        // Mutations that state each container's members: a plain key put
        // with a symbolic value, a named member added.
        weights.put(State.RECOVERING, Integer.valueOf(input.state.length()));
        seen.add(state);
        Phase phase = Phase.valueOf(input.phase);
        boolean running = phase == Phase.RUN;
        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String weightsVersions = System.getSharedMapVersions(weights);
        String seenVersions = System.getSharedMapVersions(seen);
        String summary = System.finishConcolicRegion();

        System.out.println("PATH " + path);
        System.out.println("WEIGHTS " + weightsVersions);
        System.out.println("SEEN " + seenVersions);
        require(compared == 3 && heldCompared == 1 && "DOWN".equals(name)
                        && "down".equals(text)
                        && ordinal == 1 && arm == 2 && !alive
                        && weight.intValue() == 2 && wasSeen && !running,
                "the model changed what the program computed");
        require(count(path, "\"_name\":\"equals\"") == 6
                        && path.contains("java/lang/Enum valueOf")
                        && path.contains("STATE")
                        && path.contains("ReadFromExpression"),
                "a compare of a valueOf constant is no equals of names, or"
                        + " not through its tracked read: " + path);
        require(path.contains("\"_exp\":\"N\""),
                "a compare with null is no reference test: " + path);
        require(path.contains("java/lang/Enum ordinal")
                        && path.contains("\"operation\":\"READ\"")
                        && path.contains("\"operation\":\"SNAPSHOT_BASE\"")
                        && path.contains("\"_op\":\"<<\""),
                "the switch and the EnumSet are not read at the ordinal: "
                        + path);
        int stop = path.indexOf("Y_L'String'_STOP");
        int start = path.indexOf("Y_L'String'_START");
        int run = path.indexOf("Y_L'String'_RUN");
        require(stop >= 0 && stop < start && start < run,
                "a static array of its type ordered the constants: " + path);
        require(weightsVersions.contains("Y_L'String'_ACTIVE")
                        && weightsVersions.contains("Y_L'String'_RECOVERING")
                        && seenVersions.contains("Y_L'String'_DOWN"),
                "a constant a container holds is not its name: "
                        + weightsVersions + " " + seenVersions);
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
