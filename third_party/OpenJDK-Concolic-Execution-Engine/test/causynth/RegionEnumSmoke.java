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
 * RegionState.State: `state == State.OPEN`, `equals`): each condition is over
 * that read -- a compare, equals, name(), ordinal() and a switch of it, a read
 * of the location's INITIAL, one that observed null, one of a constant with
 * a body of its own, two such reads compared, and a container's answer
 * compared with the read or a constant.  An enum with a static array of its
 * own type still states its constants in ordinal order.
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

    private static final class Unset {
        State state;
    }

    enum Mode {
        FAST {
            @Override
            int speed() {
                return 2;
            }
        },
        SLOW;

        int speed() {
            return 1;
        }
    }

    private static final class Modes {
        Mode mode = Mode.SLOW;
    }

    public static void main(String[] args) {
        Input input = new Input();
        Sink sink = new Sink();
        Held held = new Held();
        Held initial = new Held();
        Unset unset = new Unset();
        Modes modes = new Modes();
        Map<String, State> byName = new HashMap<String, State>();
        byName.put("DOWN", State.RECOVERING);
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
        String stateType = "L" + State.class.getName().replace('.', '/') + ";";
        System.observeField(held, Held.class.getName(), "state", stateType);
        System.observeField(initial, Held.class.getName(), "state",
                stateType);
        System.observeField(unset, Unset.class.getName(), "state", stateType);
        System.observeField(modes, Modes.class.getName(), "mode",
                "L" + Mode.class.getName().replace('.', '/') + ";");
        sink.state = State.getState(input.state);
        State state = sink.state;
        held.state = State.RECOVERING;
        modes.mode = Mode.FAST;
        State plain = held.state;
        int heldCompared = 0;
        int mark = conditions();
        if (plain == State.RECOVERING) heldCompared |= 1;
        String heldIs = since(mark);
        mark = conditions();
        if (plain.equals(State.ACTIVE)) heldCompared |= 2;
        String heldEquals = since(mark);

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
        int stated = conditions();
        String path = System.getConcolicPathConditionRange(0, stated);

        mark = conditions();
        int heldArm;
        switch (plain) {
            case RECOVERING:
                heldArm = 3;
                break;
            case DOWN:
                heldArm = 2;
                break;
            default:
                heldArm = 1;
                break;
        }
        String heldSwitch = since(mark);
        mark = conditions();
        if (plain.ordinal() == 2) heldCompared |= 4;
        String heldOrdinal = since(mark);
        mark = conditions();
        if (plain.name().equals("RECOVERING")) heldCompared |= 8;
        String heldName = since(mark);
        State first = initial.state;
        mark = conditions();
        if (first == State.DOWN) heldCompared |= 16;
        String initialIs = since(mark);
        State missing = unset.state;
        mark = conditions();
        if (missing == State.ACTIVE) heldCompared |= 32;
        String missingIs = since(mark);
        mark = conditions();
        if (((Object) plain) == Other.ACTIVE) heldCompared |= 64;
        String otherClass = since(mark);
        mark = conditions();
        if (plain == first) heldCompared |= 128;
        String heldPair = since(mark);
        Mode mode = modes.mode;
        mark = conditions();
        if (mode == Mode.FAST) heldCompared |= 256;
        String bodied = since(mark);
        State looked = byName.get(name);
        mark = conditions();
        if (looked == plain) heldCompared |= 512;
        String answerHeld = since(mark);
        mark = conditions();
        if (looked == State.DOWN) heldCompared |= 1024;
        String answerConstant = since(mark);
        String weightsVersions = System.getSharedMapVersions(weights);
        String seenVersions = System.getSharedMapVersions(seen);
        String summary = System.finishConcolicRegion();

        System.out.println("PATH " + path);
        System.out.println("WEIGHTS " + weightsVersions);
        System.out.println("SEEN " + seenVersions);
        require(compared == 3 && heldCompared == (1 | 4 | 8 | 16 | 256 | 512)
                        && heldArm == 3 && mode.speed() == 2
                        && looked == State.RECOVERING && "DOWN".equals(name)
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
        over("== of the held read", heldIs, "Y_L'String'_RECOVERING", "==");
        over("equals of the held read", heldEquals, "Y_L'String'_ACTIVE",
                "!=");
        overRead("a switch of the held read", heldSwitch,
                "java/lang/Enum ordinal", "\"operation\":\"READ\"");
        overRead("ordinal() of the held read", heldOrdinal,
                "java/lang/Enum ordinal");
        overRead("name() of the held read", heldName,
                "\"_name\":\"equals\"", "Y_L'String'_RECOVERING");
        over("a read of the INITIAL", initialIs, "Y_L'String'_DOWN", "==");
        require(initialIs.contains("\"versionKind\":\"INITIAL\""),
                "the INITIAL read is not of the INITIAL: " + initialIs);
        over("a read that observed null", missingIs, "Y_L'String'_ACTIVE",
                "!=");
        require(!otherClass.contains("ReadFromExpression"),
                "a compare with another class is not decided by it: "
                        + otherClass);
        require(count(heldPair, "ReadFromExpression") >= 2,
                "two held reads are not compared over both: " + heldPair);
        over("a constant with a body", bodied, "Y_L'String'_FAST", "==");
        overRead("a container's answer and the held read", answerHeld,
                "\"operation\":\"READ\"");
        require(answerConstant.contains("\"operation\":\"READ\"")
                        && answerConstant.contains("\"_name\":\"equals\"")
                        && answerConstant.contains("Y_L'String'_DOWN"),
                "a container's answer and a constant are no equals of"
                        + " names: " + answerConstant);
        require(summary.length() > 0, "no summary");
        System.out.println("CAUSYNTH_REGION_ENUM_SMOKE_OK");
    }

    private static void over(String what, String slice, String name,
                             String polarity) {
        overRead(what, slice, "\"_name\":\"equals\"", name,
                "\"_op\":\"" + polarity + "\"");
    }

    private static void overRead(String what, String slice,
                                 String... needles) {
        require(slice.contains("ReadFromExpression")
                        && !slice.contains("java/lang/Enum valueOf"),
                what + " is not over the read: " + slice);
        for (String needle : needles) {
            require(slice.contains(needle), what + " states no " + needle
                    + ": " + slice);
        }
    }

    private static int conditions() {
        String range = System.getConcolicPathConditionRange(0,
                Integer.MAX_VALUE);
        String key = "\"conditionCount\":";
        int at = range.indexOf(key);
        require(at >= 0, range);
        int end = at + key.length();
        while (end < range.length() && Character.isDigit(range.charAt(end))) {
            ++end;
        }
        return Integer.parseInt(range.substring(at + key.length(), end));
    }

    private static String since(int from) {
        String range = System.getConcolicPathConditionRange(from,
                Integer.MAX_VALUE);
        int at = range.indexOf("\"conditions\":[");
        int end = range.indexOf("],\"emittedConditionCount\"", at);
        require(at >= 0 && end > at, range);
        return expand(range, range.substring(at, end), 0);
    }

    private static String expand(String artifact, String text, int depth) {
        require(depth < 32, "an expression nests past 32: " + text);
        String marker = "{\"_type\":\"VmExpressionReference\"";
        StringBuilder out = new StringBuilder();
        int from = 0;
        for (int at = text.indexOf(marker); at >= 0;
             at = text.indexOf(marker, from)) {
            out.append(text, from, at);
            String reference = objectAt(text, at);
            out.append(expand(artifact, definition(artifact, reference),
                    depth + 1));
            from = at + reference.length();
        }
        return out.append(text.substring(from)).toString();
    }

    private static String definition(String artifact, String reference) {
        String id = "\"expressionId\":";
        int at = reference.indexOf(id) + id.length();
        int end = at;
        while (Character.isDigit(reference.charAt(end))) end++;
        String prefix = "\"_type\":\"VmExpressionDefinition\","
                + reference.substring(reference.indexOf("\"sessionId\""), end)
                + ",\"expression\":";
        int found = artifact.indexOf(prefix);
        require(found >= 0, "no definition of " + reference);
        return objectAt(artifact, found + prefix.length());
    }

    private static String objectAt(String json, int start) {
        int depth = 0;
        boolean quoted = false;
        boolean escaped = false;
        for (int index = start; index < json.length(); index++) {
            char current = json.charAt(index);
            if (quoted) {
                if (escaped) {
                    escaped = false;
                } else if (current == '\\') {
                    escaped = true;
                } else if (current == '"') {
                    quoted = false;
                }
            } else if (current == '"') {
                quoted = true;
            } else if (current == '{') {
                depth++;
            } else if (current == '}' && --depth == 0) {
                return json.substring(start, index + 1);
            }
        }
        throw new AssertionError("unterminated object: " + json.substring(start));
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
