import java.util.HashMap;
import java.util.Map;

/**
 * GraphChecker-style regression: Java bookkeeping is paused while an input
 * field is explicitly symbolized, then normal propagation resumes before the
 * region branch executes.
 */
public final class RegionPausedSymbolizationSmoke {
    private static final class Input {
        int value = 7;
    }

    private static final class State {
        final Map<Integer, Object> values =
                new HashMap<Integer, Object>();
    }

    private static final class Entry {
        final int keyId;

        Entry(int keyId) {
            this.keyId = keyId;
        }
    }

    private static final class ArrayInput {
        final Entry[] entries = {new Entry(9)};
    }

    private static volatile int sink;

    public static void main(String[] args) {
        Input input = new Input();
        long started = System.startConcolicRegion(
                "REGION.paused-symbolization",
                "ACT.paused-symbolization");
        require(started == 0L, "region start rejected: " + started);

        System.pauseConcolicPathCondition();
        symbolizeFromPausedHelper(input);
        String pausedBaseline = System.getPathCondition();
        // This is deliberately bookkeeping under the pause.  It must not
        // become part of the captured path condition.
        if (input != null) {
            sink++;
        }
        require(pausedBaseline.equals(System.getPathCondition()),
                "paused bookkeeping polluted PC");
        String whilePaused = System.getConcolicRegionSummary();
        require(has(whilePaused, "\"pathConditionRecordingPaused\":true"),
                whilePaused);
        require(has(whilePaused, "paused_helper_value"), whilePaused);
        System.resumeConcolicPathCondition();

        boolean decision = input.value > 0;
        String afterBranch = System.getPathCondition();
        String finished = System.finishConcolicRegion();

        require(decision, "unexpected concrete decision");
        require(!"[]".equals(afterBranch),
                "symbolic branch was not recorded");
        require(has(finished, "paused_helper_value"), finished);
        require(has(finished, "\"pathConditionPauseDepth\":0"), finished);
        require(sink == 1, "unexpected bookkeeping result: " + sink);

        // Match the HDFS target shape as well: a map-valued receiver field is
        // symbolized from a paused helper and used by HashMap.get only after
        // the helper has returned and recording has resumed.
        State state = new State();
        state.values.put(Integer.valueOf(42), new Object());
        started = System.startConcolicRegion(
                "REGION.paused-map-symbolization",
                "ACT.paused-map-symbolization");
        require(started == 0L, "map region start rejected: " + started);
        System.pauseConcolicPathCondition();
        symbolizeMapFromPausedHelper(state);
        System.resumeConcolicPathCondition();
        Object found = state.values.get(Integer.valueOf(42));
        String mapPc = System.getPathCondition();
        String mapFinished = System.finishConcolicRegion();
        require(found != null, "concrete map lookup unexpectedly failed");
        require(!"[]".equals(mapPc), "symbolic map get was not recorded");
        require(has(mapFinished, "paused_helper_values"), mapFinished);
        require(has(mapFinished, "\"operation\":\"READ\""), mapFinished);

        // Array symbolization installs an activation-local container state.
        // This exercises the temporary pause-depth drain: the pause must be
        // restored, and ordinary Java bookkeeping while paused adds nothing.
        ArrayInput arrayInput = new ArrayInput();
        started = System.startConcolicRegion(
                "REGION.paused-array-symbolization",
                "ACT.paused-array-symbolization");
        require(started == 0L, "array region start rejected: " + started);
        System.pauseConcolicPathCondition();
        symbolizeArrayFromPausedHelper(arrayInput);
        String beforePausedBranch = System.getPathCondition();
        if (arrayInput.entries.length > 0) {
            sink++;
        }
        String afterPausedBranch = System.getPathCondition();
        String pausedArraySummary = System.getConcolicRegionSummary();
        require(beforePausedBranch.equals(afterPausedBranch),
                "paused array bookkeeping polluted PC: "
                        + afterPausedBranch);
        require(has(pausedArraySummary,
                "\"pathConditionPauseDepth\":1"), pausedArraySummary);
        System.resumeConcolicPathCondition();
        boolean arrayDecision = arrayInput.entries[0].keyId > 0;
        String arrayFinished = System.finishConcolicRegion();
        require(arrayDecision, "unexpected array decision");
        require(has(arrayFinished, "ContainerRelation"), arrayFinished);
        require(has(arrayFinished, "\"pathConditionPauseDepth\":0"),
                arrayFinished);
        System.out.println("CAUSYNTH_REGION_PAUSED_SYMBOLIZATION_SMOKE_OK");
    }

    private static void symbolizeFromPausedHelper(Input input) {
        System.symbolizeField(input, "value", "paused_helper_value");
    }

    private static void symbolizeMapFromPausedHelper(State state) {
        System.symbolizeField(state, "values", "paused_helper_values");
    }

    private static void symbolizeArrayFromPausedHelper(ArrayInput input) {
        System.symbolizeField(input, "entries", "paused_helper_entries");
    }

    private static boolean has(String text, String fragment) {
        return text != null && text.indexOf(fragment) >= 0;
    }

    private static void require(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
