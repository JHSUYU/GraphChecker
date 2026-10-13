/**
 * The base pause a doors-only occurrence holds from its start to its close
 * ({@code System.pauseConcolicBase}), case by case, each in a region of its
 * own:
 *
 * <ol>
 *   <li>a door decided in a callee frame pushed under it, reached through a
 *   helper frame that is no part of the door (Solr's
 *   {@code ZkCmdExecutor#retryOperation}), records its branch once the base
 *   pause lifts there, its marker's input in the path condition;</li>
 *   <li>production's sequence: the base pause stands, a hook's observation
 *   bracket is taken over it, the hook lifts the base pause (the door
 *   window) and the bracket's resume lifts the rest -- the hook's frame,
 *   pushed under both, never tracks, and the program frame decides;</li>
 *   <li>a frame pushed under the base pause hands its caller no expression
 *   back, though its result slot holds one;</li>
 *   <li>nor takes one from its caller;</li>
 *   <li>a second window in one frame reads no shadow the first one left:
 *   retaking the base pause clears the region's frames;</li>
 *   <li>under an observation pause the same callee records nothing, as
 *   before;</li>
 *   <li>an observation resume never releases the base pause, and an
 *   explicit input operation restores the depth it found.</li>
 * </ol>
 */
public final class RegionBasePauseCalleeSmoke {
    private static final class Door {
        boolean fault;
        int value = 3;
    }

    private interface Op {
        int execute();
    }

    /** The helper a door is reached through. */
    private static int retry(Op op) {
        return op.execute();
    }

    public static void main(String[] args) {
        calleeDoor();
        productionSequence();
        noResultLeavesTheBoundary();
        noArgumentEntersTheBoundary();
        aSecondWindowReadsNoStaleShadow();
        anObservationPausedCalleeNeverTracks();
        theBasePauseIsNeverResumedAway();
        System.out.println("CAUSYNTH_REGION_BASE_PAUSE_CALLEE_SMOKE_OK");
    }

    private static void calleeDoor() {
        final Door door = new Door();
        start("callee-door");
        System.pauseConcolicBase();
        final long[] marker = new long[1];
        retry(new Op() {
            @Override
            public int execute() {
                return decide(door, "BASE.DOOR", marker);
            }
        });
        System.resumeConcolicBase();
        String events = System.getConcolicBranchEvents();
        String path = System.getPathCondition();
        String finished = System.finishConcolicRegion();
        check(marker[0] > 0L,
                "the callee's door marker was refused under the base pause");
        check(conditions(events, "BASE.DOOR") > 0,
                "the callee's door states no condition: " + events);
        check(has(path, "door_fault"), "no door input in the path: " + path);
        check(has(finished, "\"pathConditionPauseDepth\":0")
                && has(finished, "\"basePauseDepth\":0"), finished);
    }

    /** One door, decided in its own frame: the pause lifts (the window),
     *  the marker's input is stated, its test runs, the pause comes back. */
    private static int decide(Door door, String site, long[] marker) {
        System.resumeConcolicBase();
        System.symbolizeField(door, "fault", "door_fault");
        marker[0] = System.markConcolicBranch(site, 1);
        boolean faulted;
        if (door.fault) {
            faulted = true;
        } else {
            faulted = false;
        }
        System.pauseConcolicBase();
        return faulted ? -1 : 1;
    }

    private static void productionSequence() {
        Door door = new Door();
        start("production-sequence");
        System.pauseConcolicBase();
        long[] hook = new long[1];
        long[] decided = new long[1];
        doorInProgram(door, hook, decided);
        System.resumeConcolicBase();
        String events = System.getConcolicBranchEvents();
        String path = System.getPathCondition();
        String finished = System.finishConcolicRegion();
        check(hook[0] == 0L, "a hook frame pushed under the base and an"
                + " observation pause tracked once both lifted");
        check(!has(events, "HOOK.BRANCH"),
                "the hook frame recorded a branch: " + events);
        check(decided[0] > 0L && conditions(events, "PROGRAM.DOOR") > 0,
                "the program frame did not decide its door: " + events);
        check(has(path, "door_fault"), "no door input in the path: " + path);
        check(has(finished, "\"pathConditionPauseDepth\":0")
                && has(finished, "\"refusedObservationResumes\":0"),
                finished);
    }

    /** A program frame pushed under the base pause: the woven bracket over
     *  the door's mint hook, then the woven test. */
    private static void doorInProgram(Door door, long[] hook,
                                      long[] decided) {
        System.pauseConcolicPathCondition();
        mintHook(door, hook);
        System.resumeConcolicPathCondition();
        decided[0] = System.markConcolicBranch("PROGRAM.DOOR", 1);
        boolean faulted;
        if (door.fault) {
            faulted = true;
        } else {
            faulted = false;
        }
        System.pauseConcolicBase();
        check(!faulted, "unexpected concrete fault");
    }

    /** The mint hook: pushed under the base and the observation pause, it
     *  states the input and opens the window (RootMint#openDoorWindow);
     *  with both lifted, its own frame still does not track. */
    private static void mintHook(Door door, long[] hook) {
        System.symbolizeField(door, "fault", "door_fault");
        System.resumeConcolicBase();
        System.resumeConcolicPathCondition();
        hook[0] = System.markConcolicBranch("HOOK.BRANCH", 1);
        if (door.fault) {
            sink++;
        }
        System.pauseConcolicPathCondition();
    }

    private static void noResultLeavesTheBoundary() {
        Door door = new Door();
        start("result-boundary");
        System.pauseConcolicBase();
        // decideStale's result slot holds door_value when it returns; the
        // addition runs once the observation pause is lifted in main.
        int sum = decideStale(door) + resumeObservationAndZero();
        Integer boxed = new Integer(sum);
        String expression = System.getSymbolicExpression(boxed);
        String finished = System.finishConcolicRegion();
        check(sum == 3, "unexpected concrete sum: " + sum);
        check(!has(expression, "door_value"),
                "a frame pushed under the base pause handed back an"
                        + " expression: " + expression);
        check(has(finished, "\"pathConditionPauseDepth\":0"), finished);
    }

    /** Pushed under the base pause: in its window the operand is symbolic,
     *  then an observation pause stands, so the addition and the return run
     *  paused and its result slot keeps door_value. */
    private static int decideStale(Door door) {
        System.resumeConcolicBase();
        System.symbolizeField(door, "value", "door_value");
        return door.value + pauseObservationAndZero();
    }

    private static int pauseObservationAndZero() {
        System.pauseConcolicPathCondition();
        return 0;
    }

    private static int resumeObservationAndZero() {
        System.resumeConcolicPathCondition();
        return 0;
    }

    private static void noArgumentEntersTheBoundary() {
        Door door = new Door();
        start("argument-boundary");
        System.symbolizeField(door, "value", "param_value");
        long[] marker = new long[1];
        // The argument is loaded unpaused, so its operand slot holds
        // param_value; the base pause is taken before the call is made.
        branchOnParameter(door.value, pauseBaseAnd(marker));
        System.resumeConcolicBase();
        String events = System.getConcolicBranchEvents();
        String path = System.getPathCondition();
        String finished = System.finishConcolicRegion();
        check(marker[0] > 0L, "the paused callee's marker was refused");
        check(conditions(events, "PARAMETER.BRANCH") == 0,
                "a paused callee's parameter carried an expression: "
                        + events);
        check(!has(path, "param_value"),
                "a paused callee's parameter reached the path: " + path);
        check(has(finished, "\"pathConditionPauseDepth\":0"), finished);
    }

    private static long[] pauseBaseAnd(long[] marker) {
        System.pauseConcolicBase();
        return marker;
    }

    private static void branchOnParameter(int parameter, long[] marker) {
        System.resumeConcolicBase();
        marker[0] = System.markConcolicBranch("PARAMETER.BRANCH", 1);
        if (parameter > 0) {
            sink++;
        }
        System.pauseConcolicBase();
    }

    private static void aSecondWindowReadsNoStaleShadow() {
        Door door = new Door();
        start("second-window");
        System.pauseConcolicBase();
        long[] marker = new long[1];
        twoWindows(door, marker);
        System.resumeConcolicBase();
        String events = System.getConcolicBranchEvents();
        String path = System.getPathCondition();
        String finished = System.finishConcolicRegion();
        check(marker[0] > 0L, "the second window's marker was refused");
        check(conditions(events, "SECOND.WINDOW") == 0,
                "the second window read the first one's shadow: " + events);
        check(!has(path, "first_value"),
                "the first window's input reached the second's branch: "
                        + path);
        check(has(finished, "\"pathConditionPauseDepth\":0"), finished);
    }

    /** Two windows in one frame pushed under the base pause: a local the
     *  first set symbolic is overwritten under the pause between them. */
    private static void twoWindows(Door door, long[] marker) {
        System.resumeConcolicBase();
        System.symbolizeField(door, "value", "first_value");
        int local = door.value;
        System.pauseConcolicBase();
        local = 7;
        System.resumeConcolicBase();
        marker[0] = System.markConcolicBranch("SECOND.WINDOW", 1);
        if (local > 0) {
            sink++;
        }
        System.pauseConcolicBase();
    }

    private static void anObservationPausedCalleeNeverTracks() {
        final Door door = new Door();
        start("observation-callee");
        System.pauseConcolicPathCondition();
        final long[] marker = new long[1];
        retry(new Op() {
            @Override
            public int execute() {
                System.resumeConcolicPathCondition();
                System.symbolizeField(door, "fault", "door_fault");
                marker[0] = System.markConcolicBranch("OBSERVED.DOOR", 1);
                int answer = door.fault ? -1 : 1;
                System.pauseConcolicPathCondition();
                return answer;
            }
        });
        System.resumeConcolicPathCondition();
        String events = System.getConcolicBranchEvents();
        String finished = System.finishConcolicRegion();
        check(marker[0] == 0L,
                "a callee pushed under an observation pause tracked");
        check(!has(events, "OBSERVED.DOOR"),
                "a callee pushed under an observation pause recorded: "
                        + events);
        check(has(finished, "\"pathConditionPauseDepth\":0"), finished);
    }

    private static void theBasePauseIsNeverResumedAway() {
        Door door = new Door();
        start("depth");
        System.pauseConcolicBase();
        System.resumeConcolicPathCondition();
        String refused = System.getConcolicRegionSummary();
        System.pauseConcolicPathCondition();
        System.symbolizeField(door, "value", "depth_value");
        String restored = System.getConcolicRegionSummary();
        System.resumeConcolicPathCondition();
        System.resumeConcolicBase();
        String finished = System.finishConcolicRegion();
        check(has(refused, "\"pathConditionPauseDepth\":1")
                && has(refused, "\"basePauseDepth\":1")
                && has(refused, "\"refusedObservationResumes\":1"),
                "an observation resume released the base pause: " + refused);
        check(has(restored, "\"pathConditionPauseDepth\":2")
                && has(restored, "\"basePauseDepth\":1"),
                "a symbolize lost the depth it found: " + restored);
        check(has(finished, "\"pathConditionPauseDepth\":0")
                && has(finished, "\"basePauseDepth\":0"), finished);
    }

    private static volatile int sink;

    private static void start(String name) {
        long started = System.startConcolicRegion("REGION.base-" + name,
                "ACT.base-" + name);
        check(started == 0L, name + ": region start rejected: " + started);
    }

    /** The conditionCount of the event at {@code site}; -1 for none. */
    private static int conditions(String events, String site) {
        int at = events.indexOf("\"siteId\":\"" + site + "\"");
        if (at < 0) return -1;
        String key = "\"conditionCount\":";
        int count = events.indexOf(key, at);
        if (count < 0) return -1;
        int start = count + key.length();
        int end = start;
        while (end < events.length()
                && Character.isDigit(events.charAt(end))) {
            end++;
        }
        return Integer.parseInt(events.substring(start, end));
    }

    private static boolean has(String text, String fragment) {
        return text != null && text.indexOf(fragment) >= 0;
    }

    private static void check(boolean condition, String detail) {
        if (!condition) {
            throw new AssertionError(detail);
        }
    }
}
