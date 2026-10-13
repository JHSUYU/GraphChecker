/**
 * The base pause a doors-only occurrence holds from its start to its close
 * ({@code System.pauseConcolicBase}): a door decided in a callee frame pushed
 * under it, reached through a helper frame that is no part of the door
 * (Solr's {@code ZkCmdExecutor#retryOperation}), records its branch once the
 * base pause lifts there; under an observation pause
 * ({@code pauseConcolicPathCondition}) the same callee records nothing, as
 * before; and a frame pushed under the base pause hands its caller no
 * expression back.
 */
public final class RegionBasePauseCalleeSmoke {
    private static final class Door {
        boolean fault;
        int value = 3;
    }

    private interface Op {
        int execute();
    }

    /** The helper the door is reached through. */
    private static int retry(Op op) {
        return op.execute();
    }

    public static void main(String[] args) {
        final Door base = new Door();
        long started = System.startConcolicRegion(
                "REGION.base-pause-callee", "ACT.base-pause-callee");
        check(started == 0L, "region start rejected: " + started);
        System.pauseConcolicBase();
        String paused = System.getConcolicRegionSummary();
        final long[] baseMarker = new long[1];
        int returned = retry(new Op() {
            @Override
            public int execute() {
                return decide(base, "BASE.DOOR", true, baseMarker);
            }
        });
        System.resumeConcolicBase();
        String baseEvents = System.getConcolicBranchEvents();
        Integer boxed = new Integer(returned);
        String returnedExpression = System.getSymbolicExpression(boxed);
        String baseFinished = System.finishConcolicRegion();
        check(has(paused, "\"pathConditionPauseDepth\":1"), paused);
        check(baseMarker[0] > 0L,
                "the callee's door marker was refused under the base pause");
        check(has(baseEvents, "\"siteId\":\"BASE.DOOR\""),
                "the callee's door recorded no event: " + baseEvents);
        check(returned == 4, "unexpected concrete result: " + returned);
        check(!has(returnedExpression, "door_value"),
                "a frame pushed under the base pause handed back an"
                        + " expression: " + returnedExpression);
        check(has(baseFinished, "\"pathConditionPauseDepth\":0"),
                baseFinished);

        final Door observed = new Door();
        started = System.startConcolicRegion(
                "REGION.observation-pause-callee",
                "ACT.observation-pause-callee");
        check(started == 0L, "second region start rejected: " + started);
        System.pauseConcolicPathCondition();
        final long[] observedMarker = new long[1];
        retry(new Op() {
            @Override
            public int execute() {
                return decide(observed, "OBSERVED.DOOR", false,
                        observedMarker);
            }
        });
        System.resumeConcolicPathCondition();
        String observedEvents = System.getConcolicBranchEvents();
        String observedFinished = System.finishConcolicRegion();
        check(observedMarker[0] == 0L,
                "a callee pushed under an observation pause tracked");
        check(!has(observedEvents, "OBSERVED.DOOR"),
                "a callee pushed under an observation pause recorded: "
                        + observedEvents);
        check(has(observedFinished, "\"pathConditionPauseDepth\":0"),
                observedFinished);
        System.out.println("CAUSYNTH_REGION_BASE_PAUSE_CALLEE_SMOKE_OK");
    }

    /**
     * One door, as a doors-only occurrence decides it: the pause lifts (the
     * door window), the input is stated, its test runs under a marker, and
     * the pause is restored before the frame returns.
     */
    private static int decide(Door door, String site, boolean base,
                              long[] marker) {
        if (base) {
            System.resumeConcolicBase();
        } else {
            System.resumeConcolicPathCondition();
        }
        System.symbolizeField(door, "fault", "door_fault");
        System.symbolizeField(door, "value", "door_value");
        int value = door.value + 1;
        marker[0] = System.markConcolicBranch(site, 1);
        boolean faulted;
        if (door.fault) {
            faulted = true;
        } else {
            faulted = false;
        }
        if (base) {
            System.pauseConcolicBase();
        } else {
            System.pauseConcolicPathCondition();
        }
        return faulted ? -1 : value;
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
