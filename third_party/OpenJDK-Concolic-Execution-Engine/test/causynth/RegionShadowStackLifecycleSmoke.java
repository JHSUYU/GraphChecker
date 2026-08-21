/**
 * Guards the JVM-word lifecycle of the concolic operand shadow stack.
 *
 * <p>The test deliberately consumes symbolic category-1/category-2 values,
 * grows the concrete stack over the dead words, crosses cast and Java-call
 * boundaries, and enters a catch handler with symbolic operands still live.
 * A dead shadow must never become a condition of a later concrete branch.</p>
 */
public final class RegionShadowStackLifecycleSmoke {
    private static final class Input {
        int narrow = 7;
        long wide = 4_294_967_303L;
        double ratio = 3.25D;
        int zero = 0;
    }

    private RegionShadowStackLifecycleSmoke() {
    }

    private static int intIdentity(int value) {
        return value;
    }

    private static long longIdentity(long value) {
        return value;
    }

    private static double doubleIdentity(double value) {
        return value;
    }

    private static void discardCategory1(Input input) {
        intIdentity(input.narrow); // javac emits pop
    }

    private static void discardCategory2(Input input) {
        longIdentity(input.wide); // javac emits pop2
    }

    private static boolean concreteGuard(String[] args, int salt) {
        return args.length + salt >= salt;
    }

    private static long markThenReturn(boolean createMarker) {
        if (createMarker) {
            // No conditional executes after this native call.  The marker
            // must be cancelled when this Java activation is popped.
            return System.markConcolicBranch(
                    "SHADOW.STALE.OWNER.FRAME", 1);
        }
        // Re-entering the exact same method encourages Zero to reuse its
        // frame address.  Without pop-time invalidation, the branch above can
        // incorrectly claim the prior invocation's marker.
        return 0L;
    }

    public static void main(String[] args) throws Exception {
        Input input = new Input();
        long status = System.startConcolicRegion(
                "REGION.SHADOW.LIFECYCLE", "ACT.SHADOW.LIFECYCLE");
        require(status == 0L, "region start rejected");
        System.symbolizeField(input, "narrow", "shadow_narrow");
        System.symbolizeField(input, "wide", "shadow_wide");
        System.symbolizeField(input, "ratio", "shadow_ratio");

        System.pauseConcolicPathCondition();
        long pausedMarker = System.markConcolicBranch(
                "SHADOW.REJECTED.WHILE.PAUSED", 1);
        System.resumeConcolicPathCondition();
        require(pausedMarker == 0L,
                "paused subtree accepted a branch marker");

        long staleOwnerMarker = markThenReturn(true);
        require(staleOwnerMarker > 0L,
                "tracking frame rejected owner marker");
        markThenReturn(false);

        discardCategory1(input);
        System.markConcolicBranch("SHADOW.AFTER.POP", 1);
        if (!concreteGuard(args, 1)) {
            throw new AssertionError("impossible concrete pop guard");
        }

        discardCategory2(input);
        System.markConcolicBranch("SHADOW.AFTER.POP2", 1);
        if (!concreteGuard(args, 2)) {
            throw new AssertionError("impossible concrete pop2 guard");
        }

        // i2l followed by l2i must retain a typed symbolic value but leave no
        // category-2 companion shadow behind after narrowing.
        int castRoundTrip = (int) (long) input.narrow;
        System.markConcolicBranch("SHADOW.CAST.ROUND_TRIP", 1);
        if (castRoundTrip <= 0) {
            throw new AssertionError("unexpected cast result");
        }

        // Java-call argument transfer and return copy both span two words.
        long wideRoundTrip = longIdentity(input.wide);
        System.markConcolicBranch("SHADOW.LONG.RETURN", 1);
        if (wideRoundTrip <= 0L) {
            throw new AssertionError("unexpected long result");
        }

        double ratioRoundTrip = doubleIdentity(input.ratio);
        System.markConcolicBranch("SHADOW.DOUBLE.RETURN", 1);
        if (ratioRoundTrip >= 4.0D) {
            throw new AssertionError("unexpected double result");
        }

        // The pending marker and every live operand shadow must be discarded
        // when idiv transfers control to the handler.
        try {
            System.markConcolicBranch("SHADOW.ABANDONED.BY.EXCEPTION", 1);
            int ignored = input.narrow / input.zero;
            throw new AssertionError("division unexpectedly returned "
                    + ignored);
        } catch (ArithmeticException expected) {
            // If the exception edge failed to cancel the marker, this first
            // concrete conditional would incorrectly claim it.
            if (!concreteGuard(args, 3)) {
                throw new AssertionError("impossible catch guard");
            }
            System.markConcolicBranch("SHADOW.CATCH.CONCRETE", 1);
            if (!concreteGuard(args, 4)) {
                throw new AssertionError("impossible marked catch guard");
            }
        }

        String path = System.getConcolicPathConditionRange(
                0, Integer.MAX_VALUE);
        String events = System.getConcolicBranchEvents();
        String summary = System.finishConcolicRegion();

        require(emptyCondition(events, "SHADOW.AFTER.POP"), events);
        require(emptyCondition(events, "SHADOW.AFTER.POP2"), events);
        require(oneCondition(events, "SHADOW.CAST.ROUND_TRIP"), events);
        require(oneCondition(events, "SHADOW.LONG.RETURN"), events);
        require(oneCondition(events, "SHADOW.DOUBLE.RETURN"), events);
        require(emptyCondition(events, "SHADOW.CATCH.CONCRETE"), events);
        require(!events.contains("SHADOW.ABANDONED.BY.EXCEPTION"), events);
        require(!events.contains("SHADOW.REJECTED.WHILE.PAUSED"), events);
        require(!events.contains("SHADOW.STALE.OWNER.FRAME"), events);

        require(summary.contains("shadow_narrow")
                        && summary.contains("shadow_wide")
                        && summary.contains("shadow_ratio"), summary);
        require(path.contains("\"sourceJavaType\":\"I\"")
                        && path.contains("\"targetJavaType\":\"J\"")
                        && path.contains("\"sourceJavaType\":\"J\"")
                        && path.contains("\"targetJavaType\":\"I\""),
                "cast chain was not preserved: " + path);

        if (Boolean.getBoolean("causynth.smoke.dump")) {
            System.out.println(summary);
        }
        verifyAbandonedOwnerCleanup();
        System.out.println("CAUSYNTH_REGION_SHADOW_STACK_LIFECYCLE_SMOKE_OK");
    }

    private static void abandonedOwner() {
        long status = System.startConcolicRegion(
                "REGION.OWNER.UNWIND", "ACT.OWNER.UNWIND");
        require(status == 0L, "owner-unwind region start rejected");
        System.markConcolicBranch("OWNER.ABANDONED", 1);
        int zero = 0;
        int ignored = 17 / zero;
        throw new AssertionError("division unexpectedly returned " + ignored);
    }

    /**
     * An uncaught exception must leave a queryable fail-closed summary while
     * its handler runs, then release the process-global region lock when the
     * owner JavaThread exits.
     */
    private static void verifyAbandonedOwnerCleanup() throws Exception {
        final String[] observedSummary = new String[1];
        Thread worker = new Thread(new Runnable() {
            @Override
            public void run() {
                abandonedOwner();
            }
        }, "causynth-owner-unwind");
        worker.setUncaughtExceptionHandler(
                new Thread.UncaughtExceptionHandler() {
                    @Override
                    public void uncaughtException(Thread thread,
                                                  Throwable failure) {
                        require(failure instanceof ArithmeticException,
                                "unexpected failure: " + failure);
                        observedSummary[0] =
                                System.getConcolicRegionSummary();
                    }
                });
        worker.start();
        worker.join();

        String aborted = observedSummary[0];
        require(aborted != null, "uncaught handler did not run");
        require(aborted.contains("\"active\":false"), aborted);
        require(aborted.contains("\"aborted\":true"), aborted);
        require(aborted.contains("\"complete\":false"), aborted);
        require(aborted.contains("\"status\":\"ABORTED\""), aborted);
        require(aborted.contains("\"abortReason\":"), aborted);
        require(aborted.contains("SHADOW_STACK_EXHAUSTED")
                        || aborted.contains("OWNER_JAVA_THREAD_EXIT"),
                aborted);
        require(!aborted.contains("OWNER.ABANDONED"), aborted);

        long recovery = System.startConcolicRegion(
                "REGION.OWNER.RECOVERY", "ACT.OWNER.RECOVERY");
        require(recovery == 0L,
                "abandoned context retained global lock: " + recovery);
        String recovered = System.finishConcolicRegion();
        require(recovered.contains("\"active\":true"), recovered);
        require(recovered.contains("\"aborted\":false"), recovered);
        require(recovered.contains("\"complete\":true"), recovered);
    }

    private static boolean emptyCondition(String events, String site) {
        String event = event(events, site);
        return event.contains("\"conditionIndices\":[]")
                && event.contains("\"conditionCount\":0");
    }

    private static boolean oneCondition(String events, String site) {
        String event = event(events, site);
        return event.contains("\"conditionCount\":1")
                && !event.contains("\"conditionIndices\":[]");
    }

    private static String event(String events, String site) {
        String identity = "\"siteId\":\"" + site + "\"";
        int identityOffset = events.indexOf(identity);
        if (identityOffset < 0) return "";
        int start = events.lastIndexOf('{', identityOffset);
        int end = events.indexOf('}', identityOffset);
        return start < 0 || end < start ? "" : events.substring(start,
                end + 1);
    }

    private static void require(boolean condition, String detail) {
        if (!condition) throw new AssertionError(detail);
    }
}
