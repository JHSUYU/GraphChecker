import java.util.concurrent.CountDownLatch;

/**
 * Regression for the execution model used by GraphChecker's MiniDFSCluster
 * campaigns: many application threads share one JVM, but at most one thread
 * owns a concolic context at a time.  Consecutive regions may be owned by
 * different Java threads.
 */
public final class RegionThreadIsolationSmoke {
    private static final int THREADS = 2;
    private static final int REGIONS_PER_THREAD = 3;
    private static final int EXCEPTION_RECOVERY_ROUNDS = 8;

    private static final class Input {
        int value;

        Input(int value) {
            this.value = value;
        }
    }

    private static final class Gate {
        final CountDownLatch active = new CountDownLatch(1);
        final CountDownLatch observed = new CountDownLatch(1);
        volatile Input input;
        volatile String nonOwnerView;
    }

    private static final class AllocationPressure implements Runnable {
        final CountDownLatch firstGc = new CountDownLatch(1);
        volatile boolean running = true;
        volatile Throwable failure;
        volatile long allocations;
        volatile long gcRequests;

        public void run() {
            try {
                byte[][] ring = new byte[32][];
                int slot = 0;
                while (running) {
                    ring[slot] = new byte[8 * 1024];
                    slot = (slot + 1) & (ring.length - 1);
                    long count = ++allocations;
                    if ((count & 63L) == 1L) {
                        gcRequests++;
                        System.gc();
                        firstGc.countDown();
                    }
                }
            } catch (Throwable throwable) {
                failure = throwable;
                firstGc.countDown();
            }
        }
    }

    private static volatile int sink;

    public static void main(String[] args) throws Exception {
        AllocationPressure pressure = new AllocationPressure();
        Thread allocator = new Thread(pressure, "concurrent-gc-allocator");
        allocator.start();
        pressure.firstGc.await();
        require(pressure.failure == null,
                "allocation pressure failed: " + pressure.failure);
        long gcRequestsBeforeRegions = pressure.gcRequests;

        try {
            rejectOverlappingContextAndRecover();
            recoverAfterExceptionalControlFlow();
            for (int threadIndex = 0; threadIndex < THREADS; threadIndex++) {
                final int owner = threadIndex;
                final Gate[] gates = new Gate[REGIONS_PER_THREAD];
                for (int index = 0; index < gates.length; index++) {
                    gates[index] = new Gate();
                }

                Thread worker = new Thread(new Runnable() {
                    public void run() {
                        runRegions(owner, gates);
                    }
                }, "region-worker-" + owner);

                worker.start();
                for (int regionIndex = 0;
                     regionIndex < REGIONS_PER_THREAD;
                     regionIndex++) {
                    Gate gate = gates[regionIndex];
                    gate.active.await();

                    // The main thread has no TLS concolic context.  Its
                    // concrete branches over the same heap object must not
                    // enter the worker's path condition.
                    Input input = gate.input;
                    for (int repeat = 0; repeat < 25; repeat++) {
                        if (input.value > -1000000) {
                            sink++;
                        }
                    }
                    gate.nonOwnerView = System.getConcolicRegionSummary();
                    gate.observed.countDown();
                }
                worker.join();
            }
        } finally {
            pressure.running = false;
            allocator.join();
        }

        require(pressure.failure == null,
                "allocation pressure failed: " + pressure.failure);
        require(pressure.allocations > 0L,
                "allocation pressure did not execute");
        require(pressure.gcRequests > gcRequestsBeforeRegions,
                "GC pressure did not continue during region tests");
        require(sink == THREADS * REGIONS_PER_THREAD * 25,
                "unexpected sink=" + sink);
        System.out.println("CAUSYNTH_REGION_THREAD_ISOLATION_SMOKE_OK");
    }

    private static void recoverAfterExceptionalControlFlow() {
        Input reused = new Input(29);
        for (int round = 0; round < EXCEPTION_RECOVERY_ROUNDS; round++) {
            final String prefix = "exception_round_" + round;
            final String[] summary = new String[1];
            boolean caught = false;
            try {
                runExceptionalRegion(reused, round, prefix, summary);
            } catch (ExpectedException expected) {
                caught = true;
            }

            require(caught, "expected exception was not observed");
            require(has(summary[0], "\"regionId\":\"REGION.exception."
                    + round + "\""), summary[0]);
            require(has(summary[0], prefix), summary[0]);
            requireInactive(System.getConcolicRegionSummary());

            // Re-symbolizing the same object in a fresh context detects stale
            // symbolic ids left behind by the preceding exceptional finish.
            long recovery = System.startConcolicRegion(
                    "REGION.exception.recovery." + round,
                    "ACT.exception.recovery." + round);
            require(recovery == 0L,
                    "exception recovery start rejected: " + recovery);
            System.symbolizeField(reused, "value",
                    "exception_recovery_" + round);
            if (reused.value > -1000) {
                sink += 0;
            }
            String recovered = System.finishConcolicRegion();
            require(has(recovered, "exception_recovery_" + round),
                    recovered);
            requireInactive(System.getConcolicRegionSummary());
        }
    }

    private static void runExceptionalRegion(Input input, int round,
                                             String prefix,
                                             String[] summary) {
        long started = System.startConcolicRegion(
                "REGION.exception." + round,
                "ACT.exception." + round);
        require(started == 0L,
                "exception region start rejected: " + started);
        System.symbolizeField(input, "value", prefix);
        try {
            if (input.value > -1000) {
                throw new ExpectedException();
            }
        } finally {
            summary[0] = System.finishConcolicRegion();
        }
    }

    private static final class ExpectedException extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }

    private static void rejectOverlappingContextAndRecover()
            throws Exception {
        final CountDownLatch ownerActive = new CountDownLatch(1);
        final CountDownLatch releaseOwner = new CountDownLatch(1);
        final Throwable[] failure = new Throwable[1];

        Thread owner = new Thread(new Runnable() {
            public void run() {
                try {
                    Input input = new Input(17);
                    long started = System.startConcolicRegion(
                            "REGION.overlap.owner", "ACT.overlap.owner");
                    require(started == 0L, "owner start rejected: " + started);
                    System.symbolizeField(input, "value", "overlap_owner");
                    ownerActive.countDown();
                    await(releaseOwner);
                    if (input.value > 0) {
                        sink += 0;
                    }
                    String summary = System.finishConcolicRegion();
                    require(has(summary,
                            "\"regionId\":\"REGION.overlap.owner\""),
                            summary);
                    require(has(summary, "overlap_owner"), summary);
                } catch (Throwable throwable) {
                    failure[0] = throwable;
                    ownerActive.countDown();
                }
            }
        }, "overlap-owner");

        owner.start();
        ownerActive.await();
        if (failure[0] != null) {
            throw new AssertionError(failure[0]);
        }

        long rejected = System.startConcolicRegion(
                "REGION.overlap.contender", "ACT.overlap.contender");
        require(rejected != 0L,
                "overlapping context was not rejected");
        requireInactive(System.getConcolicRegionSummary());
        releaseOwner.countDown();
        owner.join();
        if (failure[0] != null) {
            throw new AssertionError(failure[0]);
        }

        long recovery = System.startConcolicRegion(
                "REGION.overlap.recovery", "ACT.overlap.recovery");
        require(recovery == 0L, "post-overlap recovery failed: " + recovery);
        String recovered = System.finishConcolicRegion();
        require(has(recovered,
                "\"regionId\":\"REGION.overlap.recovery\""), recovered);
        require(has(recovered, "\"pathCondition\":[]"), recovered);
    }

    private static void runRegions(int threadIndex, Gate[] gates) {
        for (int regionIndex = 0;
             regionIndex < REGIONS_PER_THREAD;
             regionIndex++) {
            String regionId = "REGION.thread." + threadIndex + "."
                    + regionIndex;
            String activationId = "ACT.thread." + threadIndex + "."
                    + regionIndex;
            String prefix = "thread_" + threadIndex + "_region_"
                    + regionIndex;
            Input input = new Input(threadIndex * 100 + regionIndex + 1);
            Gate gate = gates[regionIndex];

            long started = System.startConcolicRegion(regionId, activationId);
            require(started == 0L, "region start rejected: " + started);
            String atStart = System.getConcolicRegionSummary();
            System.symbolizeField(input, "value", prefix);
            String beforeForeignBranch = System.getPathCondition();

            gate.input = input;
            gate.active.countDown();
            await(gate.observed);

            String afterForeignBranch = System.getPathCondition();
            boolean ownDecision = input.value > -1000;
            String afterOwnBranch = System.getPathCondition();
            String finished = System.finishConcolicRegion();
            String afterFinish = System.getConcolicRegionSummary();

            require(ownDecision, "worker decision unexpectedly false");
            require(has(atStart, "\"active\":true"), atStart);
            require(has(atStart, "\"regionId\":\"" + regionId + "\""),
                    atStart);
            require(has(atStart,
                    "\"taskId\":\"" + activationId + "\""),
                    atStart);
            require(has(atStart, "\"pathCondition\":[]"), atStart);

            require(beforeForeignBranch.equals(afterForeignBranch),
                    "foreign thread polluted PC: before="
                            + beforeForeignBranch + " after="
                            + afterForeignBranch);
            require(!"[]".equals(afterOwnBranch),
                    "worker branch was not recorded");
            require(!beforeForeignBranch.equals(afterOwnBranch),
                    "worker branch did not extend PC");
            require(has(finished, "\"regionId\":\"" + regionId + "\""),
                    finished);
            require(has(finished,
                    "\"taskId\":\"" + activationId + "\""),
                    finished);
            require(has(finished, prefix), finished);

            requireInactive(gate.nonOwnerView);
            requireInactive(afterFinish);
        }
    }

    private static void await(CountDownLatch latch) {
        try {
            latch.await();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new AssertionError(interrupted);
        }
    }

    private static void requireInactive(String summary) {
        require(has(summary, "\"active\":false"), summary);
        require(has(summary, "\"regionId\":\"\""), summary);
        require(has(summary, "\"taskId\":\"\""), summary);
        require(has(summary, "\"pathCondition\":[]"), summary);
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
