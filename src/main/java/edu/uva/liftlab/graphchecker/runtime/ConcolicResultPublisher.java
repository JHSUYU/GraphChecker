package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.SharedStateReadOut;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.Executor;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ACTIVE;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.assembleRecordedSharedState;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;

final class ConcolicResultPublisher {
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    private static final ThreadPoolExecutor RESULT_PUBLICATION_EXECUTOR =
            engineThreads("causynth-result-publication-", 1, null);
    private static final ThreadPoolExecutor READ_OUT_DECODE_EXECUTOR =
            engineThreads("causynth-read-out-decode-", 1, null);

    static final int RECORD_DECODERS = 3;
    private static final List<Thread> RECORD_DECODER_THREADS =
            new CopyOnWriteArrayList<Thread>();
    private static final ThreadPoolExecutor RECORD_DECODE_EXECUTOR =
            engineThreads("causynth-read-out-record-", RECORD_DECODERS,
                    RECORD_DECODER_THREADS);

    static Executor recordDecoders() {
        return RECORD_DECODE_EXECUTOR;
    }

    private static ThreadPoolExecutor engineThreads(String name, int count,
                                                    List<Thread> made) {
        ThreadFactory threads = runnable -> {
            ThreadGroup root = Thread.currentThread().getThreadGroup();
            while (root.getParent() != null) root = root.getParent();
            Thread thread = new Thread(root, runnable, name
                    + PUBLICATION_THREAD_COUNTER.incrementAndGet(),
                    512L << 20);
            thread.setDaemon(true);
            if (made != null) made.add(thread);
            return thread;
        };
        return new ThreadPoolExecutor(count, count, 0L, TimeUnit.MILLISECONDS,
                new LinkedBlockingQueue<Runnable>(), threads);
    }
    private static int resultPublicationsInFlight;
    private static int liveSelectedRegions;

    private static final long TERMINAL_GRACE_MILLIS = 30_000L;

    static void taskUnanswered(RuntimeTask task, String detail) {
        boolean decided = FocusedReplay.noteUnansweredTask(detail);
        RowRuntime.gap(GapKind.TASK_UNANSWERED, GapClass.DIAGNOSTIC,
                task == null ? RowRuntime.sessionId()
                        : firstNonBlank(task.taskId, task.regionId,
                                task.occurrenceId, RowRuntime.sessionId()),
                detail);
        if (decided) concludeAtRefusal();
    }

    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        ActiveRegion running = null;
        List<ActiveRegion> behind = new ArrayList<>();
        Conclusion end;
        while (true) {
            List<ActiveRegion> live = null;
            synchronized (PUBLICATION_LOCK) {
                Grace grace = new Grace(TERMINAL_GRACE_MILLIS * 1_000_000L,
                        System.nanoTime(), progressLocked());
                boolean spent = gaveUp;
                while (!spent && (concluded == null || strandedAtEnd)
                        && (concluded == null ? liveSelectedRegions > 0
                        || resultPublicationsInFlight > 0
                        : stands(concluded)
                        && resultPublicationsInFlight > 0)) {
                    long remaining = grace.remaining(System.nanoTime(),
                            progressLocked());
                    if (remaining <= 0L) {
                        spent = true;
                        break;
                    }
                    try {
                        PUBLICATION_LOCK.wait(remaining / 1_000_000L,
                                (int) (remaining % 1_000_000L));
                    } catch (InterruptedException ignored) {
                        interrupted = true;
                    }
                }
                end = concluded;
                if (!spent && end != null && !strandedAtEnd) {
                    strandedAtEnd = true;
                    live = new ArrayList<>(ACTIVE.values());
                } else {
                    if (end != null || spent) stranded.addAll(ACTIVE.values());
                    if (spent && !gaveUp) {
                        running = publishingNow;
                        behind.addAll(queued);
                    }
                    gaveUp = spent;
                }
            }
            if (live == null) break;
            for (ActiveRegion active : live) {
                strandWithoutTerminal(active, endedThere(end));
            }
        }
        for (ActiveRegion active : stranded) {
            strandWithoutTerminal(active, end == null
                    ? "TERMINAL_NEVER_REACHED: the region root was still"
                    + " running " + TERMINAL_GRACE_MILLIS + "ms after the"
                    + " workload ended while nothing progressed, so this"
                    + " occurrence reached no NORMAL, THROW or bounded CUT"
                    + " terminal"
                    : endedThere(end));
        }
        String stall = " for " + TERMINAL_GRACE_MILLIS + "ms (no loop"
                + " body, settled activation, finished publication,"
                + " publication CPU or garbage collection) when the run"
                + " ended, which ended without it";
        if (running != null) {
            unsettled(running, "made no progress" + stall
                    + ": its rows may be partial");
        }
        for (ActiveRegion active : behind) {
            unsettled(active, "was queued behind one that made no progress"
                    + stall + ": it published no row");
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    private static String endedThere(Conclusion end) {
        return end + ": the region root was still running when " + end.when
                + ", and the replay ended there";
    }

    private static void unsettled(ActiveRegion active, String what) {
        String detail = "RESULT_PUBLICATION_UNSETTLED: the row publication"
                + " of this completed occurrence " + what;
        FocusedReplay.noteUnsettledPublication(detail);
        taskUnanswered(active.activation, detail);
    }

    static final class Grace {
        private final long graceNanos;
        private long[] progress;
        private long deadline;

        Grace(long graceNanos, long now, long[] progress) {
            this.graceNanos = graceNanos;
            this.progress = progress;
            this.deadline = now + graceNanos;
        }

        long remaining(long now, long[] observed) {
            if (!Arrays.equals(observed, progress)) {
                progress = observed;
                deadline = now + graceNanos;
            }
            return deadline - now;
        }
    }

    private static long[] progressLocked() {
        long[] moved = movedLocked();
        long[] progress = Arrays.copyOf(moved, moved.length + 3);
        progress[moved.length] = cpu(publishingThread);
        long decoding = cpu(decodingThread);
        boolean decodes = computing(decodingThread);
        for (Thread recordDecoder : RECORD_DECODER_THREADS) {
            decoding += cpu(recordDecoder);
            decodes |= computing(recordDecoder);
        }
        progress[moved.length + 1] = decoding;
        if (computing(publishingThread) || decodes) {
            collectedComputing = ScheduleLog.collectedMillis();
        }
        progress[moved.length + 2] = collectedComputing;
        return progress;
    }

    private static long collectedComputing;

    private static long cpu(Thread thread) {
        return thread == null ? 0L : ManagementFactory.getThreadMXBean()
                .getThreadCpuTime(thread.getId());
    }

    private static boolean computing(Thread thread) {
        return thread != null
                && thread.getState() == Thread.State.RUNNABLE;
    }

    private static long[] movedLocked() {
        long loops = 0L;
        for (ActiveRegion active : ACTIVE.values()) {
            loops += active.chargedLoopBodies;
        }
        return new long[] {publicationsFinished, loops, liveSelectedRegions,
                resultPublicationsInFlight, undecodedChars};
    }

    static final long NO_NEW_EVENT_MILLIS = 300_000L;
    private static final long LOOK_MILLIS = 10_000L;
    private static final int DUMP_FRAMES = 24;

    static void watchProgress() {
        if (FocusedReplay.obligationIds().isEmpty()
                || FocusedReplay.confirming()) {
            return;
        }
        ScheduleLog.countNewEvents();
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        Thread watch = new Thread(root, ConcolicResultPublisher::watch,
                "causynth-progress-watch");
        watch.setDaemon(true);
        watch.start();
    }

    private static void watch() {
        long bound = TimeUnit.MILLISECONDS.toNanos(NO_NEW_EVENT_MILLIS);
        FocusedComputing computing = new FocusedComputing();
        long computed = 0L;
        Grace grace = null;
        while (true) {
            try {
                Thread.sleep(LOOK_MILLIS);
            } catch (InterruptedException interrupted) {
                return;
            }
            synchronized (PUBLICATION_LOCK) {
                if (concluded != null) return;
            }
            if (computing.look()) computed++;
            if (RecordingWindow.index() == 0) continue;
            long now = System.nanoTime();
            if (grace == null) {
                grace = new Grace(bound, now, watched(computed));
                continue;
            }
            long remaining = grace.remaining(now, watched(computed));
            if (remaining > 0L) continue;
            String still = "nothing new for " + TimeUnit.NANOSECONDS
                    .toSeconds(bound - remaining) + " s (no event of a"
                    + " kind, site, node and context this run had not made"
                    + " before, no move of its question, its order or a"
                    + " hold, no focused activation computing)";
            Conclusion end = stall(still);
            if (end != null) {
                dumpThreads(still);
                conclude(end);
            }
            return;
        }
    }

    static Conclusion stall(String still) {
        if (!FocusedReplay.noProgress(still, ScheduleLog.holding())) {
            return null;
        }
        return FocusedReplay.stalledAfterFlip()
                ? Conclusion.STALLED_AFTER_FLIP : Conclusion.AT_NO_PROGRESS;
    }

    static long[] watched(long computed) {
        long[] question = FocusedReplay.questionMoved();
        long[] watched = Arrays.copyOf(question, question.length + 5);
        watched[question.length] = ScheduleLog.newKeys();
        watched[question.length + 1] = RecordingWindow.index();
        watched[question.length + 2] = ScheduleLog.settledSlots();
        watched[question.length + 3] = Confirmation.holdMoves();
        watched[question.length + 4] = computed;
        return watched;
    }

    static final class FocusedComputing {
        private final ThreadMXBean threads =
                ManagementFactory.getThreadMXBean();
        private Map<Long, Long> seen = new HashMap<Long, Long>();
        private long collected = ScheduleLog.collectedMillis();
        private long at = System.nanoTime();

        boolean look() {
            Map<Long, Long> now = new HashMap<Long, Long>();
            long most = 0L;
            for (ActiveRegion active : ACTIVE.values()) {
                if (active.finished.get() || active.thread == null
                        || !active.symbolicallyActive()) {
                    continue;
                }
                long id = active.thread.getId();
                long cpu = threads.getThreadCpuTime(id);
                if (cpu < 0L) continue;
                now.put(id, cpu);
                Long before = seen.get(id);
                if (before != null) most = Math.max(most, cpu - before);
            }
            long collectedNow = ScheduleLog.collectedMillis();
            long nanos = System.nanoTime();
            boolean computed = !now.isEmpty() && 2L * (most
                    + TimeUnit.MILLISECONDS.toNanos(collectedNow - collected))
                    >= nanos - at;
            seen = now;
            collected = collectedNow;
            at = nanos;
            return computed;
        }
    }

    private static void dumpThreads(String still) {
        StringBuilder dump = new StringBuilder("Causynth: "
                + FocusedReplay.REPLAY_NO_PROGRESS + ": " + still
                + "; its threads:");
        for (Map.Entry<Thread, StackTraceElement[]> thread
                : Thread.getAllStackTraces().entrySet()) {
            dump.append("\n\"").append(thread.getKey().getName())
                    .append("\" ").append(thread.getKey().getState());
            StackTraceElement[] frames = thread.getValue();
            for (int index = 0; index < Math.min(frames.length,
                    DUMP_FRAMES); index++) {
                dump.append("\n\tat ").append(frames[index]);
            }
            if (frames.length > DUMP_FRAMES) {
                dump.append("\n\t... ").append(frames.length - DUMP_FRAMES)
                        .append(" more");
            }
        }
        EngineConsole.println(dump.toString());
    }

    private static ActiveRegion publishingNow;
    private static Thread publishingThread;
    private static Thread decodingThread;
    private static final Set<ActiveRegion> queued =
            new LinkedHashSet<ActiveRegion>();
    private static long publicationsFinished;
    private static boolean gaveUp;
    private static boolean strandedAtEnd;
    private static long undecodedChars;

    enum Conclusion {
        AT_WITNESS("the declared occurrence observed the fatal"),
        AT_FORCED_TARGET("the declared occurrence reached its target forced"),
        AT_REFUSAL("a refusal decided every obligation this replay carries"),
        AT_MISMATCH("an edge the model chose was not taken, which refutes"
                + " the claim this run confirms"),
        AT_NO_PROGRESS("nothing new for " + NO_NEW_EVENT_MILLIS / 1000L
                + " s, which decided every obligation this replay carries"),
        STALLED_AFTER_FLIP("nothing new for " + NO_NEW_EVENT_MILLIS / 1000L
                + " s after a flip this replay was asked was taken: its"
                + " session stands, the questions still open are not"
                + " admitted");

        private final String when;

        Conclusion(String when) {
            this.when = when;
        }
    }

    static void concludeAtWitness() {
        conclude(Conclusion.AT_WITNESS);
    }

    static void concludeAtForcedTarget() {
        conclude(Conclusion.AT_FORCED_TARGET);
    }

    static void concludeAtRefusal() {
        conclude(Conclusion.AT_REFUSAL);
    }

    static void concludeAtMismatch() {
        conclude(Conclusion.AT_MISMATCH);
    }

    private static boolean stands(Conclusion end) {
        return end != Conclusion.AT_REFUSAL
                && end != Conclusion.AT_NO_PROGRESS;
    }

    private static void conclude(final Conclusion end) {
        synchronized (PUBLICATION_LOCK) {
            if (concluded != null) return;
            concluded = end;
            submittedAtEnd = stands(end) ? submitted : 0L;
            PUBLICATION_LOCK.notifyAll();
        }
        ConcolicRegionRuntime.endAdmission();
        if (stands(end)) ScheduleLog.witnessed();
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                EngineConsole.println("Causynth " + java.time.Instant.now()
                        + ": the replay ends " + end + ": " + end.when);
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-early-end").start();
    }

    static boolean concluded() {
        return concluded != null;
    }

    private static volatile Conclusion concluded;
    private static long submitted;
    private static long submittedAtEnd = Long.MAX_VALUE;

    private static void strandWithoutTerminal(ActiveRegion active,
                                              String detail) {
        if (!ConcolicRegionRuntime.strand(active)) return;
        active.releaseActivation();
        endLiveSelectedRegion();
        synchronized (active) {
            RowPublication.publishMints(active);
        }
        taskUnanswered(active.activation, detail);
    }

    static void beginLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            liveSelectedRegions++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void endLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            if (liveSelectedRegions <= 0) {
                throw new IllegalStateException(
                        "live selected region underflow");
            }
            liveSelectedRegions--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void beginSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            resultPublicationsInFlight++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void endSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            if (resultPublicationsInFlight <= 0) {
                throw new IllegalStateException(
                        "selected result publication underflow");
            }
            resultPublicationsInFlight--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void publishRunTotals() {
        configuration().publishUnansweredAddresses();
        RecordingWindow.measured();
        RowRuntime.closeSession();
    }

    static boolean awaitDecodeRoom(long chars) {
        boolean interrupted = false;
        try {
            synchronized (PUBLICATION_LOCK) {
                Grace grace = new Grace(TERMINAL_GRACE_MILLIS * 1_000_000L,
                        System.nanoTime(), progressLocked());
                while (undecodedChars > 0L
                        && undecodedChars + chars > UNDECODED_BOUND_CHARS
                        && !gaveUp && concluded == null) {
                    long remaining = grace.remaining(System.nanoTime(),
                            progressLocked());
                    if (remaining <= 0L) break;
                    try {
                        PUBLICATION_LOCK.wait(remaining / 1_000_000L,
                                (int) (remaining % 1_000_000L));
                    } catch (InterruptedException ignored) {
                        interrupted = true;
                    }
                }
                return concluded == null;
            }
        } finally {
            if (interrupted) Thread.currentThread().interrupt();
        }
    }

    static boolean decodeInOrder(long chars, Runnable decode) {
        synchronized (PUBLICATION_LOCK) {
            undecodedChars += chars;
        }
        try {
            READ_OUT_DECODE_EXECUTOR.execute(() -> {
                synchronized (PUBLICATION_LOCK) {
                    decodingThread = Thread.currentThread();
                }
                try {
                    decode.run();
                } finally {
                    decoded(chars);
                }
            });
            return true;
        } catch (RejectedExecutionException rejected) {
            decoded(chars);
            return false;
        }
    }

    private static void decoded(long chars) {
        synchronized (PUBLICATION_LOCK) {
            undecodedChars -= chars;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static boolean withholds(SharedStateReadOut readOut) {
        if (concluded == null) return false;
        synchronized (PUBLICATION_LOCK) {
            return concluded != null && (readOut.ordinal == 0L
                    || readOut.ordinal > submittedAtEnd);
        }
    }

    private static final long UNDECODED_BOUND_CHARS = 64L << 20;

    static boolean submitCompletedResultPublication(
            final ActiveRegion active,
            final SharedStateReadOut sharedState) {
        active.activation.reserveCompletedEvidence();
        configuration().releaseCandidate(active.activation);
        final long ordinal;
        synchronized (PUBLICATION_LOCK) {
            ordinal = ++submitted;
            queued.add(active);
            if (sharedState != null) sharedState.ordinal = ordinal;
        }
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(new Runnable() {
                @Override
                public void run() {
                    publishCompletedResult(active, sharedState, ordinal);
                }
            });
            return true;
        } catch (RejectedExecutionException rejected) {
            synchronized (PUBLICATION_LOCK) {
                queued.remove(active);
            }
            taskUnanswered(active.activation, "RESULT_PUBLICATION_REJECTED: "
                    + "the row publication of a completed VM occurrence could"
                    + " not be enqueued: " + rootCause(rejected));
            return false;
        }
    }

    private static void publishCompletedResult(
            ActiveRegion active, SharedStateReadOut sharedState,
            long ordinal) {
        try {
            Conclusion late;
            synchronized (PUBLICATION_LOCK) {
                late = ordinal > submittedAtEnd ? concluded : null;
                queued.remove(active);
                publishingNow = active;
                publishingThread = Thread.currentThread();
            }
            if (late != null) {
                configuration().markOccurrenceClaimed(active.activation);
                RowPublication.publishMints(active);
                taskUnanswered(active.activation, late + ": this occurrence"
                        + " was still unpublished when " + late.when
                        + ", and the replay ended there");
                return;
            }
            if (sharedState != null) sharedState.awaitDecoded();
            assembleRecordedSharedState(active, sharedState);
            RowPublication.publish(active);
            if (resultAnswersSelectedGoal(active)) {
                configuration().markOccurrenceClaimed(active.activation);
            }
        } catch (Throwable failure) {
            configuration().markOccurrenceClaimed(active.activation);
            try {
                taskUnanswered(active.activation,
                        "RESULT_PUBLICATION_FAILED: a completed VM occurrence"
                                + " could not publish its rows: "
                                + rootCause(failure));
            } catch (Throwable reportingFailure) {
                EngineConsole.println("Causynth could not publish"
                        + " TASK_UNANSWERED for "
                        + active.activation.taskId + ": "
                        + rootCause(reportingFailure));
            }
        } finally {
            synchronized (PUBLICATION_LOCK) {
                publishingNow = null;
                publicationsFinished++;
            }
            endSelectedResultPublication();
        }
    }

    private static boolean resultAnswersSelectedGoal(ActiveRegion active) {
        RuntimeTask task = active.activation;
        if (!task.loopBodyRoot || !task.capturesTargetReach) return true;
        return task.targetGuards.size() > 1
                ? RowPublication.tookDisjunct(active, new ArrayList<String>())
                : task.reachedRequiredTargetOutcome(active.targetReach);
    }
}
