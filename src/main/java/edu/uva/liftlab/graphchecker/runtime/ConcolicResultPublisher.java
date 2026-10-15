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

/**
 * Settling one region occurrence: the daemon pool that publishes its rows,
 * the process-exit barrier, and the {@link GapKind#TASK_UNANSWERED} row for
 * a planned task nothing answered.  No result envelope: the row set
 * ({@link SessionPublisher}) is the whole contract.
 */
final class ConcolicResultPublisher {
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * Publication must not hold an RPC handler after the VM read-out, and
     * must not drop a completed occurrence either: its queue has no bound.
     * Bounded at 128, it rejected SOLR-18406's declared occurrence while the
     * interpreter was still hashing the expressions of earlier ones.
     */
    private static final ThreadPoolExecutor RESULT_PUBLICATION_EXECUTOR =
            new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS,
                    new LinkedBlockingQueue<Runnable>(),
                    new ThreadFactory() {
                        @Override
                        public Thread newThread(Runnable runnable) {
                            // In the JVM's root group, not the group of the
                            // test that first published: a test framework
                            // fails its suite on a thread its group leaks.
                            ThreadGroup root =
                                    Thread.currentThread().getThreadGroup();
                            while (root.getParent() != null) {
                                root = root.getParent();
                            }
                            // Compaction recurses along an expression
                            // chain: the engine's stack (java.sh -Xss).
                            Thread thread = new Thread(root, runnable,
                                    "causynth-result-publication-"
                                            + PUBLICATION_THREAD_COUNTER
                                            .incrementAndGet(),
                                    512L << 20);
                            thread.setDaemon(true);
                            return thread;
                        }
                    });
    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static int resultPublicationsInFlight;
    /** Live selected activations not yet publishing. */
    private static int liveSelectedRegions;

    /** How long the end of a run waits on what makes no progress. */
    private static final long TERMINAL_GRACE_MILLIS = 30_000L;

    /** The row naming a task nothing answered; {@code detail} says why. */
    static void taskUnanswered(RuntimeTask task, String detail) {
        // An abandoned occurrence publishes nothing, so the replay's verdict
        // must know before it calls a prefix reproduced.
        boolean decided = FocusedReplay.noteUnansweredTask(detail);
        // Never name nothing: Fields.text would refuse; taskId may be blank.
        RowRuntime.gap(GapKind.TASK_UNANSWERED, GapClass.DIAGNOSTIC,
                task == null ? RowRuntime.sessionId()
                        : firstNonBlank(task.taskId, task.regionId,
                                task.occurrenceId, RowRuntime.sessionId()),
                detail);
        if (decided) concludeAtRefusal();
    }

    /**
     * THE SETTLE, the one wait of every end of a run (the workload's, its
     * witness's, a deciding refusal's or stall's; {@code
     * JUnitMethodRunner#exit}).
     *
     * <p>After the workload's own end it waits until no selected activation
     * is live and no publication runs; after an early end only for the
     * publications, and every activation still live is stranded at once
     * (retrying its work, it would keep resetting any grace).  Either way
     * the wait is bounded by progress: it gives up once nothing has moved
     * for {@link #TERMINAL_GRACE_MILLIS} ({@link #progressLocked}: no loop
     * body charged, no activation settled, no publication finished, no CPU
     * on the publication thread and no garbage collection), so a
     * publication that computes is never cut and one blocked is
     * (unbounded, a stuck publication kept a decided replay running to its
     * {@code replay_timeout_s}).  Then every activation still live is
     * stranded, and the publication still running and every one queued
     * behind it are named ({@code RESULT_PUBLICATION_UNSETTLED}, a seed's
     * or a confirmation's session included); the run ends without them, and
     * a later settle of the same run waits for nothing.</p>
     */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        ActiveRegion running = null;
        List<ActiveRegion> behind = new ArrayList<>();
        final Conclusion end;
        synchronized (PUBLICATION_LOCK) {
            Grace grace = new Grace(TERMINAL_GRACE_MILLIS * 1_000_000L,
                    System.nanoTime(), progressLocked());
            boolean spent = gaveUp;
            // An early end met while waiting stops the wait for the live.
            while (!spent && ((concluded == null && liveSelectedRegions > 0)
                    || resultPublicationsInFlight > 0)) {
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
            if (end != null || spent) stranded.addAll(ACTIVE.values());
            if (spent && !gaveUp) {
                // The one running, and every one queued behind it: the one
                // publication thread will reach none of them.
                running = publishingNow;
                behind.addAll(queued);
            }
            gaveUp = spent;
        }
        // Outside the barrier lock: each of these files a durable row.
        for (ActiveRegion active : stranded) {
            strandWithoutTerminal(active, end == null
                    ? "TERMINAL_NEVER_REACHED: the region root was still"
                    + " running " + TERMINAL_GRACE_MILLIS + "ms after the"
                    + " workload ended while nothing progressed, so this"
                    + " occurrence reached no NORMAL, THROW or bounded CUT"
                    + " terminal"
                    : end + ": the region root was still running when "
                    + end.when + ", and the replay ended there");
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

    /** Names one publication the run ended without; the replay's
     *  obligations admit nothing over a session missing its rows. */
    private static void unsettled(ActiveRegion active, String what) {
        String detail = "RESULT_PUBLICATION_UNSETTLED: the row publication"
                + " of this completed occurrence " + what;
        FocusedReplay.noteUnsettledPublication(detail);
        taskUnanswered(active.activation, detail);
    }

    /**
     * A wait's bound: spent once {@code graceNanos} pass with nothing moved,
     * each move restarting it.
     */
    static final class Grace {
        private final long graceNanos;
        private long[] progress;
        private long deadline;

        Grace(long graceNanos, long now, long[] progress) {
            this.graceNanos = graceNanos;
            this.progress = progress;
            this.deadline = now + graceNanos;
        }

        /** Nanoseconds left once {@code observed} is noted; not above zero
         *  when the grace is spent. */
        long remaining(long now, long[] observed) {
            if (!Arrays.equals(observed, progress)) {
                progress = observed;
                deadline = now + graceNanos;
            }
            return deadline - now;
        }
    }

    /**
     * What moves while a run settles: what {@link #movedLocked} counts, the
     * CPU the publication thread spent, and the JVM's time in garbage
     * collection (a collection stops that thread too).
     * Called under {@link #PUBLICATION_LOCK}.
     */
    private static long[] progressLocked() {
        long[] moved = movedLocked();
        long[] progress = Arrays.copyOf(moved, moved.length + 2);
        progress[moved.length] = publishingThread == null ? 0L
                : ManagementFactory.getThreadMXBean()
                .getThreadCpuTime(publishingThread.getId());
        progress[moved.length + 1] = ScheduleLog.collectedMillis();
        return progress;
    }

    /**
     * What every wait on progress counts: publications finished, loop
     * bodies the live activations charged, how many activations are live
     * and publications running, and the read-out text still to decode.
     * Called under {@link #PUBLICATION_LOCK}.
     */
    private static long[] movedLocked() {
        long loops = 0L;
        for (ActiveRegion active : ACTIVE.values()) {
            loops += active.chargedLoopBodies;
        }
        return new long[] {publicationsFinished, loops, liveSelectedRegions,
                resultPublicationsInFlight, undecodedChars};
    }

    /**
     * How long a focused replay asked a flip may stand still in its window
     * before it is decided there, by name ({@link #watchProgress}): 600 s,
     * the recording's own stall bound ({@code campaign_unbounded_stall_s}).
     * Of 1,596 Solr replays that ended by themselves (SG1, FA1-5, MB, Z),
     * an admitted one went at most 122 s without a log line inside its
     * window (a schedule stall's ceiling, 8 timeouts of 15 s), and one 300 s
     * (an HTTP call waiting out its socket timeout, NOT_ADMITTED); each of
     * the 172 killed at replay_timeout_s (solr-bugs-reindex-cleanup: an
     * Overseer command waiting for a response node already deleted, in a
     * tree whose waits never time out) worked about 80 s and then stood
     * still for 2,320 s.
     */
    static final long NO_PROGRESS_MILLIS = 600_000L;
    /** How often the watch looks. */
    private static final long LOOK_MILLIS = 10_000L;
    /** The most frames of one thread the watch's dump shows. */
    private static final int DUMP_FRAMES = 24;

    /**
     * THE WATCH of a focused replay asked a flip: once nothing has moved for
     * {@link #NO_PROGRESS_MILLIS} -- no schedule step ({@link
     * ScheduleLog#steps}: a WAKE or a tick's END is the clock, not a step),
     * nothing the settle counts ({@link #movedLocked})
     * and no thread computing ({@link Computing}) -- every question still
     * open is NOT_ADMITTED by REPLAY_NO_PROGRESS, which names the
     * schedule's holds then ({@code FocusedReplay#noProgress}, {@code
     * ScheduleLog#holding}), its threads are dumped on its log, and it ends,
     * long before {@code replay_timeout_s} would kill it: decided, its
     * session withdrawn, when no flip it was asked was taken yet ({@link
     * Conclusion#AT_NO_PROGRESS}); its session standing as the run made it,
     * the flips taken keeping their verdicts, when one was ({@link
     * Conclusion#STALLED_AFTER_FLIP}).  Only inside the
     * recording window ({@link RecordingWindow#opened}): before it the
     * cluster starts, and after it the test is over -- its teardown answers
     * nothing the question asked, and may wait (solr-18413 FA5: an admitted
     * replay's teardown stood 275 s on an Overseer command).  Never the
     * seed's replay (it carries no obligation) nor a confirmation's (its
     * verdict rules stand); a replay whose workload ended settles on the
     * settle's bound.
     */
    static void watchProgress() {
        if (FocusedReplay.obligationIds().isEmpty()
                || FocusedReplay.confirming()) {
            return;
        }
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        Thread watch = new Thread(root, ConcolicResultPublisher::watch,
                "causynth-progress-watch");
        watch.setDaemon(true);
        watch.start();
    }

    private static void watch() {
        Computing computing = new Computing();
        long computed = 0L;
        Grace grace = new Grace(TimeUnit.MILLISECONDS.toNanos(
                NO_PROGRESS_MILLIS), System.nanoTime(), watched(computed));
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
            if (!RecordingWindow.opened()) {
                grace = new Grace(TimeUnit.MILLISECONDS.toNanos(
                        NO_PROGRESS_MILLIS), System.nanoTime(),
                        watched(computed));
                continue;
            }
            long remaining = grace.remaining(System.nanoTime(),
                    watched(computed));
            if (remaining > 0L) continue;
            String still = "nothing moved for " + TimeUnit.NANOSECONDS
                    .toSeconds(TimeUnit.MILLISECONDS.toNanos(
                            NO_PROGRESS_MILLIS) - remaining) + " s (no"
                    + " schedule step, no activation began or settled, no"
                    + " loop body, no publication, no thread computing)";
            if (FocusedReplay.noProgress(still, ScheduleLog.holding())) {
                dumpThreads(still);
                conclude(FocusedReplay.stalledAfterFlip()
                        ? Conclusion.STALLED_AFTER_FLIP
                        : Conclusion.AT_NO_PROGRESS);
            }
            return;
        }
    }

    /** What the watch sees move: the settle's counts, the schedule's
     *  steps, and the looks that saw a thread computing. */
    private static long[] watched(long computed) {
        long[] moved;
        synchronized (PUBLICATION_LOCK) {
            moved = movedLocked();
        }
        long[] watched = Arrays.copyOf(moved, moved.length + 2);
        watched[moved.length] = ScheduleLog.steps();
        watched[moved.length + 1] = computed;
        return watched;
    }

    /**
     * Whether a thread computed since the last look: one thread used, with
     * the collectors, half the look's span (the schedule's measure of
     * computing, {@code ScheduleLog#lookLocked}).  One thread, not a sum: a
     * hung cluster test's threads still ping its ZooKeeper, each a little.
     */
    static final class Computing {
        private final ThreadMXBean threads =
                ManagementFactory.getThreadMXBean();
        private Map<Long, Long> seen = cpu();
        private long collected = ScheduleLog.collectedMillis();
        private long at = System.nanoTime();

        boolean look() {
            Map<Long, Long> now = cpu();
            long most = 0L;
            for (Map.Entry<Long, Long> thread : now.entrySet()) {
                Long before = seen.get(thread.getKey());
                most = Math.max(most, thread.getValue()
                        - (before == null ? 0L : before));
            }
            long collectedNow = ScheduleLog.collectedMillis();
            long nanos = System.nanoTime();
            boolean computed = 2L * (most + TimeUnit.MILLISECONDS.toNanos(
                    collectedNow - collected)) >= nanos - at;
            seen = now;
            collected = collectedNow;
            at = nanos;
            return computed;
        }

        private Map<Long, Long> cpu() {
            Map<Long, Long> cpu = new HashMap<Long, Long>();
            for (long id : threads.getAllThreadIds()) {
                long nanos = threads.getThreadCpuTime(id);
                if (nanos >= 0L) cpu.put(id, nanos);
            }
            return cpu;
        }
    }

    /** Every thread's stack on the replay log, as a SIGQUIT would put it:
     *  what the stalled run waits on. */
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

    /** Guarded by {@link #PUBLICATION_LOCK}: the publication running, its
     *  thread, how many have finished, and whether a settle gave up. */
    private static ActiveRegion publishingNow;
    private static Thread publishingThread;
    /** Submitted and not yet started, in submission order. */
    private static final Set<ActiveRegion> queued =
            new LinkedHashSet<ActiveRegion>();
    private static long publicationsFinished;
    private static boolean gaveUp;
    /** Read-out text handed to the publication thread and not yet decoded,
     *  in chars ({@link #decodeBeforePublication}). */
    private static long undecodedChars;

    /** Why a focused replay ends before its workload does. */
    private enum Conclusion {
        /** The case's declared occurrence observed the fatal. */
        AT_WITNESS("the declared occurrence observed the fatal"),
        /** A FORCE run's declared occurrence published its forced target
         *  ({@code ForcedArms}). */
        AT_FORCED_TARGET("the declared occurrence reached its target forced"),
        /** A refusal decided every obligation the replay carries
         *  ({@code FocusedReplay#refusedAt}). */
        AT_REFUSAL("a refusal decided every obligation this replay carries"),
        /** Nothing moved for {@link #NO_PROGRESS_MILLIS} ({@link
         *  #watchProgress}), which decided every obligation it carries. */
        AT_NO_PROGRESS("nothing moved for " + NO_PROGRESS_MILLIS / 1000L
                + " s, which decided every obligation this replay carries"),
        /** Nothing moved for {@link #NO_PROGRESS_MILLIS} after a flip the
         *  replay was asked was taken: the session stands as the run made
         *  it, the obligations still open NOT_ADMITTED. */
        STALLED_AFTER_FLIP("nothing moved for " + NO_PROGRESS_MILLIS / 1000L
                + " s after a flip this replay was asked was taken: its"
                + " session stands, the questions still open are not"
                + " admitted");

        private final String when;

        Conclusion(String when) {
            this.when = when;
        }
    }

    /**
     * Ends a focused replay at its witness: the case's declared occurrence
     * observed the fatal, which answers the replay's question, and what the
     * workload does after it no stage reads (SOLR-18406: a follower retried
     * the download it could no longer get, every bound lifted, until the
     * worker's clock killed the JVM and the witness session was withdrawn).
     * The schedule states the run cut there ({@link ScheduleLog#witnessed}).
     */
    static void concludeAtWitness() {
        conclude(Conclusion.AT_WITNESS);
    }

    /**
     * Ends a FORCE run at its forced target (PIPELINE §7.10): the forced
     * path condition is stated, and what the forced world does after it no
     * stage reads.  Its session is read whole up to there, as a witness's.
     */
    static void concludeAtForcedTarget() {
        conclude(Conclusion.AT_FORCED_TARGET);
    }

    /**
     * Ends a focused replay at the refusal that decided every obligation it
     * carries ({@code FocusedReplay#refusedAt}): each verdict is NOT_ADMITTED
     * whatever the run does next, and the session is published to no stage,
     * so the rest of the workload answers nothing (SOLR-18413 r5: 67 focused
     * replays of 10 to 22 minutes, each refused at a constructor's branch and
     * run to the test's end).
     */
    static void concludeAtRefusal() {
        conclude(Conclusion.AT_REFUSAL);
    }

    /**
     * The one early end, once, on a thread of its own: admission ends, and
     * the replay ends as every replay does ({@link JUnitMethodRunner#exit}),
     * whose settle, the end standing, waits only for the publications and
     * strands every activation still live.
     *
     * <p>What still publishes differs.  At the witness, at a forced
     * target, or at a stall after a flip was taken, every occurrence
     * completed before it (the witness's own among them): its session is a
     * corpus session, read whole up to there, and its schedule states the
     * run cut there.  At a refusal or a stall before any flip, no
     * publication that has not started: the session is withdrawn, and
     * draining the queue
     * into it cost a Solr replay two to five minutes past the test's end
     * (solr-18413 r5, ee).  A withheld one's mints still publish.</p>
     */
    /** Whether a replay ended so keeps its session ({@link #conclude}). */
    private static boolean stands(Conclusion end) {
        return end != Conclusion.AT_REFUSAL
                && end != Conclusion.AT_NO_PROGRESS;
    }

    private static void conclude(final Conclusion end) {
        synchronized (PUBLICATION_LOCK) {
            if (concluded != null) return;
            concluded = end;
            submittedAtEnd = stands(end) ? submitted : 0L;
            // A settle already waiting for the live stops waiting for them.
            PUBLICATION_LOCK.notifyAll();
        }
        ConcolicRegionRuntime.endAdmission();
        if (stands(end)) ScheduleLog.witnessed();
        ThreadGroup root = Thread.currentThread().getThreadGroup();
        while (root.getParent() != null) root = root.getParent();
        new Thread(root, new Runnable() {
            @Override
            public void run() {
                // The replay log's one line saying when and why it ended, as
                // a UTC instant: a workload may randomize the JVM's zone
                // (Solr's test framework does).
                EngineConsole.println("Causynth " + java.time.Instant.now()
                        + ": the replay ends " + end + ": " + end.when);
                JUnitMethodRunner.exit(0);
            }
        }, "causynth-early-end").start();
    }

    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static Conclusion concluded;
    /**
     * Publications submitted, and how many were when the replay's end
     * stood: one completed after it is no part of the question, and
     * publishing it kept the queue from ever draining (SOLR-18406's follower
     * retried the download, each retry an occurrence with its own
     * publication).  Guarded by {@link #PUBLICATION_LOCK}.
     */
    private static long submitted;
    private static long submittedAtEnd = Long.MAX_VALUE;

    /**
     * Settles one activation whose root reached no terminal before the run
     * ended.  Its path is withheld and its mints published, as an abandoned
     * occurrence's are: other activations' rows already name those symbols
     * (hdfs-11741 r1: IMPORT invariant 11, a root symbol with no
     * RootMintRow).  Its thread still runs and may mint meanwhile; its own
     * terminal, if it comes, closes its VM region
     * ({@code ConcolicRegionRuntime#strand}).
     */
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

    /**
     * Publishes what only the end of a run can state: the planned addresses
     * nothing answered, the window's duration, and the session's close,
     * which states the replay's verdict ({@link RowRuntime#closeSession}).
     * Called once, by the run's one end ({@code JUnitMethodRunner#exit}),
     * after the settle; nothing is published after it.
     */
    static void publishRunTotals() {
        configuration().publishUnansweredAddresses();
        RecordingWindow.measured();
        RowRuntime.closeSession();
    }

    /**
     * Decodes one read-out page of {@code chars} on the publication thread
     * ahead of every publication queued after it, in order (one thread, one
     * queue): an activation's pages are decoded there as they are read,
     * before its publication ({@code SharedStateCapture
     * #captureRecordedSharedState}).  The page is handed on once the pages
     * before it, not yet decoded, leave room for it under
     * {@link #UNDECODED_BOUND_CHARS} (or none is left); until then the
     * reading thread waits, bounded by progress as the settle is
     * ({@link Grace}), so a stuck publication delays it, never holds it.
     *
     * @return false when the executor refused the work
     */
    static boolean decodeBeforePublication(long chars, Runnable decode) {
        boolean interrupted = false;
        synchronized (PUBLICATION_LOCK) {
            Grace grace = new Grace(TERMINAL_GRACE_MILLIS * 1_000_000L,
                    System.nanoTime(), progressLocked());
            while (undecodedChars > 0L
                    && undecodedChars + chars > UNDECODED_BOUND_CHARS
                    && !gaveUp) {
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
            undecodedChars += chars;
        }
        if (interrupted) Thread.currentThread().interrupt();
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(() -> {
                synchronized (PUBLICATION_LOCK) {
                    publishingThread = Thread.currentThread();
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

    /**
     * The most read-out text the publication thread may hold undecoded:
     * four pages ({@code SharedStateCapture#READ_OUT_PAGE_BYTES}), 128 MB
     * of chars.  Unbounded, an owner that reads faster than one thread
     * decodes queues without end: SB12's obligation 0a1a085e98d056aa,
     * once a branch window no longer waits on the decoding (the store's
     * lock, {@code VmExpressionTable.Store}), held 109 pages, 3.5 GB, and
     * filled its 4 GB heap.
     */
    private static final long UNDECODED_BOUND_CHARS = 64L << 20;

    static boolean submitCompletedResultPublication(
            final ActiveRegion active,
            final SharedStateReadOut sharedState) {
        // Reserve loop evidence BEFORE reopening admission, so a later turn
        // cannot claim the same anchor.  Fail-closed: a failure terminates
        // the task, never rolls back a reservation another turn relies on.
        active.activation.reserveCompletedEvidence();
        configuration().releaseCandidate(active.activation);
        final long ordinal;
        synchronized (PUBLICATION_LOCK) {
            ordinal = ++submitted;
            queued.add(active);
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
            // Never decode on the RPC owner as a fallback.
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
                // Withheld as a stranded one is: its mints still published.
                configuration().markOccurrenceClaimed(active.activation);
                RowPublication.publishMints(active);
                taskUnanswered(active.activation, late + ": this occurrence"
                        + " was still unpublished when " + late.when
                        + ", and the replay ended there");
                return;
            }
            assembleRecordedSharedState(active, sharedState);
            // Here, where the write log is assembled: once, on one thread.
            RowPublication.publish(active);
            if (resultAnswersSelectedGoal(active)) {
                configuration().markOccurrenceClaimed(active.activation);
            }
        } catch (Throwable failure) {
            // Terminal: a later activation may already use the reservation.
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

    /**
     * A complete non-loop activation settles its task, target or not; a
     * loop body only by deciding the declared fatal target (no declared
     * target is "not reached": no throw stands in for it).
     */
    private static boolean resultAnswersSelectedGoal(ActiveRegion active) {
        RuntimeTask task = active.activation;
        if (!task.loopBodyRoot || !task.capturesTargetReach) return true;
        return task.targetGuards.size() > 1
                ? RowPublication.tookDisjunct(active, new ArrayList<String>())
                : task.reachedRequiredTargetOutcome(active.targetReach);
    }
}
