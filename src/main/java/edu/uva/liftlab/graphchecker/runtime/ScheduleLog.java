package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * THE schedule of one run, and the turnstile that holds a replay to a prefix
 * of another run's.
 *
 * <p>RECORDER.  Every START, CLAIM, SEND, RECV and WAKE the run makes inside
 * its recording window is appended here, in the order the run made them, by
 * the hooks that already stand at those points in BOTH passes
 * ({@code Identity.startWork}, {@code Identity} claims, the message doors of
 * {@code CausynthTraceRecorder}, {@code RuntimeTraceContext.beginTick} and the
 * timed waits {@code WorkStartSites} names).  Recording changes nothing the
 * run does: it computes the event from state the identity already keeps and
 * writes one line.</p>
 *
 * <p>ENFORCER.  A replay handed a prefix ({@link #PREFIX_ENV}) admits each of
 * its events only when it is the prefix's next one: a thread whose event is
 * not next waits, so the occurrences the replay re-runs before its flip run in
 * the order the discovering session ran them and are numbered as it numbered
 * them.  It goes on recording throughout -- its own schedule is what its
 * children inherit.  When nothing is admitted for {@link #TIMEOUT_PROPERTY}
 * while some thread waits, the prefix cannot be held: the turnstile states
 * {@code SCHEDULE_DIVERGED} with the position and both events and releases
 * every waiter.  It never blocks the run for good.</p>
 *
 * <p>PAST THE PREFIX, THE CLOCK STILL HOLDS.  The discovering session's order
 * does not end at the cut: the rest of it ({@link #SUFFIX_FILE}) is handed
 * too, and holds TIMEOUTS only.  A timeout WAKE the rest names is admitted
 * once every event the rest states before it has happened (or been given
 * up); a WAKE it does not name, and every other event, runs free.  Virtual
 * time stands in for the clock on both sides of the flip, and the flip keeps
 * everything its messages and signals cause: only the order time made is
 * kept.  Freeing the clock at the cut was a change of its own, and a large
 * one -- the replay runs on the concolic VM many times slower than the
 * recording ran, so by the cut every daemon's wall-clock timer had long run
 * out, and every daemon took its next turn at once.  hdfs-17899 bug1 and
 * hdfs-17967 paths A and C: the stale DataNode's heartbeat, recorded after
 * the workload's explicit key refresh, reached the NameNode before it, took
 * the one KeyUpdateCommand, and the planned refresh occurrence never ran in
 * any world that flipped the NameNode -- so no DataNode flip was ever
 * proposed inside one.  What a turn did not do is settled at its END: the
 * events the recording has inside the turn's span that the run has not made
 * by then are given up, since a daemon turn decides on the wall clock
 * whether its heartbeat is due.  When nothing the rest names happens for the
 * timeout while one of its WAKEs waits, the events before the earliest
 * waiting WAKE are given up (stated as {@code SCHEDULE_DIVERGED}) and it
 * takes its turn; after {@link #REST_STALLS} such stalls the next one lets
 * the rest go as a whole.  The rest holds while a timeout it names is still
 * to come; after that the run is free.  A prefix that diverges gives up the
 * one event it waited for and hands the rest of its unadmitted events to
 * the rest.</p>
 *
 * <p>ONE LIMIT, stated: the rest holds every WAKE it names, and a turn's
 * WAKE does not say what began the turn -- a DataXceiver op, begun by the
 * peer's message, is held like a daemon's timer tick.  Its recorded
 * predecessors are then its causes and have happened, unless the flip
 * removed one; that costs a stall, and the watchdog ends it.</p>
 *
 * <p>One lock for both halves, so the order this log writes IS the order the
 * turnstile admitted.</p>
 */
public final class ScheduleLog {
    /** Recording on or off; on unless a run says otherwise (A/B switch). */
    public static final String RECORD_PROPERTY = "causynth.schedule.record";
    /** Enforcement on or off when a prefix is handed (A/B switch). */
    public static final String ENFORCE_PROPERTY = "causynth.schedule.enforce";
    /** How long nothing may be admitted while a thread waits, in ms. */
    public static final String TIMEOUT_PROPERTY =
            "causynth.schedule.timeout.ms";
    /** The prefix this replay is held to: a schedule.jsonl file. */
    public static final String PREFIX_ENV = "CAUSYNTH_SCHEDULE_PREFIX";
    /** The same, as a system property; the property wins. */
    public static final String PREFIX_PROPERTY = "causynth.schedule.prefix";
    /** The prefix beside a focused replay's focus row. */
    public static final String PREFIX_FILE = "schedule_prefix.jsonl";
    /** The rest of the same order, beside the prefix: its timeouts hold. */
    public static final String SUFFIX_FILE = "schedule_suffix.jsonl";
    /** The rest, as a system property; else it stands beside the prefix. */
    public static final String SUFFIX_PROPERTY = "causynth.schedule.suffix";

    /**
     * Shorter than the waits a workload makes inside its window for its own
     * results ({@code CausynthCluster.WINDOW_WAIT_MS}, 60 s): an order that
     * cannot be held must be let go before the workload gives up on what the
     * held threads would have done.  One prefix divergence and the rest's
     * stalls ({@link #REST_STALLS}) stay under that bound together.
     */
    static final long DEFAULT_TIMEOUT_MS = 15000L;
    /**
     * How many times the rest may give events up before it is let go as a
     * whole: a run that keeps leaving the recorded order has left it, and
     * every further stall is a timeout the workload's own waits pay for.
     */
    static final int REST_STALLS = 2;

    private static final Object LOCK = new Object();

    /** Where one run's events go. */
    interface Sink {
        void write(JsonObject row);
    }

    private static Sink sink;
    /** Events made before a sink was installed, in order. */
    private static final List<JsonObject> PENDING = new ArrayList<JsonObject>();
    private static final int PENDING_LIMIT = 1 << 20;
    private static final Map<String, Integer> COUNTS =
            new HashMap<String, Integer>();
    private static long seq;

    // ---- turnstile state, guarded by LOCK --------------------------------
    private static boolean prefixLoaded;
    private static List<String> prefix = Collections.emptyList();
    private static List<ScheduleEvent> prefixEvents = Collections.emptyList();
    private static int cursor;
    private static boolean freeRun = true;
    private static int waiting;
    private static long lastAdmit;
    private static String divergence = "";
    private static long divergedAt = -1L;

    // ---- the rest of the order, past the prefix, guarded by LOCK ---------
    private static final byte OPEN = 0;
    private static final byte SEEN = 1;
    private static final byte GIVEN_UP = 2;
    /** How long a waiting WAKE's last ask counts as waiting, in ms. */
    private static final long ASK_FRESH_MS = 3000L;
    /** The rest as loaded, until the prefix ends or diverges. */
    private static List<ScheduleEvent> suffixEvents = Collections.emptyList();
    /** Whether the run is past its prefix and the rest's timeouts hold. */
    private static boolean timeouts;
    private static List<ScheduleEvent> rest = Collections.emptyList();
    private static byte[] restState = new byte[0];
    /** Per key, the rest positions no event has taken yet, in order. */
    private static final Map<String, ArrayDeque<Integer>> UNTAKEN =
            new HashMap<String, ArrayDeque<Integer>>();
    /** The first OPEN rest position: every one before it is settled. */
    private static int firstOpen;
    /** The rest's WAKEs still OPEN: while there are none, nothing holds. */
    private static int openWakes;
    private static long lastProgress;
    private static int restSeen;
    private static int givenUp;
    /** Positions a turn's END gave up: what its turn did not do. */
    private static int settledByEnd;
    /** How many times the rest has given events up. */
    private static int restStalls;
    /** Per WAKE key, the rest position it took: where its turn began. */
    private static final Map<String, Integer> TAKEN_WAKES =
            new HashMap<String, Integer>();
    /** The rest positions WAKEs wait at, each with when it last asked. */
    private static final TreeMap<Integer, Long> ASKING =
            new TreeMap<Integer, Long>();

    private ScheduleLog() {
    }

    // ---- recording -------------------------------------------------------

    /**
     * One event at a hook: held to the prefix when there is one, then
     * written.
     *
     * <p>Never throws into the workload.  An event whose context the
     * identity cannot compute is not recorded, which is the same statement
     * the rows already make for it (a LINEAGE_LOST at the site).</p>
     *
     * @return whether the event was written
     */
    public static boolean observe(ScheduleEvent.Kind kind, String site) {
        if (kind == null || !recording()) return false;
        mute();
        try {
            Pending event = pending(kind, site);
            if (event == null) return false;
            synchronized (LOCK) {
                loadPrefixLocked();
                admitLocked(event);
                appendLocked(event);
            }
            return true;
        } finally {
            unmute();
        }
    }

    /**
     * Mutes the replay's symbolic observation across this class's own work.
     *
     * <p>Only in a replay, and only around the bookkeeping: the event is
     * computed from identity state and written with Gson, none of which is
     * the workload's control flow, while the wait a {@link TimedWaits} method
     * performs IS the workload's and keeps whatever it recorded before.</p>
     */
    static void mute() {
        if (replay()) ConcolicRegionRuntime.pauseObservation();
    }

    static void unmute() {
        if (replay()) ConcolicRegionRuntime.resumeObservation();
    }

    private static volatile Boolean replay;

    private static boolean replay() {
        Boolean known = replay;
        if (known == null) {
            known = RuntimeTraceMode.configured()
                    == RuntimeTraceMode.REPLAY_CONTEXT;
            replay = known;
        }
        return known;
    }

    /**
     * The same event, admitted only if it is the prefix's next one NOW.
     *
     * <p>For a wait that holds a monitor or a lock: it cannot block here,
     * because the thread whose event IS next may need what it holds, so it
     * waits on its own primitive for a short quantum and asks again.  True
     * when the event was admitted and written -- the run is free, or the
     * event was next, or the watchdog just released the prefix.</p>
     */
    static boolean tryObserve(ScheduleEvent.Kind kind, String site) {
        if (kind == null || !recording()) return true;
        mute();
        try {
            Pending event = pending(kind, site);
            if (event == null) return true;
            return tryAdmit(event);
        } finally {
            unmute();
        }
    }

    /** Admits {@code event} if it is next NOW; see {@link #tryObserve}. */
    private static boolean tryAdmit(Pending event) {
        synchronized (LOCK) {
            loadPrefixLocked();
            if (held() && !prefix.get(cursor).equals(event.key)) {
                long idle = System.currentTimeMillis() - lastAdmit;
                if (idle < timeoutMillis()) return false;
                divergeLocked(event.key);
            }
            if (held()) {
                advanceLocked();
            } else if (timeouts) {
                // Asked only of a wait an interrupt ended: it happened now.
                takeLocked(event.key);
            }
            appendLocked(event);
            return true;
        }
    }

    // ---- one timed wait's WAKE -------------------------------------------

    /**
     * The WAKE one timed wait would make, computed once: nothing the thread
     * does while it waits changes its context, and a held wait asks about
     * its turn every quantum.
     */
    static final class Wake {
        private final Pending event;
        /** The rest position this wait last asked at, or -1; under LOCK. */
        private int asked = -1;

        private Wake(Pending event) {
            this.event = event;
        }
    }

    /**
     * The wait ended without its turn -- a signal, an element, its own
     * deadline, an interrupt: it no longer waits at the rest position it
     * asked at, and a later WAKE the watchdog would release must not keep
     * deferring to it.
     */
    static void withdraw(Wake wake) {
        if (wake == null) return;
        synchronized (LOCK) {
            if (wake.asked < 0) return;
            ASKING.remove(wake.asked);
            wake.asked = -1;
            LOCK.notifyAll();
        }
    }

    /**
     * This thread's WAKE at {@code site}, or null when there is none to make:
     * the window is not open, or the event cannot be named.
     */
    static Wake wake(String site) {
        if (!recording()) return null;
        mute();
        try {
            Pending event = pending(ScheduleEvent.Kind.WAKE, site);
            return event == null ? null : new Wake(event);
        } finally {
            unmute();
        }
    }

    /** What a held wait's ask for its turn found. */
    enum Turn {
        /** Its WAKE was the prefix's next event: admitted and written. */
        ADMITTED,
        /** Another event is next: the wait asks again after a quantum. */
        NOT_YET,
        /**
         * No order holds this wait's timeout any more -- the run is free, or
         * past its prefix and the rest names no such WAKE still to come --
         * and nothing was written: the rest of the wait is on the wall
         * clock, as it is in a replay with no prefix.
         */
        FREE,
        /**
         * The wait has no event to make -- recording is off, or its event
         * cannot be named -- so no prefix can hold it: it runs on the wall
         * clock, and nothing is written.
         */
        NO_EVENT
    }

    /**
     * Admits the wait's timeout WAKE if it is its turn NOW: the prefix's
     * next event, or -- past the prefix -- a WAKE of the rest that is due.
     *
     * <p>An order that lets a wait go does not end it.  A WAKE the rest does
     * not name, or any WAKE once the run is free, is FREE: the wait runs as
     * one in a replay with no prefix does, where it ends at its own deadline
     * or by a signal.  Ending every held wait the moment the prefix ran out made
     * each of them time out at once -- an idle IPC connection closed itself,
     * a request sender gave up its turn -- at the very point a focused
     * replay's flip is, and the session's schedule then carried those WAKEs
     * into every prefix taken from it (hdfs-17967 path A: a three-event
     * prefix of which two were such WAKEs, and the replay it held never
     * reached the occurrence it was for).</p>
     */
    static Turn turn(Wake wake) {
        if (wake == null) return Turn.NO_EVENT;
        mute();
        try {
            synchronized (LOCK) {
                loadPrefixLocked();
                if (held()) {
                    if (prefix.get(cursor).equals(wake.event.key)) {
                        advanceLocked();
                        appendLocked(wake.event);
                        return Turn.ADMITTED;
                    }
                    long idle = System.currentTimeMillis() - lastAdmit;
                    if (idle < timeoutMillis()) return Turn.NOT_YET;
                    divergeLocked(wake.event.key);
                }
                if (!timeouts) return Turn.FREE;
                int slot = restSlotLocked(wake.event.key);
                if (slot < 0) return Turn.FREE;
                if (!dueLocked(slot)) {
                    wake.asked = slot;
                    return Turn.NOT_YET;
                }
                wake.asked = -1;
                takeLocked(wake.event.key);
                appendLocked(wake.event);
                return Turn.ADMITTED;
            }
        } finally {
            unmute();
        }
    }

    /**
     * A held sleep's WAKE: blocks until it is its turn ({@link #turn}), and
     * admits and writes it -- ADMITTED.  FREE, with nothing written, when no
     * order holds it any more, and NO_EVENT when there is no event to make:
     * either way the sleep goes on on the wall clock ({@link #turn}).  An
     * interrupt while it waits ends the wait where it is, and the event is
     * written, as {@link #observe} writes it.
     */
    static Turn awaitTurn(ScheduleEvent.Kind kind, String site) {
        if (kind == null || !recording()) return Turn.NO_EVENT;
        mute();
        try {
            Pending event = pending(kind, site);
            if (event == null) return Turn.NO_EVENT;
            synchronized (LOCK) {
                loadPrefixLocked();
                if (admitLocked(event) == Admission.FREED) {
                    return Turn.FREE;
                }
                appendLocked(event);
                return Turn.ADMITTED;
            }
        } finally {
            unmute();
        }
    }

    /**
     * The wait's WAKE, written now whether it is next or not: an interrupted
     * park ends at once, as the real one does, and the prefix stands for
     * everyone else -- the rule an interrupted admission already follows.
     */
    static void admitNow(Wake wake) {
        if (wake == null) return;
        mute();
        try {
            synchronized (LOCK) {
                loadPrefixLocked();
                if (held()) {
                    if (prefix.get(cursor).equals(wake.event.key)) {
                        advanceLocked();
                    }
                } else if (timeouts) {
                    takeLocked(wake.event.key);
                }
                appendLocked(wake.event);
            }
        } finally {
            unmute();
        }
    }

    /** One event about to be admitted: its parts, computed off the lock. */
    private static final class Pending {
        private final ScheduleEvent.Kind kind;
        private final String context;
        private final String site;
        private final String occurrence;
        private final String key;

        private Pending(ScheduleEvent.Kind kind, String context, String site,
                        String occurrence) {
            this.kind = kind;
            this.context = context;
            this.site = site;
            this.occurrence = occurrence;
            this.key = ScheduleEvent.key(kind, context, site);
        }
    }

    private static Pending pending(ScheduleEvent.Kind kind, String site) {
        String stable = JvmNames.stable(Text.safe(site));
        if (stable.isEmpty()) return null;
        try {
            return new Pending(kind, contextHere(), stable,
                    Identity.innermostRegionId());
        } catch (Throwable unnamed) {
            return null;
        }
    }

    private static void appendLocked(Pending pending) {
        Integer made = COUNTS.get(pending.key);
        int k = made == null ? 0 : made;
        COUNTS.put(pending.key, k + 1);
        ScheduleEvent event = ScheduleEvent.of(seq++, pending.kind,
                pending.context, pending.site, k, pending.occurrence);
        JsonObject row = RowCodec.writeScheduleEvent(event);
        if (sink != null) {
            sink.write(row);
        } else if (PENDING.size() < PENDING_LIMIT) {
            PENDING.add(row);
        }
    }

    /** The occurrences this run has marked, so each is marked once. */
    private static final java.util.Set<String> MARKED =
            new java.util.HashSet<String>();

    /**
     * Marks where one occurrence opened: the position of the next event.
     *
     * <p>Not an event -- nothing is admitted or held by it -- but the cut a
     * task's prefix is taken at: the prefix of a replay that focuses this
     * occurrence ends where it began.  An occurrence that sends, starts and
     * waits nothing still has a beginning, which the events alone would not
     * state.</p>
     */
    static void mark(String occurrenceId) {
        String id = Text.safe(occurrenceId);
        if (id.isEmpty() || !recording()) return;
        synchronized (LOCK) {
            if (!MARKED.add(id)) return;
            JsonObject row = new JsonObject();
            row.addProperty("mark", id);
            row.addProperty("at", seq);
            if (sink != null) {
                sink.write(row);
            } else if (PENDING.size() < PENDING_LIMIT) {
                PENDING.add(row);
            }
        }
    }

    /** The event context: the attributed node, then the causal context. */
    static String contextHere() {
        String node = Text.safe(RuntimeTraceContext.nodeHere());
        return node + "|" + Identity.contextHere().render();
    }

    private static boolean recording() {
        if (!CausynthTraceRecorder.recordingStarted()) return false;
        return !"false".equalsIgnoreCase(
                Text.safe(System.getProperty(RECORD_PROPERTY)));
    }

    /**
     * Installs where this run's events go, and drains what came first.
     *
     * <p>A replay installs its session's publisher; the recording installs a
     * file beside its trace.  Events the run made before either -- the window
     * opens before the session does in some workloads -- are kept in order and
     * written first.</p>
     */
    static void install(Sink target) {
        synchronized (LOCK) {
            if (target == null || sink != null) return;
            sink = target;
            for (JsonObject row : PENDING) {
                target.write(row);
            }
            PENDING.clear();
        }
    }

    /** The recording's sink: {@code schedule.jsonl} beside its trace. */
    static void installFile(final File directory) {
        if (directory == null) return;
        final File file = new File(directory,
                edu.uva.liftlab.graphchecker.contract.SessionDir.SCHEDULE);
        install(new Sink() {
            private BufferedWriter writer;
            private boolean failed;

            @Override
            public void write(JsonObject row) {
                if (failed) return;
                try {
                    if (writer == null) {
                        writer = new BufferedWriter(new OutputStreamWriter(
                                new FileOutputStream(file, false),
                                StandardCharsets.UTF_8));
                    }
                    writer.write(RowCodec.toLine(row));
                    writer.newLine();
                    writer.flush();
                } catch (IOException unwritable) {
                    failed = true;
                    System.err.println("Causynth could not write the schedule"
                            + " to " + file + ": " + unwritable);
                }
            }
        });
    }

    // ---- enforcement -----------------------------------------------------

    /**
     * Admits one event: held to the prefix, when it is the prefix's next one;
     * past the prefix, a timeout WAKE the rest names when it is due, and
     * anything else at once; free, at once.
     *
     * <p>A thread whose event is not next waits on the lock -- which it
     * releases while it waits, so the thread whose event IS next can be
     * admitted.  The watchdog is PROGRESS, not a per-thread clock: a replay
     * on the concolic VM may take long between two events, and what shows the
     * order cannot be held is that nothing at all was admitted for the whole
     * timeout while someone waited.</p>
     */
    private static Admission admitLocked(Pending event) {
        long timeout = timeoutMillis();
        int asked = -1;
        waiting++;
        try {
            while (true) {
                if (held()) {
                    if (prefix.get(cursor).equals(event.key)) {
                        advanceLocked();
                        return Admission.NEXT;
                    }
                    long idle = System.currentTimeMillis() - lastAdmit;
                    if (idle >= timeout) {
                        divergeLocked(event.key);
                        continue;
                    }
                    LOCK.wait(Math.max(1L, Math.min(timeout - idle, 1000L)));
                    continue;
                }
                if (!timeouts) return Admission.FREED;
                if (event.kind != ScheduleEvent.Kind.WAKE) {
                    // Only time is held past the prefix: whatever else the
                    // run does happens when it happens, and the flip keeps
                    // what it changes.
                    takeLocked(event.key);
                    return Admission.NEXT;
                }
                int slot = restSlotLocked(event.key);
                if (slot < 0) return Admission.FREED;
                if (dueLocked(slot)) {
                    takeLocked(event.key);
                    return Admission.NEXT;
                }
                asked = slot;
                // Past the timeout, an earlier WAKE is still asking: it
                // decides, and every take, give-up or withdrawal notifies.
                long idle = System.currentTimeMillis() - lastProgress;
                LOCK.wait(Math.max(10L, Math.min(timeout - idle, 1000L)));
            }
        } catch (InterruptedException interrupted) {
            // The workload interrupted its own thread -- a shutdown, a
            // cancelled task.  That is the workload's to see, not the
            // order's to answer: this thread stops waiting for its turn, the
            // flag is put back, and the order stands for everyone else.  The
            // event is still written, where it happened, because it did.
            Thread.currentThread().interrupt();
            if (timeouts) takeLocked(event.key);
            return Admission.INTERRUPTED;
        } finally {
            if (asked >= 0) ASKING.remove(asked);
            waiting--;
        }
    }

    /** How one blocking admission ended. */
    private enum Admission {
        /** The event was next (or due), and the order moved. */
        NEXT,
        /** Nothing holds the event: the run is free, or the rest names no such WAKE. */
        FREED,
        /** The workload interrupted the thread while it waited. */
        INTERRUPTED
    }

    /** Whether the replay is held to its prefix, event by event, right now. */
    private static boolean held() {
        return !freeRun && !timeouts;
    }

    /** One admission: the cursor moves, and every waiter looks again. */
    private static void advanceLocked() {
        cursor++;
        lastAdmit = System.currentTimeMillis();
        if (cursor >= prefix.size()) {
            // The prefix is used up, which is where the flip is: from here
            // only the rest's timeouts hold.
            enterRestLocked(suffixEvents);
        }
        LOCK.notifyAll();
    }

    /**
     * Past the prefix: the rest of the order, whose timeout WAKEs hold.  Free
     * at once when it names none.  Its watchdog starts now.
     */
    private static void enterRestLocked(List<ScheduleEvent> events) {
        rest = events;
        restState = new byte[events.size()];
        UNTAKEN.clear();
        ASKING.clear();
        TAKEN_WAKES.clear();
        firstOpen = 0;
        openWakes = 0;
        for (int index = 0; index < events.size(); index++) {
            ScheduleEvent event = events.get(index);
            ArrayDeque<Integer> slots = UNTAKEN.get(event.key());
            if (slots == null) {
                slots = new ArrayDeque<Integer>();
                UNTAKEN.put(event.key(), slots);
            }
            slots.addLast(index);
            if (event.kind() == ScheduleEvent.Kind.WAKE) openWakes++;
        }
        lastProgress = System.currentTimeMillis();
        timeouts = openWakes > 0;
        freeRun = !timeouts;
        LOCK.notifyAll();
    }

    /** The rest position an event of {@code key} takes, or -1: none left. */
    private static int restSlotLocked(String key) {
        ArrayDeque<Integer> slots = UNTAKEN.get(key);
        return slots == null || slots.isEmpty() ? -1 : slots.peekFirst();
    }

    /**
     * Whether the rest's WAKE at {@code slot} may take its turn now: every
     * event the rest states before it has happened or was given up -- or
     * nothing the rest names has happened for the timeout, and no WAKE before
     * it is waiting, and the events before it are given up now.
     *
     * <p>A given-up position may still be taken by its event when it comes
     * late: the position it takes is the earliest of its key not yet taken,
     * given up or not.</p>
     */
    private static boolean dueLocked(int slot) {
        if (firstOpen >= slot) return true;
        long now = System.currentTimeMillis();
        ASKING.put(slot, now);
        if (now - lastProgress < timeoutMillis()) return false;
        // An ask not renewed for a few quanta is a wait that ended
        // otherwise (a signal); it waits for nothing.
        java.util.Iterator<Map.Entry<Integer, Long>> asks =
                ASKING.entrySet().iterator();
        while (asks.hasNext()) {
            if (asks.next().getValue() < now - ASK_FRESH_MS) asks.remove();
        }
        if (!ASKING.isEmpty() && ASKING.firstKey() < slot) return false;
        if (restStalls >= REST_STALLS) {
            releaseRestLocked(slot);
        } else {
            restStalls++;
            giveUpLocked(slot);
        }
        return true;
    }

    /** An event of {@code key} happened: it takes its rest position. */
    private static void takeLocked(String key) {
        ArrayDeque<Integer> slots = UNTAKEN.get(key);
        if (slots == null || slots.isEmpty()) return;
        int slot = slots.pollFirst();
        ASKING.remove(slot);
        ScheduleEvent event = rest.get(slot);
        if (restState[slot] == OPEN
                && event.kind() == ScheduleEvent.Kind.WAKE) {
            openWakes--;
        }
        restState[slot] = SEEN;
        restSeen++;
        if (event.kind() == ScheduleEvent.Kind.WAKE) {
            TAKEN_WAKES.put(key, slot);
        } else if (event.kind() == ScheduleEvent.Kind.END) {
            settleTurnLocked(event, slot);
        }
        settleLocked();
    }

    /**
     * A turn's END settles the turn: what the recording has between the
     * turn's WAKE and its END and the run has not made by now -- other than
     * another turn's WAKE -- is given up.  The turn is over, and what it did
     * not do it will not do: a daemon's turn decides on the wall clock
     * whether its heartbeat is due, so a recorded turn's RPC need not recur,
     * and every timeout the rest names after it would otherwise wait out the
     * watchdog for it.  Another thread's event recorded inside the span loses
     * only its place ahead of later timeouts; it takes its position when it
     * comes.
     */
    private static void settleTurnLocked(ScheduleEvent end, int endSlot) {
        Integer began = TAKEN_WAKES.get(ScheduleEvent.key(
                ScheduleEvent.Kind.WAKE, end.context(), end.site()));
        if (began == null || began >= endSlot) return;
        for (int index = Math.max(began + 1, firstOpen); index < endSlot;
             index++) {
            if (restState[index] != OPEN
                    || rest.get(index).kind() == ScheduleEvent.Kind.WAKE) {
                continue;
            }
            restState[index] = GIVEN_UP;
            settledByEnd++;
        }
    }

    /**
     * The rest has stalled {@link #REST_STALLS} times and would again: it is
     * let go as a whole, stated, and the run is free.
     */
    private static void releaseRestLocked(int slot) {
        int open = 0;
        for (int index = firstOpen; index < restState.length; index++) {
            if (restState[index] == OPEN) {
                restState[index] = GIVEN_UP;
                open++;
            }
        }
        givenUp += open;
        openWakes = 0;
        stateLocked("schedule-rest#" + firstOpen, "past the prefix, the rest"
                + " of the discovering run's order stalled " + restStalls
                + " time(s) and would again ("
                + rest.get(slot).render() + " at rest position " + slot
                + " waited " + timeoutMillis() + " ms): its " + open
                + " open event(s) are given up and the run is free");
        settleLocked();
    }

    /** Gives up every OPEN rest position before {@code slot}, stated. */
    private static void giveUpLocked(int slot) {
        int from = firstOpen;
        int count = 0;
        ScheduleEvent first = null;
        for (int index = firstOpen; index < slot; index++) {
            if (restState[index] != OPEN) continue;
            if (first == null) first = rest.get(index);
            if (rest.get(index).kind() == ScheduleEvent.Kind.WAKE) openWakes--;
            restState[index] = GIVEN_UP;
            count++;
        }
        givenUp += count;
        stateLocked("schedule-rest#" + from, "past the prefix, " + count
                + " event(s) of the discovering run's order from rest"
                + " position " + from + " on (the first "
                + (first == null ? "?" : first.render()) + ") did not"
                + " happen for " + timeoutMillis() + " ms while the timeout "
                + rest.get(slot).render() + " at rest position " + slot
                + " waited: they are given up and it takes its turn");
        settleLocked();
    }

    /** The rest moved: its first open position, and whether it still holds. */
    private static void settleLocked() {
        lastProgress = System.currentTimeMillis();
        while (firstOpen < restState.length && restState[firstOpen] != OPEN) {
            firstOpen++;
        }
        if (openWakes <= 0) {
            // No timeout the rest names is still to come: nothing holds.
            timeouts = false;
            freeRun = true;
        }
        LOCK.notifyAll();
    }

    /**
     * Whether this replay is held to its order right now -- its prefix, or
     * the rest's timeouts.
     *
     * <p>Only inside the recording window: the order is the window's, and a
     * wait begun before the workload opened it -- an idle IPC connection, a
     * daemon's first sleep -- is the set-up's, which runs on the wall clock
     * exactly as it did when the order was recorded.  Taking it over would
     * return it at once, over and over, and time out whatever it was idling
     * for.</p>
     */
    public static boolean enforcing() {
        if (!CausynthTraceRecorder.recordingStarted()) return false;
        synchronized (LOCK) {
            loadPrefixLocked();
            return !freeRun;
        }
    }


    private static void divergeLocked(String actual) {
        if (!held()) return;
        String expected = cursor < prefixEvents.size()
                ? prefixEvents.get(cursor).render() : "(end of prefix)";
        divergedAt = cursor;
        List<ScheduleEvent> remaining = new ArrayList<ScheduleEvent>(
                prefixEvents.subList(cursor, prefixEvents.size()));
        remaining.addAll(suffixEvents);
        divergence = "at prefix position " + cursor + " of "
                + prefix.size() + " the run's next event was "
                + render(actual) + " and the prefix's was " + expected
                + "; nothing was admitted for " + timeoutMillis()
                + " ms, so every waiter is released: that event is given up"
                + " and the prefix's other " + (prefix.size() - cursor - 1)
                + " unadmitted event(s) join the rest of the order, whose"
                + " timeouts alone hold from here";
        enterRestLocked(remaining);
        // Only the prefix's next event is known not to have happened for
        // the timeout; the events behind it were held back by it, and get
        // their own time -- the rest's watchdog starts now, and the waits
        // blocked here ask for their positions before anything else is
        // given up.
        if (timeouts && restState[0] == OPEN) {
            if (rest.get(0).kind() == ScheduleEvent.Kind.WAKE) openWakes--;
            restState[0] = GIVEN_UP;
            givenUp++;
            settleLocked();
        }
        stateLocked("schedule#" + cursor, divergence);
    }

    /** One SCHEDULE_DIVERGED statement, on the session and on stderr. */
    private static void stateLocked(String where, String detail) {
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    where, detail);
        } catch (Throwable unpublished) {
            // stderr below is the statement then.
        }
        System.err.println("Causynth schedule diverged: " + detail);
    }

    private static String render(String key) {
        String[] parts = key.split("\n", -1);
        return parts.length == 3
                ? parts[0] + " " + parts[2] + " @ " + parts[1] : key;
    }

    /** The divergence this replay stated, or "" when it held its prefix. */
    public static String divergence() {
        synchronized (LOCK) {
            return divergence;
        }
    }

    private static long timeoutMillis() {
        String configured = Text.safe(System.getProperty(TIMEOUT_PROPERTY));
        if (configured.isEmpty()) return DEFAULT_TIMEOUT_MS;
        try {
            long value = Long.parseLong(configured);
            return value > 0L ? value : DEFAULT_TIMEOUT_MS;
        } catch (NumberFormatException malformed) {
            return DEFAULT_TIMEOUT_MS;
        }
    }

    /**
     * Reads the order this replay was handed, once: its prefix, and the rest.
     *
     * <p>The prefix from the property, else the environment, else the file
     * beside the focus row in the worker directory; the rest from its
     * property, else beside the focus row.  Neither, or enforcement switched
     * off, is a free run from the first event -- which is exactly the replay
     * this class replaced.</p>
     */
    private static void loadPrefixLocked() {
        if (prefixLoaded) return;
        prefixLoaded = true;
        if ("false".equalsIgnoreCase(
                Text.safe(System.getProperty(ENFORCE_PROPERTY)))) {
            return;
        }
        Path file = prefixFile();
        Path restFile = suffixFile();
        if (file == null && restFile == null) return;
        try {
            installLocked(file == null
                            ? Collections.<ScheduleEvent>emptyList()
                            : SessionReader.readSchedule(file),
                    restFile == null
                            ? Collections.<ScheduleEvent>emptyList()
                            : SessionReader.readSchedule(restFile));
        } catch (IOException | RuntimeException unreadable) {
            System.err.println("Causynth could not read the schedule "
                    + file + " / " + restFile + ": " + unreadable
                    + "; the replay runs free");
        }
    }

    /** Holds the run to {@code events}, then to the timeouts of {@code after}. */
    private static void installLocked(List<ScheduleEvent> events,
                                      List<ScheduleEvent> after) {
        List<String> keys = new ArrayList<String>(events.size());
        for (ScheduleEvent event : events) {
            keys.add(event.key());
        }
        prefixEvents = new ArrayList<ScheduleEvent>(events);
        prefix = keys;
        suffixEvents = new ArrayList<ScheduleEvent>(after);
        cursor = 0;
        lastAdmit = System.currentTimeMillis();
        if (keys.isEmpty()) {
            enterRestLocked(suffixEvents);
        } else {
            timeouts = false;
            freeRun = false;
        }
    }

    private static Path prefixFile() {
        String named = Text.safe(System.getProperty(PREFIX_PROPERTY));
        if (named.isEmpty()) named = Text.safe(System.getenv(PREFIX_ENV));
        if (!named.isEmpty()) return Paths.get(named);
        return besideFocus(PREFIX_FILE);
    }

    private static Path suffixFile() {
        String named = Text.safe(System.getProperty(SUFFIX_PROPERTY));
        if (!named.isEmpty()) return Paths.get(named);
        return besideFocus(SUFFIX_FILE);
    }

    private static Path besideFocus(String name) {
        String worker = Text.safe(
                System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (!worker.isEmpty()) {
            Path beside = Paths.get(worker).resolve(name);
            if (beside.toFile().isFile()) return beside;
        }
        return null;
    }

    /** How far the replay got through its order, for its session. */
    public static String progress() {
        synchronized (LOCK) {
            if (prefix.isEmpty() && suffixEvents.isEmpty()) return "no prefix";
            String held = cursor + " of " + prefix.size()
                    + " prefix events admitted"
                    + (divergedAt >= 0 ? ", diverged at " + divergedAt : "");
            if (!rest.isEmpty()) {
                held += "; of the rest's " + rest.size() + " events "
                        + restSeen + " happened, " + givenUp
                        + " were given up in " + restStalls + " stall(s)"
                        + " and " + settledByEnd + " settled by their"
                        + " turn's END";
            }
            return held;
        }
    }

    /** Test hook: installs a prefix directly and starts enforcing it. */
    static void enforceForTests(List<ScheduleEvent> events) {
        enforceForTests(events, Collections.<ScheduleEvent>emptyList());
    }

    /** Test hook: a prefix, and the rest of the order past it. */
    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after) {
        synchronized (LOCK) {
            prefixLoaded = true;
            if (events.isEmpty() && after.isEmpty()) {
                freeRun = true;
                return;
            }
            installLocked(events, after);
        }
    }

    public static void resetForTests() {
        synchronized (LOCK) {
            sink = null;
            PENDING.clear();
            COUNTS.clear();
            MARKED.clear();
            seq = 0L;
            prefixLoaded = false;
            prefix = Collections.emptyList();
            prefixEvents = Collections.emptyList();
            suffixEvents = Collections.emptyList();
            cursor = 0;
            freeRun = true;
            timeouts = false;
            rest = Collections.emptyList();
            restState = new byte[0];
            UNTAKEN.clear();
            ASKING.clear();
            firstOpen = 0;
            openWakes = 0;
            lastProgress = 0L;
            restSeen = 0;
            givenUp = 0;
            settledByEnd = 0;
            restStalls = 0;
            TAKEN_WAKES.clear();
            waiting = 0;
            lastAdmit = 0L;
            divergence = "";
            divergedAt = -1L;
            LOCK.notifyAll();
        }
    }
}
