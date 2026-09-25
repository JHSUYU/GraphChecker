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
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * THE schedule of one run, and the one rule that holds a replay to another
 * run's.
 *
 * <p>RECORDER.  Every START, CLAIM, SEND, RECV, WAKE, END and INTERRUPT the
 * run makes inside its recording window is appended here, in the order the
 * run made them, by the hooks that stand at those points in BOTH passes.
 * Recording changes nothing the run does.</p>
 *
 * <p>ONE ORDER, ONE RULE.  A replay is handed the discovering session's
 * order: the prefix up to its task's cut ({@link #PREFIX_ENV}) and the rest
 * past it ({@link #SUFFIX_FILE}), read as one list of SLOTS.  An event takes
 * the earliest slot of its key {@code (kind, c, site)} that is still open or
 * was given up; an event with no such slot runs free at once -- the run made
 * something the discovering one did not, and holding it could only stall
 * whoever waits behind it.  A slot before the cut, and a WAKE slot
 * anywhere, is HELD: its event waits until every earlier slot is settled.
 * Any other slot past the cut is taken at once (past the cut only time is
 * held; the flip keeps what it changes).  An INTERRUPT is never held: the
 * interrupter's own events order it.</p>
 *
 * <p>WHAT DID NOT HAPPEN IS SETTLED, three ways, each stated.  An
 * occurrence that CLOSES makes no further event, so the slots the order
 * held for it and it did not make are dead ({@code schedule-settled#}); a
 * turn's END gives up what the turn did not do; and the WATCHDOG, when
 * nothing was settled for the timeout while some thread waits and the
 * threads that do not wait are not computing, gives up every open slot
 * before the earliest waiting one ({@code schedule#} before the cut,
 * {@code schedule-rest#} past it).  A given-up slot is still taken by its
 * event if it comes late, so the order stays aligned; a dead one is not.
 * After {@link #REST_STALLS} give-ups past the cut the rest is let go.  A
 * stall that outlasts {@link #CEILING} timeouts is given up whatever the
 * CPU does, so the order never holds a run for good.</p>
 *
 * <p>One lock for both halves, so the order this log writes IS the order
 * the rule admitted.</p>
 */
public final class ScheduleLog {
    /** How long nothing may be settled while a thread waits, in ms. */
    public static final String TIMEOUT_PROPERTY =
            "causynth.schedule.timeout.ms";
    /** The prefix this replay is held to: a schedule.jsonl file. */
    public static final String PREFIX_ENV = "CAUSYNTH_SCHEDULE_PREFIX";
    /** The same, as a system property; the property wins. */
    public static final String PREFIX_PROPERTY = "causynth.schedule.prefix";
    /** The prefix beside a focused replay's focus row. */
    public static final String PREFIX_FILE = "schedule_prefix.jsonl";
    /** The rest of the same order, beside the prefix. */
    public static final String SUFFIX_FILE = "schedule_suffix.jsonl";
    /** The rest, as a system property; else it stands beside the prefix. */
    public static final String SUFFIX_PROPERTY = "causynth.schedule.suffix";

    /**
     * Shorter than the waits a workload makes inside its window for its own
     * results ({@code CausynthCluster.WINDOW_WAIT_MS}, 60 s).
     */
    static final long DEFAULT_TIMEOUT_MS = 15000L;
    /** Give-ups past the cut before the rest is let go as a whole. */
    static final int REST_STALLS = 2;
    /**
     * Where a wait no slot holds waits while the prefix stands: at the cut,
     * for all of it ({@link #turn}).
     */
    private static final int AT_THE_CUT = -1;

    /** A stall this many timeouts long is given up whatever the CPU does. */
    static final int CEILING = 8;
    /** How often the watchdog samples the CPU of the threads not waiting. */
    private static final long CPU_SAMPLE_MS = 1000L;

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

    // ---- the order, guarded by LOCK ---------------------------------------
    private static final byte OPEN = 0;
    private static final byte TAKEN = 1;
    private static final byte GIVEN_UP = 2;
    private static final byte DEAD = 3;

    private static boolean loaded;
    /** Whether an open slot still holds anything: read without the lock. */
    private static volatile boolean holds;
    private static List<ScheduleEvent> order = Collections.emptyList();
    private static int cut;
    private static byte[] state = new byte[0];
    /** Per key, the slots not taken and not dead, in order. */
    private static final Map<String, ArrayDeque<Integer>> SLOTS =
            new HashMap<String, ArrayDeque<Integer>>();
    /** Per recorded occurrence, the slots its events were. */
    private static final Map<String, List<Integer>> BY_OCCURRENCE =
            new HashMap<String, List<Integer>>();
    /** Per WAKE key, the slot it took: where its turn began. */
    private static final Map<String, Integer> TAKEN_WAKES =
            new HashMap<String, Integer>();
    /** The threads waiting for a turn, each with the slot it waits at. */
    private static final Map<Thread, Integer> WAITERS =
            new HashMap<Thread, Integer>();
    private static int firstOpen;
    /**
     * The first open slot that stands in a later event's way: an open WAKE
     * slot never does.  A WAKE is a daemon's turn, and the thread that
     * makes it may be behind a lock a held thread holds -- hdfs-17960's
     * NameNode restart held the namesystem lock at its slot 169 while the
     * replication-queue daemon needed it to reach its WAKE at 168, an order
     * no run under the schedule can make and the recording made by timing
     * -- so nobody waits for a late WAKE; the WAKE, when it comes, still
     * takes its slot.  A WAKE that comes EARLY is held to its slot as
     * before, and one the recording did not make at all waits at the cut:
     * a daemon's turn never comes sooner than recorded, and is never waited
     * for.
     */
    private static int firstBlocking;
    /** Open slots that hold: before the cut, or a WAKE. */
    private static int openHeld;
    private static long lastProgress;
    private static int restStalls;
    private static int taken;
    private static int ranFree;
    private static int givenUp;
    private static int stalls;
    private static int dead;
    private static int settledByEnd;
    private static final Map<Long, Long> CPU_SEEN = new HashMap<Long, Long>();
    private static long cpuSampledAt;
    private static boolean computing;

    private ScheduleLog() {
    }

    // ---- recording -------------------------------------------------------

    /**
     * One event at a hook: admitted by the order when there is one, then
     * written.  Never throws into the workload.
     *
     * @return whether the event was written
     */
    public static boolean observe(ScheduleEvent.Kind kind, String site) {
        return observe(kind, site, "");
    }

    /**
     * The same, for a SEND: {@code endpoint} is the producer endpoint the
     * message carries, stated on the event so the receiver's anchor names
     * the sender in the rows.
     */
    public static boolean observe(ScheduleEvent.Kind kind, String site,
                                  String endpoint) {
        if (kind == null || !RecordingWindow.opened()) return false;
        mute();
        try {
            Pending event = pending(kind, site, endpoint);
            if (event == null) return false;
            synchronized (LOCK) {
                loadOrderLocked();
                admitLocked(event);
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

    // ---- one timed wait's WAKE -------------------------------------------

    /**
     * The WAKE one timed wait would make, computed once: nothing the thread
     * does while it waits changes its context.
     */
    static final class Wake {
        private final Pending event;

        private Wake(Pending event) {
            this.event = event;
        }
    }

    /** This thread's WAKE at {@code site}, or null when there is none. */
    static Wake wake(String site) {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            Pending event = pending(ScheduleEvent.Kind.WAKE, site);
            return event == null ? null : new Wake(event);
        } finally {
            unmute();
        }
    }

    /** The wait no longer waits for a turn (a signal ended it, or more). */
    static void withdraw(Wake wake) {
        if (wake == null) return;
        synchronized (LOCK) {
            if (WAITERS.remove(Thread.currentThread()) != null) {
                LOCK.notifyAll();
            }
        }
    }

    /** What a held wait's ask for its turn found. */
    enum Turn {
        /** Its WAKE slot was due: taken and written. */
        ADMITTED,
        /**
         * An earlier slot is open, or no slot is left for this WAKE while
         * the prefix still stands: the wait asks again after a quantum.
         */
        NOT_YET,
        /**
         * No slot holds this wait's timeout -- the order names no such WAKE
         * still to come -- and the prefix is settled, and nothing was
         * written: the rest of the wait is on the wall clock.
         */
        FREE,
        /** The wait has no event to make, so nothing can hold it. */
        NO_EVENT
    }

    /**
     * Asks once, without blocking, whether the wait's timeout WAKE may take
     * its turn: for a wait that holds a monitor or a lock, which waits on
     * its own primitive between asks.
     */
    static Turn turn(Wake wake) {
        if (wake == null) return Turn.NO_EVENT;
        mute();
        try {
            synchronized (LOCK) {
                loadOrderLocked();
                Thread self = Thread.currentThread();
                while (true) {
                    int slot = holds ? slotOf(wake.event) : -1;
                    if (slot < 0 && !prefixStandsLocked()) {
                        WAITERS.remove(self);
                        return Turn.FREE;
                    }
                    if (slot < 0) {
                        // A WAKE THE RECORDING DID NOT MAKE IS SLEPT THROUGH
                        // while the prefix stands: the recording's thread
                        // slept past every event before the cut, and only a
                        // slower replay's wall clock would end it sooner --
                        // v28's seed replays had the DataNode actors heartbeat
                        // ahead of the workload's own, which the recording's
                        // window never saw.  So it waits AT THE CUT, as a
                        // waiter the watchdog counts: a prefix nothing is
                        // making is given up as any stall is, and then the
                        // wait is the clock's.  A signal still ends it.
                        WAITERS.put(self, AT_THE_CUT);
                        if (!watchdogLocked()) return Turn.NOT_YET;
                        continue;
                    }
                    if (dueLocked(slot)) {
                        WAITERS.remove(self);
                        takeLocked(slot);
                        appendLocked(wake.event);
                        return Turn.ADMITTED;
                    }
                    WAITERS.put(self, slot);
                    if (!watchdogLocked()) return Turn.NOT_YET;
                }
            }
        } finally {
            unmute();
        }
    }

    /**
     * The wait's WAKE, written when the wall clock ended a wait no slot
     * held ({@link Turn#FREE}): nothing holds it, so it is admitted at once.
     */
    static void timedOut(Wake wake) {
        if (wake == null) return;
        mute();
        try {
            synchronized (LOCK) {
                loadOrderLocked();
                admitLocked(wake.event);
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
        private final String endpoint;
        private final String key;

        private Pending(ScheduleEvent.Kind kind, String context, String site,
                        String occurrence, String endpoint) {
            this.kind = kind;
            this.context = context;
            this.site = site;
            this.occurrence = occurrence;
            this.endpoint = endpoint;
            this.key = ScheduleEvent.key(kind, context, site);
        }
    }

    private static Pending pending(ScheduleEvent.Kind kind, String site) {
        return pending(kind, site, "");
    }

    /**
     * The event this hook makes, or null when it makes none.
     *
     * <p>AN EVENT WITH NO IDENTITY HOLDS NO PLACE.  A thread whose context
     * is {@code Lost} is one no scope reached, and every such thread shares
     * that one context, so the k of its key would count all their events
     * together -- a cross-thread counter, which an event's identity may
     * never be (G8).  Ordered by it, the slower replay met the recording's
     * k's in another interleaving and waited for them: hdfs-17967 path B
     * v26, once the lineage weave put work starts on the NameNode's IPC
     * reader threads, stalled five times and gave up 42 of 80 slots.  So it
     * is neither written nor held, in the recording and in the replay alike,
     * and runs free.</p>
     */
    private static Pending pending(ScheduleEvent.Kind kind, String site,
                                   String endpoint) {
        String stable = JvmNames.stable(Text.safe(site));
        if (stable.isEmpty()) return null;
        try {
            if (Identity.contextHere().isLost()) return null;
            return new Pending(kind, contextHere(), stable,
                    Identity.innermostRegionId(), Text.safe(endpoint));
        } catch (Throwable unnamed) {
            return null;
        }
    }

    private static void appendLocked(Pending pending) {
        Integer made = COUNTS.get(pending.key);
        int k = made == null ? 0 : made;
        COUNTS.put(pending.key, k + 1);
        ScheduleEvent event = ScheduleEvent.of(seq++, pending.kind,
                pending.context, pending.site, k, pending.occurrence,
                pending.endpoint);
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
        if (id.isEmpty() || !RecordingWindow.opened()) return;
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

    /**
     * The event context: the attributed node, the causal context, and the
     * thread handoffs inside it ({@link Identity#handoffs}) -- so the k of a
     * key counts one thread's events, never two threads' interleaved.
     */
    static String contextHere() {
        String node = Text.safe(RuntimeTraceContext.nodeHere());
        String handoffs = Identity.handoffs();
        return node + "|" + Identity.contextHere().render()
                + (handoffs.isEmpty() ? "" : "|" + handoffs);
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

    // ---- the rule ---------------------------------------------------------

    /**
     * Admits one event and writes it: free when no slot holds it, at once
     * when its slot is not held or already due, else when every earlier
     * slot is settled.  The thread waits on the lock, which it releases
     * while it waits; the watchdog runs from here.
     */
    private static void admitLocked(Pending event) {
        if (!holds) {
            appendLocked(event);
            return;
        }
        Thread self = Thread.currentThread();
        try {
            while (true) {
                int slot = slotOf(event);
                if (slot < 0 && event.kind == ScheduleEvent.Kind.WAKE
                        && prefixStandsLocked()) {
                    // A daemon's turn the recording did not make waits at
                    // the cut, as a timed wait no slot holds does (#turn):
                    // hdfs-17967 path B's DataNode actors slept into the
                    // window and, on the replay's slower clock, took their
                    // turns -- and their heartbeats -- before the workload's
                    // own, where the recording's slept through.
                    WAITERS.put(self, AT_THE_CUT);
                    if (watchdogLocked()) continue;
                    LOCK.wait(Math.max(1L, Math.min(timeoutMillis(), 1000L)));
                    continue;
                }
                if (slot < 0) {
                    ranFree++;
                    appendLocked(event);
                    return;
                }
                if (event.kind == ScheduleEvent.Kind.INTERRUPT
                        || !heldKind(slot) || dueLocked(slot)) {
                    takeLocked(slot);
                    appendLocked(event);
                    return;
                }
                WAITERS.put(self, slot);
                if (watchdogLocked()) continue;
                LOCK.wait(Math.max(1L, Math.min(timeoutMillis(), 1000L)));
            }
        } catch (InterruptedException interrupted) {
            // The workload interrupted its own thread: that is the
            // workload's to see.  The event happened here, so it takes its
            // slot here, and the order stands for everyone else.
            Thread.currentThread().interrupt();
            int slot = slotOf(event);
            if (slot >= 0) takeLocked(slot);
            appendLocked(event);
        } finally {
            WAITERS.remove(self);
        }
    }

    /**
     * The slot an event takes: of the slots of its key still open or given
     * up, the earliest one its OWN occurrence made in the recording, else
     * the earliest one; -1 when none is left.  Two threads under one
     * context make events of one key -- two RPCs a request issues at once
     * -- and which one comes first is the scheduler's; the occurrence is
     * what the event IS, so it keeps its own slot and its message its own
     * anchor (hdfs-17899-bug2, v22: two SPS sends swapped slots and every
     * later event of both exchanges was unnamed).
     */
    private static int slotOf(Pending event) {
        ArrayDeque<Integer> slots = SLOTS.get(event.key);
        if (slots == null || slots.isEmpty()) return -1;
        if (!event.occurrence.isEmpty()) {
            for (int slot : slots) {
                if (event.occurrence.equals(order.get(slot).occurrence())) {
                    return slot;
                }
            }
        }
        return slots.peekFirst();
    }

    /** Whether a slot holds its event: before the cut, or a WAKE. */
    private static boolean heldKind(int slot) {
        return slot < cut
                || order.get(slot).kind() == ScheduleEvent.Kind.WAKE;
    }

    /** Whether every slot before {@code slot} is settled or an open WAKE. */
    private static boolean dueLocked(int slot) {
        return firstBlocking >= slot;
    }

    /** Whether the prefix still stands: an open non-WAKE slot before the cut. */
    private static boolean prefixStandsLocked() {
        return holds && firstBlocking < cut;
    }

    /** An event took its slot. */
    private static void takeLocked(int slot) {
        ScheduleEvent event = order.get(slot);
        ArrayDeque<Integer> slots = SLOTS.get(event.key());
        if (slots != null) slots.remove(Integer.valueOf(slot));
        if (state[slot] == OPEN && heldKind(slot)) openHeld--;
        state[slot] = TAKEN;
        taken++;
        if (event.kind() == ScheduleEvent.Kind.WAKE) {
            TAKEN_WAKES.put(event.key(), slot);
        } else if (event.kind() == ScheduleEvent.Kind.END) {
            settleTurnLocked(event, slot);
        }
        settleLocked();
    }

    /** An open slot is given up: its event may still come and take it. */
    private static void giveUpLocked(int slot) {
        if (state[slot] != OPEN) return;
        if (heldKind(slot)) openHeld--;
        state[slot] = GIVEN_UP;
        givenUp++;
    }

    /**
     * A turn's END settles the turn: what the recording has between the
     * turn's WAKE and its END and the run has not made -- other than another
     * turn's WAKE -- is given up.  A daemon's turn decides on the wall clock
     * whether its heartbeat is due, so a recorded turn's RPC need not recur.
     */
    private static void settleTurnLocked(ScheduleEvent end, int endSlot) {
        Integer began = TAKEN_WAKES.get(ScheduleEvent.key(
                ScheduleEvent.Kind.WAKE, end.context(), end.site()));
        if (began == null || began >= endSlot) return;
        for (int index = Math.max(began + 1, firstOpen); index < endSlot;
             index++) {
            if (state[index] != OPEN
                    || order.get(index).kind() == ScheduleEvent.Kind.WAKE) {
                continue;
            }
            if (heldKind(index)) openHeld--;
            state[index] = GIVEN_UP;
            settledByEnd++;
        }
    }

    /** Something was settled: the first open slot, and whether any holds. */
    private static void settleLocked() {
        lastProgress = System.currentTimeMillis();
        cpuSampledAt = 0L;
        while (firstOpen < state.length && state[firstOpen] != OPEN) {
            firstOpen++;
        }
        firstBlocking = Math.max(firstBlocking, firstOpen);
        while (firstBlocking < state.length
                && (state[firstBlocking] != OPEN
                || order.get(firstBlocking).kind()
                        == ScheduleEvent.Kind.WAKE)) {
            firstBlocking++;
        }
        holds = openHeld > 0;
        LOCK.notifyAll();
    }

    /**
     * An occurrence closed: it makes no further event, so every slot the
     * order held for it that it did not make is dead.  Stated before the
     * cut, where the discovering run did more there than this one.
     */
    static void closed(String occurrenceId) {
        if (!holds || occurrenceId == null) return;
        mute();
        try {
            synchronized (LOCK) {
                List<Integer> slots = BY_OCCURRENCE.remove(occurrenceId);
                if (slots == null) return;
                int count = 0;
                int first = -1;
                for (int slot : slots) {
                    if (state[slot] != OPEN && state[slot] != GIVEN_UP) {
                        continue;
                    }
                    if (state[slot] == OPEN && heldKind(slot)) openHeld--;
                    state[slot] = DEAD;
                    ArrayDeque<Integer> keyed =
                            SLOTS.get(order.get(slot).key());
                    if (keyed != null) keyed.remove(Integer.valueOf(slot));
                    dead++;
                    count++;
                    if (first < 0) first = slot;
                }
                if (count == 0) return;
                if (first < cut) {
                    stateLocked("schedule-settled#" + first, "occurrence "
                            + occurrenceId + " closed without making " + count
                            + " event(s) the order held for it (the first "
                            + order.get(first).render() + " at slot " + first
                            + "): they are settled and no later event takes"
                            + " them");
                }
                settleLocked();
            }
        } finally {
            unmute();
        }
    }

    /**
     * The watchdog, run by a waiting thread: true when it settled something
     * and every waiter should look again.
     */
    private static boolean watchdogLocked() {
        if (WAITERS.isEmpty()) return false;
        long now = System.currentTimeMillis();
        long timeout = timeoutMillis();
        long idle = now - lastProgress;
        if (idle < timeout) return false;
        if (idle < CEILING * timeout && computingLocked(now)) return false;
        // A wait no slot holds waits for the whole prefix: it bounds a
        // give-up at the cut and is never a stall past it.
        int earliest = Integer.MAX_VALUE;
        for (int slot : WAITERS.values()) {
            earliest = Math.min(earliest, slot == AT_THE_CUT ? cut : slot);
        }
        boolean atTheCut = WAITERS.containsValue(AT_THE_CUT)
                && earliest == cut;
        stalls++;
        if (!atTheCut && earliest >= cut && restStalls >= REST_STALLS) {
            int open = 0;
            for (int index = firstOpen; index < state.length; index++) {
                if (state[index] == OPEN) {
                    giveUpLocked(index);
                    open++;
                }
            }
            stateLocked("schedule-rest#" + earliest, "past the cut the order"
                    + " stalled " + restStalls + " time(s) and would again"
                    + " (" + order.get(earliest).render() + " at slot "
                    + earliest + " waited " + idle + " ms): its " + open
                    + " open slot(s) are given up and the run is free");
            settleLocked();
            return true;
        }
        int first = -1;
        int count = 0;
        for (int index = firstOpen; index < earliest; index++) {
            if (state[index] != OPEN) continue;
            if (first < 0) first = index;
            giveUpLocked(index);
            count++;
        }
        if (count == 0) return false;
        if (!atTheCut && earliest >= cut) restStalls++;
        stateLocked((first < cut ? "schedule#" : "schedule-rest#") + first,
                count + " slot(s) of the order from " + first + " on (the"
                        + " first " + order.get(first).render() + ") did not"
                        + " happen for " + idle + " ms with the run idle,"
                        + " while " + (atTheCut
                                ? "a wait the order does not name waited at"
                                + " the cut"
                                : order.get(earliest).render()
                                + " waited at slot " + earliest)
                        + ": they are given up, and each still takes its"
                        + " slot if it comes");
        settleLocked();
        return true;
    }

    /**
     * Whether the threads that do not wait for a turn used at least half a
     * CPU since the last look: a run computing between two events -- the
     * concolic VM is many times slower than the recording -- is progress,
     * not a stall.  The first look after a settlement answers yes and takes
     * the sample the next one is measured from.
     */
    private static boolean computingLocked(long now) {
        if (cpuSampledAt != 0L && now - cpuSampledAt < CPU_SAMPLE_MS) {
            return computing;
        }
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        Set<Long> waiting = new HashSet<Long>();
        for (Thread thread : WAITERS.keySet()) waiting.add(thread.getId());
        Map<Long, Long> seen = new HashMap<Long, Long>();
        long used = 0L;
        for (long id : threads.getAllThreadIds()) {
            long cpu = threads.getThreadCpuTime(id);
            if (cpu < 0L) continue;
            seen.put(id, cpu);
            if (waiting.contains(id)) continue;
            Long before = CPU_SEEN.get(id);
            used += cpu - (before == null ? 0L : before);
        }
        boolean first = cpuSampledAt == 0L;
        long span = now - cpuSampledAt;
        CPU_SEEN.clear();
        CPU_SEEN.putAll(seen);
        cpuSampledAt = now;
        computing = first
                || used * 2L >= TimeUnit.MILLISECONDS.toNanos(span);
        return computing;
    }

    /** One SCHEDULE_DIVERGED statement, on the session and on stderr. */
    private static void stateLocked(String where, String detail) {
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    where, detail);
        } catch (Throwable unpublished) {
            // stderr below is the statement then.
        }
        System.err.println("Causynth schedule: " + detail);
    }

    /**
     * Whether this replay is held to its order right now: inside the
     * recording window, with an open slot that holds.  A wait begun before
     * the window is the set-up's and runs on the wall clock.
     */
    public static boolean enforcing() {
        if (!RecordingWindow.opened()) return false;
        if (!loaded) {
            synchronized (LOCK) {
                loadOrderLocked();
            }
        }
        return holds;
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
     * Reads the order this replay was handed, once: its prefix, from the
     * property, else the environment, else beside the focus row; the rest
     * from its property, else beside the focus row.
     */
    private static void loadOrderLocked() {
        if (loaded) return;
        loaded = true;
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
            return;
        }
        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                System.err.println("Causynth schedule: " + progress());
            }
        }, "causynth-schedule-progress"));
    }

    /** Holds the run to {@code events}, cut, then {@code after}. */
    private static void installLocked(List<ScheduleEvent> events,
                                      List<ScheduleEvent> after) {
        List<ScheduleEvent> all = new ArrayList<ScheduleEvent>(events);
        all.addAll(after);
        order = all;
        cut = events.size();
        state = new byte[all.size()];
        SLOTS.clear();
        BY_OCCURRENCE.clear();
        TAKEN_WAKES.clear();
        WAITERS.clear();
        openHeld = 0;
        for (int index = 0; index < all.size(); index++) {
            ScheduleEvent event = all.get(index);
            ArrayDeque<Integer> slots = SLOTS.get(event.key());
            if (slots == null) {
                slots = new ArrayDeque<Integer>();
                SLOTS.put(event.key(), slots);
            }
            slots.addLast(index);
            if (!event.occurrence().isEmpty()) {
                List<Integer> held = BY_OCCURRENCE.get(event.occurrence());
                if (held == null) {
                    held = new ArrayList<Integer>();
                    BY_OCCURRENCE.put(event.occurrence(), held);
                }
                held.add(index);
            }
            if (heldKind(index)) openHeld++;
        }
        firstOpen = 0;
        firstBlocking = 0;
        restStalls = 0;
        settleLocked();
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

    /** How the replay went through its order: its statement at exit. */
    static String progress() {
        synchronized (LOCK) {
            if (order.isEmpty()) return "no order";
            return "of an order of " + order.size() + " slot(s) (prefix "
                    + cut + "): " + taken + " taken, " + givenUp
                    + " given up in " + stalls + " stall(s), " + dead
                    + " settled by their occurrence's close, " + settledByEnd
                    + " settled by their turn's END; " + ranFree
                    + " event(s) ran free";
        }
    }

    /** Test hook: installs a prefix directly and starts holding to it. */
    static void enforceForTests(List<ScheduleEvent> events) {
        enforceForTests(events, Collections.<ScheduleEvent>emptyList());
    }

    /** Test hook: a prefix, and the rest of the order past it. */
    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after) {
        synchronized (LOCK) {
            loaded = true;
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
            loaded = false;
            holds = false;
            order = Collections.emptyList();
            cut = 0;
            state = new byte[0];
            SLOTS.clear();
            BY_OCCURRENCE.clear();
            TAKEN_WAKES.clear();
            WAITERS.clear();
            firstOpen = 0;
            firstBlocking = 0;
            openHeld = 0;
            lastProgress = 0L;
            restStalls = 0;
            taken = 0;
            ranFree = 0;
            givenUp = 0;
            stalls = 0;
            dead = 0;
            settledByEnd = 0;
            CPU_SEEN.clear();
            cpuSampledAt = 0L;
            computing = false;
            LOCK.notifyAll();
        }
    }
}
