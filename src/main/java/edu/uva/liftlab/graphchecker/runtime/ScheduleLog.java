package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
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
 * <p>RECORDER.  Every START, CLAIM, SEND, RECV, WAKE, END and INTERRUPT in
 * the recording window is appended in run order, in BOTH passes, changing
 * nothing the run does.</p>
 *
 * <p>ONE ORDER, ONE RULE.  A replay gets the discovering run's order as one
 * list of SLOTS: prefix to the cut ({@link #PREFIX_ENV}), rest after
 * ({@link #SUFFIX_FILE}).  An event takes the earliest open or given-up slot
 * of its key {@code (kind, c, site)}; with none it runs free.  A slot before
 * the cut, or a WAKE slot anywhere, is HELD until every earlier slot is
 * settled; other slots past the cut are taken at once.  INTERRUPT is never
 * held.  While the prefix stands a WAKE with no slot is held too: at the
 * cut when the recording never made it, and past its recorded count -- a
 * loop polling longer than recorded -- once per move of the order, unless
 * its loop reads a CLOCK root ({@link #waitsAtLocked}).</p>
 *
 * <p>SETTLING what did not happen: a CLOSED occurrence's untaken slots are
 * dead; a turn's END gives up what the turn did not do; a WAITER gives up
 * what its own occurrence, in its own context, did not make before its slot
 * (one thread, in program order, now past them); the WATCHDOG, after
 * a timeout with waiters and none of the threads that owe the slots before
 * the earliest waiter computing, first lets the waits held without a slot
 * go, then, a grace later, gives up every open slot before the earliest
 * waiter.  A given-up slot is still taken if its event comes late; a dead
 * one is not.  {@link #REST_STALLS} and {@link #CEILING} bound how long the
 * order can hold a run.</p>
 *
 * <p>One lock for both halves: the written order IS the admitted order.</p>
 */
public final class ScheduleLog {
    /** How long nothing may be settled while a thread waits, in ms. */
    public static final String TIMEOUT_PROPERTY =
            "causynth.schedule.timeout.ms";
    /** The prefix this replay is held to: a schedule.jsonl file. */
    public static final String PREFIX_ENV = "CAUSYNTH_SCHEDULE_PREFIX";
    /** The same, as a system property; the property wins. */
    public static final String PREFIX_PROPERTY = "causynth.schedule.prefix";
    public static final String PREFIX_FILE = "schedule_prefix.jsonl";
    public static final String SUFFIX_FILE = "schedule_suffix.jsonl";
    /** The rest, as a system property; else it stands beside the prefix. */
    public static final String SUFFIX_PROPERTY = "causynth.schedule.suffix";

    /** Below the workload's own window waits (60 s). */
    static final long DEFAULT_TIMEOUT_MS = 15000L;
    /** Give-ups past the cut before the rest is let go as a whole. */
    static final int REST_STALLS = 2;
    /** Where a wait no slot holds waits while the prefix stands and its
     *  context has no slot left. */
    private static final int AT_THE_CUT = -1;
    /** An event that waits nowhere: it is written now. */
    private static final int GO = -2;

    /** How long the waits a let-go released have to make progress before
     *  the watchdog acts again: the stall it answered stands meanwhile. */
    static final long LET_GO_GRACE_MS = 2000L;

    /** A stall this many timeouts long is given up whatever the CPU does. */
    static final int CEILING = 8;
    private static final long CPU_SAMPLE_MS = 1000L;

    private static final Object LOCK = new Object();

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
    /** Per event context, the slots its events were. */
    private static final Map<String, List<Integer>> BY_CONTEXT =
            new HashMap<String, List<Integer>>();
    /** Per WAKE key, the slot it took: where its turn began. */
    private static final Map<String, Integer> TAKEN_WAKES =
            new HashMap<String, Integer>();
    /** The threads waiting for a turn, each with the slot it waits at. */
    private static final Map<Thread, Integer> WAITERS =
            new HashMap<Thread, Integer>();
    /**
     * The waiters the order holds without a slot, each with the WAKE it
     * waits to make: one the recording never made (AT THE CUT), or a poll
     * past its recorded count ({@link #waitsAtLocked}).  Only these can be
     * let go.  A subset of {@link #WAITERS}.
     */
    private static final Map<Thread, Pending> HELD =
            new HashMap<Thread, Pending>();
    /** Held threads the watchdog let go, until the wait ends. */
    private static final Set<Thread> LET_GO = new HashSet<Thread>();
    /** How many times a slot was settled: the order's moves. */
    private static long moves;
    /**
     * Per WAKE key, {@link #moves} before its last WAKE was written: a poll
     * past its recorded count goes again only once the order moved since.
     * The slot a loop's last recorded WAKE took is itself a move, so the
     * first poll past the count goes at once.
     */
    private static final Map<String, Long> POLLED =
            new HashMap<String, Long>();
    /**
     * Whether this thread's last observed event was a vacant WAKE: one the
     * recording never made, held at the cut and let go only because the run
     * could go no further ({@link #vacated}).
     */
    private static final ThreadLocal<Boolean> VACANT = new ThreadLocal<Boolean>();
    /** Whether the watchdog let the cut's waits go since a slot was taken. */
    private static boolean letGoSinceProgress;
    /** When the watchdog last let waits go: its grace runs from here. */
    private static long letGoAt;
    /**
     * Per thread, the context of the last event it made under the order,
     * and whether that event was a WAKE no slot held: the thread is then a
     * poll past what the order holds, and its CPU is no one's progress.
     */
    private static final Map<Thread, Bound> BOUND =
            new java.util.WeakHashMap<Thread, Bound>();
    private static int firstOpen;
    /**
     * The first open slot in a later event's way; an open WAKE never is,
     * since its daemon may be blocked behind a lock a held thread owns.  A
     * daemon's turn never comes sooner than recorded, and is never waited
     * for.
     */
    private static int firstBlocking;
    /** Open slots that hold: before the cut, or a WAKE. */
    private static int openHeld;
    private static long lastProgress;
    private static int restStalls;
    private static int taken;
    private static int ranFree;
    private static int letGo;
    private static int closedOpen;
    private static int givenUp;
    private static int stalls;
    private static int dead;
    private static int settledByEnd;
    private static int passed;
    private static final Map<Long, Long> CPU_SEEN = new HashMap<Long, Long>();
    private static long cpuSampledAt;
    private static boolean computing;

    private ScheduleLog() {
    }

    /** What a thread's last admitted event says about it ({@link #BOUND}). */
    private static final class Bound {
        private final String context;
        private final boolean polling;

        private Bound(String context, boolean polling) {
            this.context = context;
            this.polling = polling;
        }
    }

    // ---- recording -------------------------------------------------------

    /**
     * One event at a hook, admitted then written; never throws.
     *
     * @return whether the event was written
     */
    public static boolean observe(ScheduleEvent.Kind kind, String site) {
        return observe(kind, site, "");
    }

    /** For a SEND: {@code endpoint} is the producer endpoint it carries. */
    public static boolean observe(ScheduleEvent.Kind kind, String site,
                                  String endpoint) {
        return observe(kind, site, endpoint, null);
    }

    /** Where an event stands: its context and region ({@link #stanceHere}).
     */
    public static final class Stance {
        private final String context;
        private final String region;

        private Stance(String context, String region) {
            this.context = context;
            this.region = region;
        }
    }

    /** Where an event on this thread would stand now, or null outside the
     *  window or any attributable context. */
    public static Stance stanceHere() {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            return standing();
        } finally {
            unmute();
        }
    }

    /** {@link #stanceHere}, already muted. */
    private static Stance standing() {
        try {
            CausalContext context = Identity.contextHere();
            return context.isLost() || unordered(context) ? null
                    : new Stance(contextOf(context),
                    Identity.innermostRegionId());
        } catch (Throwable unnamed) {
            return null;
        }
    }

    /** The transports whose receipts no order awaits ({@link #unawaited}). */
    private static final Set<String> UNAWAITED =
            java.util.concurrent.ConcurrentHashMap.newKeySet();

    /**
     * A transport's receipt is never awaited (a shared store's read: how
     * many notifications a run takes is the store's timing), so neither is
     * the work it causes: an event in a context it anchored is free, as a
     * Lost one is, in the recording and in every replay.
     */
    static void unawaited(String transport) {
        UNAWAITED.add(Text.safe(transport).toUpperCase(java.util.Locale.ROOT));
    }

    private static boolean unordered(CausalContext context) {
        if (!(context instanceof CausalContext.Anchor)) return false;
        String site = ((CausalContext.Anchor) context).rpcSite();
        int slash = site.indexOf('/');
        return UNAWAITED.contains(slash < 0 ? site : site.substring(0, slash));
    }

    /** The same, standing where {@code at} says rather than on this thread
     *  (a response stands where its request was received). */
    public static boolean observe(ScheduleEvent.Kind kind, String site,
                                  String endpoint, Stance at) {
        VACANT.remove();
        if (kind == null || !RecordingWindow.opened()) return false;
        mute();
        try {
            Pending event = pending(kind, site, endpoint, at);
            if (event == null) return false;
            admit(event);
            return true;
        } finally {
            unmute();
        }
    }

    /**
     * Whether the event this thread just observed was a vacant WAKE: a turn
     * the recording never made, which the replay held at the cut and let go
     * because the run was idle -- something the order waits for waits on it
     * (a pool's shutdown awaiting the task the turn runs in).  A turn that
     * may be skipped is skipped then ({@code MessageDoors#vacant}).  Never
     * true in a recording, which holds nothing.
     */
    static boolean vacated() {
        return Boolean.TRUE.equals(VACANT.get());
    }

    /**
     * Mutes replay observation around this class's bookkeeping, never around
     * the workload's own wait ({@link TimedWaits}).
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

    /** The WAKE one timed wait would make, computed once. */
    static final class Wake {
        private final Pending event;

        private Wake(Pending event) {
            this.event = event;
        }
    }

    static Wake wake(String site) {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            Pending event = pending(ScheduleEvent.Kind.WAKE, site, "", null);
            return event == null ? null : new Wake(event);
        } finally {
            unmute();
        }
    }

    static void withdraw(Wake wake) {
        if (wake == null) return;
        synchronized (LOCK) {
            LET_GO.remove(Thread.currentThread());
            HELD.remove(Thread.currentThread());
            if (WAITERS.remove(Thread.currentThread()) != null) {
                LOCK.notifyAll();
            }
        }
    }

    /** What a held wait's ask for its turn found. */
    enum Turn {
        /** Its WAKE slot was due: taken and written. */
        ADMITTED,
        /** Not due yet, or held with no slot while the prefix stands: ask
         *  again. */
        NOT_YET,
        /** No slot and nothing holds it: its own deadline, on the wall
         *  clock. */
        FREE,
        /** The wait has no event to make, so nothing can hold it. */
        NO_EVENT
    }

    /**
     * Asks once, without blocking, whether the timeout WAKE may take its
     * turn; for a wait that waits on its own primitive between asks.
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
                    int at = waitsAtLocked(wake.event, slot);
                    if (at == GO) {
                        WAITERS.remove(self);
                        if (slot < 0) return Turn.FREE;
                        admittedLocked(wake.event, slot);
                        return Turn.ADMITTED;
                    }
                    // Not due: a signal still ends the wait meanwhile.
                    WAITERS.put(self, at);
                    if (!passedLocked(wake.event, at) && !watchdogLocked()) {
                        return Turn.NOT_YET;
                    }
                }
            }
        } finally {
            unmute();
        }
    }

    /** The WAKE of a {@link Turn#FREE} wait the wall clock ended. */
    static void timedOut(Wake wake) {
        if (wake == null) return;
        mute();
        try {
            admit(wake.event);
        } finally {
            unmute();
        }
    }

    /** One event about to be admitted, computed off the lock. */
    private static final class Pending {
        private final ScheduleEvent.Kind kind;
        private final String context;
        private final String site;
        private final String occurrence;
        private final String endpoint;
        private final String key;
        /** Whether this wait's loop reads a CLOCK root; asked once, under
         *  the lock, only of a poll past its recorded count. */
        private Boolean clockLoop;

        private Pending(ScheduleEvent.Kind kind, String context, String site,
                        String occurrence, String endpoint) {
            this.kind = kind;
            this.context = context;
            this.site = site;
            this.occurrence = occurrence;
            this.endpoint = endpoint;
            this.key = ScheduleEvent.key(kind, context, site);
        }

        private String render() {
            return kind.name() + " " + site + " @ " + context;
        }
    }

    /**
     * The event this hook makes, or null.  A {@code Lost} context makes none:
     * all Lost threads share it, so its k would be a cross-thread counter
     * (G8) and would stall the replay.
     */
    private static Pending pending(ScheduleEvent.Kind kind, String site,
                                   String endpoint, Stance at) {
        String stable = JvmNames.stable(Text.safe(site));
        if (stable.isEmpty()) return null;
        Stance stance = at != null ? at : standing();
        if (stance == null) return null;
        return new Pending(kind, stance.context, stable, stance.region,
                Text.safe(endpoint));
    }

    private static void appendLocked(Pending pending) {
        Integer made = COUNTS.get(pending.key);
        int k = made == null ? 0 : made;
        COUNTS.put(pending.key, k + 1);
        ScheduleEvent event = ScheduleEvent.of(seq++, pending.kind,
                pending.context, pending.site, k, pending.occurrence,
                pending.endpoint);
        writeLocked(RowCodec.writeScheduleEvent(event));
    }

    /** One row to the sink, or held until one is installed. */
    private static void writeLocked(JsonObject row) {
        if (sink != null) {
            sink.write(row);
        } else if (PENDING.size() < PENDING_LIMIT) {
            PENDING.add(row);
        }
    }

    private static final Set<String> MARKED = new HashSet<String>();

    /**
     * Marks where one occurrence opened: not an event, but the cut of a
     * prefix that focuses it.
     */
    static void mark(String occurrenceId) {
        String id = Text.safe(occurrenceId);
        if (id.isEmpty() || !RecordingWindow.opened()) return;
        synchronized (LOCK) {
            if (!MARKED.add(id)) return;
            JsonObject row = new JsonObject();
            row.addProperty("mark", id);
            row.addProperty("at", seq);
            writeLocked(row);
        }
    }

    /**
     * The event context: node, causal context and {@link Identity#handoffs},
     * so a key's k never counts two threads interleaved.
     */
    static String contextHere() {
        return contextOf(Identity.contextHere());
    }

    private static String contextOf(CausalContext context) {
        String node = Text.safe(RuntimeTraceContext.nodeHere());
        String handoffs = Identity.handoffs();
        return node + "|" + context.render()
                + (handoffs.isEmpty() ? "" : "|" + handoffs);
    }

    /** Installs where events go, draining those made before it. */
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
        final File file = new File(directory, SessionDir.SCHEDULE);
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

    private static void admit(Pending event) {
        synchronized (LOCK) {
            loadOrderLocked();
            admitLocked(event);
        }
    }

    /** Admits one event by THE rule and writes it; runs the watchdog. */
    private static void admitLocked(Pending event) {
        if (!holds) {
            appendLocked(event);
            return;
        }
        Thread self = Thread.currentThread();
        try {
            while (true) {
                int slot = slotOf(event);
                int at = waitsAtLocked(event, slot);
                if (at == GO) {
                    if (slot < 0 && event.kind == ScheduleEvent.Kind.WAKE
                            && LET_GO.contains(self)) {
                        VACANT.set(Boolean.TRUE);
                    }
                    admittedLocked(event, slot);
                    return;
                }
                WAITERS.put(self, at);
                if (passedLocked(event, at) || watchdogLocked()) continue;
                LOCK.wait(Math.max(1L, Math.min(timeoutMillis(), 1000L)));
            }
        } catch (InterruptedException interrupted) {
            // The workload's interrupt is its own; the event still takes
            // its slot.
            Thread.currentThread().interrupt();
            admittedLocked(event, slotOf(event));
        } finally {
            WAITERS.remove(self);
            HELD.remove(self);
            LET_GO.remove(self);
        }
    }

    /**
     * Writes an event the order admitted, into {@code slot} or free (-1),
     * and binds its thread to its context ({@link #BOUND}).
     */
    private static void admittedLocked(Pending event, int slot) {
        long before = moves;
        if (slot >= 0) {
            takeLocked(slot);
        } else {
            ranFree++;
        }
        appendLocked(event);
        boolean wake = event.kind == ScheduleEvent.Kind.WAKE;
        if (wake) POLLED.put(event.key, before);
        BOUND.put(Thread.currentThread(), new Bound(event.context,
                wake && slot < 0));
    }

    /**
     * The slot an event takes: the earliest of its key made by its OWN
     * occurrence, else the earliest; -1 when none.  Two concurrent RPCs under
     * one context share a key, and must not swap slots (and anchors).
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

    /**
     * Where {@code event}, whose slot is {@code slot} (-1: none), waits now,
     * or {@link #GO}.  INTERRUPT is never held.  A WAKE no slot holds is
     * held while the prefix stands, and only then ({@link #HELD}):
     *
     * <ul>
     *   <li>one the recording never made waits AT THE CUT;</li>
     *   <li>one PAST ITS RECORDED COUNT is a loop polling longer than
     *       recorded, for what another context brings.  It waits until its
     *       context's next slot is due -- only its next turn makes that
     *       slot's event -- and then polls once per move of the order since
     *       its previous WAKE ({@link #POLLED}): a poll between two moves
     *       would read what the last one read.  A loop that reads a CLOCK
     *       root ({@link ClockLoops}) waits for time only the clock brings,
     *       and goes as soon as its slot is due.  With no slot of its
     *       context left, it waits at the cut.</li>
     * </ul>
     *
     * The watchdog lets a held wait go when the run idles.  Released, a
     * timed wait still waits out its own deadline ({@link TimedWaits}).
     */
    private static int waitsAtLocked(Pending event, int slot) {
        Thread self = Thread.currentThread();
        HELD.remove(self);
        if (slot >= 0) {
            return event.kind == ScheduleEvent.Kind.INTERRUPT
                    || !heldKind(slot) || dueLocked(slot) ? GO : slot;
        }
        if (event.kind != ScheduleEvent.Kind.WAKE || !prefixStandsLocked()) {
            return GO;
        }
        int next = SLOTS.containsKey(event.key)
                ? nextOpenLocked(BY_CONTEXT.get(event.context)) : -1;
        if (next >= 0) {
            if (!dueLocked(next)) return next;
            if (movedSincePollLocked(event) || clockLoopLocked(event)) {
                return GO;
            }
        }
        if (LET_GO.contains(self)) return GO;
        HELD.put(self, event);
        return next >= 0 ? next : AT_THE_CUT;
    }

    /** Whether the order moved since the last WAKE of {@code event}'s key. */
    private static boolean movedSincePollLocked(Pending event) {
        Long polled = POLLED.get(event.key);
        return polled == null || moves > polled;
    }

    /**
     * Whether {@code event}'s wait -- on this thread's stack now -- is a
     * clock's loop.  Asked per wait: one context's waits at one site (a
     * {@code TimeOut}'s sleep) may stand in different loops.
     */
    private static boolean clockLoopLocked(Pending event) {
        if (event.clockLoop == null) {
            event.clockLoop = ClockLoops.reads(
                    Thread.currentThread().getStackTrace());
        }
        return event.clockLoop;
    }

    /** The first open slot of {@code slots}, or -1. */
    private static int nextOpenLocked(List<Integer> slots) {
        if (slots == null) return -1;
        for (int slot : slots) {
            if (slot >= firstOpen && state[slot] == OPEN) return slot;
        }
        return -1;
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

    /** Whether the prefix stands: an open non-WAKE slot before the cut. */
    private static boolean prefixStandsLocked() {
        return holds && firstBlocking < cut;
    }

    private static void takeLocked(int slot) {
        ScheduleEvent event = order.get(slot);
        markLocked(slot, TAKEN);
        taken++;
        letGoSinceProgress = false;
        if (event.kind() == ScheduleEvent.Kind.WAKE) {
            TAKEN_WAKES.put(event.key(), slot);
        } else if (event.kind() == ScheduleEvent.Kind.END) {
            settleTurnLocked(event, slot);
        }
        settleLocked();
    }

    /**
     * Moves one slot to {@code next}; a TAKEN or DEAD one leaves its key's
     * queue, so no event takes it again.
     */
    private static void markLocked(int slot, byte next) {
        if (state[slot] == OPEN && heldKind(slot)) openHeld--;
        state[slot] = next;
        if (next == GIVEN_UP) return;
        ArrayDeque<Integer> keyed = SLOTS.get(order.get(slot).key());
        if (keyed != null) keyed.remove(Integer.valueOf(slot));
    }

    /** An open slot is given up: its event may still come and take it. */
    private static void giveUpLocked(int slot) {
        if (state[slot] != OPEN) return;
        markLocked(slot, GIVEN_UP);
        givenUp++;
    }

    /** A turn's END gives up what the turn did not make, WAKEs aside. */
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
            markLocked(index, GIVEN_UP);
            settledByEnd++;
        }
    }

    /**
     * The slots before {@code at} that the waiter's own occurrence, in its
     * own context, did not make: one thread makes them in program order and
     * waits past them, so only a watchdog timeout would settle them (a8
     * reader-chunk.flush: a NameNode handler whose block report enqueued
     * nothing held addBlock past the client's 60 s).  Given up, WAKEs aside.
     */
    private static boolean passedLocked(Pending event, int at) {
        List<Integer> own = event.occurrence.isEmpty() ? null
                : BY_OCCURRENCE.get(event.occurrence);
        if (own == null) return false;
        int count = 0;
        for (int slot : own) {
            if (slot >= at) break;
            ScheduleEvent passedOver = order.get(slot);
            if (state[slot] != OPEN
                    || passedOver.kind() == ScheduleEvent.Kind.WAKE
                    || !event.context.equals(passedOver.context())) {
                continue;
            }
            markLocked(slot, GIVEN_UP);
            count++;
        }
        if (count == 0) return false;
        passed += count;
        settleLocked();
        return true;
    }

    /**
     * Something was settled -- the order moved: the first open slot, and
     * whether any holds.
     */
    private static void settleLocked() {
        moves++;
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

    /** The workload closed its window: what the order still holds is let go. */
    static void windowClosed() {
        mute();
        try {
            synchronized (LOCK) {
                if (!holds) return;
                int first = -1;
                for (int index = firstOpen; index < state.length; index++) {
                    if (state[index] != OPEN) continue;
                    if (first < 0) first = index;
                    markLocked(index, DEAD);
                    closedOpen++;
                }
                if (first >= 0) {
                    stateLocked("schedule-closed#" + first, closedOpen
                            + " slot(s) of the order from " + first + " on"
                            + " (the first " + order.get(first).render()
                            + ") were open when the workload closed its"
                            + " window: they are settled");
                }
                settleLocked();
            }
        } finally {
            unmute();
        }
    }

    /** An occurrence closed: its untaken slots are dead. */
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
                    markLocked(slot, DEAD);
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
     * The watchdog, run by a waiter: true when it settled something or let
     * waits go.  A stall is a timeout with no slot settled and none of the
     * threads that owe the slots before the earliest waiter computing
     * ({@link #computingLocked}), or {@link #CEILING} timeouts whatever they
     * do; both are measured from the stall's start, which a let-go does not
     * move.  Its first answer lets the waits held without a slot go; a grace
     * later, the slots before the earliest waiter are given up; when that
     * settles nothing, the held waits are let go again, a grace apart.
     */
    private static boolean watchdogLocked() {
        if (WAITERS.isEmpty()) return false;
        long now = System.currentTimeMillis();
        long timeout = timeoutMillis();
        long idle = now - lastProgress;
        if (idle < timeout || now - letGoAt < LET_GO_GRACE_MS) return false;
        // An AT_THE_CUT waiter bounds a give-up at the cut.
        int earliest = Integer.MAX_VALUE;
        for (int slot : WAITERS.values()) {
            earliest = Math.min(earliest, slot == AT_THE_CUT ? cut : slot);
        }
        if (idle < CEILING * timeout && computingLocked(now, earliest)) {
            return false;
        }
        if (!letGoSinceProgress && !HELD.isEmpty()) {
            letGoHeldLocked(idle, now);
            return true;
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
        if (count == 0) {
            // Nothing before the held polls is open: only they can move.
            if (HELD.isEmpty()) return false;
            letGoHeldLocked(idle, now);
            return true;
        }
        if (!atTheCut && earliest >= cut) restStalls++;
        stateLocked((first < cut ? "schedule#" : "schedule-rest#") + first,
                count + " slot(s) of the order from " + first + " on (the"
                        + " first " + order.get(first).render() + ") did not"
                        + " happen for " + idle + " ms with the run idle,"
                        + " while " + waitingAtLocked(earliest)
                        + ": they are given up, and each still takes its"
                        + " slot if it comes");
        settleLocked();
        return true;
    }

    /**
     * Lets every wait held without a slot go.  With the run idle, a wait
     * the recording never made -- a pool thread's -- or a loop polling past
     * its recorded count may be what the order's next event is behind, and
     * giving the order up settles nothing that holds it.  Its event runs
     * free.  The stall stands: the waits let go have {@link
     * #LET_GO_GRACE_MS}, not another timeout, to make progress.
     */
    private static void letGoHeldLocked(long idle, long now) {
        String held = heldLocked(HELD.keySet().iterator().next());
        int count = HELD.size();
        LET_GO.addAll(HELD.keySet());
        letGo += count;
        letGoSinceProgress = true;
        letGoAt = now;
        stateLocked("schedule-let-go#" + firstBlocking, count + " wait(s)"
                + " held without a slot (" + held + ") for " + idle + " ms"
                + " with the run idle, while " + (firstBlocking < order.size()
                        ? order.get(firstBlocking).render() : "nothing")
                + " at slot " + firstBlocking + " did not happen: they are"
                + " let go before any slot is given up");
        LOCK.notifyAll();
    }

    /** What waits at {@code earliest}, as it names itself. */
    private static String waitingAtLocked(int earliest) {
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            int at = waiter.getValue() == AT_THE_CUT ? cut : waiter.getValue();
            if (at == earliest && HELD.containsKey(waiter.getKey())) {
                return heldLocked(waiter.getKey()) + " waited "
                        + (waiter.getValue() == AT_THE_CUT ? "at the cut"
                                : "at slot " + earliest);
            }
        }
        return order.get(earliest).render() + " waited at slot " + earliest;
    }

    /** A held wait, as it names itself. */
    private static String heldLocked(Thread thread) {
        Pending held = HELD.get(thread);
        return SLOTS.containsKey(held.key)
                ? held.render() + " past its recorded count"
                : "the unrecorded " + held.render();
    }

    /**
     * Whether the threads that owe the order's next events used at least
     * half a CPU since the last look: the slow concolic VM computing toward
     * them is progress, not a stall.  They are the threads whose last event
     * stood in a context owning an open non-WAKE slot before {@code
     * earliest}, or in work such a context handed on ({@link #owes}), and
     * that neither wait nor poll past what the order holds ({@link #BOUND}).
     * Nothing else counts: the result publication ({@code causynth-*}
     * threads make no event), a store notification's parse, a thread no
     * event bound, a loop polling past its recorded count.
     */
    private static boolean computingLocked(long now, int earliest) {
        if (cpuSampledAt != 0L && now - cpuSampledAt < CPU_SAMPLE_MS) {
            return computing;
        }
        Set<String> owners = new HashSet<String>();
        for (int index = firstBlocking;
             index < Math.min(earliest, state.length); index++) {
            if (state[index] == OPEN
                    && order.get(index).kind() != ScheduleEvent.Kind.WAKE) {
                owners.add(order.get(index).context());
            }
        }
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        Map<Long, Long> seen = new HashMap<Long, Long>();
        long used = 0L;
        for (Map.Entry<Thread, Bound> bound : BOUND.entrySet()) {
            Thread thread = bound.getKey();
            if (bound.getValue().polling || WAITERS.containsKey(thread)
                    || !owes(bound.getValue().context, owners)) {
                continue;
            }
            long cpu = threads.getThreadCpuTime(thread.getId());
            if (cpu < 0L) continue;
            seen.put(thread.getId(), cpu);
            // A thread first counted now has no span measured yet.
            Long before = CPU_SEEN.get(thread.getId());
            if (before != null) used += cpu - before;
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

    /**
     * Whether {@code context} is one of {@code owners}, or work one of them
     * handed on: its context extended by handoffs ({@link #contextOf}).
     */
    private static boolean owes(String context, Set<String> owners) {
        if (owners.contains(context)) return true;
        for (int bar = context.indexOf('|'); bar > 0;
             bar = context.indexOf('|', bar + 1)) {
            if (owners.contains(context.substring(0, bar))) return true;
        }
        return false;
    }

    /** One SCHEDULE_DIVERGED statement, on the session and on stderr. */
    private static void stateLocked(String where, String detail) {
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    where, detail);
        } catch (Throwable unpublished) {
        }
        System.err.println("Causynth schedule: " + detail);
    }

    /** Whether the replay is held right now: in the window, a slot holds. */
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

    /** Reads the order this replay was handed, once. */
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
            // An order it cannot read, it left at its first event.
            stateLocked(String.valueOf(file == null ? restFile : file),
                    "the schedule " + file + " / " + restFile + " could not"
                            + " be read (" + unreadable + "), so the replay"
                            + " runs free from its first event");
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
        BY_CONTEXT.clear();
        TAKEN_WAKES.clear();
        WAITERS.clear();
        HELD.clear();
        LET_GO.clear();
        POLLED.clear();
        moves = 0L;
        letGoSinceProgress = false;
        letGoAt = 0L;
        BOUND.clear();
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
            List<Integer> own = BY_CONTEXT.get(event.context());
            if (own == null) {
                own = new ArrayList<Integer>();
                BY_CONTEXT.put(event.context(), own);
            }
            own.add(index);
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
        return orderFile(named, PREFIX_FILE);
    }

    private static Path suffixFile() {
        return orderFile(Text.safe(System.getProperty(SUFFIX_PROPERTY)),
                SUFFIX_FILE);
    }

    /** The file {@code named}, else {@code name} in the worker directory. */
    private static Path orderFile(String named, String name) {
        if (!named.isEmpty()) return Paths.get(named);
        String worker = FocusedReplay.workerDir();
        if (worker.isEmpty()) return null;
        Path beside = Paths.get(worker).resolve(name);
        return beside.toFile().isFile() ? beside : null;
    }

    /** The replay's account of its order, at exit. */
    static String progress() {
        synchronized (LOCK) {
            if (order.isEmpty()) return "no order";
            return "of an order of " + order.size() + " slot(s) (prefix "
                    + cut + "): " + taken + " taken, " + givenUp
                    + " given up in " + stalls + " stall(s), " + dead
                    + " settled by their occurrence's close, " + settledByEnd
                    + " settled by their turn's END, " + passed
                    + " passed by their own occurrence; " + ranFree
                    + " event(s) ran free, " + letGo + " of them let go at"
                    + " the cut; " + closedOpen + " open at the window's"
                    + " close";
        }
    }

    static void enforceForTests(List<ScheduleEvent> events) {
        enforceForTests(events, Collections.<ScheduleEvent>emptyList());
    }

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
            BY_CONTEXT.clear();
            TAKEN_WAKES.clear();
            WAITERS.clear();
            HELD.clear();
            LET_GO.clear();
            POLLED.clear();
            ClockLoops.resetForTests();
            moves = 0L;
            letGoSinceProgress = false;
            letGoAt = 0L;
            BOUND.clear();
            firstOpen = 0;
            firstBlocking = 0;
            openHeld = 0;
            lastProgress = 0L;
            restStalls = 0;
            taken = 0;
            ranFree = 0;
            letGo = 0;
            closedOpen = 0;
            givenUp = 0;
            stalls = 0;
            dead = 0;
            settledByEnd = 0;
            passed = 0;
            CPU_SEEN.clear();
            cpuSampledAt = 0L;
            computing = false;
            LOCK.notifyAll();
        }
    }
}
