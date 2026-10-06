package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
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
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
 * settled; other slots past the cut are taken at once.  An INTERRUPT slot
 * holds nothing and is in no later event's way: it is taken if it comes.
 * While the prefix stands a WAKE with no slot is held too: at the
 * cut when the recording never made it, and past its recorded count -- a
 * loop polling longer than recorded -- once per move of the order, unless
 * its loop reads a CLOCK root ({@link #waitsAtLocked}).  An order cut at its
 * witness ({@link ScheduleEvent#WITNESS}) holds such a WAKE to its END, not
 * its cut: that run made nothing it does not list before its witness.</p>
 *
 * <p>SETTLING what did not happen: a CLOSED occurrence's untaken slots are
 * dead; a turn's END gives up what the turn did not do; a WAITER gives up
 * what its own occurrence, in its own context, did not make before its slot
 * (one thread, in program order, now past them); the WATCHDOG, once the
 * order's FRONTIER -- its first open slot that is no WAKE or INTERRUPT,
 * which every wait for a slot or the line waits on -- has stood a timeout,
 * counted from its last move or its earliest waiter's arrival, whichever is
 * later, with no thread computing toward it, first lets the waits held
 * without a slot go, then, a grace later, gives up every open slot before
 * the earliest waiter a slot holds.  A slot taken past the frontier or an event run free moves
 * no such wait (a poll past its recorded count goes on any move, but waits
 * for no slot's event), and a thread making them away from the frontier's
 * context computes elsewhere ({@link #computingLocked}).  A given-up slot
 * is still taken if its event comes late; a dead one is not.  A wait for a
 * slot is held at most {@link #CEILING} timeouts and a grace; a wait held
 * without a slot is let go once the frontier stood a timeout, at most
 * CEILING timeouts while a thread computes toward it; after {@link
 * #REST_STALLS} give-ups past the cut the rest is let go.</p>
 *
 * <p>One lock for both halves: the written order IS the admitted order.</p>
 */
public final class ScheduleLog {
    /** How long the order's frontier may stand while a thread waits, in
     *  ms. */
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
    /** Where a wait no slot holds waits while the line stands and its
     *  context has no slot left ({@link #line}). */
    private static final int AT_THE_LINE = -1;
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
    /**
     * Where a WAKE no slot holds waits: the cut, or the order's end when its
     * run was cut at its witness -- that run's log orders nothing after, so
     * a daemon turn it never made came, if at all, after all of it
     * (hdfs-17967-pathC r1b: CONFIRM ran the target DataNode's first
     * BP_SERVICE_ACTOR turn free, before the anchor, and it refreshed the
     * keys the witness had failed on).
     */
    private static int line;
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
    /** When each of {@link #WAITERS} began to wait: a stall is timed from
     *  the earliest ({@link #stallSinceLocked}). */
    private static final Map<Thread, Long> ARRIVED =
            new HashMap<Thread, Long>();
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
    /**
     * Whether the watchdog let held waits go since the frontier moved: one
     * let-go per frontier, then the give-up.  A slot taken past the frontier
     * moves no wait for a slot, so it earns the held waits no second let-go
     * before that give-up; one per take would hold the give-up off for as
     * long as anything ran elsewhere.
     */
    private static boolean letGoSinceProgress;
    /** When the watchdog last let waits go: its grace runs from here. */
    private static long letGoAt;
    /** The engine's own threads are named so; their CPU is no progress. */
    private static final String ENGINE_THREAD = "causynth-";
    private static int firstOpen;
    /**
     * The first open slot in a later event's way ({@link #blocking}): an
     * open WAKE never is, since its daemon may be blocked behind a lock a
     * held thread owns -- a daemon's turn never comes sooner than recorded,
     * and is never waited for -- nor an open INTERRUPT, which another
     * thread's call made where the interrupted thread then stood ({@link
     * #heldKind}).
     */
    private static int firstBlocking;
    /** Open slots that hold ({@link #heldKind}). */
    private static int openHeld;
    /**
     * When {@link #firstBlocking}, the order's frontier, last moved: every
     * wait for a slot or the line waits on it.  Slots settled past it move
     * none of them (a free-running test loop's polls taking their later
     * slots past the cut: hdfs-17899-bug2 w4d1 CONFIRM, a BPServiceActor's
     * turn END the frontier for its test's 30 s wait).
     */
    private static long lastProgress;
    /** The stall the CPU looks belong to ({@link #stallSinceLocked}). */
    private static long stallSince;
    /**
     * The threads seen since the last CPU look at an event AWAY from the
     * frontier: run free, or into a slot past it, in neither the frontier's
     * context nor its occurrence.  Such a thread runs on elsewhere, not
     * toward the frontier ({@link #computingLocked}).
     */
    private static final Set<Long> ELSEWHERE = new HashSet<Long>();
    /**
     * The threads the watchdog let go since the frontier moved: never
     * {@link #ELSEWHERE}, since what a released wait runs next may be what
     * the frontier waits for.
     */
    private static final Set<Long> RELEASED = new HashSet<Long>();
    /**
     * Whether a thread was seen since the last CPU look at an event in the
     * frontier's own context or occurrence: its owner at work, whatever CPU
     * share it gets (the VM's arena mutex, a collection, a busy host).
     */
    private static boolean ownerAtWork;
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
    /** The collectors' summed time at the last look, in ms. */
    private static long collectedSeen;
    private static long cpuSampledAt;
    private static boolean computing;

    private ScheduleLog() {
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

    /** For a SEND: {@code endpoint} is the producer endpoint it carries; for
     *  a RECV into the receiver's own context, the one it took in. */
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

    /**
     * Whether a context makes no event: one an unawaited receipt anchored,
     * or one anchored by a message this run stated no SEND for ({@link
     * #SENDERS}): sent before the window, from a Lost turn, or from a
     * context of its own that makes none.  Its cause is outside the order,
     * so the order cannot hold what it causes -- hdfs-adhoc-19/35: a
     * DataNode's first block report went out before the window and its
     * reply, with the NameNode's commands, came inside it, a slot a replay
     * whose report was answered before its window never made.  A response
     * sent in such a context states no SEND either, so the work its reply
     * causes is free too.  Once the bounded store dropped a sender, a miss
     * may be one it dropped: that sender is unknown, its context ordered,
     * and each such sender named ({@code schedule-sender-unknown}).
     */
    private static boolean unordered(CausalContext context) {
        if (!(context instanceof CausalContext.Anchor)) return false;
        CausalContext.Anchor anchor = (CausalContext.Anchor) context;
        String site = anchor.rpcSite();
        int slash = site.indexOf('/');
        if (UNAWAITED.contains(slash < 0 ? site : site.substring(0, slash))) {
            return true;
        }
        String sender = anchor.producerEndpointId();
        long dropped;
        synchronized (SENDERS) {
            if (SENDERS.containsKey(sender)) return false;
            dropped = SENDERS.evicted();
            if (dropped == 0L) return true;
            if (!UNKNOWN_SENDERS.add(sender)) return false;
        }
        stateLocked("schedule-sender-unknown#" + sender, "the sender " + sender
                + " of " + context.render() + " is not among this run's "
                + Interactions.LIMIT + " latest SEND stances (" + dropped
                + " dropped): whether its SEND was stated is unknown, so the"
                + " context is ordered");
        return false;
    }

    /** The senders a miss after a drop left unknown, each named once. */
    private static final Set<String> UNKNOWN_SENDERS = new HashSet<String>();

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
            takeTurnWake(TURN.get());
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

    /** The WAKE a held timed wait would make, computed quietly: asking
     *  names no turn, as the free wait of a recording asks nothing. */
    static Wake wake(String site) {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            Pending event = Lineage.quietly(() -> pending(
                    ScheduleEvent.Kind.WAKE, site, "", null));
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
            if (doneWaitingLocked(Thread.currentThread())) {
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
            while (true) {
                synchronized (LOCK) {
                    loadOrderLocked();
                    Thread self = Thread.currentThread();
                    int slot = holds ? slotOf(wake.event) : -1;
                    int at = waitsAtLocked(wake.event, slot);
                    if (at == GO && (slot < 0 || turnWritten())) {
                        doneWaitingLocked(self);
                        if (slot < 0) return Turn.FREE;
                        admittedLocked(wake.event, slot);
                        return Turn.ADMITTED;
                    }
                    if (at != GO) {
                        // Not due: a signal still ends the wait meanwhile.
                        waitLocked(self, at);
                        if (!passedLocked(wake.event, at)
                                && !watchdogLocked()) {
                            return Turn.NOT_YET;
                        }
                        continue;
                    }
                }
                // Due, and the turn's first event: its WAKE first, outside
                // the lock (due itself, as every slot before this one is).
                takeTurnWake(TURN.get());
            }
        } finally {
            unmute();
        }
    }

    /**
     * Asks once, without blocking, whether the WAKE of a {@link Turn#FREE}
     * wait the wall clock ended may be written, and writes it when it may
     * (true).  Not yet (false): the waiter waits a quantum on its own
     * primitive and asks again, so the monitor or lock its wait released
     * stays released until the WAKE is written, as the JVM returns from a
     * wait only then.  Admitted holding it, the WAKE of an
     * {@code IncrementalBlockReportManager#waitTillNextIBR} past its recorded
     * count held the manager's monitor through its hold, and the DataXceiver
     * whose block notify the order waited for blocked on that monitor
     * (hdfs-adhoc-19, -39).
     */
    static boolean timedOut(Wake wake) {
        if (wake == null) return true;
        mute();
        try {
            takeTurnWake(TURN.get());
            synchronized (LOCK) {
                loadOrderLocked();
                if (!holds) {
                    appendLocked(wake.event);
                    return true;
                }
                Thread self = Thread.currentThread();
                if (!admitNowLocked(wake.event, self)) return false;
                doneWaitingLocked(self);
                HELD.remove(self);
                LET_GO.remove(self);
                return true;
            }
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
     * (IDENTITY §8) and would stall the replay.
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

    // ---- a turn's WAKE ---------------------------------------------------

    /**
     * The WAKE of one turn begun ({@code RuntimeTraceContext#beginTick}),
     * computed at its begin and written before its first event, in both
     * passes: a turn that makes no event holds no slot.  A loop whose turns
     * do nothing (hdfs-adhoc-16: a DataNode actor whose heartbeats a test
     * disabled never waits) recorded 0.89M turns, 1.78M slots, its replay
     * 47k.  In a replay that first event first takes the WAKE's slot, held as
     * a tick's WAKE is.
     */
    static final class TurnWake {
        private final Pending event;
        private final long hop;
        private final TurnWake outer;
        private boolean written;
        private boolean vacant;

        private TurnWake(Pending event, long hop, TurnWake outer) {
            this.event = event;
            this.hop = hop;
            this.outer = outer;
        }

        String site() {
            return event.site;
        }
    }

    /** Per thread, the innermost turn begun ({@link TurnWake}). */
    private static final ThreadLocal<TurnWake> TURN =
            new ThreadLocal<TurnWake>();

    /**
     * A turn of lineage hop {@code hop} begins: its WAKE waits for the
     * turn's first event.  Its thread is seen away from the frontier, so a
     * loop spinning through empty turns never defers a stall.  Null outside
     * the window or any attributable context.
     */
    static TurnWake turnBegun(String site, long hop) {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            String stable = JvmNames.stable(Text.safe(site));
            Stance stance = standing();
            if (stable.isEmpty() || stance == null) return null;
            TurnWake turn = new TurnWake(new Pending(ScheduleEvent.Kind.WAKE,
                    stance.context, stable, stance.region, ""), hop,
                    TURN.get());
            TURN.set(turn);
            synchronized (LOCK) {
                long self = Thread.currentThread().getId();
                if (firstBlocking < order.size()
                        && !RELEASED.contains(self)) {
                    ELSEWHERE.add(self);
                }
            }
            return turn;
        } finally {
            unmute();
        }
    }

    /** Whether this thread's innermost turn has written its WAKE (or no
     *  turn stands). */
    private static boolean turnWritten() {
        TurnWake turn = TURN.get();
        return turn == null || turn.written;
    }

    /** Writes {@code turn}'s WAKE, the turns it began inside first, unless
     *  written: as the turn's first event is admitted, in both passes.  The
     *  turn's k is named by it ({@code Lineage#name}). */
    private static void takeTurnWake(TurnWake turn) {
        if (turn == null || turn.written) return;
        turn.written = true;
        takeTurnWake(turn.outer);
        VACANT.remove();
        admit(turn.event);
        turn.vacant = vacated();
        VACANT.remove();
        Lineage.name(turn.hop);
    }

    /** Whether {@code turn} is vacant ({@link #vacated}); asking writes its
     *  WAKE. */
    static boolean vacant(TurnWake turn) {
        if (turn == null) return false;
        mute();
        try {
            takeTurnWake(turn);
        } finally {
            unmute();
        }
        return turn.vacant;
    }

    /** {@code turn} ends: whether its WAKE was written, so its END is. */
    static boolean turnEnded(TurnWake turn) {
        if (turn == null) return false;
        if (TURN.get() == turn) {
            if (turn.outer == null) TURN.remove();
            else TURN.set(turn.outer);
        }
        return turn.written;
    }

    private static void appendLocked(Pending pending) {
        Integer made = COUNTS.get(pending.key);
        int k = made == null ? 0 : made;
        COUNTS.put(pending.key, k + 1);
        if (pending.kind == ScheduleEvent.Kind.SEND
                && !pending.endpoint.isEmpty()) {
            ContextShape.Stance stance =
                    ContextShape.Stance.ofSend(pending.context);
            if (stance != null) {
                synchronized (SENDERS) {
                    SENDERS.put(pending.endpoint, stance);
                }
            }
        }
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
     * Where each message of this run was sent from, by its producer
     * endpoint: its SEND's stance, the run's own counterpart of the
     * recording's ({@code causynth.RecordedMessages}), so this run's contexts
     * are shaped by the rule PLAN shaped the recording's by ({@link
     * #shape}).  Bounded as {@link Interactions} is: an evicted sender is
     * unknown.  Its own monitor, a leaf: {@code ConcolicTaskPlan} asks under
     * its own.
     */
    private static final Interactions.Bounded<ContextShape.Stance> SENDERS =
            Interactions.bounded();

    /** The shape of {@code context} over this run's senders so far. */
    static List<String> shape(CausalContext context) {
        synchronized (SENDERS) {
            return ContextShape.of(context, SENDERS::get);
        }
    }

    /**
     * Marks where one occurrence opened: not an event, but the cut of a
     * prefix that focuses it.
     */
    static void mark(String occurrenceId) {
        String id = Text.safe(occurrenceId);
        if (id.isEmpty() || !RecordingWindow.opened()) return;
        synchronized (LOCK) {
            if (!MARKED.add(id)) return;
            writeLocked(RowCodec.writeScheduleMark(id, seq));
        }
    }

    /**
     * States which invocation of a parameterized workload test this run is
     * ({@link ScheduleEvent#INVOCATION}), before its window: a schedule
     * holds the order of one invocation, and a replay of another would take
     * its slots for what they are not.  A replay held to a run that states
     * another is refused by name: the test's argument factory listed its
     * arguments in another order in the two runs.
     */
    static void invocation(String stated) {
        // A recording is handed no order: nothing to compare.
        for (Path file : Arrays.asList(prefixFile(), suffixFile())) {
            JsonObject held = held(file);
            String ran = held == null || !held.has("of") ? null
                    : held.get("of").getAsString();
            if (ran != null && !ran.equals(stated)) {
                throw new IllegalStateException("this replay runs invocation "
                        + stated + " of the workload's parameterized test,"
                        + " the run it follows (" + file + ") ran " + ran
                        + ": its argument source listed its arguments in"
                        + " another order");
            }
        }
        synchronized (LOCK) {
            writeLocked(RowCodec.writeScheduleInvocation(stated));
        }
    }

    /** The invocation an order file states, or null. */
    private static JsonObject held(Path file) {
        if (file == null || !file.toFile().isFile()) return null;
        try {
            return SessionReader.readScheduleInvocation(file);
        } catch (IOException unreadable) {
            // Its schedule names an unreadable order once it loads it.
            return null;
        }
    }

    /**
     * Marks this run cut at its witness ({@link ScheduleEvent#WITNESS}):
     * what it makes after the declared occurrence observed the fatal is not
     * its question, and the run ends there.
     */
    static void witnessed() {
        if (!RecordingWindow.opened()) return;
        synchronized (LOCK) {
            writeLocked(RowCodec.writeScheduleMark(ScheduleEvent.WITNESS,
                    seq));
        }
    }

    /**
     * The event context: node, causal context and {@link Identity#handoffs},
     * so a key's k never counts two threads interleaved.
     */
    static String contextOf(CausalContext context) {
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
                    EngineConsole.println("Causynth could not write the "
                            + "schedule to " + file + ": " + unwritable);
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
            while (!admitNowLocked(event, self)) {
                LOCK.wait(Math.max(1L, Math.min(timeoutMillis(), 1000L)));
            }
        } catch (InterruptedException interrupted) {
            // The workload's interrupt is its own; the event still takes
            // its slot.
            Thread.currentThread().interrupt();
            admittedLocked(event, slotOf(event));
        } finally {
            doneWaitingLocked(self);
            HELD.remove(self);
            LET_GO.remove(self);
        }
    }

    /**
     * One ask of THE rule for {@code event}: admitted and written (true), or
     * not yet (false), {@code self} kept waiting at its position for the
     * watchdog; runs the watchdog.
     */
    private static boolean admitNowLocked(Pending event, Thread self) {
        while (true) {
            int slot = slotOf(event);
            int at = waitsAtLocked(event, slot);
            if (at == GO) {
                if (slot < 0 && event.kind == ScheduleEvent.Kind.WAKE
                        && LET_GO.contains(self)) {
                    VACANT.set(Boolean.TRUE);
                }
                admittedLocked(event, slot);
                return true;
            }
            waitLocked(self, at);
            if (!passedLocked(event, at) && !watchdogLocked()) return false;
        }
    }

    /** {@code self} waits at {@code at}; its arrival is kept while it
     *  waits on. */
    private static void waitLocked(Thread self, int at) {
        if (WAITERS.put(self, at) == null) {
            ARRIVED.put(self, System.currentTimeMillis());
        }
    }

    /** {@code self} waits no more; true when it did. */
    private static boolean doneWaitingLocked(Thread self) {
        ARRIVED.remove(self);
        return WAITERS.remove(self) != null;
    }

    /**
     * Writes an event the order admitted, into {@code slot} or free (-1); a
     * WAKE marks where its loop's next poll past the count may go from
     * ({@link #POLLED}).  It is seen first ({@link #seenLocked}): taking the
     * frontier's slot starts what it saw over.
     */
    private static void admittedLocked(Pending event, int slot) {
        long before = moves;
        seenLocked(event, slot);
        if (slot >= 0) {
            takeLocked(slot);
        } else {
            ranFree++;
        }
        appendLocked(event);
        if (event.kind == ScheduleEvent.Kind.WAKE) {
            POLLED.put(event.key, before);
        }
        Thread self = Thread.currentThread();
        Made made = MADE.get(self);
        if (made == null || !made.context.equals(event.context)) {
            made = new Made(event.context);
            MADE.put(self, made);
        }
        made.sites.add(event.kind + " " + event.site);
    }

    /** What a thread made in the context of its last admitted event, since
     *  it entered it: the sites a waiter no occurrence names passes
     *  ({@link #passedLocked}). */
    private static final class Made {
        private final String context;
        private final Set<String> sites = new HashSet<String>();

        private Made(String context) {
            this.context = context;
        }
    }

    private static final Map<Thread, Made> MADE =
            new java.util.WeakHashMap<Thread, Made>();

    /**
     * What an admitted event shows of its thread.  In the frontier's own
     * context or occurrence -- where {@link #slotOf} and {@link
     * #passedLocked} place a thread's own events -- it is the frontier's
     * owner's: at work (a retried call's extra sends, its turn's next step,
     * a WAKE taking its slot, a loop polling the clock toward it), except a
     * poll past its recorded count that went only because the order moved
     * or the watchdog let it go, which waits on others' work; never
     * elsewhere.  Run free or into a slot past the frontier anywhere else,
     * its thread runs on {@link #ELSEWHERE}, unless the watchdog released it
     * since the frontier moved.
     */
    private static void seenLocked(Pending event, int slot) {
        if (firstBlocking >= order.size()) return;
        ScheduleEvent frontier = order.get(firstBlocking);
        long self = Thread.currentThread().getId();
        if (event.context.equals(frontier.context())
                || (!event.occurrence.isEmpty()
                && event.occurrence.equals(frontier.occurrence()))) {
            ownerAtWork |= event.kind != ScheduleEvent.Kind.WAKE || slot >= 0
                    || clockLoopLocked(event);
        } else if ((slot < 0 || slot > firstBlocking)
                && !RELEASED.contains(self)) {
            ELSEWHERE.add(self);
        }
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
     * or {@link #GO}.  An INTERRUPT is never held ({@link #heldKind}).  A
     * WAKE no slot holds is
     * held while the line stands ({@link #line}: the prefix, or the whole
     * order cut at its witness), and only then ({@link #HELD}):
     *
     * <ul>
     *   <li>one the recording never made waits AT THE LINE;</li>
     *   <li>one PAST ITS RECORDED COUNT is a loop polling longer than
     *       recorded, for what another context brings.  It waits until its
     *       context's next slot is due -- only its next turn makes that
     *       slot's event -- and then polls once per move of the order since
     *       its previous WAKE ({@link #POLLED}): a poll between two moves
     *       would read what the last one read.  A loop that reads a CLOCK
     *       root ({@link ClockLoops}) waits for time only the clock brings,
     *       and goes as soon as its slot is due.  With no slot of its
     *       context left, it waits at the line.</li>
     * </ul>
     *
     * The watchdog lets a held wait go when the run idles.  Released, a
     * timed wait still waits out its own deadline ({@link TimedWaits}).
     */
    private static int waitsAtLocked(Pending event, int slot) {
        Thread self = Thread.currentThread();
        HELD.remove(self);
        if (slot >= 0) {
            return !heldKind(slot) || dueLocked(slot) ? GO : slot;
        }
        if (event.kind != ScheduleEvent.Kind.WAKE || !lineStandsLocked()) {
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
        return next >= 0 ? next : AT_THE_LINE;
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

    /**
     * Whether a slot holds its event: before the cut, or a WAKE; never an
     * INTERRUPT.  Whether an interrupt is observed at all, and in which
     * context, is the state the interrupted thread stood in when another
     * thread's call came: a Hadoop IPC sender idle between two calls stands
     * in its last call's claim, so its INTERRUPT at a client's stop names
     * whichever call went last (hdfs-adhoc-03's seed replay held its order
     * at two such slots, 17 s each).  The interrupter's own events hold the
     * order; nothing waits for the INTERRUPT.
     */
    private static boolean heldKind(int slot) {
        ScheduleEvent.Kind kind = order.get(slot).kind();
        return kind != ScheduleEvent.Kind.INTERRUPT
                && (slot < cut || kind == ScheduleEvent.Kind.WAKE);
    }

    /**
     * Whether an open slot is in a later event's way: neither a WAKE nor an
     * INTERRUPT ({@link #firstBlocking}).
     */
    private static boolean blocking(int slot) {
        ScheduleEvent.Kind kind = order.get(slot).kind();
        return kind != ScheduleEvent.Kind.WAKE
                && kind != ScheduleEvent.Kind.INTERRUPT;
    }

    /** Whether every slot before {@code slot} is settled or an open WAKE. */
    private static boolean dueLocked(int slot) {
        return firstBlocking >= slot;
    }

    /** Whether the line stands: an open non-WAKE slot before it. */
    private static boolean lineStandsLocked() {
        return holds && firstBlocking < line;
    }

    private static void takeLocked(int slot) {
        ScheduleEvent event = order.get(slot);
        if (PASSED_SLOTS.remove(slot)) {
            stateLocked("schedule-passed-late#" + slot, event.render()
                    + " came after a later event of its context passed it"
                    + " (schedule-passed): it takes its given-up slot "
                    + slot);
        }
        markLocked(slot, TAKEN);
        taken++;
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
     *
     * <p>A waiter no occurrence names passes the earlier slots of its own
     * exact context, no occurrence naming them either, at any site it made
     * since it last entered that context ({@link Made}: every kind and site
     * of its events there, not only a loop's) -- so the rest of a loop it
     * left is passed (a test polling with a wall-clock sleep made fewer RPCs
     * than the recording did: hdfs-adhoc-44, TestFileTruncate's
     * checkBlockRecovery, 171 recorded, 8 replayed).  Threads an unwoven
     * starter started share their creator's context, so such a give-up is
     * named, counted per context; given up, not dead, a slot is still taken
     * if its event comes, and that late take is named too.</p>
     */
    private static boolean passedLocked(Pending event, int at) {
        boolean byContext = event.occurrence.isEmpty();
        List<Integer> own = byContext ? BY_CONTEXT.get(event.context)
                : BY_OCCURRENCE.get(event.occurrence);
        Made made = byContext ? MADE.get(Thread.currentThread()) : null;
        if (own == null || byContext && (made == null
                || !made.context.equals(event.context))) {
            return false;
        }
        int count = 0;
        int first = -1;
        for (int slot : own) {
            if (slot >= at) break;
            ScheduleEvent passedOver = order.get(slot);
            if (state[slot] != OPEN
                    || passedOver.kind() == ScheduleEvent.Kind.WAKE
                    || !event.context.equals(passedOver.context())
                    || byContext && (!passedOver.occurrence().isEmpty()
                    || !made.sites.contains(passedOver.kind() + " "
                            + passedOver.site()))) {
                continue;
            }
            markLocked(slot, GIVEN_UP);
            if (byContext) PASSED_SLOTS.add(slot);
            if (first < 0) first = slot;
            count++;
        }
        if (count == 0) return false;
        passed += count;
        if (byContext) {
            int times = PASSED_BY_CONTEXT.merge(event.context, 1,
                    Integer::sum);
            stateLocked("schedule-passed#" + first, count + " slot(s) of"
                    + " the order from " + first + " on (the first "
                    + order.get(first).render() + ") were passed by "
                    + event.render() + ", the next event of their context,"
                    + " which no occurrence names (" + times + " time(s) in"
                    + " this context): they are given up, and each still"
                    + " takes its slot if it comes");
        }
        settleLocked();
        return true;
    }

    /** The slots a waiter no occurrence names passed, while untaken: a
     *  late take of one is named ({@link #takeLocked}). */
    private static final Set<Integer> PASSED_SLOTS = new HashSet<Integer>();

    /** Per context, how often a waiter no occurrence names passed its
     *  earlier slots ({@link #passedLocked}). */
    private static final Map<String, Integer> PASSED_BY_CONTEXT =
            new HashMap<String, Integer>();

    /**
     * Something was settled -- the order moved: the first open slot, the
     * frontier, and whether any holds.
     */
    private static void settleLocked() {
        moves++;
        while (firstOpen < state.length && state[firstOpen] != OPEN) {
            firstOpen++;
        }
        int frontier = firstBlocking;
        firstBlocking = Math.max(firstBlocking, firstOpen);
        while (firstBlocking < state.length
                && (state[firstBlocking] != OPEN
                || !blocking(firstBlocking))) {
            firstBlocking++;
        }
        if (firstBlocking > frontier) frontierMovedLocked();
        holds = openHeld > 0 || firstBlocking < line;
        LOCK.notifyAll();
    }

    /** The frontier moved: every waiter's stall starts over, and what was
     *  seen of the old frontier's owner is forgotten. */
    private static void frontierMovedLocked() {
        lastProgress = System.currentTimeMillis();
        letGoSinceProgress = false;
        RELEASED.clear();
        ELSEWHERE.clear();
        ownerAtWork = false;
    }

    /**
     * Where the stall runs from: the frontier's last move, or its earliest
     * current waiter's arrival when that came later -- the frontier owes
     * nothing to a wait that has not begun.
     */
    private static long stallSinceLocked() {
        long earliest = Long.MAX_VALUE;
        for (long arrived : ARRIVED.values()) {
            earliest = Math.min(earliest, arrived);
        }
        return Math.max(lastProgress, earliest);
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
     * waits go.  A stall is the order's frontier standing a timeout with no
     * thread computing toward it ({@link #computingLocked}), or {@link
     * #CEILING} timeouts whatever threads do; both are measured from {@link
     * #stallSinceLocked}, which neither a let-go nor a slot taken past the
     * frontier moves, and the stall's CPU is looked at from its start.  Its
     * first answer lets the waits held without a slot go; a grace later, the
     * slots before the earliest waiter are given up.  With only polls past
     * their recorded count waiting, it lets them go again, a grace apart.
     */
    private static boolean watchdogLocked() {
        if (WAITERS.isEmpty()) return false;
        long now = System.currentTimeMillis();
        long timeout = timeoutMillis();
        long since = stallSinceLocked();
        if (since != stallSince) {
            // A new stall: not yet looked at.  Its CPU counts from here, or
            // from a look at most CPU_SAMPLE_MS older.
            stallSince = since;
            computing = true;
            if (now - cpuSampledAt >= CPU_SAMPLE_MS) lookLocked(now, false);
        }
        long stood = now - since;
        if (stood < timeout || now - letGoAt < LET_GO_GRACE_MS) return false;
        if (stood < CEILING * timeout && computingLocked(now)) return false;
        // A poll held past its recorded count stands at its context's due
        // slot and waits for no slot's event, so it bounds no give-up (it
        // would shadow the stalled slot); a wait AT_THE_LINE bounds one at
        // the line.
        int earliest = Integer.MAX_VALUE;
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            int slot = waiter.getValue();
            if (slot == AT_THE_LINE) {
                earliest = Math.min(earliest, line);
            } else if (!HELD.containsKey(waiter.getKey())) {
                earliest = Math.min(earliest, slot);
            }
        }
        if (!HELD.isEmpty() && (!letGoSinceProgress
                || earliest == Integer.MAX_VALUE)) {
            letGoHeldLocked(stood, now);
            return true;
        }
        if (earliest == Integer.MAX_VALUE) return false;
        boolean atTheLine = WAITERS.containsValue(AT_THE_LINE)
                && earliest == line;
        stalls++;
        if (!atTheLine && earliest >= cut && restStalls >= REST_STALLS) {
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
                    + earliest + " waited " + stood + " ms): its " + open
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
        if (!atTheLine && earliest >= cut) restStalls++;
        stateLocked((first < cut ? "schedule#" : "schedule-rest#") + first,
                count + " slot(s) of the order from " + first + " on (the"
                        + " first " + order.get(first).render() + ") did not"
                        + " happen in the " + stood + " ms the frontier"
                        + " stood at slot " + firstBlocking + ", while "
                        + waitingAtLocked(earliest)
                        + ": they are given up, and each still takes its"
                        + " slot if it comes");
        settleLocked();
        return true;
    }

    /**
     * Lets every wait held without a slot go.  With the frontier stalled, a
     * wait the recording never made -- a pool thread's, or a daemon's whose
     * own turn's END is the frontier -- or a loop polling past its recorded
     * count may be what the frontier's event is behind, and giving the
     * order up settles nothing that holds it.  Its event runs free.  The
     * stall stands: the waits let go have {@link #LET_GO_GRACE_MS}, not
     * another timeout, to make progress.
     */
    private static void letGoHeldLocked(long stood, long now) {
        String held = heldLocked(HELD.keySet().iterator().next());
        int count = HELD.size();
        LET_GO.addAll(HELD.keySet());
        for (Thread thread : HELD.keySet()) RELEASED.add(thread.getId());
        letGo += count;
        letGoSinceProgress = true;
        letGoAt = now;
        stateLocked("schedule-let-go#" + firstBlocking, count + " wait(s)"
                + " held without a slot (" + held + ") for " + stood + " ms"
                + " while " + (firstBlocking < order.size()
                        ? order.get(firstBlocking).render() : "nothing")
                + " at slot " + firstBlocking + " did not happen: they are"
                + " let go before any slot is given up");
        LOCK.notifyAll();
    }

    /** What waits at {@code earliest}, as it names itself. */
    private static String waitingAtLocked(int earliest) {
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            if (earliest == line && waiter.getValue() == AT_THE_LINE) {
                return heldLocked(waiter.getKey()) + " waited at the "
                        + (line == cut ? "cut" : "order's end");
            }
        }
        return order.get(earliest).render() + " waited at slot " + earliest;
    }

    /** A held wait, as it names itself. */
    private static String heldLocked(Thread thread) {
        Pending held = HELD.get(thread);
        if (held == null) return "a wait the order does not name";
        return SLOTS.containsKey(held.key)
                ? held.render() + " past its recorded count"
                : "the unrecorded " + held.render();
    }

    /**
     * Whether something is computing toward the frontier, as the last look
     * saw it; a new look once {@link #CPU_SAMPLE_MS} passed since that one.
     * The slow concolic VM computing is progress, not a stall.  A stall is
     * deferred, never missed, and {@link #CEILING} bounds the deferral.
     */
    private static boolean computingLocked(long now) {
        if (now - cpuSampledAt >= CPU_SAMPLE_MS) lookLocked(now, true);
        return computing;
    }

    /**
     * One look at the threads' CPU and the collectors' time since the last
     * look ({@code measure}), which then starts the next; a look that does
     * not measure starts a stall's ({@link #watchdogLocked}).  Something
     * computes toward the frontier when its owner was seen at work in its
     * context ({@link #ownerAtWork}), whatever CPU share it got; or when one
     * thread that may owe it used, with the collectors, half the look's
     * span.  Which thread owes the frontier's event cannot be seen between
     * two of its events (a pool thread reused, a client call computing
     * toward its first send, a parent toward a child's first event), so
     * every thread may but three.  One waiting for a turn computes nothing.
     * The engine's own ({@link #ENGINE_THREAD}: the result publication, the
     * trace parse) owes the order nothing.  One seen {@link #ELSEWHERE} was
     * making its own events, not the frontier's (a test's polling loop and
     * the RPCs it drives).  An unseen owner is one thread, so one thread's
     * CPU counts, not a sum: the traffic a free-running loop drives through
     * threads that make no event (an IPC reader, a connection's receiver)
     * adds up to no one computing.  A collection stops the owner too, so its
     * time counts as the owner's.
     */
    private static void lookLocked(long now, boolean measure) {
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        Set<Long> waiting = new HashSet<Long>();
        for (Thread thread : WAITERS.keySet()) waiting.add(thread.getId());
        Map<Long, Long> seen = new HashMap<Long, Long>();
        long most = 0L;
        for (ThreadInfo info
                : threads.getThreadInfo(threads.getAllThreadIds())) {
            if (info == null) continue;
            long id = info.getThreadId();
            long cpu = threads.getThreadCpuTime(id);
            if (cpu < 0L) continue;
            seen.put(id, cpu);
            if (waiting.contains(id) || ELSEWHERE.contains(id)
                    || info.getThreadName().startsWith(ENGINE_THREAD)) {
                continue;
            }
            Long before = CPU_SEEN.get(id);
            most = Math.max(most, cpu - (before == null ? 0L : before));
        }
        long collected = collectedMillis();
        long stopped = TimeUnit.MILLISECONDS.toNanos(collected - collectedSeen);
        computing = !measure || ownerAtWork || 2L * (most + stopped)
                >= TimeUnit.MILLISECONDS.toNanos(now - cpuSampledAt);
        CPU_SEEN.clear();
        CPU_SEEN.putAll(seen);
        collectedSeen = collected;
        cpuSampledAt = now;
        ELSEWHERE.clear();
        ownerAtWork = false;
    }

    /** The collectors' summed time so far, in ms. */
    private static long collectedMillis() {
        long millis = 0L;
        for (GarbageCollectorMXBean collector
                : ManagementFactory.getGarbageCollectorMXBeans()) {
            millis += Math.max(0L, collector.getCollectionTime());
        }
        return millis;
    }

    /** One SCHEDULE_DIVERGED statement, on the session and on stderr. */
    private static void stateLocked(String where, String detail) {
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    where, detail);
        } catch (Throwable unpublished) {
        }
        EngineConsole.println("Causynth schedule: " + detail);
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

    static long timeoutMillis() {
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
                            : SessionReader.readSchedule(restFile),
                    restFile != null && SessionReader.readScheduleMarks(
                            restFile).containsKey(ScheduleEvent.WITNESS));
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
                EngineConsole.println("Causynth schedule: " + progress());
            }
        }, "causynth-schedule-progress"));
    }

    /** Holds the run to {@code events}, cut, then {@code after}, which a
     *  run cut at its witness ends at. */
    private static void installLocked(List<ScheduleEvent> events,
                                      List<ScheduleEvent> after,
                                      boolean atWitness) {
        List<ScheduleEvent> all = new ArrayList<ScheduleEvent>(events);
        all.addAll(after);
        order = all;
        cut = events.size();
        line = atWitness ? all.size() : cut;
        state = new byte[all.size()];
        SLOTS.clear();
        BY_OCCURRENCE.clear();
        BY_CONTEXT.clear();
        TAKEN_WAKES.clear();
        WAITERS.clear();
        ARRIVED.clear();
        HELD.clear();
        LET_GO.clear();
        POLLED.clear();
        PASSED_BY_CONTEXT.clear();
        PASSED_SLOTS.clear();
        MADE.clear();
        moves = 0L;
        letGoAt = 0L;
        stallSince = -1L;
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
        frontierMovedLocked();
        settleLocked();
    }

    /** Writes one mark row into this run's schedule, before the window as
     *  inside it. */
    static void writeMark(JsonObject row) {
        synchronized (LOCK) {
            writeLocked(row);
        }
    }

    /** The startup marks of the order this replay is handed, prefix then
     *  rest; none in a recording ({@link StartupOrder}). */
    static List<JsonObject> startupMarks() {
        List<JsonObject> marks = new ArrayList<JsonObject>();
        for (Path file : Arrays.asList(prefixFile(), suffixFile())) {
            if (file == null || !file.toFile().isFile()) continue;
            try {
                marks.addAll(SessionReader.readScheduleStartup(file));
            } catch (IOException unreadable) {
                // Its schedule names an unreadable order once it loads it.
            }
        }
        return marks;
    }

    /** This thread waits on something no slot holds ({@code StartupOrder}'s
     *  hold): it is away from the frontier, deferring no stall. */
    static void elsewhere() {
        synchronized (LOCK) {
            long self = Thread.currentThread().getId();
            if (firstBlocking < order.size() && !RELEASED.contains(self)) {
                ELSEWHERE.add(self);
            }
        }
    }

    /** A divergence the order states by name ({@code SCHEDULE_DIVERGED}). */
    static void diverged(String where, String detail) {
        stateLocked(where, detail);
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
                    + " passed by their own occurrence or context ("
                    + PASSED_BY_CONTEXT.size() + " context(s) without an"
                    + " occurrence); " + ranFree
                    + " event(s) ran free, " + letGo + " of them let go"
                    + " where no slot held them; " + closedOpen
                    + " open at the window's"
                    + " close";
        }
    }

    static void enforceForTests(List<ScheduleEvent> events) {
        enforceForTests(events, Collections.<ScheduleEvent>emptyList());
    }

    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after) {
        enforceForTests(events, after, false);
    }

    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after,
                                boolean atWitness) {
        synchronized (LOCK) {
            loaded = true;
            installLocked(events, after, atWitness);
        }
    }

    public static void resetForTests() {
        TURN.remove();
        synchronized (LOCK) {
            sink = null;
            PENDING.clear();
            COUNTS.clear();
            MARKED.clear();
            synchronized (SENDERS) {
                SENDERS.clear();
                UNKNOWN_SENDERS.clear();
            }
            seq = 0L;
            loaded = false;
            holds = false;
            order = Collections.emptyList();
            cut = 0;
            line = 0;
            state = new byte[0];
            SLOTS.clear();
            BY_OCCURRENCE.clear();
            BY_CONTEXT.clear();
            TAKEN_WAKES.clear();
            WAITERS.clear();
            ARRIVED.clear();
            HELD.clear();
            LET_GO.clear();
            POLLED.clear();
            PASSED_BY_CONTEXT.clear();
            PASSED_SLOTS.clear();
            MADE.clear();
            ClockLoops.resetForTests();
            moves = 0L;
            letGoSinceProgress = false;
            letGoAt = 0L;
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
            stallSince = -1L;
            CPU_SEEN.clear();
            ELSEWHERE.clear();
            RELEASED.clear();
            ownerAtWork = false;
            collectedSeen = 0L;
            cpuSampledAt = 0L;
            computing = false;
            LOCK.notifyAll();
        }
    }
}
