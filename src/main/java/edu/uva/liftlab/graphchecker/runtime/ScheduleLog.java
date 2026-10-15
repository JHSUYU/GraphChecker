package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RunSpellings;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.StableEventNames;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

/**
 * THE schedule of one run, and the one rule that holds a replay to another
 * run's.
 *
 * <p>RECORDER.  Every START, CLAIM, SEND, WRITE, RECV, WAKE, END and
 * INTERRUPT in the recording window is appended in run order, in BOTH
 * passes, changing nothing the run does.</p>
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
 * its loop reads a CLOCK root ({@link #waitsAtLocked}).  An event of a
 * timed-wait loop's turn ({@code Root:WAKE/<wait>#k}, whose k counts the
 * loop's wakes) held at its slot is held so too: it bounds no give-up, and
 * let go it takes that slot.  A WRITE never
 * passes an earlier held write to its location: one the order lacks, or
 * one whose slot holds nothing (past the cut), waits for it until it is
 * taken or given up.  An order cut at its
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
    /** The rest, beside the prefix in the worker directory. */
    public static final String SUFFIX_FILE = "schedule_suffix.jsonl";

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

    /**
     * The one lock of the order.  Lock order: {@code Confirmation}'s lock,
     * then this one, then {@code FocusedReplay}'s -- a superseded
     * publication's turn is settled under Confirmation's ({@link
     * #turnNotTaken}) -- and nothing taken under this one calls back up that
     * chain: this class never calls Confirmation.
     */
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
    /**
     * Every event key this run made, as progress counts it ({@link
     * #madeKey}), so {@link #newKeys} grows only by what the run had not
     * done before; guarded by {@link #LOCK}.
     */
    private static final Set<String> MADE_KEYS = new HashSet<String>();
    /** Whether this run counts them: only a focused replay's watch asks
     *  ({@link #countNewEvents}); a recording, the seed and CONFIRM pay
     *  nothing. */
    private static volatile boolean counting;
    /** When the last new key was made ({@code System.nanoTime}, 0 before
     *  any) and the longest span between two; guarded by {@link #LOCK}. */
    private static long lastNewNanos;
    private static long longestQuietNanos;

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
    /**
     * Per location a WRITE writes (its site, {@link ScheduleEvent#written}),
     * the slots of the writes there, in order: a write there does not pass
     * an earlier one the order holds ({@link #conflictLocked}).
     */
    private static final Map<String, List<Integer>> BY_LOCATION =
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
     * The waiters the order holds for no slot's event, each with the event
     * it waits to make: a WAKE the recording never made (AT THE CUT), a poll
     * past its recorded count, a read behind a write to its location, or an
     * event of a timed-wait loop's turn at a slot its k may have taken from
     * another turn ({@link #waitsAtLocked}).  Only these can be let go, and
     * none bounds a give-up.  A subset of {@link #WAITERS}.
     */
    private static final Map<Thread, Pending> HELD =
            new HashMap<Thread, Pending>();
    /** Held threads the watchdog let go, until the wait ends. */
    private static final Set<Thread> LET_GO = new HashSet<Thread>();
    /**
     * The waiters whose WRITE waits for an earlier held write to its
     * location ({@link #conflictLocked}), at the slot after it, so the give-up
     * that settles it lets them go.  A subset of {@link #WAITERS}; never let
     * go, and never passing their own context's slots there: where they
     * wait is the other write's place, not theirs.
     */
    private static final Set<Thread> CONFLICTED = new HashSet<Thread>();
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

    /**
     * A node's view's stance ({@link ScheduleEvent.Kind#PUBLISH}): its own
     * context, {@code <node>|VIEW}, in no region -- a publication is no
     * work of the callback that made it, whose context is free.
     */
    public static Stance viewStance(String node) {
        return new Stance(trimmed(node) + "|"
                + ContextShape.Stance.VIEW_STANCE, "");
    }

    /**
     * Whether {@code kind} at {@code site}, standing at {@code at}, would be
     * admitted now: no order held, no slot of it, or its slot due.  Asked
     * without waiting, so the thread that cannot wait (a watch callback
     * holding its collection's refresh lock) hands the event to one that
     * can ({@code Confirmation#publishing}).
     */
    public static boolean dueNow(ScheduleEvent.Kind kind, String site,
                                 Stance at) {
        if (kind == null || !RecordingWindow.opened()) return true;
        mute();
        try {
            synchronized (LOCK) {
                loadOrderLocked();
                if (!holds) return true;
                Pending event = pending(kind, site, "", at);
                if (event == null) return true;
                int slot = slotOf(event);
                return slot < 0 || !heldKind(slot) || dueLocked(slot);
            }
        } finally {
            unmute();
        }
    }

    /**
     * A node's publication of {@code site}'s version of a view reached its
     * door (a notification's, before its turn is asked, or the system's own
     * at once): the node's open PUBLISH slots of that view at an older
     * version, but those still on their way ({@code coming}: deferred on
     * the node's publisher; or in flight, begun and being published, {@link
     * #publicationBegins}), will never come -- a notification fetches the
     * newest version, so a callback that fetched this one never publishes
     * an older one, and a node never publishes an older version after a
     * newer -- so each is given up now, by name, not by the watchdog at the
     * frontier's cost.  Now, not once this version is in force: its own
     * turn is after theirs, so it would wait for them (review R3: a
     * callback that fetched v9 and never published v8).  The system's own
     * publication at once ({@code atOnce}) settles this version's turn too:
     * the view is at that version already, so what the turn holds back
     * reads it as recorded, and a notification of it -- none may come, the
     * fetch that made it having set the watch the next one answers -- re-
     * points nothing (Z3Q's seed: a command's refresh published v4 on the
     * Overseer's node, and the recorded callback's turn stood 15 s; Z3R's
     * tra seed: AliasesManager's notifications of aliases.json v1 and v2
     * came after the node's own publication and took their given-up
     * slots).  A given-up slot is still taken if its event comes late.
     */
    public static void publicationReached(String node, String site,
                                          Set<Long> coming, boolean atOnce) {
        settleTurns(node, site, atOnce ? Settle.UP_TO : Settle.OLDER, coming,
                atOnce ? "its node put " + site + " in force at once (the"
                        + " system's own publication), so what this turn"
                        + " holds back reads that version already"
                        : "its node's publication of " + site + " reached its"
                        + " door, so this older version, not on its way, will"
                        + " never be published");
    }

    /** Which open PUBLISH slots of a view {@link #settleTurns} settles. */
    private enum Settle {
        /** Below the version. */
        OLDER,
        /** At or below it. */
        UP_TO,
        /** At it. */
        AT
    }

    /**
     * A PUBLISH turn its publication will not take ({@code why}: superseded
     * before it applied, or put in force at once in a pairing world), given
     * up now by name.
     */
    public static void turnNotTaken(String node, String site, String why) {
        settleTurns(node, site, Settle.AT, Collections.<Long>emptySet(), why);
    }

    /** {@link #publicationReached} and {@link #turnNotTaken}: the node's
     *  open PUBLISH slots of the view {@code which} names against {@code
     *  site}'s version, but those {@code coming}. */
    private static void settleTurns(String node, String site, Settle which,
                                    Set<Long> coming, String why) {
        if (node == null || site == null || !RecordingWindow.opened()) return;
        int at = site.lastIndexOf('@');
        if (at < 0) return;
        String view = site.substring(0, at + 1);
        long version;
        try {
            version = Long.parseLong(site.substring(at + 1));
        } catch (NumberFormatException none) {
            return;
        }
        mute();
        try {
            synchronized (LOCK) {
                loadOrderLocked();
                List<Integer> slots = BY_CONTEXT.get(trimmed(node) + "|"
                        + ContextShape.Stance.VIEW_STANCE);
                if (slots == null) return;
                boolean moved = false;
                for (int slot : slots) {
                    ScheduleEvent event = order.get(slot);
                    if (state[slot] != OPEN
                            || event.kind() != ScheduleEvent.Kind.PUBLISH
                            || !event.site().startsWith(view)) {
                        continue;
                    }
                    long held;
                    try {
                        held = Long.parseLong(event.site().substring(
                                view.length()));
                    } catch (NumberFormatException none) {
                        continue;
                    }
                    boolean settles = which == Settle.AT ? held == version
                            : held < version || which == Settle.UP_TO
                            && held == version;
                    // One in flight is on its way too: begun, its caller
                    // still publishing it (review SA: v9's door gave v8's
                    // slot up while v8's callback had not yet constructed
                    // its state, so what v8 holds back read v7).
                    if (!settles || coming.contains(held)
                            || IN_FLIGHT.containsKey(slot)) {
                        continue;
                    }
                    giveUpLocked(slot);
                    stateLocked("schedule-publish-settled#" + slot,
                            event.render() + " given up: " + why);
                    moved = true;
                }
                if (moved) settleLocked();
            }
        } finally {
            unmute();
        }
    }

    /**
     * Which of a node's views' head publications, by their PUBLISH {@code
     * sites}, are due now ({@link #dueNow}); the node's publisher asks, never
     * blocking on a turn (review B2), and waits on its own primitive between
     * asks.  For the rest it is a WAITER, as a held timed wait is ({@link
     * #turn(Wake)}): at the earliest of their slots, so the watchdog runs on
     * its asks and its give-up stops at that slot -- a publication whose
     * predecessor never comes gives way by name, and no other waiter's
     * give-up runs past it (review R1).  It waits no more once an ask finds
     * none not due, or {@link #waitsNoMore}.
     */
    public static Set<String> duePublications(String node,
                                              Collection<String> sites) {
        Set<String> due = new HashSet<String>();
        if (!RecordingWindow.opened()) {
            due.addAll(sites);
            return due;
        }
        mute();
        try {
            Stance at = viewStance(node);
            Thread self = Thread.currentThread();
            synchronized (LOCK) {
                loadOrderLocked();
                while (true) {
                    due.clear();
                    int earliest = Integer.MAX_VALUE;
                    for (String site : sites) {
                        Pending event = holds ? pending(
                                ScheduleEvent.Kind.PUBLISH, site, "", at)
                                : null;
                        int slot = event == null ? -1 : slotOf(event);
                        if (slot < 0 || !heldKind(slot) || dueLocked(slot)) {
                            due.add(site);
                        } else {
                            earliest = Math.min(earliest, slot);
                        }
                    }
                    if (earliest == Integer.MAX_VALUE) {
                        if (doneWaitingLocked(self)) LOCK.notifyAll();
                        return due;
                    }
                    waitLocked(self, earliest);
                    if (!due.isEmpty() || !watchdogLocked()) return due;
                }
            }
        } finally {
            unmute();
        }
    }

    /** This thread waits for no turn any more: a wait that ended on its own
     *  primitive ({@link #withdraw}), or a publisher with no publication
     *  left to wait for ({@link #duePublications}). */
    public static void waitsNoMore() {
        synchronized (LOCK) {
            Thread self = Thread.currentThread();
            LET_GO.remove(self);
            HELD.remove(self);
            if (doneWaitingLocked(self)) LOCK.notifyAll();
        }
    }

    /**
     * A PUBLISH whose publication runs, its turn due -- published by the
     * notification's caller or applied by its node's publisher ({@code
     * Confirmation#begin}, {@code #settle}): the
     * turn is taken once the publication is in force ({@link
     * #publicationInForce}), so nothing the order lets go after it reads
     * past it (review S1; SGF3 snapshot-no-active) -- unless the apply
     * waits, past {@link #PUBLISH_GRACE_MS} at the frontier, on a lock
     * whose owner the order
     * holds: the system's own locks it takes (Solr's collection refresh
     * lock, the reader's update lock) may be held by a thread waiting for
     * its turn behind this slot (a forced refresh's READ behind the WRITE
     * behind it), so the watchdog takes the turn on its behalf, named, and
     * the order moves (review R2, R2a; {@link #inFlightLocked}).
     */
    static final class Publication {
        private final Pending event;
        private final int slot;
        private final Thread publisher;
        private final long began;
        /** The last look at its apply: when, the publisher's CPU (ns, -1
         *  unknown) and the collectors' time (ms) then. */
        private long lookedAt;
        private long cpuLooked;
        private long collectedLooked;
        /** The watchdog took its turn on its behalf (guarded by LOCK). */
        private boolean taken;

        private Publication(Pending event, int slot, Thread publisher,
                            long began) {
            this.event = event;
            this.slot = slot;
            this.publisher = publisher;
            this.began = began;
            this.lookedAt = began;
            this.cpuLooked = cpuOf(publisher);
            this.collectedLooked = collectedMillis();
        }
    }

    /** How long a PUBLISH's apply at the frontier may wait on something,
     *  rather than compute, before its turn is taken for it, in ms. */
    static final long PUBLISH_GRACE_MS = 500L;

    /** The PUBLISH applies in flight, by slot ({@link Publication}). */
    private static final Map<Integer, Publication> IN_FLIGHT =
            new HashMap<Integer, Publication>();

    /**
     * This thread begins {@code site}'s publication on {@code node}, its turn
     * due ({@code Confirmation#begin}): the in-flight
     * publication whose turn {@link #publicationInForce} takes, or null
     * where no slot holds it.
     */
    public static Publication publicationBegins(String node, String site) {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            synchronized (LOCK) {
                loadOrderLocked();
                if (!holds) return null;
                Pending event = pending(ScheduleEvent.Kind.PUBLISH, site, "",
                        viewStance(node));
                int slot = event == null ? -1 : slotOf(event);
                if (slot < 0 || state[slot] != OPEN) return null;
                Publication applying = new Publication(event, slot,
                        Thread.currentThread(), System.currentTimeMillis());
                IN_FLIGHT.put(slot, applying);
                return applying;
            }
        } finally {
            unmute();
        }
    }

    /** {@code site}'s publication on {@code node} is in force: its PUBLISH
     *  turn, unless the watchdog took it for its apply ({@code applying},
     *  {@link #publicationBegins}). */
    public static void publicationInForce(Publication applying, String node,
                                          String site) {
        if (applying != null) {
            mute();
            try {
                synchronized (LOCK) {
                    IN_FLIGHT.remove(applying.slot, applying);
                    if (applying.taken) return;
                }
            } finally {
                unmute();
            }
        }
        observe(ScheduleEvent.Kind.PUBLISH, site, "", viewStance(node));
    }

    /**
     * The watchdog's first look ({@link #watchdogLocked}): a PUBLISH's apply
     * in flight at the frontier.  The thread applying it -- its node's
     * publisher, an engine thread whose CPU no look counts, or the
     * notification's own -- is looked at here: computing, it holds the
     * order as any owner of the frontier at work does (false: nothing else
     * is done), up to {@link #CEILING} timeouts.  Waiting past {@link
     * #PUBLISH_GRACE_MS} -- under half its time on CPU or in the collectors
     * since the last look -- on a lock whose owner, or that owner's own
     * lock's, waits for a turn ({@link #heldByTheOrderLocked}): a cycle
     * through the order, so its turn is taken for it, the event written now
     * and named, and the publication lands when its apply ends (true;
     * review R2).  Waiting on anything else -- a lock a thread the order
     * does not hold owns (a VM-slow thread, a callback decoding the next
     * version), a wait no owner states -- it is as computing: taken early,
     * what comes after it would read the version before it (review R2a).
     * Null where no apply stands there, or past the ceiling, and the
     * watchdog looks on as for any frontier.
     */
    private static Boolean inFlightLocked(long now) {
        Publication applying = IN_FLIGHT.get(firstBlocking);
        if (applying == null || state[applying.slot] != OPEN) return null;
        if (now - applying.lookedAt >= PUBLISH_GRACE_MS) {
            long cpu = cpuOf(applying.publisher);
            long collected = collectedMillis();
            long span = now - applying.lookedAt;
            long used = cpu < 0L || applying.cpuLooked < 0L ? span
                    : TimeUnit.NANOSECONDS.toMillis(cpu - applying.cpuLooked);
            long busy = used + collected - applying.collectedLooked;
            applying.lookedAt = now;
            applying.cpuLooked = cpu;
            applying.collectedLooked = collected;
            String cycle = 2L * busy < span
                    ? heldByTheOrderLocked(applying.publisher) : null;
            if (cycle != null) {
                applying.taken = true;
                IN_FLIGHT.remove(applying.slot);
                takeLocked(applying.slot);
                appendLocked(applying.event);
                stateLocked("schedule-publish-blocked#" + applying.slot,
                        applying.event.render() + " at slot " + applying.slot
                                + ": its apply on "
                                + applying.publisher.getName() + " waited, "
                                + span + " ms of the " + (now - applying.began)
                                + " ms it ran at the frontier, on " + cycle
                                + ", which waits for its turn behind it: its"
                                + " turn is taken now, and the publication"
                                + " lands when the apply ends");
                return Boolean.TRUE;
            }
        }
        return now - applying.began < CEILING * timeoutMillis()
                ? Boolean.FALSE : null;
    }

    /**
     * The lock {@code publisher} waits on as its owner chain names it, when
     * an owner on that chain -- the lock's, or the lock that owner waits
     * on's, a few hops -- is a thread waiting for its turn ({@link
     * #WAITERS}), the applying thread and every node's publisher aside;
     * else null: no lock with an owner, an owner the order does not hold,
     * or a hop through this class's own
     * {@link #LOCK} -- a thread merely entering it waits on the watchdog
     * that holds it, itself a waiter, which is no cycle (review R2b).  A
     * Solr lock the watchdog's own thread owns while it waits for its turn
     * is one: that waiter runs the watchdog on its asks.
     */
    private static String heldByTheOrderLocked(Thread publisher) {
        // A node's publisher waits for a turn between its asks, never under
        // a lock the system takes: no cycle runs through one (a callback in
        // flight waiting on the update lock the publisher holds applying
        // another view's head).
        Set<Long> waiting = new HashSet<Long>();
        for (Thread thread : WAITERS.keySet()) {
            if (!thread.getName().startsWith(
                    Confirmation.PUBLISHER_THREAD)) {
                waiting.add(thread.getId());
            }
        }
        waiting.remove(publisher.getId());
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        int order = System.identityHashCode(LOCK);
        StringBuilder chain = new StringBuilder();
        Set<Long> seen = new HashSet<Long>();
        long id = publisher.getId();
        for (int hop = 0; hop < OWNER_HOPS && seen.add(id); hop++) {
            ThreadInfo info = threads.getThreadInfo(id);
            if (info == null || info.getLockOwnerId() < 0L
                    || info.getLockInfo() == null
                    || info.getLockInfo().getIdentityHashCode() == order) {
                return null;
            }
            chain.append(chain.length() == 0 ? "" : ", which waits on ")
                    .append(info.getLockName()).append(" held by \"")
                    .append(info.getLockOwnerName()).append('"');
            id = info.getLockOwnerId();
            if (waiting.contains(id)) return chain.toString();
        }
        return null;
    }

    /** How far {@link #heldByTheOrderLocked} follows lock owners. */
    private static final int OWNER_HOPS = 8;

    /** A thread's CPU time in ns, or -1 where the JVM states none. */
    private static long cpuOf(Thread thread) {
        try {
            return ManagementFactory.getThreadMXBean().getThreadCpuTime(
                    thread.getId());
        } catch (UnsupportedOperationException none) {
            return -1L;
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
        UNAWAITED.add(trimmed(transport).toUpperCase(java.util.Locale.ROOT));
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
        if (wake != null) waitsNoMore();
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
     * (true).  Not yet (false: the order holds it, or a native
     * reproduction's realized order, {@link #realizedLocked}): the waiter
     * waits a quantum on its own primitive and asks again, so the monitor
     * or lock its wait released stays released until the WAKE is written,
     * as the JVM returns from a wait only then.  Admitted holding it, the WAKE of an
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
                    if (!realizedLocked(wake.event)) return false;
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
        /** A WRITE the order lacks: the held write to its location it waits
         *  for, fixed at its first ask ({@link #conflictLocked}); -1 none,
         *  -2 not asked yet. */
        private int conflict = -2;

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
        String stable = JvmNames.stable(trimmed(site));
        if (stable.isEmpty()) return null;
        Stance stance = at != null ? at : standing();
        if (stance == null) return null;
        return new Pending(kind, stance.context, stable, stance.region,
                trimmed(endpoint));
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
            String stable = JvmNames.stable(trimmed(site));
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
        holdRealizedLocked(pending);
        Integer made = COUNTS.get(pending.key);
        int k = made == null ? 0 : made;
        COUNTS.put(pending.key, k + 1);
        madeRealizedLocked(pending, k);
        if (pending.kind == ScheduleEvent.Kind.SEND
                && !pending.endpoint.isEmpty() && !AWAITED.isEmpty()) {
            names.sent(pending.context, pending.site, pending.endpoint);
        }
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
        if (counting && MADE_KEYS.add(madeKey(pending))) {
            long now = System.nanoTime();
            if (lastNewNanos != 0L) {
                longestQuietNanos = Math.max(longestQuietNanos,
                        now - lastNewNanos);
            }
            lastNewNanos = now;
        }
        ScheduleEvent event = ScheduleEvent.of(seq++, pending.kind,
                pending.context, pending.site, k, pending.occurrence,
                pending.endpoint, Identity.afterLastEvent());
        writeLocked(RowCodec.writeScheduleEvent(event));
    }

    // ---- a native reproduction's realized order --------------------------

    /**
     * A planted run's ORDER rows of events ({@code explore.RealizedOrder}:
     * the order the session CONFIRM saw ran in from the moved roots on),
     * read at the first event: per event, by {@link #eventId}, the rows
     * holding it after others; null until read.
     */
    private static Map<String, List<Ordered>> realized;
    /** The events a realized row waits for. */
    private static final Set<String> AWAITED = new HashSet<String>();
    /** Those of {@link #AWAITED} this run made. */
    private static final Set<String> MADE_AWAITED = new HashSet<String>();
    /** Per awaited event, the rows whose wait for it gave way before it
     *  came: each {@link RecordingPlant#LATE} when it comes. */
    private static final Map<String, List<Ordered>> OVERDUE =
            new HashMap<String, List<Ordered>>();
    /** Per event held, when its hold gives way. */
    private static final Map<String, Long> DUE = new HashMap<String, Long>();
    /** This run's stable event names, which the realized rows state (fed
     *  its SENDs while it holds an order). */
    private static StableEventNames names = new StableEventNames();

    /** One realized ORDER row: its number, and its two events. */
    private static final class Ordered {
        private final int row;
        private final String before;
        private final String after;

        private Ordered(int row, String before, String after) {
            this.row = row;
            this.before = before;
            this.after = after;
        }
    }

    /** One event's identity across runs: kind, context ({@link
     *  StableEventNames} for a realized row), site and k. */
    static String eventId(String kind, String context, String site, int k) {
        return kind + " " + site + " @ " + context + " #" + k;
    }

    private static void loadRealizedLocked() {
        if (realized != null) return;
        realized = new HashMap<String, List<Ordered>>();
        if (RecordingPlant.planting()) {
            readRealizedLocked(Paths.get(RecordingPlant.file()));
        }
    }

    /** Test seam: this run is held to {@code plant}'s realized order. */
    static void realizedForTests(Path plant) {
        synchronized (LOCK) {
            realized = new HashMap<String, List<Ordered>>();
            readRealizedLocked(plant);
        }
    }

    private static void readRealizedLocked(Path plant) {
        try {
            for (JsonObject row : RowCodec.readJsonl(plant)) {
                if (!RecordingPlant.ORDER.equals(JsonFields.optionalString(
                        row, RecordingPlant.KIND))
                        || JsonFields.optionalString(row,
                        RecordingPlant.SCOPE).isEmpty()) {
                    continue;
                }
                String before = eventId(row.getAsJsonObject("before"));
                String after = eventId(row.getAsJsonObject("after"));
                realized.computeIfAbsent(after,
                        key -> new ArrayList<Ordered>()).add(new Ordered(
                        row.get(RecordingPlant.ROW).getAsInt(), before,
                        after));
                AWAITED.add(before);
            }
        } catch (IOException | RuntimeException unreadable) {
            // The plant's other readers name an unreadable plant; held to
            // nothing, every row of it states nothing.
            realized.clear();
            AWAITED.clear();
        }
    }

    private static String eventId(JsonObject event) {
        return eventId(JsonFields.optionalString(event, "kind"),
                JsonFields.optionalString(event, "context"),
                JsonFields.optionalString(event, "site"),
                event.get("k").getAsInt());
    }

    /**
     * THE REALIZED ORDER, held at an event's admission in a native
     * reproduction: the event waits until every event its rows order before
     * it was made ({@link #realizedLocked}).  An interrupt meanwhile is kept
     * pending, as a timed wait keeps one: the event still comes after what
     * the confirmed world made before it, and the interrupt is the
     * workload's (a shutdown interrupting the held thread is how
     * solr-bugs-restore-construction's old RESTORE task ends).  Called under
     * {@link #LOCK}, which the wait releases.
     */
    private static void holdRealizedLocked(Pending pending) {
        boolean interrupted = false;
        try {
            while (!realizedLocked(pending)) {
                try {
                    LOCK.wait(200L);
                } catch (InterruptedException interrupt) {
                    interrupted = true;
                }
            }
        } finally {
            if (interrupted) Thread.currentThread().interrupt();
        }
    }

    /**
     * Whether {@code pending} may be made now under the realized order,
     * asked without blocking: when every event its rows order before it was
     * made (each row APPLIED), or the run no longer holds an order.  A row
     * first found waiting is HOLDING; one still waiting at the order's
     * timeout ({@code Confirmation#ORDER_TIMEOUT_PROPERTY}) from then is
     * UNHELD, and every hold of the run gives way ({@link
     * RecordingPlant#gaveWay}): the run no longer runs the confirmed world.
     * A timed wait's WAKE asks this way ({@link #timedOut}), so what its wait
     * released stays released while it is held.
     */
    private static boolean realizedLocked(Pending pending) {
        loadRealizedLocked();
        if (realized.isEmpty() || RecordingPlant.orderGaveWay()) return true;
        String context = names.context(pending.context);
        if (context == null) return true;
        Integer made = COUNTS.get(pending.key);
        String id = eventId(pending.kind.name(), context,
                pending.site, made == null ? 0 : made);
        List<Ordered> rows = realized.get(id);
        if (rows == null) return true;
        List<Ordered> missing = new ArrayList<Ordered>();
        for (Ordered row : rows) {
            if (!MADE_AWAITED.contains(row.before)) missing.add(row);
        }
        long now = System.currentTimeMillis();
        Long due = DUE.get(id);
        if (!missing.isEmpty() && (due == null || now < due)) {
            if (due == null) {
                DUE.put(id, now + Long.getLong(
                        Confirmation.ORDER_TIMEOUT_PROPERTY,
                        Confirmation.ORDER_TIMEOUT_MS));
                for (Ordered row : missing) {
                    RecordingPlant.ordered(RecordingPlant.HOLDING, row.row,
                            row.after, row.before);
                }
            }
            return false;
        }
        realized.remove(id);
        DUE.remove(id);
        for (Ordered row : rows) {
            boolean held = !missing.contains(row);
            RecordingPlant.ordered(held ? RecordingPlant.APPLIED
                    : RecordingPlant.UNHELD, row.row, row.after, row.before);
            if (!held) {
                OVERDUE.computeIfAbsent(row.before,
                        key -> new ArrayList<Ordered>()).add(row);
            }
        }
        if (!missing.isEmpty()) {
            RecordingPlant.gaveWay();
            LOCK.notifyAll();
        }
        return true;
    }

    /** An event made: what waits for it may go on, and a row whose wait
     *  for it gave way states it came late. */
    private static void madeRealizedLocked(Pending pending, int k) {
        if (AWAITED.isEmpty()) return;
        String context = names.context(pending.context);
        if (context == null) return;
        String id = eventId(pending.kind.name(), context, pending.site, k);
        if (!AWAITED.contains(id) || !MADE_AWAITED.add(id)) return;
        LOCK.notifyAll();
        List<Ordered> late = OVERDUE.remove(id);
        for (Ordered row : late == null
                ? Collections.<Ordered>emptyList() : late) {
            RecordingPlant.ordered(RecordingPlant.LATE, row.row, row.after,
                    row.before);
        }
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
        String id = trimmed(occurrenceId);
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
     * Marks this run cut where it ended with its session standing ({@link
     * ScheduleEvent#WITNESS}): at its witness, at a FORCE run's forced
     * target, or at a stall after a flip was taken ({@code
     * ConcolicResultPublisher#conclude}).  What it would make after is not
     * its question, and a replay held to its order waits for none of it.
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
        String node = trimmed(RuntimeTraceContext.nodeHere());
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
            CONFLICTED.remove(self);
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
            if ((CONFLICTED.contains(self) || !passedLocked(event, at))
                    && !watchdogLocked()) {
                return false;
            }
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
     * An event of a timed-wait loop's turn ({@link #timedWaitTurn}) whose
     * slot is not due is held at it the same way: its k is a count of
     * wakes, so the slot may be another turn's; let go, it takes it.
     *
     * A WRITE never passes an earlier held write to its location: a slot
     * that holds is due only past it, and one that holds nothing (past the
     * cut) or no slot at all waits for it ({@link #conflictLocked}).
     *
     * The watchdog lets a held wait go when the run idles.  Released, a
     * timed wait still waits out its own deadline ({@link TimedWaits}).
     */
    private static int waitsAtLocked(Pending event, int slot) {
        Thread self = Thread.currentThread();
        HELD.remove(self);
        CONFLICTED.remove(self);
        if (event.kind == ScheduleEvent.Kind.READ) {
            // A read waits only behind the writes to its location before
            // its slot, never for the frontier; one the order lacks, or of a
            // location no write of the order wrote, runs free.  The wait is
            // held: while the order moves the read waits for its write, and
            // a grace into a stall it is let go with the write's slot kept,
            // never given up for it.  A read's k-th slot is the recording's
            // k-th read of its context there, and a context that read more
            // often than recorded (a poll, a cache refresh) waits for a later
            // write than its own -- the writer may wait on the reader then
            // (solr-adhoc-39 MB29s: 37 such stalls, 447 s).
            if (slot < 0) return GO;
            int write = conflictLocked(event, slot);
            if (write < 0 || owesBeforeLocked(event, write)
                    || LET_GO.contains(self)) {
                return GO;
            }
            CONFLICTED.add(self);
            HELD.put(self, event);
            return write + 1;
        }
        boolean turn = timedWaitTurn(event.context);
        if (slot >= 0 && heldKind(slot) && !dueLocked(slot)
                && !(turn && LET_GO.contains(self))) {
            if (!turn) return slot;
            // A timed-wait loop's turn: its k counts the loop's wakes, which
            // the replay's timing moves, so its slot may be another turn's.
            // Held like a poll past its count: it bounds no give-up, and let
            // go it takes the slot its key found -- a WRITE still behind an
            // earlier held write to its location, below (solr-adhoc-39
            // MB29s: a queue write in replayed turn #88 waited at recorded
            // #88's slot and bounded a give-up of 4251 slots).
            HELD.put(self, event);
            return slot;
        }
        if (slot < 0 && deadLocked(event)) return GO;
        if (event.kind == ScheduleEvent.Kind.WRITE) {
            int conflict = conflictLocked(event, slot);
            // A writer whose own context holds a slot before that write
            // owes it: held behind the later write, it held the order there
            // until the watchdog, and every later slot of its context with
            // it (solr-adhoc-19 MB14s: a node's extra compare-and-set retry
            // at its terms node, then its eight registration slots, a stall
            // each; 39 MB18s: 45 such writes given up one by one, behind
            // writes up to 970 slots past the frontier).
            if (conflict >= 0 && !owesBeforeLocked(event, conflict)) {
                CONFLICTED.add(self);
                return conflict + 1;
            }
        }
        if (slot >= 0) return GO;
        if (event.kind != ScheduleEvent.Kind.WAKE || !lineStandsLocked()) {
            return GO;
        }
        int next = SLOTS.containsKey(event.key)
                ? nextOpenLocked(BY_CONTEXT.get(event.context)) : -1;
        if (next >= 0) {
            if (!dueLocked(next)) return next;
            // The frontier its own context's: the loop owes it, and holding
            // the poll holds the frontier until the watchdog (solr-adhoc-19
            // SG1: ZkController#waitForCoreNodeName, 66 stalls, 991 s).
            if (movedSincePollLocked(event) || clockLoopLocked(event)
                    || next == firstBlocking) {
                return GO;
            }
        }
        if (LET_GO.contains(self)) return GO;
        HELD.put(self, event);
        return next >= 0 ? next : AT_THE_LINE;
    }

    /** Whether {@code event}'s own context holds an open slot that blocks
     *  before {@code slot}: only its thread makes it. */
    private static boolean owesBeforeLocked(Pending event, int slot) {
        List<Integer> own = BY_CONTEXT.get(event.context);
        if (own == null) return false;
        for (int at : own) {
            if (at >= slot) return false;
            if (at >= firstOpen && state[at] == OPEN && blocking(at)) {
                return true;
            }
        }
        return false;
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
     * The held write to {@code event}'s location it waits for, or -1: the
     * first open slot that holds of a WRITE there before its own {@code
     * slot}; with no slot -- a write the recording did not make there (a
     * create-if-absent another node's write found made, a retry, an extra
     * sequential create) -- the one that was next there when it first
     * asked, fixed then, never every later write there.  It waits until
     * that slot is settled: taken, or given up by the watchdog like any
     * slot (a write that never comes costs a stall, never the run: on
     * solr-bug-reindex a given-up write still conflicted, and a core-admin
     * CREATE's queue write waited for ever behind the Overseer's, which the
     * Overseer makes only once its poll sees that CREATE complete).
     */
    private static int conflictLocked(Pending event, int slot) {
        if (slot < 0 && event.conflict != -2) {
            return event.conflict >= 0 && state[event.conflict] == OPEN
                    ? event.conflict : -1;
        }
        int conflict = -1;
        List<Integer> writes = BY_LOCATION.get(event.site);
        if (writes != null) {
            for (int write : writes) {
                if (slot >= 0 && write >= slot) break;
                // A write waits behind the reads before it too; a read
                // behind writes alone.
                if (event.kind == ScheduleEvent.Kind.READ && order.get(write)
                        .kind() == ScheduleEvent.Kind.READ) {
                    continue;
                }
                if (state[write] == OPEN && heldKind(write)) {
                    conflict = write;
                    break;
                }
            }
        }
        if (slot < 0) event.conflict = conflict;
        return conflict;
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
                && kind != ScheduleEvent.Kind.INTERRUPT
                && kind != ScheduleEvent.Kind.READ;
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
        String key = order.get(slot).key();
        ArrayDeque<Integer> keyed = SLOTS.get(key);
        if (keyed != null) keyed.remove(Integer.valueOf(slot));
        if (next == DEAD) DEAD_BY_KEY.merge(key, 1, Integer::sum);
    }

    /**
     * Per key, the slots settled dead ({@link #closed}) that no event of
     * the key took since.  Such an event runs free: the order no longer
     * holds its place, so it is neither a write the recording never made
     * there, which waits behind the next write to its location, nor a poll
     * past its recorded count.  An occurrence's id can name other work in
     * the replay than in the recording -- a daemon's loop region left and
     * entered again between two turns -- and its close then kills slots
     * whose events still come (solr-adhoc-19, round MB8s: the Overseer's
     * state.json write, its slot dead with the region its turns shared in
     * the recording, waited behind its own write 110 slots on, and the
     * three nodes polling for the replica names it wrote stalled the order
     * thirty times, then failed their registrations).
     */
    private static final Map<String, Integer> DEAD_BY_KEY =
            new HashMap<String, Integer>();

    /** The context families whose frontier event a stall gave up: a later
     *  frontier of theirs stands a grace, not a timeout ({@link
     *  #watchdogLocked}). */
    private static final Set<String> FAILED = new HashSet<String>();

    /** How a timed-wait loop's turn renders ({@code
     *  RuntimeTraceContext#beginWake}): {@code Root:WAKE/<wait>#k}. */
    private static final String TIMED_WAIT_TURN =
            "Root:" + Role.WAKE.name() + "/";

    /**
     * Whether an event context stands in a timed-wait loop's turn: its
     * causal context, after the node, is {@code Root:WAKE/<wait>#k}, whose k
     * counts the loop's wakes -- a timing fact, so the k-th turn of a replay
     * is another turn than the recording's k-th.
     */
    static boolean timedWaitTurn(String context) {
        return context.startsWith(TIMED_WAIT_TURN, context.indexOf('|') + 1);
    }

    private static final java.util.regex.Pattern TURN_OR_ANCHOR =
            java.util.regex.Pattern.compile("#[0-9]+|Anchor:[0-9a-f]+");

    /**
     * A context's family: its node and causal context, a root's turn number
     * and an anchor's endpoint left out ({@code Root:WAKE/<wait>#*}, {@code
     * Anchor:*@SOLR_HTTP/test}), its start frames too -- the turns of one
     * daemon, the receipts of one kind of message on one node.  A replay
     * that numbers a daemon's turns or mints a message's endpoint otherwise
     * misses each of them in turn.
     */
    static String familyOf(String context) {
        int node = context.indexOf('|');
        int frames = node < 0 ? -1 : context.indexOf('|', node + 1);
        String shape = frames < 0 ? context : context.substring(0, frames);
        java.util.regex.Matcher numbered = TURN_OR_ANCHOR.matcher(shape);
        StringBuffer family = new StringBuffer();
        while (numbered.find()) {
            numbered.appendReplacement(family,
                    numbered.group().startsWith("#") ? "#*" : "Anchor:*");
        }
        return numbered.appendTail(family).toString();
    }

    /** Whether {@code event}'s key has a dead slot left: then it takes it
     *  (the event runs free). */
    private static boolean deadLocked(Pending event) {
        Integer dead = DEAD_BY_KEY.get(event.key);
        if (dead == null) return false;
        if (dead == 1) {
            DEAD_BY_KEY.remove(event.key);
        } else {
            DEAD_BY_KEY.put(event.key, dead - 1);
        }
        return true;
    }

    /** An open slot is given up: its event may still come and take it. */
    private static void giveUpLocked(int slot) {
        if (state[slot] != OPEN) return;
        markLocked(slot, GIVEN_UP);
        givenUp++;
        FocusedReplay.departed(slot + " (" + order.get(slot).render()
                + (slot < cut ? ", in the prefix" : ", past the cut at "
                + cut) + ")");
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
     * slots before the earliest waiter a slot holds are given up.  With only
     * waits held without a slot waiting (polls past their recorded count,
     * waits at the line), it lets them go again, a grace apart.  A PUBLISH
     * whose apply is in flight at the frontier is looked at first ({@link
     * #inFlightLocked}): no wait held behind it is let go meanwhile, to read
     * the version before it.
     */
    private static boolean watchdogLocked() {
        if (WAITERS.isEmpty()) return false;
        long now = System.currentTimeMillis();
        Boolean applying = inFlightLocked(now);
        if (applying != null) return applying;
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
        if (now - letGoAt < LET_GO_GRACE_MS) return false;
        // A wait held without a slot is let go a grace into a stall nothing
        // computes toward, not a timeout: the frontier may be behind it, and
        // its event runs free anyway once let go (SG1: 92 such stalls across
        // six study checks, 15 s each).
        if (!HELD.isEmpty() && !letGoSinceProgress && stood < timeout
                && stood >= LET_GO_GRACE_MS && !computingLocked(now)) {
            letGoHeldLocked(stood, now);
            return true;
        }
        // A wait held without a slot -- a poll past its recorded count at
        // its context's due slot, or at the line -- waits for no slot's
        // event, so it bounds no give-up: at a slot it would shadow the
        // stalled one, at the line it would give up every slot before it
        // (solr-adhoc-13 MB6: a replica poll held at the cut, 4560 slots at
        // once).  It is let go instead, a grace apart; so is a read held
        // behind a write.
        int earliest = Integer.MAX_VALUE;
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            if (!HELD.containsKey(waiter.getKey())) {
                earliest = Math.min(earliest, waiter.getValue());
            }
        }
        // What the stall gives up first: the one slot a conflicted write
        // waits behind, else the frontier.  A read stands a grace, not a
        // timeout: its slot holds no frontier.  So does a slot in a context
        // family that missed its event in a stall before: that family
        // diverged from the recording, and each of its later slots cost a
        // timeout of its own (SG2: 69 of solr-adhoc-38's 138 give-up stalls,
        // 63 of 19's 70, on a context that had failed one; MB21s/MB22s: 26
        // of 31's 69, 34 of 10's 58, on another turn or anchor of a family
        // that had; MB29s: 102 of 39's 145 conflicts stood the timeout, the
        // family judged by the waiting write's context, not by the one it
        // waited for).
        boolean conflicted = earliest != Integer.MAX_VALUE
                && onlyConflictedAtLocked(earliest);
        int first = conflicted ? earliest - 1 : firstBlocking;
        long bound = first < order.size()
                && (order.get(first).kind() == ScheduleEvent.Kind.READ
                || FAILED.contains(familyOf(order.get(first).context())))
                ? Math.min(timeout, LET_GO_GRACE_MS) : timeout;
        if (stood < bound) return false;
        if (stood < CEILING * bound && computingLocked(now)) return false;
        if (!HELD.isEmpty() && (!letGoSinceProgress
                || earliest == Integer.MAX_VALUE)) {
            letGoHeldLocked(stood, now);
            return true;
        }
        if (earliest == Integer.MAX_VALUE) return false;
        if (conflicted) {
            // A write the order lacks there, or one whose slot holds nothing,
            // waits at the slot after the one write to its location it
            // follows: that write alone is given up, never the run of other
            // nodes' events before it, and it is no stall past the cut.  One
            // already settled is the waiter's to see at its next ask, and
            // nothing to do (another waiter asking first spun on it:
            // solr-18413 MB3, 628 stalls at one slot).
            int write = earliest - 1;
            if (state[write] != OPEN) return false;
            stalls++;
            giveUpLocked(write);
            FAILED.add(familyOf(order.get(write).context()));
            stateLocked("schedule-write#" + write, "the "
                    + (order.get(write).kind() == ScheduleEvent.Kind.READ
                            ? "read" : "write") + " at slot "
                    + write + " (" + order.get(write).render() + ") did not"
                    + " happen in the " + stood + " ms the frontier stood at"
                    + " slot " + firstBlocking + ", while a write to its"
                    + " location waited for it: it alone is given up, and"
                    + " still takes its slot if it comes");
            settleLocked();
            return true;
        }
        stalls++;
        if (earliest >= cut && restStalls >= REST_STALLS) {
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
        String frontierContext = firstBlocking < order.size()
                ? order.get(firstBlocking).context() : null;
        int from = -1;
        int count = 0;
        for (int index = firstOpen; index < earliest; index++) {
            if (state[index] != OPEN) continue;
            if (from < 0) from = index;
            giveUpLocked(index);
            count++;
        }
        if (count == 0) return false;
        if (frontierContext != null) FAILED.add(familyOf(frontierContext));
        if (earliest >= cut) restStalls++;
        stateLocked((from < cut ? "schedule#" : "schedule-rest#") + from,
                count + " slot(s) of the order from " + from + " on (the"
                        + " first " + order.get(from).render() + ") did not"
                        + " happen in the " + stood + " ms the frontier"
                        + " stood at slot " + firstBlocking + ", while "
                        + order.get(earliest).render() + " waited at slot "
                        + earliest + ": they are given up, and each still takes its"
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

    /** Whether every waiter at {@code slot} is a write waiting behind the
     *  write to its location ({@link #CONFLICTED}). */
    private static boolean onlyConflictedAtLocked(int slot) {
        boolean any = false;
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            if (waiter.getValue() != slot) continue;
            if (!CONFLICTED.contains(waiter.getKey())) return false;
            any = true;
        }
        return any;
    }

    /** A held wait, as it names itself. */
    private static String heldLocked(Thread thread) {
        Pending held = HELD.get(thread);
        if (held == null) return "a wait the order does not name";
        if (held.kind == ScheduleEvent.Kind.READ) {
            return held.render() + " behind a write to its location";
        }
        Integer at = WAITERS.get(thread);
        if (held.kind != ScheduleEvent.Kind.WAKE && at != null && at >= 0
                && timedWaitTurn(held.context)) {
            return held.render() + " in a timed wait's turn, at slot " + at;
        }
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
    static long collectedMillis() {
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

    /**
     * How many distinct events this run has made so far ({@link #madeKey}):
     * what a replay's watch counts as progress ({@code
     * ConcolicResultPublisher#watchProgress}).  A loop that only does again
     * what it did adds none, however busy (PV7-38: PULL replicas polling a
     * leader left down, a test retrying against it, for 36 minutes).
     */
    static int newKeys() {
        synchronized (LOCK) {
            return MADE_KEYS.size();
        }
    }

    /** From now on this run counts its distinct events ({@link #newKeys}):
     *  a focused replay's watch is armed. */
    static void countNewEvents() {
        counting = true;
    }

    /** Slots of the order taken or given up so far: bounded by the order,
     *  what the replay's watch counts besides its new events. */
    static long settledSlots() {
        synchronized (LOCK) {
            return (long) taken + givenUp;
        }
    }

    /**
     * An event as progress counts it: its kind; its site, with every name
     * the run minted for itself taken out ({@link RunSpellings#strip}: a
     * sequential znode's counter, a session id, a host and port, an
     * identity hash); its node and its context's shape ({@link #shape}: per
     * anchor hop the RPC site and the sender's node, then the root's role
     * and api -- no invocation count, anchor hash or handoff), names the
     * engine built and never stripped (a node named like a number would
     * fold two nodes).  A poll, a retry or a watch made again makes no new
     * key; other code, another store location, another request handler or
     * another node does.  A view's PUBLISH names the version it put in
     * force, so a loop publishing new versions still makes new keys: the
     * safe direction, a cut missed, never a run cut.
     */
    private static String madeKey(Pending pending) {
        ContextShape.Stance stance =
                ContextShape.Stance.ofSend(pending.context);
        return pending.kind.name() + " " + RunSpellings.strip(pending.site)
                + " | " + (stance == null ? pending.context
                : stance.node() + "|" + shape(stance.context()));
    }

    /**
     * The schedule's holds at this moment, for a stall's verdict ({@code
     * FocusedReplay#noProgress}): how many threads wait for a turn, where
     * the one waiting longest waits and since when, and how many of them
     * the order holds with no slot or behind a held write to their
     * location; {@code ""} when no thread waits, so a stall the engine's
     * own hold made is told from one the workload made.
     */
    static String holding() {
        synchronized (LOCK) {
            if (WAITERS.isEmpty()) return "";
            Thread longest = null;
            long since = Long.MAX_VALUE;
            for (Map.Entry<Thread, Long> arrived : ARRIVED.entrySet()) {
                if (arrived.getValue() < since) {
                    since = arrived.getValue();
                    longest = arrived.getKey();
                }
            }
            return WAITERS.size() + " thread(s) held for a turn"
                    + (longest == null ? "" : ", the longest (\""
                    + longest.getName() + "\") at slot "
                    + WAITERS.get(longest) + " for "
                    + (System.currentTimeMillis() - since) / 1000L + " s")
                    + "; " + HELD.size() + " held with no slot, "
                    + CONFLICTED.size() + " behind a held write";
        }
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
        String configured = trimmed(System.getProperty(TIMEOUT_PROPERTY));
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
                            restFile).containsKey(ScheduleEvent.WITNESS),
                    readsHeld());
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

    /**
     * Holds the run to {@code events}, cut, then {@code after}, which a run
     * cut at its witness ends at.  A READ takes a slot only at a location a
     * WRITE of the order wrote.  Where {@code readsHeld} is false -- a run
     * the model orders: a world's planted pairings, CONFIRM, a native
     * reproduction's plant -- the reads past the cut take none: there the
     * model's order puts each read (its pairings' ORDER rows), and a flipped
     * world that reads before the newer write is not held back to the
     * recorded place.  The prefix ends before the first event the model
     * reorders ({@code SchedulePrefix}), so its reads keep their places.
     */
    private static void installLocked(List<ScheduleEvent> events,
                                      List<ScheduleEvent> after,
                                      boolean atWitness, boolean readsHeld) {
        Set<String> written = new HashSet<String>();
        for (List<ScheduleEvent> part : Arrays.asList(events, after)) {
            for (ScheduleEvent event : part) {
                if (event.kind() == ScheduleEvent.Kind.WRITE) {
                    written.add(event.site());
                }
            }
        }
        events = heldReads(events, written, true);
        after = heldReads(after, written, readsHeld);
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
        CONFLICTED.clear();
        BY_LOCATION.clear();
        DEAD_BY_KEY.clear();
        FAILED.clear();
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
            if (event.kind() == ScheduleEvent.Kind.WRITE
                    || event.kind() == ScheduleEvent.Kind.READ) {
                BY_LOCATION.computeIfAbsent(event.site(),
                        location -> new ArrayList<Integer>()).add(index);
            }
            if (heldKind(index)) openHeld++;
        }
        firstOpen = 0;
        firstBlocking = 0;
        restStalls = 0;
        frontierMovedLocked();
        settleLocked();
    }

    /** {@code events} with no READ but those {@code readsHeld} keeps at a
     *  location {@code written}. */
    private static List<ScheduleEvent> heldReads(List<ScheduleEvent> events,
                                                 Set<String> written,
                                                 boolean readsHeld) {
        List<ScheduleEvent> kept = new ArrayList<ScheduleEvent>(events.size());
        for (ScheduleEvent event : events) {
            if (event.kind() != ScheduleEvent.Kind.READ
                    || readsHeld && written.contains(event.site())) {
                kept.add(event);
            }
        }
        return kept;
    }

    /** Whether this replay holds its reads to the recorded order: not one
     *  the model orders ({@link #installLocked}). */
    private static boolean readsHeld() {
        return !FocusedReplay.pairs() && !FocusedReplay.confirming()
                && !RecordingPlant.planting();
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
        String named = JsonFields.setting(PREFIX_PROPERTY, PREFIX_ENV);
        return named.isEmpty() ? besideWorker(PREFIX_FILE) : Paths.get(named);
    }

    private static Path suffixFile() {
        return besideWorker(SUFFIX_FILE);
    }

    /** {@code name} in the worker directory, or null. */
    private static Path besideWorker(String name) {
        String worker = FocusedReplay.workerDir();
        if (worker.isEmpty()) return null;
        Path beside = Paths.get(worker).resolve(name);
        return beside.toFile().isFile() ? beside : null;
    }

    /**
     * The replay's account of its order, at exit, and of its progress: how
     * many distinct events it made ({@link #newKeys}), the longest span
     * between two new ones and how long ago the last one was -- what the
     * watch's bound is measured against ({@code
     * ConcolicResultPublisher#NO_NEW_EVENT_MILLIS}).
     */
    static String progress() {
        synchronized (LOCK) {
            long now = System.nanoTime();
            String made = !counting ? "" : MADE_KEYS.size()
                    + " distinct event(s)" + (lastNewNanos == 0L ? ""
                    : ", at most " + TimeUnit.NANOSECONDS.toSeconds(
                    longestQuietNanos) + " s between two new ones, the last "
                    + TimeUnit.NANOSECONDS.toSeconds(now - lastNewNanos)
                    + " s ago") + "; ";
            if (order.isEmpty()) return made + "no order";
            return made + "of an order of " + order.size()
                    + " slot(s) (prefix "
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

    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after,
                                boolean atWitness) {
        enforceForTests(events, after, atWitness, true);
    }

    /** With {@code readsHeld} false, as a run the model orders. */
    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after,
                                boolean atWitness, boolean readsHeld) {
        synchronized (LOCK) {
            loaded = true;
            installLocked(events, after, atWitness, readsHeld);
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
            MADE_KEYS.clear();
            counting = false;
            lastNewNanos = 0L;
            longestQuietNanos = 0L;
            realized = null;
            names = new StableEventNames();
            AWAITED.clear();
            MADE_AWAITED.clear();
            OVERDUE.clear();
            DUE.clear();
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
            CONFLICTED.clear();
            BY_LOCATION.clear();
            DEAD_BY_KEY.clear();
            IN_FLIGHT.clear();
            FAILED.clear();
            POLLED.clear();
            PASSED_BY_CONTEXT.clear();
            PASSED_SLOTS.clear();
            MADE.clear();
            ClockLoops.resetForTests();
            RunNames.resetForTests();
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
