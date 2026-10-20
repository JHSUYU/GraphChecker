package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.RunSpellings;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
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
import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

public final class ScheduleLog {
    public static final String TIMEOUT_PROPERTY =
            "causynth.schedule.timeout.ms";
    public static final String PREFIX_ENV = "CAUSYNTH_SCHEDULE_PREFIX";
    public static final String PREFIX_PROPERTY = "causynth.schedule.prefix";
    public static final String PREFIX_FILE = "schedule_prefix.jsonl.gz";
    public static final String SUFFIX_FILE = "schedule_suffix.jsonl.gz";
    public static final String RECORDING_FILE = "schedule.jsonl";

    static final long DEFAULT_TIMEOUT_MS = 15000L;
    static final int REST_STALLS = 2;
    private static final int AT_THE_LINE = -1;
    private static final int GO = -2;

    static final long LET_GO_GRACE_MS = 2000L;

    static final int CEILING = 8;
    private static final long CPU_SAMPLE_MS = 1000L;

    private static final Object LOCK = new Object();

    interface Sink {
        void write(JsonObject row);
    }

    private static Sink sink;
    private static final List<JsonObject> PENDING = new ArrayList<JsonObject>();
    private static final int PENDING_LIMIT = 1 << 20;
    private static final Map<String, Integer> COUNTS =
            new HashMap<String, Integer>();
    private static long seq;
    private static final Set<String> MADE_KEYS = new HashSet<String>();
    private static volatile boolean counting;
    private static long lastNewNanos;
    private static long longestQuietNanos;

    private static final byte OPEN = 0;
    private static final byte TAKEN = 1;
    private static final byte GIVEN_UP = 2;
    private static final byte DEAD = 3;

    private static boolean loaded;
    private static volatile boolean holds;
    private static List<ScheduleEvent> order = Collections.emptyList();
    private static int cut;
    private static int line;
    private static byte[] state = new byte[0];
    private static final Map<String, ArrayDeque<Integer>> SLOTS =
            new HashMap<String, ArrayDeque<Integer>>();
    private static String[] slotKeys = new String[0];
    private static String[] slotContexts = new String[0];
    private static final Map<String, List<Integer>> BY_OCCURRENCE =
            new HashMap<String, List<Integer>>();
    private static final Map<String, List<Integer>> BY_CONTEXT =
            new HashMap<String, List<Integer>>();
    private static final Map<String, List<Integer>> BY_LOCATION =
            new HashMap<String, List<Integer>>();
    private static final Map<String, Integer> TAKEN_WAKES =
            new HashMap<String, Integer>();
    private static final Map<Thread, Integer> WAITERS =
            new HashMap<Thread, Integer>();
    private static final Map<Thread, Long> ARRIVED =
            new HashMap<Thread, Long>();
    private static final Map<Thread, Pending> HELD =
            new HashMap<Thread, Pending>();
    private static final Set<Thread> LET_GO = new HashSet<Thread>();
    private static final Set<Thread> CONFLICTED = new HashSet<Thread>();
    private static long moves;
    private static final Map<String, Long> POLLED =
            new HashMap<String, Long>();
    private static final ThreadLocal<Boolean> VACANT = new ThreadLocal<Boolean>();
    private static boolean letGoSinceProgress;
    private static long letGoAt;
    private static final String ENGINE_THREAD = "causynth-";
    private static int firstOpen;
    private static int firstBlocking;
    private static int openHeld;
    private static long lastProgress;
    private static long stallSince;
    private static final Set<Long> ELSEWHERE = new HashSet<Long>();
    private static final Set<Long> RELEASED = new HashSet<Long>();
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
    private static long collectedSeen;
    private static long cpuSampledAt;
    private static boolean computing;
    private static boolean computedInStall;

    private ScheduleLog() {
    }


    public static boolean observe(ScheduleEvent.Kind kind, String site) {
        return observe(kind, site, "");
    }

    public static boolean observe(ScheduleEvent.Kind kind, String site,
                                  String endpoint) {
        return observe(kind, site, endpoint, null);
    }

    public static final class Stance {
        private final String context;
        private final String region;

        private Stance(String context, String region) {
            this.context = context;
            this.region = region;
        }
    }

    public static Stance viewStance(String node) {
        return new Stance(trimmed(node) + "|"
                + ContextShape.Stance.VIEW_STANCE, "");
    }

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

    private enum Settle {
        OLDER,
        UP_TO,
        AT
    }

    public static void turnNotTaken(String node, String site, String why) {
        settleTurns(node, site, Settle.AT, Collections.<Long>emptySet(), why);
    }

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

    public static void waitsNoMore() {
        synchronized (LOCK) {
            Thread self = Thread.currentThread();
            LET_GO.remove(self);
            HELD.remove(self);
            if (doneWaitingLocked(self)) LOCK.notifyAll();
        }
    }

    static final class Publication {
        private final Pending event;
        private final int slot;
        private final Thread publisher;
        private final long began;
        private long lookedAt;
        private long cpuLooked;
        private long collectedLooked;
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

    static final long PUBLISH_GRACE_MS = 500L;

    private static final Map<Integer, Publication> IN_FLIGHT =
            new HashMap<Integer, Publication>();

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

    private static String heldByTheOrderLocked(Thread publisher) {
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

    private static final int OWNER_HOPS = 8;

    private static long cpuOf(Thread thread) {
        try {
            return ManagementFactory.getThreadMXBean().getThreadCpuTime(
                    thread.getId());
        } catch (UnsupportedOperationException none) {
            return -1L;
        }
    }

    public static Stance stanceHere() {
        if (!RecordingWindow.opened()) return null;
        mute();
        try {
            return standing();
        } finally {
            unmute();
        }
    }

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

    private static final Set<String> UNAWAITED =
            java.util.concurrent.ConcurrentHashMap.newKeySet();

    static void unawaited(String transport) {
        UNAWAITED.add(trimmed(transport).toUpperCase(java.util.Locale.ROOT));
    }

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

    private static final Set<String> UNKNOWN_SENDERS = new HashSet<String>();

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

    static boolean vacated() {
        return Boolean.TRUE.equals(VACANT.get());
    }

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

    enum Turn {
        ADMITTED,
        NOT_YET,
        FREE,
        NO_EVENT
    }

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
                        waitLocked(self, at);
                        if (!passedLocked(wake.event, at)
                                && !watchdogLocked()) {
                            return Turn.NOT_YET;
                        }
                        continue;
                    }
                }
                takeTurnWake(TURN.get());
            }
        } finally {
            unmute();
        }
    }

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

    private static final class Pending {
        private final ScheduleEvent.Kind kind;
        private final String context;
        private final String site;
        private final String occurrence;
        private final String endpoint;
        private final String key;
        private final String slotContext;
        private final String slotKey;
        private final String slotOccurrence;
        private Boolean clockLoop;
        private int conflict = -2;

        private Pending(ScheduleEvent.Kind kind, String context, String site,
                        String occurrence, String endpoint) {
            this.kind = kind;
            this.context = context;
            this.site = site;
            this.occurrence = occurrence;
            this.endpoint = endpoint;
            this.key = ScheduleEvent.key(kind, context, site);
            boolean turn = StableEventNames.timedWaitTurn(context);
            this.slotContext = turn ? StableEventNames.turnFamily(context) : context;
            this.slotKey = turn ? ScheduleEvent.key(kind, slotContext, site)
                    : key;
            this.slotOccurrence = turn ? "" : occurrence;
        }

        private String render() {
            return kind.name() + " " + site + " @ " + context;
        }
    }

    private static Pending pending(ScheduleEvent.Kind kind, String site,
                                   String endpoint, Stance at) {
        String stable = JvmNames.stable(trimmed(site));
        if (stable.isEmpty()) return null;
        Stance stance = at != null ? at : standing();
        if (stance == null) return null;
        return new Pending(kind, stance.context, stable, stance.region,
                trimmed(endpoint));
    }


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

    private static final ThreadLocal<TurnWake> TURN =
            new ThreadLocal<TurnWake>();

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

    private static boolean turnWritten() {
        TurnWake turn = TURN.get();
        return turn == null || turn.written;
    }

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


    private static Map<String, List<Ordered>> realized;
    private static final Set<String> AWAITED = new HashSet<String>();
    private static final Set<String> MADE_AWAITED = new HashSet<String>();
    private static final Map<String, List<Ordered>> OVERDUE =
            new HashMap<String, List<Ordered>>();
    private static final Map<String, Long> DUE = new HashMap<String, Long>();
    private static StableEventNames names = new StableEventNames();

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

    private static void writeLocked(JsonObject row) {
        if (sink != null) {
            sink.write(row);
        } else if (PENDING.size() < PENDING_LIMIT) {
            PENDING.add(row);
        }
    }

    private static final Set<String> MARKED = new HashSet<String>();

    private static final Interactions.Bounded<ContextShape.Stance> SENDERS =
            Interactions.bounded();

    static List<String> shape(CausalContext context) {
        synchronized (SENDERS) {
            return ContextShape.of(context, SENDERS::get);
        }
    }

    static void mark(String occurrenceId) {
        String id = trimmed(occurrenceId);
        if (id.isEmpty() || !RecordingWindow.opened()) return;
        synchronized (LOCK) {
            if (!MARKED.add(id)) return;
            writeLocked(RowCodec.writeScheduleMark(id, seq));
        }
    }

    static void invocation(String stated) {
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

    private static JsonObject held(Path file) {
        if (file == null || !file.toFile().isFile()) return null;
        try {
            return SessionReader.readScheduleInvocation(file);
        } catch (IOException unreadable) {
            return null;
        }
    }

    static void witnessed() {
        if (!RecordingWindow.opened()) return;
        synchronized (LOCK) {
            writeLocked(RowCodec.writeScheduleMark(ScheduleEvent.WITNESS,
                    seq));
        }
    }

    static String contextOf(CausalContext context) {
        String node = trimmed(RuntimeTraceContext.nodeHere());
        String handoffs = Identity.handoffs();
        return node + "|" + context.render()
                + (handoffs.isEmpty() ? "" : "|" + handoffs);
    }

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

    static void installFile(final File directory) {
        if (directory == null) return;
        final File file = new File(directory, RECORDING_FILE);
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


    private static void admit(Pending event) {
        synchronized (LOCK) {
            loadOrderLocked();
            admitLocked(event);
        }
    }

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
            Thread.currentThread().interrupt();
            admittedLocked(event, slotOf(event));
        } finally {
            doneWaitingLocked(self);
            HELD.remove(self);
            LET_GO.remove(self);
            CONFLICTED.remove(self);
        }
    }

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

    private static void waitLocked(Thread self, int at) {
        if (WAITERS.put(self, at) == null) {
            ARRIVED.put(self, System.currentTimeMillis());
        }
    }

    private static boolean doneWaitingLocked(Thread self) {
        ARRIVED.remove(self);
        return WAITERS.remove(self) != null;
    }

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
            POLLED.put(event.slotKey, before);
        }
        Thread self = Thread.currentThread();
        Made made = MADE.get(self);
        if (made == null || !made.context.equals(event.slotContext)) {
            made = new Made(event.slotContext);
            MADE.put(self, made);
        }
        made.sites.add(event.kind + " " + event.site);
    }

    private static final class Made {
        private final String context;
        private final Set<String> sites = new HashSet<String>();

        private Made(String context) {
            this.context = context;
        }
    }

    private static final Map<Thread, Made> MADE =
            new java.util.WeakHashMap<Thread, Made>();

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

    private static int slotOf(Pending event) {
        ArrayDeque<Integer> slots = SLOTS.get(event.slotKey);
        if (slots == null || slots.isEmpty()) return -1;
        if (!event.slotOccurrence.isEmpty()) {
            for (int slot : slots) {
                if (event.slotOccurrence.equals(
                        order.get(slot).occurrence())) {
                    return slot;
                }
            }
        }
        int next = slots.peekFirst();
        return pastItsLoopLocked(event, next) ? -1 : next;
    }

    private static boolean pastItsLoopLocked(Pending event, int next) {
        if (event.kind != ScheduleEvent.Kind.WAKE
                || !event.occurrence.isEmpty()
                || StableEventNames.timedWaitTurn(event.context)) {
            return false;
        }
        Integer last = TAKEN_WAKES.get(event.key);
        List<Integer> own = BY_CONTEXT.get(event.slotContext);
        if (last == null || last >= next || own == null) return false;
        int from = Collections.binarySearch(own, last);
        for (int at = from < 0 ? -from - 1 : from + 1; at < own.size();
             at++) {
            int slot = own.get(at);
            if (slot >= next) return false;
            if (state[slot] != OPEN) continue;
            if (PAST_LOOP.add(event.key + "\n" + next)) {
                stateLocked("schedule-past-loop#" + next, event.render()
                        + " came again after its key's slot " + last
                        + " while its context's slot " + slot + " ("
                        + order.get(slot).render() + ") is open before the"
                        + " key's next slot " + next + ": it polls past its"
                        + " loop's recorded count and takes no slot");
            }
            return true;
        }
        return false;
    }

    private static final Set<String> PAST_LOOP = new HashSet<String>();

    private static String slotOccurrenceOf(int slot) {
        ScheduleEvent event = order.get(slot);
        return StableEventNames.timedWaitTurn(event.context()) ? "" : event.occurrence();
    }

    private static int waitsAtLocked(Pending event, int slot) {
        Thread self = Thread.currentThread();
        HELD.remove(self);
        CONFLICTED.remove(self);
        if (event.kind == ScheduleEvent.Kind.READ) {
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
        boolean turn = StableEventNames.timedWaitTurn(event.context);
        if (slot >= 0 && heldKind(slot) && !dueLocked(slot)
                && !(turn && LET_GO.contains(self))) {
            if (!turn) return slot;
            HELD.put(self, event);
            return slot;
        }
        if (slot < 0 && deadLocked(event)) return GO;
        if (event.kind == ScheduleEvent.Kind.WRITE) {
            int conflict = conflictLocked(event, slot);
            if (conflict >= 0 && !owesBeforeLocked(event, conflict)) {
                CONFLICTED.add(self);
                return conflict + 1;
            }
        }
        if (slot >= 0) return GO;
        if (event.kind != ScheduleEvent.Kind.WAKE || !lineStandsLocked()) {
            return GO;
        }
        int next = SLOTS.containsKey(event.slotKey)
                ? nextOpenLocked(BY_CONTEXT.get(event.slotContext)) : -1;
        if (next >= 0) {
            if (!dueLocked(next)) return next;
            if (movedSincePollLocked(event) || clockLoopLocked(event)
                    || next == firstBlocking) {
                return GO;
            }
        }
        if (LET_GO.contains(self)) return GO;
        HELD.put(self, event);
        return next >= 0 ? next : AT_THE_LINE;
    }

    private static boolean owesBeforeLocked(Pending event, int slot) {
        List<Integer> own = BY_CONTEXT.get(event.slotContext);
        if (own == null) return false;
        for (int at : own) {
            if (at >= slot) return false;
            if (at >= firstOpen && state[at] == OPEN && blocking(at)) {
                return true;
            }
        }
        return false;
    }

    private static boolean movedSincePollLocked(Pending event) {
        Long polled = POLLED.get(event.slotKey);
        return polled == null || moves > polled;
    }

    private static boolean clockLoopLocked(Pending event) {
        if (event.clockLoop == null) {
            event.clockLoop = ClockLoops.reads(
                    Thread.currentThread().getStackTrace());
        }
        return event.clockLoop;
    }

    private static int nextOpenLocked(List<Integer> slots) {
        if (slots == null) return -1;
        for (int slot : slots) {
            if (slot >= firstOpen && state[slot] == OPEN) return slot;
        }
        return -1;
    }

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

    private static boolean heldKind(int slot) {
        ScheduleEvent.Kind kind = order.get(slot).kind();
        return kind != ScheduleEvent.Kind.INTERRUPT
                && (slot < cut || kind == ScheduleEvent.Kind.WAKE);
    }

    private static boolean blocking(int slot) {
        ScheduleEvent.Kind kind = order.get(slot).kind();
        return kind != ScheduleEvent.Kind.WAKE
                && kind != ScheduleEvent.Kind.INTERRUPT
                && kind != ScheduleEvent.Kind.READ;
    }

    private static boolean dueLocked(int slot) {
        return firstBlocking >= slot;
    }

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

    private static void markLocked(int slot, byte next) {
        if (state[slot] == OPEN && heldKind(slot)) openHeld--;
        state[slot] = next;
        if (next == GIVEN_UP) return;
        String key = slotKeys[slot];
        ArrayDeque<Integer> keyed = SLOTS.get(key);
        if (keyed != null) keyed.remove(Integer.valueOf(slot));
        if (next == DEAD) DEAD_BY_KEY.merge(key, 1, Integer::sum);
    }

    private static final Map<String, Integer> DEAD_BY_KEY =
            new HashMap<String, Integer>();

    private static final Set<String> FAILED = new HashSet<String>();

    private static final java.util.regex.Pattern TURN_OR_ANCHOR =
            java.util.regex.Pattern.compile("#[0-9]+|Anchor:[0-9a-f]+");

    static String familyOf(String context) {
        String held = FAMILIES.get(context);
        if (held != null) return held;
        String family = family(context);
        if (FAMILIES.size() >= FAMILIES_HELD) FAMILIES.clear();
        FAMILIES.put(context, family);
        return family;
    }

    private static final Map<String, String> FAMILIES =
            new ConcurrentHashMap<String, String>();
    private static final int FAMILIES_HELD = 1 << 14;

    private static String family(String context) {
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

    private static boolean deadLocked(Pending event) {
        Integer dead = DEAD_BY_KEY.get(event.slotKey);
        if (dead == null) return false;
        if (dead == 1) {
            DEAD_BY_KEY.remove(event.slotKey);
        } else {
            DEAD_BY_KEY.put(event.slotKey, dead - 1);
        }
        return true;
    }

    private static void giveUpLocked(int slot) {
        if (state[slot] != OPEN) return;
        markLocked(slot, GIVEN_UP);
        givenUp++;
        FocusedReplay.departed(slot + " (" + order.get(slot).render()
                + (slot < cut ? ", in the prefix" : ", past the cut at "
                + cut) + ")");
    }

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

    private static boolean passedLocked(Pending event, int at) {
        boolean byContext = event.slotOccurrence.isEmpty();
        List<Integer> own = byContext ? BY_CONTEXT.get(event.slotContext)
                : BY_OCCURRENCE.get(event.slotOccurrence);
        Made made = byContext ? MADE.get(Thread.currentThread()) : null;
        if (own == null || byContext && (made == null
                || !made.context.equals(event.slotContext))) {
            return false;
        }
        int count = 0;
        int first = -1;
        for (int slot : own) {
            if (slot >= at) break;
            ScheduleEvent passedOver = order.get(slot);
            if (state[slot] != OPEN
                    || passedOver.kind() == ScheduleEvent.Kind.WAKE
                    || !event.slotContext.equals(slotContexts[slot])
                    || byContext && (!slotOccurrenceOf(slot).isEmpty()
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
            int times = PASSED_BY_CONTEXT.merge(event.slotContext, 1,
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

    private static final Set<Integer> PASSED_SLOTS = new HashSet<Integer>();

    private static final Map<String, Integer> PASSED_BY_CONTEXT =
            new HashMap<String, Integer>();

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

    private static void frontierMovedLocked() {
        lastProgress = System.currentTimeMillis();
        letGoSinceProgress = false;
        RELEASED.clear();
        ELSEWHERE.clear();
        ownerAtWork = false;
    }

    private static long stallSinceLocked() {
        long earliest = Long.MAX_VALUE;
        for (long arrived : ARRIVED.values()) {
            earliest = Math.min(earliest, arrived);
        }
        return Math.max(lastProgress, earliest);
    }

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

    private static boolean behindReadsOnlyLocked(int first, int waiter) {
        if (waiter >= order.size()
                || order.get(waiter).kind() != ScheduleEvent.Kind.WRITE) {
            return false;
        }
        for (int at = first; at < waiter; at++) {
            if (state[at] == OPEN
                    && order.get(at).kind() != ScheduleEvent.Kind.READ) {
                return false;
            }
        }
        return true;
    }

    private static boolean watchdogLocked() {
        if (WAITERS.isEmpty()) return false;
        long now = System.currentTimeMillis();
        Boolean applying = inFlightLocked(now);
        if (applying != null) return applying;
        long timeout = timeoutMillis();
        long since = stallSinceLocked();
        if (since != stallSince) {
            stallSince = since;
            computing = true;
            computedInStall = false;
            if (now - cpuSampledAt >= CPU_SAMPLE_MS) lookLocked(now, false);
        }
        long stood = now - since;
        if (now - letGoAt < LET_GO_GRACE_MS) return false;
        if (!HELD.isEmpty() && !letGoSinceProgress && stood < timeout
                && stood >= LET_GO_GRACE_MS && !computingLocked(now)) {
            letGoHeldLocked(stood, now);
            return true;
        }
        int earliest = Integer.MAX_VALUE;
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            if (!HELD.containsKey(waiter.getKey())) {
                earliest = Math.min(earliest, waiter.getValue());
            }
        }
        if (!HELD.isEmpty() && letGoSinceProgress
                && earliest == Integer.MAX_VALUE
                && stood >= LET_GO_GRACE_MS) {
            letGoHeldLocked(stood, now);
            return true;
        }
        boolean conflicted = earliest != Integer.MAX_VALUE
                && onlyConflictedAtLocked(earliest);
        int first = conflicted ? earliest - 1 : firstBlocking;
        boolean idle = stood >= LET_GO_GRACE_MS && !computingLocked(now)
                && !computedInStall;
        long bound = idle || first < order.size()
                && (order.get(first).kind() == ScheduleEvent.Kind.READ
                || FAILED.contains(familyOf(order.get(first).context())))
                ? Math.min(timeout, LET_GO_GRACE_MS) : timeout;
        if (stood < bound) return false;
        if (stood < CEILING * bound && computingLocked(now)
                && !behindReadsOnlyLocked(first, earliest)) {
            return false;
        }
        if (!HELD.isEmpty() && !letGoSinceProgress) {
            letGoHeldLocked(stood, now);
            return true;
        }
        if (earliest == Integer.MAX_VALUE) return false;
        if (conflicted) {
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

    private static boolean onlyConflictedAtLocked(int slot) {
        boolean any = false;
        for (Map.Entry<Thread, Integer> waiter : WAITERS.entrySet()) {
            if (waiter.getValue() != slot) continue;
            if (!CONFLICTED.contains(waiter.getKey())) return false;
            any = true;
        }
        return any;
    }

    private static String heldLocked(Thread thread) {
        Pending held = HELD.get(thread);
        if (held == null) return "a wait the order does not name";
        if (held.kind == ScheduleEvent.Kind.READ) {
            return held.render() + " behind a write to its location";
        }
        Integer at = WAITERS.get(thread);
        if (held.kind != ScheduleEvent.Kind.WAKE && at != null && at >= 0
                && StableEventNames.timedWaitTurn(held.context)) {
            return held.render() + " in a timed wait's turn, at slot " + at;
        }
        return SLOTS.containsKey(held.slotKey)
                ? held.render() + " past its recorded count"
                : "the unrecorded " + held.render();
    }

    private static boolean computingLocked(long now) {
        if (now - cpuSampledAt >= CPU_SAMPLE_MS) lookLocked(now, true);
        return computing;
    }

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
        computedInStall |= measure && computing;
        CPU_SEEN.clear();
        CPU_SEEN.putAll(seen);
        collectedSeen = collected;
        cpuSampledAt = now;
        ELSEWHERE.clear();
        ownerAtWork = false;
    }

    static long collectedMillis() {
        long millis = 0L;
        for (GarbageCollectorMXBean collector
                : ManagementFactory.getGarbageCollectorMXBeans()) {
            millis += Math.max(0L, collector.getCollectionTime());
        }
        return millis;
    }

    private static void stateLocked(String where, String detail) {
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    where, detail);
        } catch (Throwable unpublished) {
        }
        EngineConsole.println("Causynth schedule: " + detail);
    }

    static int newKeys() {
        synchronized (LOCK) {
            return MADE_KEYS.size();
        }
    }

    static void countNewEvents() {
        counting = true;
    }

    static long settledSlots() {
        synchronized (LOCK) {
            return (long) taken + givenUp;
        }
    }

    private static String madeKey(Pending pending) {
        ContextShape.Stance stance =
                ContextShape.Stance.ofSend(pending.context);
        String site = RunSpellings.strip(pending.site);
        if (pending.kind == ScheduleEvent.Kind.PUBLISH) {
            site = PUBLISHED_VERSION.matcher(site).replaceFirst("");
        }
        return pending.kind.name() + " " + site + " | " + (stance == null
                ? pending.context
                : stance.node() + "|" + shape(stance.context()));
    }

    private static final java.util.regex.Pattern PUBLISHED_VERSION =
            java.util.regex.Pattern.compile("@\\d+$");

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
            stateLocked(String.valueOf(file == null ? restFile : file),
                    "the schedule " + file + " / " + restFile + " could not"
                            + " be read (" + unreadable + "), so the replay"
                            + " runs free from its first event");
            return;
        }
    }

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
        slotKeys = new String[all.size()];
        slotContexts = new String[all.size()];
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
        PAST_LOOP.clear();
        MADE.clear();
        moves = 0L;
        letGoAt = 0L;
        stallSince = -1L;
        openHeld = 0;
        for (int index = 0; index < all.size(); index++) {
            ScheduleEvent event = all.get(index);
            boolean turn = StableEventNames.timedWaitTurn(event.context());
            slotContexts[index] = turn ? StableEventNames.turnFamily(event.context())
                    : event.context();
            slotKeys[index] = turn ? ScheduleEvent.key(event.kind(),
                    slotContexts[index], event.site()) : event.key();
            ArrayDeque<Integer> slots = SLOTS.get(slotKeys[index]);
            if (slots == null) {
                slots = new ArrayDeque<Integer>();
                SLOTS.put(slotKeys[index], slots);
            }
            slots.addLast(index);
            if (!slotOccurrenceOf(index).isEmpty()) {
                List<Integer> held = BY_OCCURRENCE.get(event.occurrence());
                if (held == null) {
                    held = new ArrayList<Integer>();
                    BY_OCCURRENCE.put(event.occurrence(), held);
                }
                held.add(index);
            }
            List<Integer> own = BY_CONTEXT.get(slotContexts[index]);
            if (own == null) {
                own = new ArrayList<Integer>();
                BY_CONTEXT.put(slotContexts[index], own);
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

    private static List<ScheduleEvent> heldReads(List<ScheduleEvent> events,
                                                 Set<String> written,
                                                 boolean readsHeld) {
        List<ScheduleEvent> kept = new ArrayList<ScheduleEvent>(events.size());
        for (ScheduleEvent event : events) {
            if (event.kind() != ScheduleEvent.Kind.READ
                    || readsHeld && written.contains(event.site())
                    && !StableEventNames.timedWaitTurn(event.context())) {
                kept.add(event);
            }
        }
        return kept;
    }

    private static boolean readsHeld() {
        return !FocusedReplay.pairs() && !FocusedReplay.confirming()
                && !RecordingPlant.planting();
    }

    static void writeMark(JsonObject row) {
        synchronized (LOCK) {
            writeLocked(row);
        }
    }

    static List<JsonObject> startupMarks() {
        List<JsonObject> marks = new ArrayList<JsonObject>();
        for (Path file : Arrays.asList(prefixFile(), suffixFile())) {
            if (file == null || !file.toFile().isFile()) continue;
            try {
                marks.addAll(SessionReader.readScheduleStartup(file));
            } catch (IOException unreadable) {
            }
        }
        return marks;
    }

    static void elsewhere() {
        synchronized (LOCK) {
            long self = Thread.currentThread().getId();
            if (firstBlocking < order.size() && !RELEASED.contains(self)) {
                ELSEWHERE.add(self);
            }
        }
    }

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

    private static Path besideWorker(String name) {
        String worker = FocusedReplay.workerDir();
        if (worker.isEmpty()) return null;
        Path beside = Paths.get(worker).resolve(name);
        return beside.toFile().isFile() ? beside : null;
    }

    static void stateProgress() {
        synchronized (LOCK) {
            if (order.isEmpty()) return;
        }
        EngineConsole.println("Causynth schedule: " + progress());
    }

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

    static void enforceForTests(List<ScheduleEvent> events,
                                List<ScheduleEvent> after,
                                boolean atWitness, boolean readsHeld) {
        synchronized (LOCK) {
            loaded = true;
            installLocked(events, after, atWitness, readsHeld);
        }
    }
}
