package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

/**
 * THE application's clocks.  The weave replaces every {@code
 * System.nanoTime()} and {@code System.currentTimeMillis()} of a woven class
 * with {@link #nanos} and {@link #millis}, in BOTH passes ({@code
 * CausynthPipeline#replaceClock}); a wrapper (Hadoop's {@code Time}) reads
 * through its body.  The JDK's own reads, a library jar's, and the engine's
 * (the watchdog, a timed wait's deadline) stay the host's.
 *
 * <p>A RECORDING reads the host, and stamps every schedule row with what the
 * application's clocks read there ({@code ScheduleLog}): its first read
 * ({@link ScheduleEvent#ORIGIN}), each event, each startup mark, the
 * window's opening ({@link ScheduleEvent#OPEN}).</p>
 *
 * <p>A REPLAY reads the recording's timeline, moved to start at its own
 * first read: {@code v = max(last, min(hi, lo + host time since lo moved))}.
 * {@code lo} is the stamp of the furthest point the replay has reached --
 * its origin, each startup pass it completed, its window's opening, each
 * slot settled at or before the order's frontier ({@code ScheduleLog
 * #publishTimeLocked}) -- and {@code hi} the stamp of the next it has not,
 * plus one tick of the millisecond clock ({@link #TICK_NANOS}: a read and
 * the event it decides stand in one millisecond of the recording, and the
 * replay's read that set what it compares may stand a fraction of one
 * later -- hdfs-adhoc-17's DataNodes set their next heartbeat 96 us before
 * the turn that sent it) inside the window, the frontier's slot while the
 * line stands; before it, with no tick, from the origin the first startup
 * pass the order marks, and from a pass on the pass itself -- time stands
 * at the latest pass reached until the next pass or the opening: what a
 * node does once
 * it joined, the recording did at once (17's first heartbeats, in the
 * millisecond of the last registration), and the replay's lag after it is
 * its own slowness.  Past the line, after the window closed, or with no
 * order, nothing caps it.  A timed wait moves time a nanosecond past where
 * it stood when the wait began, and a wait that ran its time out to its
 * deadline, never past the cap; the waiter's own millisecond clock moves one
 * millisecond ({@link #waited}).  So a replay's application time never runs
 * ahead of its place in the order but by those steps (a slower replay waits
 * at the cap where the recording's heartbeat was not yet due), never behind
 * it (a turn its slot released early reads at least its slot's instant), and
 * no thread reads time going back, nor its nanosecond clock behind what
 * another thread read before it.  No read is keyed and none is written: a value set
 * at start-up and a read compared with it stand on one timeline (the parked
 * keyed replay mixed two, and handed threads sharing a key each other's
 * start-up times).</p>
 *
 * <p>A read never blocks: the cap holds time, never a thread.  Before the
 * window, a timed wait that runs its time out past the cap time stands at,
 * with no startup taker held, lifts the cap to its deadline and no further
 * ({@link #waited}): at once at a mark time ran up to -- the start-up runs
 * slower than its recording, and code that sleeps and then measures how
 * long it slept needs that time to have passed (hdfs-11741, round TM13: no
 * startup mark before the opening, time stood at it while a DataNode's
 * heartbeat waits ran out and no heartbeat came due, two minutes in the
 * seed and in every obligation replay; hdfs-adhoc-22/25 stood as long at
 * their first registration) -- and at a startup pass this run made only
 * once time stood there a schedule timeout, since what a node does once it
 * joined the recording did at once (17's first heartbeats).  A held
 * startup taker's own hold bounds that wait.  Inside the window a cap is
 * lifted after a stall by the watchdog's test (a timeout with nothing
 * computing, or the ceiling, {@code ScheduleLog#stalledLocked}) and only
 * when no thread waits on the order, whose watchdog otherwise moves the
 * frontier ({@code ScheduleLog#clockAtCap}).  Lifts are counted at exit.</p>
 */
public final class Clocks {
    private static final Object LOCK = new Object();
    /** Per thread, the millisecond its {@code currentTimeMillis} reads stand
     *  on since its last timed wait ({@link #waited}). */
    private static final ThreadLocal<long[]> OWN_MILLIS =
            ThreadLocal.withInitial(() -> new long[] {Long.MIN_VALUE});
    /** Nanoseconds in a millisecond. */
    private static final long MILLI = TimeUnit.MILLISECONDS.toNanos(1L);
    /** What a cap allows past its instant: one millisecond tick. */
    static final long TICK_NANOS = TimeUnit.MILLISECONDS.toNanos(1L);
    /** One cap's ask for a lift at most this often. */
    private static final long ASK_NANOS = TimeUnit.SECONDS.toNanos(1L);

    /**
     * Where time stands since the replay last moved it: from {@code base}
     * at {@code hostAt} (the host's {@code nanoTime}) on, at most {@code
     * hi}, both on this run's timeline.
     */
    private static final class Bounds {
        final long baseNanos;
        /** The millisecond clock's base, in nanoseconds of wall time: its
         *  reading derives from it, so no move floors a fraction away and
         *  {@code currentTimeMillis} never drifts behind {@code nanoTime}. */
        final long baseWallNanos;
        final long hostAt;
        /** {@link Long#MAX_VALUE}: no cap. */
        final long hiNanos;
        final long hiMillis;
        /** What the cap is, as a lift names it; null: no cap. */
        final String cap;
        final boolean inWindow;
        /** Whether the cap is a startup pass this run made (time stands at
         *  it by design), not a mark time ran up to. */
        final boolean atPass;
        /** When a read first stood at the cap (host nanos), 0 before. */
        final AtomicLong reached = new AtomicLong();

        Bounds(long baseNanos, long baseWallNanos, long hostAt, long hiNanos,
               long hiMillis, String cap, boolean inWindow, boolean atPass) {
            this.baseNanos = baseNanos;
            this.baseWallNanos = baseWallNanos;
            this.hostAt = hostAt;
            this.hiNanos = hiNanos;
            this.hiMillis = hiMillis;
            this.cap = cap;
            this.inWindow = inWindow;
            this.atPass = atPass;
        }

        long nanos(long host) {
            return Math.min(hiNanos, baseNanos + (host - hostAt));
        }

        long wallNanos(long host) {
            long ran = baseWallNanos + (host - hostAt);
            return hiMillis == Long.MAX_VALUE ? ran
                    : Math.min(hiMillis * MILLI, ran);
        }

        long millis(long host) {
            return Math.floorDiv(wallNanos(host), MILLI);
        }
    }

    /** One mark of the order's timeline before its first window. */
    private static final class Mark {
        final String name;
        final long nanos;
        final long millis;
        boolean reached;

        Mark(String name, long nanos, long millis) {
            this.name = name;
            this.nanos = nanos;
            this.millis = millis;
        }
    }

    private static volatile boolean started;
    /** Null: the host's clocks (a recording; a replay whose order states
     *  no origin). */
    private static volatile Bounds bounds;
    private static final AtomicLong LAST_NANOS =
            new AtomicLong(Long.MIN_VALUE);
    private static final AtomicLong LAST_MILLIS =
            new AtomicLong(Long.MIN_VALUE);
    /** This run's host reading at its first read less the order's origin:
     *  what moves a recorded stamp onto this run's timeline. */
    private static long shiftNanos;
    private static long shiftMillis;
    /** Guarded by LOCK: the order's marks before its first window
     *  (startup passes, then its opening), and the opening of each. */
    private static final List<Mark> STARTUP = new ArrayList<Mark>();
    private static final Map<String, Mark> PASSES = new HashMap<String, Mark>();
    private static final List<Mark> OPENS = new ArrayList<Mark>();
    private static boolean windowSeen;
    /** When a read at a cap last asked for a lift (host nanos). */
    private static final AtomicLong ASKED = new AtomicLong();
    private static final LongAdder AT_CAP = new LongAdder();
    private static int liftsUnwaited;
    private static int liftsDeadline;
    /** The caps a deadline lifted, each named once. */
    private static final java.util.Set<String> LIFTED =
            new java.util.HashSet<String>();

    private Clocks() {
    }

    // ---- the application's reads ------------------------------------------

    /** {@code System.nanoTime()} of a woven class. */
    public static long nanos() {
        return read(true, true);
    }

    /** {@code System.currentTimeMillis()} of a woven class. */
    public static long millis() {
        return read(false, true);
    }

    /** What the application's {@code nanoTime} reads now, asking for no
     *  lift: a schedule row's stamp. */
    static long stampNanos() {
        return read(true, false);
    }

    /** What the application's {@code currentTimeMillis} reads now. */
    static long stampMillis() {
        return read(false, false);
    }

    private static long read(boolean nanos, boolean asks) {
        if (!started) start();
        Bounds at = bounds;
        if (at == null) {
            return nanos ? System.nanoTime() : System.currentTimeMillis();
        }
        long host = System.nanoTime();
        long ran = nanos ? at.nanos(host) : at.millis(host);
        if (ran >= (nanos ? at.hiNanos : at.hiMillis)) {
            AT_CAP.increment();
            at.reached.compareAndSet(0L, host);
            if (asks) atCap(at, host);
        }
        long read = (nanos ? LAST_NANOS : LAST_MILLIS).accumulateAndGet(ran,
                Math::max);
        return asks && !nanos ? Math.max(read, OWN_MILLIS.get()[0]) : read;
    }

    /**
     * A timed wait of {@code timeoutNanos} begins ({@code TimedWaits}):
     * where time stands now, the base of the floor {@link #waited} sets;
     * null with no model.
     */
    static long[] waitBegins(long timeoutNanos) {
        if (!started) start();
        if (bounds == null) return null;
        return new long[] {read(true, false), read(false, false),
                timeoutNanos, 0L};
    }

    /** The wait {@code began} ended by its timeout. */
    static void timedOut(long[] began) {
        if (began != null) began[3] = 1L;
    }

    /**
     * The timed wait {@code began} returned: time moves a nanosecond past
     * where it stood then, and past a timeout to the deadline on both
     * clocks, never past the cap; this thread's millisecond clock moves one
     * millisecond past where it stood then.
     *
     * <p>A real clock moves across a sleep, and code divides by what it
     * moved: Hadoop's GcTimeMonitor divides by its run's span on {@code
     * currentTimeMillis} after its first sleep, and with time standing at a
     * cap it died in every replay of rounds TM1 and TM2.  A wait that ran
     * its time out saw that time pass (hdfs-adhoc-17, round TM7: a
     * DataNode's wait for its next heartbeat ran out on the host while the
     * order still stood 0.6 s before it, and its turn found the heartbeat
     * not due); the order still holds what no recorded event has reached (a
     * wait the recording ended by a signal before its timeout finds its
     * deadline past the cap).</p>
     *
     * <p>Every thread's clock, since a value one thread sets another
     * compares: a step one thread alone saw put a DataNode actor's {@code
     * lastIBR} past what its DataXceiver then read, {@code sendImmediately}
     * found the received block's report not due, and hdfs-adhoc-25's client
     * met NotReplicatedYet where the recording logged its edit (round TM9:
     * 32 give-ups against 8 with no model).  A nanosecond, so the waits of
     * a whole start-up move no decision made in milliseconds: time creeping
     * on for every reader ran 17's start-up 29 ms past its first
     * registration (round TM5), and one millisecond past a pass set a
     * heartbeat 0.4 ms late (round TM6).  The millisecond clock moves for the
     * waiter alone, from where every thread's stood: a step every sleep
     * added for everyone would carry it a millisecond per sleep.</p>
     */
    static void waited(long[] began) {
        Bounds at = bounds;
        if (began == null || at == null) return;
        if (began[3] != 0L && at.cap != null && !at.inWindow
                && began[2] > at.hiNanos - began[0]
                && began[2] < Long.MAX_VALUE - began[0]
                && (!at.atPass || stoodATimeout(at))
                && !StartupOrder.holding()) {
            at = liftedTo(began);
        }
        long nanos = began[0] + 1L;
        long millis = Long.MIN_VALUE;
        if (began[3] != 0L && at.cap != null) {
            nanos = Math.max(nanos, upTo(began[0], began[2], at.hiNanos));
            millis = upTo(began[1], TimeUnit.NANOSECONDS.toMillis(began[2]),
                    at.hiMillis);
        }
        LAST_NANOS.accumulateAndGet(nanos, Math::max);
        LAST_MILLIS.accumulateAndGet(millis, Math::max);
        long[] own = OWN_MILLIS.get();
        own[0] = Math.max(own[0], began[1] + 1L);
    }

    /** Whether time has stood at {@code at}'s cap one schedule timeout. */
    private static boolean stoodATimeout(Bounds at) {
        long since = at.reached.get();
        return since != 0L && System.nanoTime() - since
                >= TimeUnit.MILLISECONDS.toNanos(ScheduleLog.timeoutMillis());
    }

    /** {@code from + by}, at most {@code cap}. */
    private static long upTo(long from, long by, long cap) {
        return by >= cap - from ? cap : from + by;
    }

    /**
     * A read stood at the cap: inside the window of the order, at most once
     * a second, a lift is asked for ({@code ScheduleLog#clockAtCap}).
     */
    private static void atCap(Bounds at, long host) {
        if (!at.inWindow) return;
        long asked = ASKED.get();
        if (asked != 0L && host - asked < ASK_NANOS
                || !ASKED.compareAndSet(asked, host)) {
            return;
        }
        ScheduleLog.clockAtCap();
    }

    /**
     * Before the window, the timed wait {@code began} ran its time out past
     * the cap time stood at: the cap moves to its deadline, no further,
     * time standing where it stood until then.  Returns where time is
     * bounded now.
     */
    private static Bounds liftedTo(long[] began) {
        long nanos = began[0] + began[2];
        long millis = began[1] + TimeUnit.NANOSECONDS.toMillis(began[2]);
        String stood;
        boolean first;
        Bounds now;
        synchronized (LOCK) {
            now = bounds;
            if (now == null || now.inWindow || now.cap == null
                    || now.hiNanos >= nanos) {
                return now;
            }
            // Named after the mark it was lifted from, so each mark's
            // lifts are one row however many waits move it on.
            stood = now.cap;
            moveLocked(now.hiNanos, now.hiMillis, nanos, millis, stood,
                    false, false);
            liftsDeadline++;
            first = LIFTED.add(stood);
            now = bounds;
        }
        if (first) {
            ScheduleLog.diverged("clock#" + stood, "before the window the"
                    + " application's clocks stood at " + stood + " while "
                    + Thread.currentThread().getName() + "'s timed wait of "
                    + TimeUnit.NANOSECONDS.toMillis(began[2]) + " ms ran out"
                    + " past it: time runs on to each such wait's deadline"
                    + " (every lift counted at exit)");
        }
        return now;
    }

    // ---- the replay's place, as the order moves it ------------------------

    /**
     * The first read: a recording, or a replay whose order states no
     * origin, reads the host; a replay reads its order's timeline from here.
     * Every run states its origin.
     */
    private static void start() {
        long nanos;
        long millis;
        synchronized (LOCK) {
            if (started) return;
            long host = System.nanoTime();
            long wall = System.currentTimeMillis();
            List<JsonObject> marks = ScheduleLog.timelineMarks();
            JsonObject origin = null;
            for (JsonObject mark : marks) {
                if (ScheduleEvent.ORIGIN.equals(mark.get("mark")
                        .getAsString())) {
                    origin = mark;
                    break;
                }
            }
            if (origin != null) {
                shiftNanos = host - RowCodec.scheduleNanos(origin);
                shiftMillis = wall - RowCodec.scheduleMillis(origin);
                load(marks);
                bounds = new Bounds(host, wall * MILLI, host, Long.MAX_VALUE,
                        Long.MAX_VALUE, null, false, false);
                publishStartupLocked();
                Runtime.getRuntime().addShutdownHook(new Thread(
                        () -> EngineConsole.println("Causynth clocks: "
                                + progress()), "causynth-clocks"));
            } else if (!marks.isEmpty() || ScheduleLog.ordered()) {
                ScheduleLog.diverged("clock#origin", "the order this replay"
                        + " follows states no first clock read: the"
                        + " application reads the host's clocks");
            }
            started = true;
            nanos = host;
            millis = wall;
        }
        ScheduleLog.writeMark(RowCodec.writeScheduleTime(
                ScheduleEvent.ORIGIN, nanos, millis));
    }

    /** Files the order's startup passes and openings, on this timeline. */
    private static void load(List<JsonObject> marks) {
        Map<String, Integer> passes = new HashMap<String, Integer>();
        for (JsonObject row : marks) {
            String kind = row.get("mark").getAsString();
            long nanos = RowCodec.scheduleNanos(row) + shiftNanos;
            long millis = RowCodec.scheduleMillis(row) + shiftMillis;
            if (ScheduleEvent.OPEN.equals(kind)) {
                Mark open = new Mark("the window's opening " + OPENS.size(),
                        nanos, millis);
                if (OPENS.isEmpty()) STARTUP.add(open);
                OPENS.add(open);
            } else if (ScheduleEvent.STARTUP.equals(kind)
                    && OPENS.isEmpty()) {
                String step = row.get("step").getAsString();
                String who = row.get("who").getAsString();
                int n = passes.merge(step + "\n" + who, 1, Integer::sum) - 1;
                Mark pass = new Mark("startup " + step + " " + who + "#" + n,
                        nanos, millis);
                STARTUP.add(pass);
                PASSES.put(step + "\n" + who + "#" + n, pass);
            }
        }
    }

    /**
     * A startup pass ({@code who#n} of {@code step}) completed or was given
     * up before the window: time reaches its mark.
     */
    static void passed(String step, String pass) {
        synchronized (LOCK) {
            Mark mark = PASSES.get(step + "\n" + pass);
            if (mark == null || mark.reached || windowSeen
                    || bounds == null) {
                return;
            }
            mark.reached = true;
            publishStartupLocked();
        }
    }

    /**
     * Before the window: from the origin up to the first mark, then
     * standing at the latest pass reached (until the next pass or the
     * next mark), each cap exactly at its instant.
     */
    private static void publishStartupLocked() {
        Mark at = null;
        Mark next = null;
        for (Mark mark : STARTUP) {
            if (!mark.reached) {
                next = mark;
                break;
            }
            at = mark;
        }
        // Exactly at the mark, no tick: what a node read after it joined,
        // it read after the pass (hdfs-adhoc-17, round TM6: one tick past
        // its pass, a DataNode set its next heartbeat 0.4 ms past the
        // recording's, and its turn #1 found it not due).
        Mark cap = at != null ? at : next;
        moveLocked(at == null ? Long.MIN_VALUE : at.nanos,
                at == null ? Long.MIN_VALUE : at.millis,
                cap == null ? Long.MAX_VALUE : cap.nanos,
                cap == null ? Long.MAX_VALUE : cap.millis,
                cap == null ? null : cap.name, false, cap != null && cap == at);
    }

    /**
     * The workload opened its window (its {@code index}-th): time reaches
     * the order's opening of it, standing there; the order caps it at once
     * after ({@code ScheduleLog#windowOpened}, under its lock, which owns
     * the cap: an order read after the opening let time run 2-12 s free,
     * round TM3).
     */
    static void windowOpened(int index) {
        if (!started) start();
        synchronized (LOCK) {
            windowSeen = true;
            if (bounds == null) return;
            Mark open = index >= 1 && index <= OPENS.size()
                    ? OPENS.get(index - 1) : null;
            moveLocked(open == null ? Long.MIN_VALUE : open.nanos,
                    open == null ? Long.MIN_VALUE : open.millis,
                    open == null ? Long.MAX_VALUE : open.nanos + TICK_NANOS,
                    open == null ? Long.MAX_VALUE : open.millis + 1L,
                    open == null ? null : open.name, true, false);
        }
    }

    /**
     * Inside the window: the order reached the stamp {@code lo} and not yet
     * {@code hi} (recorded, {@link Long#MIN_VALUE} / {@link Long#MAX_VALUE}
     * for none); {@code cap} names {@code hi}.
     */
    static void reached(long loNanos, long loMillis, long hiNanos,
                        long hiMillis, String cap) {
        synchronized (LOCK) {
            if (bounds == null) return;
            moveLocked(shifted(loNanos, shiftNanos),
                    shifted(loMillis, shiftMillis),
                    ticked(shifted(hiNanos, shiftNanos), TICK_NANOS),
                    ticked(shifted(hiMillis, shiftMillis), 1L), cap, true,
                    false);
        }
    }

    /** The window closed: nothing caps time any more. */
    static void free() {
        synchronized (LOCK) {
            if (bounds == null) return;
            moveLocked(Long.MIN_VALUE, Long.MIN_VALUE, Long.MAX_VALUE,
                    Long.MAX_VALUE, null, true, false);
        }
    }

    /** A cap inside the window was lifted (no thread waits on the order). */
    static void liftedUnwaited() {
        synchronized (LOCK) {
            liftsUnwaited++;
        }
    }

    /** A cap one tick past its instant; none stays none. */
    private static long ticked(long cap, long tick) {
        return cap == Long.MAX_VALUE ? cap : cap + tick;
    }

    private static long shifted(long stamp, long shift) {
        return stamp == Long.MIN_VALUE || stamp == Long.MAX_VALUE ? stamp
                : stamp + shift;
    }

    /**
     * Time moves on from where it stands now, or from {@code lo} when that
     * is later, never past {@code hi}: it never jumps back, and never jumps
     * ahead but to a place the replay reached.
     */
    private static void moveLocked(long loNanos, long loMillis, long hiNanos,
                                   long hiMillis, String cap,
                                   boolean inWindow, boolean atPass) {
        Bounds now = bounds;
        long host = System.nanoTime();
        bounds = new Bounds(Math.max(loNanos, now.nanos(host)),
                Math.max(loMillis == Long.MIN_VALUE ? Long.MIN_VALUE
                        : loMillis * MILLI, now.wallNanos(host)), host, hiNanos,
                hiMillis, cap, inWindow, atPass);
    }

    /** The replay's account of its clocks, at exit. */
    static String progress() {
        synchronized (LOCK) {
            Bounds at = bounds;
            long host = System.nanoTime();
            long behind = at == null ? 0L
                    : TimeUnit.NANOSECONDS.toMillis(host - at.nanos(host));
            return "the application read its order's timeline; "
                    + AT_CAP.sum() + " read(s) stood at a cap, "
                    + (liftsUnwaited + liftsDeadline) + " cap(s) lifted ("
                    + liftsUnwaited + " with no thread waiting on the order, "
                    + liftsDeadline + " to a timed wait's deadline before the"
                    + " window); at exit it ran "
                    + behind + " ms behind the host";
        }
    }

    /** Test seam: a fresh JVM. */
    static void resetForTests() {
        synchronized (LOCK) {
            started = false;
            bounds = null;
            LAST_NANOS.set(Long.MIN_VALUE);
            LAST_MILLIS.set(Long.MIN_VALUE);
            shiftNanos = 0L;
            shiftMillis = 0L;
            STARTUP.clear();
            PASSES.clear();
            OPENS.clear();
            LIFTED.clear();
            windowSeen = false;
            AT_CAP.reset();
            ASKED.set(0L);
            OWN_MILLIS.remove();
            liftsUnwaited = 0;
            liftsDeadline = 0;
        }
    }
}
