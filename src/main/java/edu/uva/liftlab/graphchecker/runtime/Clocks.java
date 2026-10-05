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
 * the turn that sent it): inside the window the frontier's slot while the
 * line stands; before it, from the origin the first startup pass the order
 * marks, and from a pass on the pass itself -- time stands at the latest
 * pass reached until the next pass or the opening: what a node does once
 * it joined, the recording did at once (17's first heartbeats, in the
 * millisecond of the last registration), and the replay's lag after it is
 * its own slowness.  Past the line, after the window closed, or with no
 * order, nothing caps it.  So a replay's application time never runs ahead
 * of its place in the order (a slower replay waits at the cap where the
 * recording's heartbeat was not yet due), nor behind it (a turn its slot
 * released early reads at least its slot's instant), and two threads never
 * read time going back.  No read is keyed and none is written: a value set
 * at start-up and a read compared with it stand on one timeline (the parked
 * keyed replay mixed two, and handed threads sharing a key each other's
 * start-up times).</p>
 *
 * <p>A read never blocks: the cap holds time, never a thread.  A read that
 * finds a cap standing a stall -- the watchdog's test: a schedule timeout
 * with nothing computing, or eight whatever runs ({@code
 * ScheduleLog#stalledLocked}) -- asks for it to be lifted: before the window
 * it is, by name: time standing at a pass runs on toward the next mark, and
 * time standing at the next mark runs past it ({@link #liftLocked});
 * inside, only when no thread waits on the order, whose watchdog otherwise
 * moves the frontier ({@code ScheduleLog#clockAtCap}).  A slow start-up
 * computing past its cap is no stall: lifted, its time would run ahead of
 * the window's opening and stand there while the order caught up
 * (hdfs-11741, round TM1: lifted after a timeout, the window opened 62 s
 * of model time past its recorded instant).  Lifts are counted at exit.</p>
 */
public final class Clocks {
    private static final Object LOCK = new Object();
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
        final long baseMillis;
        final long hostAt;
        /** {@link Long#MAX_VALUE}: no cap. */
        final long hiNanos;
        final long hiMillis;
        /** What the cap is, as a lift names it; null: no cap. */
        final String cap;
        final boolean inWindow;
        /** When a read first stood at the cap (host nanos), 0 before. */
        final AtomicLong reached = new AtomicLong();

        Bounds(long baseNanos, long baseMillis, long hostAt, long hiNanos,
               long hiMillis, String cap, boolean inWindow) {
            this.baseNanos = baseNanos;
            this.baseMillis = baseMillis;
            this.hostAt = hostAt;
            this.hiNanos = hiNanos;
            this.hiMillis = hiMillis;
            this.cap = cap;
            this.inWindow = inWindow;
        }

        long nanos(long host) {
            return Math.min(hiNanos, baseNanos + (host - hostAt));
        }

        long millis(long host) {
            return Math.min(hiMillis, baseMillis
                    + TimeUnit.NANOSECONDS.toMillis(host - hostAt));
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
    /** Whether time standing at the latest pass reached was released
     *  toward the next mark by a stall. */
    private static boolean released;
    private static boolean windowSeen;
    /** When a read at a cap last asked for a lift (host nanos). */
    private static final AtomicLong ASKED = new AtomicLong();
    private static final LongAdder AT_CAP = new LongAdder();
    private static int liftsUnwaited;
    private static int liftsStartup;

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
            if (asks) atCap(at, host);
        }
        return (nanos ? LAST_NANOS : LAST_MILLIS).accumulateAndGet(ran,
                Math::max);
    }

    /**
     * A read stood at the cap; at most once a second, a lift is asked for:
     * inside the window of the order ({@code ScheduleLog#clockAtCap}),
     * before it here, once the cap stood a stall ({@code
     * ScheduleLog#capStalled}).
     */
    private static void atCap(Bounds at, long host) {
        at.reached.compareAndSet(0L, host);
        long asked = ASKED.get();
        if (asked != 0L && host - asked < ASK_NANOS
                || !ASKED.compareAndSet(asked, host)) {
            return;
        }
        if (at.inWindow) {
            ScheduleLog.clockAtCap();
            return;
        }
        long stood = host - at.reached.get();
        if (!ScheduleLog.capStalled(TimeUnit.NANOSECONDS.toMillis(stood))) {
            return;
        }
        String lifted;
        synchronized (LOCK) {
            lifted = bounds == at ? liftLocked() : null;
        }
        if (lifted != null) {
            ScheduleLog.diverged("clock#" + lifted, "the application's"
                    + " clocks stood " + TimeUnit.NANOSECONDS.toMillis(stood)
                    + " ms at the instant of " + lifted + ", marked in the"
                    + " order before the window, with nothing computing:"
                    + " they run on past it toward the next mark");
        }
    }

    /**
     * A startup cap is lifted: time standing at a pass runs on toward the
     * next mark; time standing at the next mark runs past it, the mark
     * counted as reached, on toward the one after.  Returns what it stood
     * at.
     */
    private static String liftLocked() {
        Mark at = null;
        Mark next = null;
        for (Mark mark : STARTUP) {
            if (!mark.reached) {
                next = mark;
                break;
            }
            at = mark;
        }
        Mark lifted = at != null && !released ? at : next;
        if (lifted == null) return null;
        lifted.reached = true;
        released = true;
        liftsStartup++;
        publishStartupLocked();
        return lifted.name;
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
                bounds = new Bounds(host, wall, host, Long.MAX_VALUE,
                        Long.MAX_VALUE, null, false);
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
            released = false;
            publishStartupLocked();
        }
    }

    /**
     * Before the window: from the origin up to the first mark, then
     * standing at the latest pass reached (until released, then up to the
     * next mark), each cap one tick past its instant.
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
        Mark cap = at == null || released ? next : at;
        moveLocked(at == null ? Long.MIN_VALUE : at.nanos,
                at == null ? Long.MIN_VALUE : at.millis,
                cap == null ? Long.MAX_VALUE : cap.nanos + TICK_NANOS,
                cap == null ? Long.MAX_VALUE : cap.millis + 1L,
                cap == null ? null : cap.name, false);
    }

    /**
     * The workload opened its window (its {@code index}-th): time reaches
     * the order's opening of it, and the order holds it from here.
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
                    Long.MAX_VALUE, Long.MAX_VALUE, null, true);
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
                    ticked(shifted(hiMillis, shiftMillis), 1L), cap, true);
        }
    }

    /** The window closed: nothing caps time any more. */
    static void free() {
        synchronized (LOCK) {
            if (bounds == null) return;
            moveLocked(Long.MIN_VALUE, Long.MIN_VALUE, Long.MAX_VALUE,
                    Long.MAX_VALUE, null, true);
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
                                   boolean inWindow) {
        Bounds now = bounds;
        long host = System.nanoTime();
        bounds = new Bounds(Math.max(loNanos, now.nanos(host)),
                Math.max(loMillis, now.millis(host)), host, hiNanos,
                hiMillis, cap, inWindow);
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
                    + (liftsUnwaited + liftsStartup) + " cap(s) lifted ("
                    + liftsUnwaited + " with no thread waiting on the order, "
                    + liftsStartup + " at a startup mark); at exit it ran "
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
            released = false;
            windowSeen = false;
            AT_CAP.reset();
            ASKED.set(0L);
            liftsUnwaited = 0;
            liftsStartup = 0;
        }
    }
}
