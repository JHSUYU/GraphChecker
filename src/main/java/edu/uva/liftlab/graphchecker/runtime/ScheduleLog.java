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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
 * them.  When the prefix is used up the replay runs free, exactly as a replay
 * with no prefix does, and goes on recording -- its own schedule is what its
 * children inherit.  When nothing is admitted for {@link #TIMEOUT_PROPERTY}
 * while some thread waits, the prefix cannot be held: the turnstile states
 * {@code SCHEDULE_DIVERGED} with the position and both events, releases every
 * waiter and runs free.  It never blocks the run for good.</p>
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

    /**
     * Shorter than the waits a workload makes for its own results (20 s is
     * the common bound): a prefix that cannot be held must be let go before
     * the workload gives up on what the held threads would have done.
     */
    static final long DEFAULT_TIMEOUT_MS = 15000L;

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
     */
    public static void observe(ScheduleEvent.Kind kind, String site) {
        if (kind == null || !recording()) return;
        mute();
        try {
            Pending event = pending(kind, site);
            if (event == null) return;
            synchronized (LOCK) {
                loadPrefixLocked();
                admitLocked(event.key);
                appendLocked(event);
            }
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
            if (!freeRun && !prefix.get(cursor).equals(event.key)) {
                long idle = System.currentTimeMillis() - lastAdmit;
                if (idle < timeoutMillis()) return false;
                divergeLocked(event.key);
            }
            if (!freeRun) advanceLocked();
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

        private Wake(Pending event) {
            this.event = event;
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

    /** Admits the wait's timeout WAKE if it is next NOW ({@link #tryObserve}). */
    static boolean tryAdmit(Wake wake) {
        if (wake == null) return true;
        mute();
        try {
            return tryAdmit(wake.event);
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
                if (!freeRun && prefix.get(cursor).equals(wake.event.key)) {
                    advanceLocked();
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
     * Admits one event: at once when the run is free, else when it is the
     * prefix's next one.
     *
     * <p>A thread whose event is not next waits on the lock -- which it
     * releases while it waits, so the thread whose event IS next can be
     * admitted.  The watchdog is PROGRESS, not a per-thread clock: a replay
     * on the concolic VM may take long between two events, and what shows the
     * prefix cannot be held is that nothing at all was admitted for the whole
     * timeout while someone waited.</p>
     */
    private static void admitLocked(String key) {
        if (freeRun) return;
        long timeout = timeoutMillis();
        waiting++;
        try {
            while (!freeRun && !prefix.get(cursor).equals(key)) {
                long idle = System.currentTimeMillis() - lastAdmit;
                if (idle >= timeout) {
                    divergeLocked(key);
                    break;
                }
                try {
                    LOCK.wait(Math.max(1L, Math.min(timeout - idle, 1000L)));
                } catch (InterruptedException interrupted) {
                    // The workload interrupted its own thread -- a shutdown,
                    // a cancelled task.  That is the workload's to see, not
                    // the prefix's to answer: this thread stops waiting for
                    // its turn, the flag is put back, and the prefix stands
                    // for everyone else.  The event is still written, where
                    // it happened, because it did.
                    Thread.currentThread().interrupt();
                    return;
                }
            }
        } finally {
            waiting--;
        }
        if (freeRun) return;
        advanceLocked();
    }

    /** One admission: the cursor moves, and every waiter looks again. */
    private static void advanceLocked() {
        cursor++;
        lastAdmit = System.currentTimeMillis();
        if (cursor >= prefix.size()) {
            // The prefix is used up: from here the replay runs free, which
            // is where its flip is.
            freeRun = true;
        }
        LOCK.notifyAll();
    }

    /**
     * Whether this replay is held to its prefix right now.
     *
     * <p>Only inside the recording window: the prefix is the window's order,
     * and a wait begun before the workload opened it -- an idle IPC
     * connection, a daemon's first sleep -- is the set-up's, which runs on
     * the wall clock exactly as it did when the prefix was recorded.  Taking
     * it over would return it at once, over and over, and time out whatever
     * it was idling for.</p>
     */
    public static boolean enforcing() {
        if (!CausynthTraceRecorder.recordingStarted()) return false;
        synchronized (LOCK) {
            loadPrefixLocked();
            return !freeRun;
        }
    }


    private static void divergeLocked(String actual) {
        if (freeRun) return;
        String expected = cursor < prefixEvents.size()
                ? prefixEvents.get(cursor).render() : "(end of prefix)";
        divergedAt = cursor;
        divergence = "at prefix position " + cursor + " of "
                + prefix.size() + " the run's next event was "
                + render(actual) + " and the prefix's was " + expected
                + "; nothing was admitted for " + timeoutMillis()
                + " ms, so every waiter is released and the replay runs free";
        freeRun = true;
        LOCK.notifyAll();
        try {
            RowRuntime.gap(GapKind.SCHEDULE_DIVERGED, GapClass.DIAGNOSTIC,
                    "schedule#" + cursor, divergence);
        } catch (Throwable unpublished) {
            System.err.println("Causynth schedule diverged: " + divergence);
        }
        System.err.println("Causynth schedule diverged: " + divergence);
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
     * Reads the prefix this replay was handed, once.
     *
     * <p>From the property, else the environment, else the file beside the
     * focus row in the worker directory.  No prefix, or enforcement switched
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
        if (file == null) return;
        try {
            List<ScheduleEvent> events = SessionReader.readSchedule(file);
            if (events.isEmpty()) return;
            List<String> keys = new ArrayList<String>(events.size());
            for (ScheduleEvent event : events) {
                keys.add(event.key());
            }
            prefixEvents = events;
            prefix = keys;
            cursor = 0;
            freeRun = false;
            lastAdmit = System.currentTimeMillis();
        } catch (IOException | RuntimeException unreadable) {
            System.err.println("Causynth could not read the schedule prefix "
                    + file + ": " + unreadable + "; the replay runs free");
        }
    }

    private static Path prefixFile() {
        String named = Text.safe(System.getProperty(PREFIX_PROPERTY));
        if (named.isEmpty()) named = Text.safe(System.getenv(PREFIX_ENV));
        if (!named.isEmpty()) return Paths.get(named);
        String worker = Text.safe(
                System.getenv("CAUSYNTH_CONCOLIC_WORKER_DIR"));
        if (!worker.isEmpty()) {
            Path beside = Paths.get(worker).resolve(PREFIX_FILE);
            if (beside.toFile().isFile()) return beside;
        }
        return null;
    }

    /** How far the replay got through its prefix, for its session. */
    public static String progress() {
        synchronized (LOCK) {
            if (prefix.isEmpty()) return "no prefix";
            return cursor + " of " + prefix.size() + " prefix events admitted"
                    + (divergedAt >= 0 ? ", diverged at " + divergedAt : "");
        }
    }

    /** Test hook: installs a prefix directly and starts enforcing it. */
    static void enforceForTests(List<ScheduleEvent> events) {
        synchronized (LOCK) {
            prefixLoaded = true;
            prefixEvents = new ArrayList<ScheduleEvent>(events);
            List<String> keys = new ArrayList<String>(events.size());
            for (ScheduleEvent event : events) keys.add(event.key());
            prefix = keys;
            cursor = 0;
            freeRun = keys.isEmpty();
            lastAdmit = System.currentTimeMillis();
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
            cursor = 0;
            freeRun = true;
            waiting = 0;
            lastAdmit = 0L;
            divergence = "";
            divergedAt = -1L;
            LOCK.notifyAll();
        }
    }
}
