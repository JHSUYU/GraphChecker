package edu.uva.liftlab.graphchecker.smt;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

/**
 * THE z3 driver: one query text in, one answer out.  It launches the
 * process, enforces the budget, drains both streams, and parses verdict,
 * model and errors; what an answer MEANS is the caller's policy.
 *
 * <p>Only {@code sat}/{@code unsat} is decided ({@link Answer#decided()});
 * a timeout, {@code unknown} or {@code (error ...)} is not a refutation.</p>
 *
 * <p>Model, core and reason are each asked in their OWN run after the
 * verdict: {@code (get-value ...)} on an unsat query makes z3 print a
 * routine error that would hide real ones.  Only the core run tracks the
 * named assertions ({@link #CORE_TRACKING}).</p>
 *
 * <p>Every run is two z3 processes, one per arithmetic engine
 * ({@link #ARITHMETIC}), and its answer the first one DECIDED; the other is
 * killed.  z3's time on one query swings by orders of magnitude with the
 * engine (SOLR-18413 r9's composed query: past 30 minutes under
 * {@code smt.arith.solver 2}, a second under 6), and neither is the faster
 * one on every query (2 closes the nested {@code mod 2^32} terms wrapping
 * arithmetic writes, where 6 can branch for minutes).</p>
 */
public final class Z3 {

    /** The budget one question gets when the campaign names none. */
    public static final long DEFAULT_TIMEOUT_MILLIS = 20_000L;

    /**
     * What makes z3 track named assertions for an unsat core, set by the
     * run that asks for the core and by no other.  Tracked, every named
     * assertion stays behind a literal of its own and z3 simplifies nothing
     * across them: a disjunct whose selector the rest forces false is still
     * searched.  The verdict is the same either way; the time is not
     * (hdfs-17967-pathA r4: 40 s a sat valuation tracked, 1 s untracked;
     * hdfs-17899-bug3 r4: over 20 minutes against 0.1 s).  A query states
     * no such option itself.
     */
    static final String CORE_TRACKING =
            "(set-option :produce-unsat-cores true)\n";

    /** How z3 says it could not read the query. */
    private static final String ERROR = "(error ";

    /** The status of an answer no process lived long enough to print. */
    private static final String TIMEOUT = "timeout";

    /**
     * The arithmetic engines a run races ({@code smt.arith.solver}), the
     * preferred first: the one every lowered query states
     * ({@code VmTermLowering#preamble}), so a published query read alone is
     * the question its preferred run answered.
     */
    static final int[] ARITHMETIC = {2, 6};

    /** How a query states its arithmetic engine: this, its digits, ")". */
    static final String ARITHMETIC_OPENING = "(set-option :smt.arith.solver ";

    /**
     * How long the preferred engine may still answer after the other one
     * decided: as long again as that one took, and at least this.  Within
     * it the preferred answer wins, so a query the preferred engine alone
     * decides promptly answers as it did before the race, model and all.
     */
    static final long PREFERRED_GRACE_MILLIS = 1000L;

    /** How often a race looks at the engine it is not waiting on. */
    private static final long POLL_MILLIS = 20L;

    /** What one question answered. */
    public static final class Answer {
        private final String status;
        private final Map<String, String> values;
        private final List<String> core;
        /** Whether a core run said unsat and named the core. */
        private final boolean coreKnown;
        private final String reason;

        private Answer(String status, Map<String, String> values,
                       List<String> core, boolean coreKnown, String reason) {
            this.status = status;
            this.values = Collections.unmodifiableMap(values);
            this.core = Collections.unmodifiableList(core);
            this.coreKnown = coreKnown;
            this.reason = reason;
        }

        /** The first line z3 printed: sat, unsat, unknown, or neither. */
        public String status() {
            return status;
        }

        public boolean sat() {
            return "sat".equals(status);
        }

        public boolean unsat() {
            return "unsat".equals(status);
        }

        /** Whether the solver answered the question at all. */
        public boolean decided() {
            return sat() || unsat();
        }

        /** Whether the budget ran out before z3 said anything. */
        public boolean timedOut() {
            return TIMEOUT.equals(status);
        }

        /**
         * Why the solver did not decide ({@code :reason-unknown}), or "";
         * asked only of an undecided, non-timeout answer.
         */
        public String reason() {
            return reason;
        }

        /** Symbol -> the value the model gave it, for the symbols asked. */
        public Map<String, String> values() {
            return values;
        }

        /** The names of the conjuncts one unsat answer closed on; empty
         *  where {@link #coreKnown} is not. */
        public List<String> core() {
            return core;
        }

        /**
         * Whether {@link #core} is the core: asked, and its own run said
         * unsat.  A core run that timed out, found no room or answered
         * unknown names nothing, which is not the empty core: what the
         * answer rests on is then unknown.
         */
        public boolean coreKnown() {
            return coreKnown;
        }

        /**
         * What a disjunction whose every disjunct {@code refuted} answered
         * unsat answers: unsat, its core the union of theirs (each model
         * takes one disjunct, which its own core refutes), known only where
         * every one of theirs is.
         */
        public static Answer unsatOfAll(List<Answer> refuted) {
            Set<String> core = new LinkedHashSet<String>();
            boolean known = true;
            for (Answer each : refuted) {
                core.addAll(each.core());
                known &= each.coreKnown();
            }
            return new Answer("unsat", Collections.<String, String>emptyMap(),
                    new ArrayList<String>(core), known, "");
        }

        @Override
        public String toString() {
            return status + (values.isEmpty() ? "" : " " + values)
                    + (core.isEmpty() ? "" : " core" + core);
        }
    }

    private final Path z3;
    private final long timeoutMillis;
    /** Asks may run on several threads, each its own z3 process. */
    private final AtomicInteger runs = new AtomicInteger();
    private final Set<String> errors = new TreeSet<String>();

    public Z3(Path executable, long timeoutMillis) {
        this.z3 = executable == null ? Paths.get("z3") : executable;
        this.timeoutMillis = timeoutMillis <= 0L
                ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis;
    }

    /** The budget a question gets when its ask names none. */
    public long timeoutMillis() {
        return timeoutMillis;
    }

    /** How many times z3 was asked; the cost of one composition. */
    public int runs() {
        return runs.get();
    }

    /**
     * Every {@code (error ...)} z3 answered, over every ask including the
     * auxiliary ones: an error means z3 could not read the query, and one
     * anywhere invalidates the claim.
     */
    public List<String> errors() {
        synchronized (errors) {
            return new ArrayList<String>(errors);
        }
    }

    /**
     * One question: this query, this model request, this core request.
     *
     * @param query         the declarations and assertions, without a
     *                      {@code check-sat}
     * @param modelSymbols  the constants whose value a sat answer must carry
     * @param wantCore      whether an unsat answer should name its core
     */
    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore) {
        return ask(query, modelSymbols, wantCore, 0L);
    }

    /** The same ask with its verdict under its own budget. */
    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        String text = query == null ? "" : query;
        return ask(output -> output.write(text), modelSymbols, wantCore,
                budgetMillis);
    }

    /** The same ask over a query written out rather than held. */
    public Answer ask(ArtifactIO.Body query, List<String> modelSymbols,
                      boolean wantCore) {
        return ask(query, modelSymbols, wantCore, 0L);
    }

    /**
     * The same ask with its verdict under its own budget ({@code <= 0}: the
     * instance's).  A decided verdict's model and core runs keep the
     * instance's: each solves again, and a tracked core run can take far
     * longer than its verdict ({@link #CORE_TRACKING}).  Same instance, so
     * the run counter and error set stay whole.
     *
     * <p>The query is WRITTEN to each z3, never copied into one text per
     * run: a composition's body runs past 200 MB, asked on
     * many threads at once ({@code compose.Disjunction}), and a copy per
     * ask (the text, the text with its command, its bytes) ran the
     * composer out of an 8 GB heap (hdfs-11741 m1).  What each run reads
     * back is z3's answer to the one command after it.</p>
     */
    public Answer ask(ArtifactIO.Body query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        long budget = budgetMillis > 0L ? budgetMillis : timeoutMillis;
        String status = firstLine(run("", query, "(check-sat)\n", budget));
        Map<String, String> values = Collections.emptyMap();
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
            values = parseValues(run("", query, valueCommand(modelSymbols),
                    timeoutMillis));
        }
        List<String> core = Collections.emptyList();
        boolean coreKnown = false;
        if (wantCore && "unsat".equals(status)) {
            // A core run that did not say unsat (its budget ran out, no
            // host had room, it answered unknown) names no core.
            String printed = run(CORE_TRACKING, query,
                    "(check-sat)\n(get-unsat-core)\n", timeoutMillis);
            coreKnown = "unsat".equals(firstLine(printed));
            if (coreKnown) core = parseCore(printed);
        }
        // Not after a timeout: it would spend the budget again for "".
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)
                && !TIMEOUT.equals(status)) {
            reason = parseReason(run("", query,
                    "(check-sat)\n(get-info :reason-unknown)\n", budget));
        }
        return new Answer(status, values, core, coreKnown, reason);
    }

    /**
     * The exact text {@link #ask} sends for a model; published artifacts
     * must use it so the file is the question actually solved.
     */
    public static String modelQuery(String query, List<String> modelSymbols) {
        return (query == null ? "" : query) + valueCommand(modelSymbols);
    }

    /** The commands that ask a sat query for these constants' values. */
    private static String valueCommand(List<String> modelSymbols) {
        StringBuilder text = new StringBuilder("(check-sat)\n(get-value (");
        if (modelSymbols != null) {
            for (String symbol : modelSymbols) {
                text.append(' ').append(symbol);
            }
        }
        return text.append("))\n").toString();
    }

    // ------------------------------------------------------------------
    // The process.
    // ------------------------------------------------------------------

    /**
     * How far past its budget a z3 stops itself ({@code -T}, whole seconds).
     * The driver stops z3 at the budget; z3's own clock matters only when
     * the driver is still there but no longer driving (a JVM that hangs);
     * one that died takes its z3s with it ({@link #DIES_WITH_ITS_DRIVER}:
     * lift06 once ran four {@code z3 -in -smt2} of 2.4 GB each 8.5 h past
     * their JVMs).  Past the budget, so a live driver is always the one that
     * stops z3.
     */
    static final long ORPHAN_MARGIN_SECONDS = 10L;

    /**
     * The z3 processes running now, each with its pid (-1: unknown), whose
     * resident memory {@link #enter} reads.  A JVM that ends (a bound's or
     * a stop's TERM) takes them with it at once; one killed outright runs
     * no hook, and the kernel kills its z3s ({@link #DIES_WITH_ITS_DRIVER}).
     */
    private static final Map<Process, Integer> LIVE =
            new ConcurrentHashMap<Process, Integer>();

    /**
     * What every z3 is started under: the kernel sends it KILL when the
     * thread that started it is gone ({@code PR_SET_PDEATHSIG}), so no z3
     * outlives its JVM, however that JVM ended -- a KILL, the kernel's OOM
     * killer -- where a shutdown hook never runs and z3's own clock
     * ({@link #hardTimeout}) let an orphan run out a 30-minute budget.  The
     * thread that starts a run waits for it and kills it on its way out
     * ({@link #run}), so the signal reaches only orphans.
     */
    static final String[] DIES_WITH_ITS_DRIVER =
            {"setpriv", "--pdeathsig", "KILL", "--"};

    /**
     * How full a host's memory may be, in percent, before another z3
     * starts: the ceiling every start of a campaign keeps
     * ({@code CAUSYNTH_HOST_MAX_USED_PCT}; tools/lib/gc-env.sh states the
     * owner's 70 where nothing else does, and so does this where no script
     * started the JVM).  One that is no percentage is refused.
     */
    static final int CEILING_PERCENT =
            ceilingPercent(System.getenv("CAUSYNTH_HOST_MAX_USED_PCT"));

    static int ceilingPercent(String stated) {
        if (stated == null) return 70;
        String text = stated.trim();
        int percent = text.matches("[0-9]{1,3}") ? Integer.parseInt(text) : 0;
        if (percent < 1 || percent > 100) {
            throw new IllegalStateException("CAUSYNTH_HOST_MAX_USED_PCT must"
                    + " be a percentage in 1..100: \"" + stated + "\"");
        }
        return percent;
    }

    /** Runs in flight in this JVM, each its two engines. */
    private static final AtomicInteger RUNNING = new AtomicInteger();

    /** What a run waiting for room waits on, and how often it looks. */
    private static final Object ROOM = new Object();
    private static final long ROOM_POLL_MILLIS = 500L;

    /**
     * The most resident memory one z3 of this JVM has held, in kB, read as
     * runs are admitted; until one is read, what a z3 is taken to grow to
     * (i1's per-path z3s held 0.1 GB, m1's 1 GB, a whole 124 MB body 0.4).
     */
    private static long largestKb = 256L * 1024L;

    /**
     * Waits until this host has room for one more run and counts it in:
     * true; false when interrupted first.  Room: the host's available
     * memory, less what each running z3 may still grow to (the largest any
     * z3 of this JVM has held) and two such z3s for the new run, at least
     * the share {@link #CEILING_PERCENT} keeps free.  A JVM with no run in
     * flight starts one anyway: it holds nothing it could give back by
     * waiting.  A composition asks many paths at once
     * ({@code compose.Disjunction}): sixteen z3s of hdfs-11741 m1's paths,
     * a GB each beside the composer's 15, took a host to 82 %.
     */
    private static boolean enter() {
        synchronized (ROOM) {
            while (RUNNING.get() > 0 && !hostHasRoom(owed())) {
                try {
                    ROOM.wait(ROOM_POLL_MILLIS);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    return false;
                }
            }
            RUNNING.incrementAndGet();
            return true;
        }
    }

    private static void leave() {
        RUNNING.decrementAndGet();
        synchronized (ROOM) {
            ROOM.notifyAll();
        }
    }

    /**
     * In kB, what this JVM's z3s may still take: each running one up to the
     * largest any has held, and the new run's two engines that much each.
     */
    private static long owed() {
        long held = 0L;
        List<Long> each = new ArrayList<Long>();
        for (int pid : LIVE.values()) {
            long kb = residentKb(pid);
            if (kb < 0L) continue;
            each.add(kb);
            largestKb = Math.max(largestKb, kb);
        }
        for (long kb : each) held += largestKb - kb;
        return held + 2L * largestKb;
    }

    /** Whether MemAvailable less {@code owedKb} is at least what the
     *  ceiling keeps free; a host whose memory cannot be read is taken to
     *  have room. */
    static boolean hostHasRoom(long owedKb) {
        long total = -1L;
        long available = -1L;
        try {
            for (String line : java.nio.file.Files.readAllLines(
                    Paths.get("/proc/meminfo"), StandardCharsets.UTF_8)) {
                if (line.startsWith("MemTotal:")) total = kilobytes(line);
                if (line.startsWith("MemAvailable:")) {
                    available = kilobytes(line);
                }
            }
        } catch (IOException | RuntimeException unreadable) {
            return true;
        }
        return total <= 0L || available < 0L || (available - owedKb) * 100L
                >= total * (100L - CEILING_PERCENT);
    }

    /** A process's resident memory in kB, or -1 once it is gone. */
    private static long residentKb(int pid) {
        if (pid <= 0) return -1L;
        try {
            for (String line : java.nio.file.Files.readAllLines(Paths.get(
                    "/proc", Integer.toString(pid), "status"),
                    StandardCharsets.UTF_8)) {
                if (line.startsWith("VmRSS:")) return kilobytes(line);
            }
        } catch (IOException | RuntimeException gone) {
            return -1L;
        }
        return -1L;
    }

    private static long kilobytes(String line) {
        String[] words = line.trim().split("\\s+");
        return words.length < 2 ? -1L : Long.parseLong(words[1]);
    }

    /**
     * A started process's pid: Java 8 states it only in its UNIXProcess's
     * own field.  -1 where it cannot be read: that z3's memory is then not
     * counted (the run is still bounded by its driver's budget).
     */
    private static int pidOf(Process process) {
        try {
            java.lang.reflect.Field pid =
                    process.getClass().getDeclaredField("pid");
            pid.setAccessible(true);
            return pid.getInt(process);
        } catch (ReflectiveOperationException | RuntimeException unknown) {
            return -1;
        }
    }

    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            for (Process process : LIVE.keySet()) process.destroyForcibly();
        }, "graphchecker-z3-reaper"));
    }

    /** z3's own wall clock for one run of {@code budgetMillis}. */
    static String hardTimeout(long budgetMillis) {
        return "-T:" + ((budgetMillis + 999L) / 1000L + ORPHAN_MARGIN_SECONDS);
    }

    /**
     * One run: the query under each arithmetic engine ({@link #ARITHMETIC}),
     * two z3 processes, and the first DECIDED answer -- the preferred
     * engine's when it decides within {@link #PREFERRED_GRACE_MILLIS} of the
     * other's -- with the other killed.  Both undecided: the preferred
     * one's answer.  Both share the budget, enforced here; z3's own
     * ({@link #hardTimeout}) only outlives a driver that hangs.  A run
     * starts once its host has room ({@link #enter}); an interrupted one
     * answers as a timeout, its z3s killed.  Each run says what it answered
     * and how long it took, waiting for room included, on stderr: a quiet
     * log is then one run's own wall, bounded by its budget.
     */
    private String run(String prefix, ArtifactIO.Body query, String suffix,
                       long budgetMillis) {
        int run = runs.incrementAndGet();
        long started = System.nanoTime();
        String answer = TIMEOUT;
        if (enter()) {
            try {
                answer = raced(prefix, query, suffix, budgetMillis);
            } finally {
                leave();
            }
        }
        String said = firstLine(answer);
        System.err.println("z3 run " + run + " (" + command(suffix) + "): "
                + (said.length() > 40 ? said.substring(0, 40) + "..." : said)
                + " in " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime()
                - started) / 1000.0 + " s");
        return answer;
    }

    /** The command a run's suffix asks: its last line's name. */
    private static String command(String suffix) {
        String[] lines = suffix.trim().split("\n");
        String last = lines[lines.length - 1].replace("(", "").trim();
        int end = last.indexOf(' ');
        return (end < 0 ? last : last.substring(0, end)).replace(")", "");
    }

    /** {@link #run} once it has room: both engines, raced. */
    private String raced(String prefix, ArtifactIO.Body query, String suffix,
                         long budgetMillis) {
        long started = System.nanoTime();
        long deadline = started
                + TimeUnit.MILLISECONDS.toNanos(budgetMillis);
        Process[] engines = new Process[ARITHMETIC.length];
        List<AtomicReference<String>> read =
                new ArrayList<AtomicReference<String>>();
        List<Thread> readers = new ArrayList<Thread>();
        try {
            for (int at = 0; at < engines.length; at++) {
                AtomicReference<String> output =
                        new AtomicReference<String>(null);
                read.add(output);
                engines[at] = launch(ARITHMETIC[at], prefix, query, suffix,
                        budgetMillis, output, readers);
            }
            return answerOf(race(engines, read, readers, started, deadline));
        } finally {
            for (Process engine : engines) {
                if (engine == null) continue;
                engine.destroyForcibly();
                LIVE.remove(engine);
            }
        }
    }

    /**
     * The printed answer {@link #run} returns, or {@link #TIMEOUT}: the
     * preferred engine's as soon as it decides; the other's once it has
     * decided and the preferred one has not within its grace; when neither
     * decides, the preferred engine's.
     */
    private static String race(Process[] engines,
                               List<AtomicReference<String>> read,
                               List<Thread> readers, long started,
                               long deadline) {
        long otherDecidedAt = 0L;
        try {
            while (true) {
                String preferred = finished(engines[0], read.get(0),
                        readers.get(0));
                if (preferred != null && decided(preferred)) return preferred;
                String other = finished(engines[1], read.get(1),
                        readers.get(1));
                long now = System.nanoTime();
                if (other != null && decided(other)) {
                    if (otherDecidedAt == 0L) otherDecidedAt = now;
                    long took = otherDecidedAt - started;
                    long grace = Math.max(took, TimeUnit.MILLISECONDS
                            .toNanos(PREFERRED_GRACE_MILLIS));
                    if (preferred != null || now - otherDecidedAt >= grace) {
                        return other;
                    }
                }
                if (preferred != null && other != null) return preferred;
                if (now >= deadline) return TIMEOUT;
                Process waited = preferred == null ? engines[0] : engines[1];
                waited.waitFor(Math.min(POLL_MILLIS, Math.max(1L,
                        TimeUnit.NANOSECONDS.toMillis(deadline - now))),
                        TimeUnit.MILLISECONDS);
            }
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            return TIMEOUT;
        }
    }

    /** What an engine printed once it ended and its output is read, else
     *  null; one that never launched printed why. */
    private static String finished(Process engine,
                                   AtomicReference<String> read,
                                   Thread reader)
            throws InterruptedException {
        if (engine == null) return read.get();
        if (engine.isAlive()) return null;
        // Its output ends with it: bounded only against a pipe held open.
        reader.join(TimeUnit.SECONDS.toMillis(ORPHAN_MARGIN_SECONDS));
        return read.get() == null ? "" : read.get();
    }

    private static boolean decided(String printed) {
        String verdict = firstLine(printed);
        return "sat".equals(verdict) || "unsat".equals(verdict);
    }

    /** How one engine is stated ({@link #ARITHMETIC_OPENING}). */
    static String arithmeticOption(int engine) {
        return ARITHMETIC_OPENING + engine + ")";
    }

    /**
     * A query on its way to one engine's z3: every arithmetic option it
     * states replaced by that engine's as the text streams through, since
     * the query's own would win over the one {@link #launch} states first.
     * Streamed, never copied: a composition's query runs past 200 MB
     * ({@link #ask(ArtifactIO.Body, List, boolean, long)}).
     */
    static final class EngineWriter extends Writer {
        private final Writer out;
        private final String option;
        /** What may still open an option: a prefix of
         *  {@link #ARITHMETIC_OPENING}, then its digits. */
        private final StringBuilder held = new StringBuilder();

        EngineWriter(Writer out, int engine) {
            this.out = out;
            this.option = arithmeticOption(engine);
        }

        @Override
        public void write(char[] text, int from, int length)
                throws IOException {
            int end = from + length;
            int at = from;
            while (at < end) {
                if (held.length() == 0) {
                    int open = at;
                    while (open < end && text[open] != '(') open++;
                    out.write(text, at, open - at);
                    if (open == end) return;
                    at = open;
                }
                take(text[at++]);
            }
        }

        private void take(char c) throws IOException {
            int matched = held.length();
            int opening = ARITHMETIC_OPENING.length();
            if (matched < opening ? c == ARITHMETIC_OPENING.charAt(matched)
                    : c >= '0' && c <= '9') {
                held.append(c);
                return;
            }
            if (c == ')' && matched > opening) {
                held.setLength(0);
                out.write(option);
                return;
            }
            release();
            // The opening's '(' is its first character and its only one.
            if (c == '(') held.append(c);
            else out.write(c);
        }

        private void release() throws IOException {
            out.write(held.toString());
            held.setLength(0);
        }

        @Override
        public void flush() throws IOException {
            out.flush();
        }

        @Override
        public void close() throws IOException {
            try {
                release();
            } finally {
                out.close();
            }
        }
    }

    /**
     * One z3 fed {@code prefix}, the query and {@code suffix} under one
     * arithmetic {@code engine} ({@link EngineWriter}), its output read into
     * {@code read} by a thread of its own (and its input written by another:
     * else large queries deadlock); null when it could not start,
     * {@code read} then saying why (undecided, not a z3 {@code (error ...)}).
     */
    private Process launch(int engine, String prefix, ArtifactIO.Body query,
                           String suffix, long budgetMillis,
                           AtomicReference<String> read,
                           List<Thread> readers) {
        Process process;
        try {
            List<String> command = new ArrayList<String>(
                    Arrays.asList(DIES_WITH_ITS_DRIVER));
            command.addAll(Arrays.asList(z3.toString(),
                    hardTimeout(budgetMillis), "-in", "-smt2"));
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.redirectErrorStream(true);
            process = builder.start();
        } catch (IOException notLaunched) {
            read.set("error " + notLaunched.getMessage());
            readers.add(null);
            return null;
        }
        LIVE.put(process, pidOf(process));
        Thread writer = new Thread(() -> {
            try (BufferedWriter input = new BufferedWriter(new EngineWriter(
                    new OutputStreamWriter(process.getOutputStream(),
                            StandardCharsets.UTF_8), engine), 1 << 16)) {
                input.write(arithmeticOption(engine) + "\n");
                input.write(prefix);
                query.writeTo(input);
                input.write(suffix);
            } catch (IOException closed) {
                // z3 closed its input after answering, or was killed.
            }
        }, "graphchecker-z3-writer");
        Thread reader = new Thread(() -> {
            try {
                read.set(readAll(process.getInputStream()));
            } catch (IOException truncated) {
                // A broken pipe answers nothing: "" is undecided.
                read.set("");
            }
        }, "graphchecker-z3-reader");
        writer.setDaemon(true);
        reader.setDaemon(true);
        writer.start();
        reader.start();
        readers.add(reader);
        return process;
    }

    /**
     * The answer z3 printed: its WARNING lines dropped (the optimizer warns
     * it ignores an objective under quantifiers, then answers on the next
     * line, which every reader here takes as the first), every error line
     * remembered.
     */
    private String answerOf(String printed) {
        if (printed == null) return "";
        List<String> kept = new ArrayList<String>();
        for (String line : printed.split("\n", -1)) {
            if (!line.startsWith("WARNING:")) kept.add(line);
        }
        String output = String.join("\n", kept);
        int at = output.indexOf(ERROR);
        while (at >= 0) {
            int end = output.indexOf('\n', at);
            synchronized (errors) {
                errors.add((end < 0 ? output.substring(at)
                        : output.substring(at, end)).trim());
            }
            at = output.indexOf(ERROR, at + ERROR.length());
        }
        return output;
    }

    private static String readAll(InputStream stream) throws IOException {
        ByteArrayOutputStream buffer = new ByteArrayOutputStream();
        byte[] chunk = new byte[8192];
        int count;
        while ((count = stream.read(chunk)) > 0) {
            buffer.write(chunk, 0, count);
        }
        return new String(buffer.toByteArray(), StandardCharsets.UTF_8);
    }

    private static String firstLine(String output) {
        if (output == null) return "";
        int end = output.indexOf('\n');
        return (end < 0 ? output : output.substring(0, end)).trim();
    }

    // ------------------------------------------------------------------
    // Reading the answer.
    // ------------------------------------------------------------------

    /** The {@code ((sym val) ...)} block a sat answer carries. */
    static Map<String, String> parseValues(String output) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        SExpression block = answerBlock(output, false);
        if (block == null || block.atom()) return values;
        for (SExpression pair : block.children()) {
            List<SExpression> parts = pair.children();
            if (parts.size() < 2) continue;
            // Strip SMT-LIB |bars| from the name.
            values.put(unquoted(parts.get(0).text()), normalize(output
                    .substring(parts.get(1).start,
                            parts.get(parts.size() - 1).end)));
        }
        return values;
    }

    /** {@code |x|} is how SMT-LIB spells the name {@code x}. */
    static String unquoted(String name) {
        String text = name == null ? "" : name.trim();
        return text.length() >= 2 && text.startsWith("|")
                && text.endsWith("|")
                ? text.substring(1, text.length() - 1) : text;
    }

    /** {@code (- 5)} is what a model says; {@code -5} is what Java says. */
    static String normalize(String value) {
        String text = value == null ? "" : value.trim();
        if (text.startsWith("(-") && text.endsWith(")")) {
            String digits = text.substring(2, text.length() - 1).trim();
            if (!digits.isEmpty()) return "-" + digits;
        }
        return text;
    }

    /**
     * The Java String a model's String value denotes, or null when the value
     * is no SMT-LIB string literal: {@code ""} inside it is one quote, and
     * a backslash, {@code u} and {@code {h..}} or four hex digits the
     * character with that code point, as z3 prints what is not printable
     * ASCII.
     */
    public static String javaString(String value) {
        String text = value == null ? "" : value.trim();
        if (text.length() < 2 || text.charAt(0) != '"'
                || text.charAt(text.length() - 1) != '"') {
            return null;
        }
        String body = text.substring(1, text.length() - 1);
        StringBuilder string = new StringBuilder();
        for (int at = 0; at < body.length(); at++) {
            char c = body.charAt(at);
            if (c == '"') {
                if (at + 1 >= body.length() || body.charAt(at + 1) != '"') {
                    return null;
                }
                string.append('"');
                at++;
                continue;
            }
            int end = escapeEnd(body, at);
            if (end < 0) {
                string.append(c);
                continue;
            }
            String hex = body.charAt(at + 2) == '{'
                    ? body.substring(at + 3, end - 1)
                    : body.substring(at + 2, end);
            string.appendCodePoint(Integer.parseInt(hex, 16));
            at = end - 1;
        }
        return string.toString();
    }

    /** Where a code-point escape ({@link #javaString}) at {@code at} ends,
     *  or -1 when none starts there. */
    private static int escapeEnd(String body, int at) {
        if (!body.startsWith("\\u", at)) return -1;
        if (body.startsWith("{", at + 2)) {
            int close = body.indexOf('}', at + 3);
            return close > at + 3 && close <= at + 8
                    && hex(body.substring(at + 3, close)) ? close + 1 : -1;
        }
        return at + 6 <= body.length() && hex(body.substring(at + 2, at + 6))
                ? at + 6 : -1;
    }

    private static boolean hex(String digits) {
        for (char c : digits.toCharArray()) {
            if (Character.digit(c, 16) < 0) return false;
        }
        return !digits.isEmpty();
    }

    /** The text of one {@code (:reason-unknown "…")} line, or "". */
    private static String parseReason(String output) {
        if (output == null) return "";
        int at = output.indexOf(":reason-unknown");
        if (at < 0) return "";
        int open = output.indexOf('"', at);
        int close = open < 0 ? -1 : output.indexOf('"', open + 1);
        if (open < 0 || close < 0) return "";
        return output.substring(open + 1, close).trim();
    }

    /** The names an unsat core lists, in the order z3 printed them. */
    static List<String> parseCore(String output) {
        List<String> names = new ArrayList<String>();
        SExpression block = answerBlock(output, true);
        if (block == null) return names;
        for (SExpression name : block.children()) names.add(name.text());
        return names;
    }

    /**
     * The list z3 printed after its verdict line: the first term there, or
     * ({@code firstList}) the first parenthesised one; null when none.
     */
    private static SExpression answerBlock(String output, boolean firstList) {
        int verdictEnd = output == null ? -1 : output.indexOf('\n');
        if (verdictEnd < 0) return null;
        int at = firstList ? output.indexOf('(', verdictEnd) : verdictEnd + 1;
        return at < 0 ? null : SExpression.parse(output, at);
    }
}
