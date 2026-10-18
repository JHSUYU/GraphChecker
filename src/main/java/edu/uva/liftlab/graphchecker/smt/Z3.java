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
 *
 * <p>EVERY z3 RUNS UNDER A MEMORY CAP its JVM's charge covers ({@link
 * Room}): the campaign charges a JVM that runs z3 its footprint and a z3
 * room of R MB ({@code --z3-room-mb}), and every z3 of the JVM holds a slot
 * of it -- a lone ask's engines half the room each, a whole disjunction
 * asked with others a slot of the room shared that many ways ({@link
 * #shared}), a pair of scoped z3s the whole room ({@link Z3Incremental})
 * -- started with
 * z3's own {@code memory_max_size} at the slot less what z3's accounting
 * misses ({@link #MISSED_MB}); a run starts only while its two slots fit in
 * what the room has free.  A z3 at its cap prints {@code (error "out of
 * memory")}: the answer {@link #MEMOUT}, undecided by name as a timeout is,
 * never a refutation and no error of the query (SGF3-adhoc-13: one z3 of a
 * composer charged its JVM only grew to 10.9 GB in 20 minutes, swap full,
 * its host unreachable for a minute).</p>
 *
 * <p>A solver may also hold rooms on OTHER HOSTS ({@code --z3-hosts}),
 * charged on their hosts' ledgers for its JVM's life: only the plain pairs
 * of scoped z3s run there, over ssh ({@link Z3Incremental}); every other z3
 * runs here.  solr-adhoc-10 SGF7: a composer of a 16 GB heap had room for
 * one pair here, and its decide ran out its 30 minutes with 315 z3 runs,
 * questions unasked, while twelve hosts of 30 GB sat idle.</p>
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
    static final String TIMEOUT = "timeout";

    /** What a z3 at its memory cap prints (4.14.1, exit 101), and the
     *  status it is read as: undecided by name, no error of the query. */
    static final String OUT_OF_MEMORY = "(error \"out of memory\")";
    static final String MEMOUT = "memout";

    /**
     * What a z3's resident memory holds past the {@code memory_max_size} it
     * is started under, in MB: its binary and stacks, which z3's own
     * accounting does not count (measured on 4.14.1: 12-20 MB at caps of
     * 20-90 MB; at 1 and 2 GB caps the resident peak stayed below the cap).
     * A slot of S MB starts its z3 at S less this.
     */
    static final int MISSED_MB = 64;

    /** The least slot a z3 can be started in. */
    static final int LEAST_SLOT_MB = 2 * MISSED_MB;

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
     * decided a run that asks a model or a core: as long again as that one
     * took, and at least this.  Within it the preferred answer wins, so a
     * query the preferred engine alone decides promptly answers as it did
     * before the race, model and all.  A run that asks neither takes the
     * first decided verdict at once: it is the same whichever engine gives
     * it (SGF6-bugs-snapshot-no-active 0001's self-check: a path engine 6
     * satisfied in 22 s, engine 2 undecided at 120 s, answered at 44 s).
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

        Answer(String status, Map<String, String> values,
               List<String> core, boolean coreKnown, String reason) {
            this.status = status;
            this.values = Collections.unmodifiableMap(values);
            this.core = Collections.unmodifiableList(core);
            this.coreKnown = coreKnown;
            this.reason = reason;
        }

        /** A decided answer -- {@code sat} and its model's values, or
         *  {@code unsat} -- another run gave the same query text: the hard
         *  lane's ({@code ObligationSolverMain --decide}), or one kept by
         *  the text ({@code explore.Solved}); no core. */
        public static Answer decided(String status,
                                     Map<String, String> values) {
            if (!"sat".equals(status) && !"unsat".equals(status)) {
                throw new IllegalArgumentException("not a decided answer: "
                        + status);
            }
            return new Answer(status, values,
                    Collections.<String>emptyList(), false, "");
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

        /** Whether z3 stopped at its memory cap: undecided by name. */
        public boolean memOut() {
            return MEMOUT.equals(status);
        }

        /**
         * Why the solver did not decide ({@code :reason-unknown}), or "";
         * asked only of an undecided answer that is no timeout and no
         * memout (a memout's names the cap it hit).
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

    /**
     * One JVM's z3 room: the MB its charge holds for its z3 processes
     * ({@code --z3-room-mb}), and the slots its running z3s hold.  A run
     * takes its two slots before it starts, in the order the runs asked
     * (so a run alone, in half the room an engine, is not passed by smaller
     * ones forever), waiting while they do not fit in what is free,
     * and gives them back when its z3s are gone; a run alone always fits,
     * its slots being at most half the room each.  A room on another host
     * ({@link #host}) holds the scoped z3s placed there, each for its life.
     */
    static final class Room {
        final int mb;
        /** The host its z3s run on; null: this JVM's. */
        final String host;
        /** The command that runs a command line on {@link #host}, the line
         *  its last argument ({@link #ssh}); empty here. */
        final List<String> reach;
        private int held;
        private long issued;
        private long serving;
        private final Set<Long> abandoned = new java.util.HashSet<Long>();

        Room(int mb) {
            this(null, mb, Collections.<String>emptyList());
        }

        Room(String host, int mb, List<String> reach) {
            if (mb < 2 * LEAST_SLOT_MB) {
                throw new IllegalArgumentException("a z3 room of " + mb
                        + " MB holds no run: at least " + 2 * LEAST_SLOT_MB);
            }
            this.mb = mb;
            this.host = host;
            this.reach = Collections.unmodifiableList(
                    new ArrayList<String>(reach));
        }

        /** Takes {@code need} MB once every run that asked before took
         *  its own and they fit: true; false when interrupted first. */
        synchronized boolean take(int need) {
            long ticket = issued++;
            while (ticket != serving || held + need > mb) {
                try {
                    wait();
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                    abandoned.add(ticket);
                    pass();
                    return false;
                }
            }
            held += need;
            serving++;
            pass();
            return true;
        }

        /** The turn past the runs that stopped waiting, and every waiter
         *  told. */
        private void pass() {
            while (abandoned.remove(serving)) serving++;
            notifyAll();
        }

        synchronized void give(int need) {
            held -= need;
            notifyAll();
        }

        synchronized int held() {
            return held;
        }

        /** Whether a run waits for its turn: one holding slots gives them
         *  back between questions ({@code Z3Incremental}). */
        synchronized boolean contended() {
            return issued > serving;
        }
    }

    private final Path z3;
    private final long timeoutMillis;
    /** Asks may run on several threads, each its own z3 process. */
    private final AtomicInteger runs;
    private final Set<String> errors;
    private final Room room;
    /** Its rooms on other hosts, in the order they were named. */
    private final List<Room> hosts;
    /** A directory every host sees, where what a remote z3 reads first is
     *  written ({@code Z3Incremental}); null where there are no hosts. */
    private final Path visible;
    /** The slot each z3 of this solver's runs holds, in MB. */
    private final int slotMb;
    /** The slot a run of this solver holds alone, in MB: half its own room
     *  ({@link #Z3(Path, long, Rooms, int)}: a question's, in a room its JVM
     *  shares among the questions it answers at once). */
    private final int aloneMb;
    /** {@link System#nanoTime} past which no run starts and every run's
     *  budget ends ({@link #until}); 0: none. */
    private final long deadlineNanos;

    /**
     * A solver whose z3s share a room of {@code roomMb} (what its JVM's
     * charge holds for them, {@code --z3-room-mb}); a lone ask's two
     * engines take half of it each.
     */
    public Z3(Path executable, long timeoutMillis, int roomMb) {
        this(executable, timeoutMillis, roomMb,
                Collections.<Room>emptyList(), null);
    }

    /**
     * A JVM's z3 room shared by the questions it answers at once (a host's
     * solver, {@code explore.ObligationSolverMain --serve}): what its charge
     * holds for their z3s, {@code --z3-room-mb}.
     */
    public static final class Rooms {
        private final Room room;

        public Rooms(int mb) {
            this.room = new Room(mb);
        }
    }

    /**
     * One question's solver in a room its JVM shares ({@link Rooms}): its
     * runs hold slots of half {@code questionMb} each, as they would alone in
     * a room of their own, so a run's memory cap, and what a run at its cap
     * answers, are the question's however many questions share the room; a
     * run waits only for its turn at the room, its budget counted from its
     * start.
     */
    public Z3(Path executable, long timeoutMillis, Rooms shared,
              int questionMb) {
        this(executable == null ? Paths.get("z3") : executable,
                timeoutMillis <= 0L ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis,
                new AtomicInteger(), new TreeSet<String>(), shared.room,
                Collections.<Room>emptyList(), null,
                Math.min(questionMb, shared.room.mb) / 2, 0L,
                Math.min(questionMb, shared.room.mb) / 2);
    }

    /** A solver of the same z3, at {@code timeoutMillis}, in a room of
     *  {@code roomMb} its own (a hard lane's model finished in a solver,
     *  {@code explore.ObligationFactory#solve}). */
    public Z3 alone(long timeoutMillis, int roomMb) {
        return new Z3(z3, timeoutMillis, roomMb);
    }


    /**
     * The same with rooms on other hosts, host -&gt; MB, reached by
     * {@link #ssh} ({@code --z3-hosts}), what their remote z3s read first
     * written in {@code visible}, a directory every host sees.
     */
    public Z3(Path executable, long timeoutMillis, int roomMb,
              Map<String, Integer> hosts, Path visible) {
        this(executable, timeoutMillis, roomMb, rooms(hosts), visible);
    }

    Z3(Path executable, long timeoutMillis, int roomMb, List<Room> hosts,
       Path visible) {
        this(executable == null ? Paths.get("z3") : executable,
                timeoutMillis <= 0L ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis,
                new AtomicInteger(), new TreeSet<String>(), new Room(roomMb),
                Collections.unmodifiableList(new ArrayList<Room>(hosts)),
                visible, roomMb / 2, 0L, roomMb / 2);
        if (!hosts.isEmpty() && visible == null) {
            throw new IllegalArgumentException("z3 rooms on " + hosts.size()
                    + " other host(s) and no directory they all see");
        }
    }

    private Z3(Path z3, long timeoutMillis, AtomicInteger runs,
               Set<String> errors, Room room, List<Room> hosts, Path visible,
               int slotMb, long deadlineNanos, int aloneMb) {
        this.z3 = z3;
        this.timeoutMillis = timeoutMillis;
        this.runs = runs;
        this.errors = errors;
        this.room = room;
        this.hosts = hosts;
        this.visible = visible;
        this.slotMb = slotMb;
        this.deadlineNanos = deadlineNanos;
        this.aloneMb = aloneMb;
    }

    /**
     * How a command line runs on {@code host}: ssh, never asking for a
     * password, giving up on a host that does not answer.
     */
    static List<String> ssh(String host) {
        return Arrays.asList("ssh", "-o", "BatchMode=yes", "-o",
                "ConnectTimeout=20", host);
    }

    private static List<Room> rooms(Map<String, Integer> hosts) {
        List<Room> rooms = new ArrayList<Room>();
        for (Map.Entry<String, Integer> host : hosts.entrySet()) {
            rooms.add(new Room(host.getKey(), host.getValue(),
                    ssh(host.getKey())));
        }
        return rooms;
    }

    /**
     * The same solver ending every run at {@code deadlineNanos}
     * ({@link System#nanoTime}): a run's budget is at most what is left, and
     * one that would start past it answers {@link #TIMEOUT} -- undecided,
     * never a verdict -- without a z3.  A named bound's (a composition's
     * decide budget, {@code ClaimPolicy#DECIDE_BUDGET_MS}).
     */
    public Z3 until(long deadlineNanos) {
        return new Z3(z3, timeoutMillis, runs, errors, room, hosts, visible,
                slotMb, deadlineNanos, aloneMb);
    }

    /** Whether this solver's deadline ({@link #until}) has passed. */
    public boolean pastDeadline() {
        return deadlineNanos != 0L && System.nanoTime() - deadlineNanos >= 0L;
    }

    /**
     * The same solver -- its room, run counter and errors -- whose z3s hold
     * slots of {@code slotMb} (at most half its own room, {@link #aloneMb}):
     * a caller that asks many at once (a disjunction's paths) runs as many as
     * their slots fit in the room, the rest waiting for one to end.
     */
    public Z3 slotted(int slotMb) {
        return new Z3(z3, timeoutMillis, runs, errors, room, hosts, visible,
                Math.max(LEAST_SLOT_MB, Math.min(slotMb, aloneMb)),
                deadlineNanos, aloneMb);
    }

    /** The same solver as {@code asksAtOnce} callers ask it together: each
     *  z3 a slot of its own room shared that many ways. */
    public Z3 shared(int asksAtOnce) {
        return slotted(2 * aloneMb / (ARITHMETIC.length * Math.max(1,
                asksAtOnce)));
    }

    /** The memory cap, in MB, each z3 of this solver starts under. */
    public int capMb() {
        return slotMb - MISSED_MB;
    }

    /** What the slots of this solver's room's running z3s hold, in MB. */
    int roomHeldMb() {
        return room.held();
    }

    /** The room this solver's z3s hold their slots in. */
    Room room() {
        return room;
    }

    /** Its rooms on other hosts ({@code --z3-hosts}). */
    List<Room> hosts() {
        return hosts;
    }

    /** Where what a remote z3 reads first is written: every host sees it. */
    Path visible() {
        return visible;
    }

    Path executable() {
        return z3;
    }

    /** One more run of this solver's count, its number. */
    int countRun() {
        return runs.incrementAndGet();
    }

    /** One {@code (error ...)} line z3 printed ({@link #errors}). */
    void noteError(String line) {
        synchronized (errors) {
            errors.add(line.trim());
        }
    }

    /** {@code budgetMillis}, at most what this solver's deadline leaves
     *  ({@link #until}); none left: at most 0. */
    long budgetLeft(long budgetMillis) {
        return deadlineNanos == 0L ? budgetMillis : Math.min(budgetMillis,
                TimeUnit.NANOSECONDS.toMillis(deadlineNanos
                        - System.nanoTime()));
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
        if (MEMOUT.equals(status)) {
            // At its slot's cap: undecided there, never asked again alone
            // (a whole disjunction asked at a shared slot goes path by
            // path, each a smaller question: compose.Disjunction#ask).
            return new Answer(status, Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList(), false, "out of memory at"
                    + " its cap of " + capMb() + " MB (memory_max_size)");
        }
        // Its engines disagreeing: undecided, named among its errors.
        if (status.startsWith(DISAGREE)) return undecided(status);
        Map<String, String> values = Collections.emptyMap();
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
            // Its model cut by a shared slot's cap: that run once more
            // alone, never the verdict again (a verdict with no model
            // selects no path).
            String printed = payload("", query, valueCommand(modelSymbols));
            if (firstLine(printed).startsWith(DISAGREE)) {
                return undecided(firstLine(printed));
            }
            if ("unsat".equals(firstLine(printed))) {
                return disagree("its verdict sat, its model's run unsat");
            }
            values = parseValues(printed);
        }
        List<String> core = Collections.emptyList();
        boolean coreKnown = false;
        if (wantCore && "unsat".equals(status)) {
            // A core run that did not say unsat (its budget ran out, no
            // host had room, it answered unknown, its cap alone too) names
            // no core: the verdict stands, unsat, its core unknown -- never
            // asked again for a core, nor undecided for want of one.
            String printed = payload(CORE_TRACKING, query,
                    "(check-sat)\n(get-unsat-core)\n");
            if (firstLine(printed).startsWith(DISAGREE)) {
                return undecided(firstLine(printed));
            }
            if ("sat".equals(firstLine(printed))) {
                return disagree("its verdict unsat, its core's run sat");
            }
            coreKnown = "unsat".equals(firstLine(printed))
                    && answerBlock(printed, true) != null;
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

    /** How a contradiction between two runs or engines of one question
     *  starts ({@link #disagree}). */
    static final String DISAGREE = "(error \"engines disagree: ";

    /**
     * Two decided answers to one question that differ -- its two engines
     * in one run, or its verdict's run and its model's or core's: an error
     * ({@link #errors}, which refuses the claim by name) and an undecided
     * answer, never a verdict.
     */
    private Answer disagree(String how) {
        String error = DISAGREE + how + "\")";
        noteError(error);
        return undecided(error);
    }

    private static Answer undecided(String status) {
        return new Answer(status, Collections.<String, String>emptyMap(),
                Collections.<String>emptyList(), false, "");
    }

    /**
     * A decided verdict's payload run -- its model, its core -- under the
     * instance's budget ({@link #ask}); at a shared slot's cap, that run once
     * more alone, in half the room an engine (SGF6-bugs-snapshot-no-active
     * 0001: 26 of 48 core runs at a path slot's 704 MB cap re-asked their
     * whole question alone, verdict and core, each holding the composer's
     * whole room for minutes).
     */
    private String payload(String prefix, ArtifactIO.Body query,
                           String suffix) {
        String printed = run(prefix, query, suffix, timeoutMillis);
        if (MEMOUT.equals(firstLine(printed)) && slotMb < aloneMb) {
            printed = slotted(aloneMb).run(prefix, query, suffix,
                    timeoutMillis);
        }
        return printed;
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
        return "(check-sat)\n" + getValue(modelSymbols);
    }

    /** The command that asks a sat answer for these constants' values. */
    static String getValue(List<String> modelSymbols) {
        StringBuilder text = new StringBuilder("(get-value (");
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
     * The z3 processes running now.  A JVM that ends (a bound's or a stop's
     * TERM) takes them with it at once; one killed outright runs no hook,
     * and the kernel kills its z3s ({@link #DIES_WITH_ITS_DRIVER}).
     */
    private static final Set<Process> LIVE =
            Collections.newSetFromMap(new ConcurrentHashMap<Process, Boolean>());

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

    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            for (Process process : LIVE) process.destroyForcibly();
        }, "graphchecker-z3-reaper"));
    }

    /** z3's own wall clock for one run of {@code budgetMillis}. */
    static String hardTimeout(long budgetMillis) {
        return "-T:" + ((budgetMillis + 999L) / 1000L + ORPHAN_MARGIN_SECONDS);
    }

    /** The command one z3 of a slot of {@code slotMb} runs, for a run of
     *  {@code budgetMillis}: its memory cap, its own clock, the query on its
     *  input. */
    static List<String> command(Path z3, int slotMb, long budgetMillis) {
        List<String> command = new ArrayList<String>(
                Arrays.asList(DIES_WITH_ITS_DRIVER));
        command.addAll(Arrays.asList(z3.toString(),
                "memory_max_size=" + (slotMb - MISSED_MB),
                hardTimeout(budgetMillis), "-in", "-smt2"));
        return command;
    }

    /**
     * One run: the query under each arithmetic engine ({@link #ARITHMETIC}),
     * two z3 processes, and the first DECIDED answer -- the preferred
     * engine's when it decides within {@link #PREFERRED_GRACE_MILLIS} of the
     * other's -- with the other killed.  Both undecided: the preferred
     * one's answer.  Both share the budget, enforced here; z3's own
     * ({@link #hardTimeout}) only outlives a driver that hangs.  A run
     * starts once its two slots fit in its room ({@link Room#take}); an
     * interrupted one answers as a timeout, its z3s killed.  Each run says
     * what it answered and how long it took, waiting for room included, on
     * stderr: a quiet log is then one run's own wall, bounded by its budget.
     */
    private String run(String prefix, ArtifactIO.Body query, String suffix,
                       long budgetMillis) {
        // Past its deadline (until) no run starts: no z3, no count.
        if (pastDeadline()) return TIMEOUT;
        int run = runs.incrementAndGet();
        long started = System.nanoTime();
        String answer = TIMEOUT;
        int slots = ARITHMETIC.length * slotMb;
        if (room.take(slots)) {
            try {
                // Its budget at most what its deadline leaves (until).
                long budget = budgetLeft(budgetMillis);
                if (budget > 0L) {
                    answer = raced(prefix, query, suffix, budget);
                }
            } finally {
                room.give(slots);
            }
        }
        said(run, command(suffix), firstLine(answer), started);
        return answer;
    }

    /** What one run answered and how long it took, on stderr. */
    static void said(int run, String command, String said,
                     long startedNanos) {
        System.err.println("z3 run " + run + " (" + command + "): "
                + (said.length() > 40 ? said.substring(0, 40) + "..." : said)
                + " in " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime()
                - startedNanos) / 1000.0 + " s");
    }

    /** A z3 now running, taken with its JVM ({@link #LIVE}). */
    static void track(Process process) {
        LIVE.add(process);
    }

    /** A z3 gone. */
    static void untrack(Process process) {
        LIVE.remove(process);
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
            String printed = race(engines, read, readers, started, deadline,
                    suffix);
            // A cap hit before the payload asked for was printed: the run
            // answered nothing, whatever verdict it printed first.
            return answerOf(memoryOut(printed) && !decided(printed, suffix)
                    ? OUT_OF_MEMORY : printed);
        } finally {
            for (Process engine : engines) {
                if (engine == null) continue;
                engine.destroyForcibly();
                // Its slot is given back once its memory is: when it is gone.
                try {
                    engine.waitFor(ORPHAN_MARGIN_SECONDS, TimeUnit.SECONDS);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
                untrack(engine);
            }
        }
    }

    /**
     * The printed answer {@link #run} returns, or {@link #TIMEOUT}: the
     * preferred engine's as soon as it decides; the other's once it has
     * decided and the preferred one has not within its grace -- at once
     * where {@code suffix} asks no model and no core
     * ({@link #PREFERRED_GRACE_MILLIS}); when neither decides, the
     * preferred engine's.  Both decided, differing: an {@code (error ...)}
     * that names them ({@link #DISAGREE}), never either verdict.
     */
    private static String race(Process[] engines,
                               List<AtomicReference<String>> read,
                               List<Thread> readers, long started,
                               long deadline, String suffix) {
        long otherDecidedAt = 0L;
        boolean payload = suffix.contains("(get-value")
                || suffix.contains("(get-unsat-core)");
        try {
            while (true) {
                String preferred = finished(engines[0], read.get(0),
                        readers.get(0));
                String other = finished(engines[1], read.get(1),
                        readers.get(1));
                boolean otherDecides = other != null
                        && decided(other, suffix);
                if (preferred != null && decided(preferred, suffix)) {
                    return otherDecides ? agreed(preferred, other)
                            : preferred;
                }
                long now = System.nanoTime();
                if (otherDecides) {
                    if (otherDecidedAt == 0L) otherDecidedAt = now;
                    long took = otherDecidedAt - started;
                    long grace = Math.max(took, TimeUnit.MILLISECONDS
                            .toNanos(PREFERRED_GRACE_MILLIS));
                    if (!payload || preferred != null
                            || now - otherDecidedAt >= grace) {
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

    /** {@code preferred}, where {@code other} decided the same; else an
     *  error naming both verdicts ({@link #DISAGREE}). */
    private static String agreed(String preferred, String other) {
        String one = firstLine(preferred);
        String two = firstLine(other);
        return one.equals(two) ? preferred : DISAGREE + "engine "
                + ARITHMETIC[0] + " " + one + ", engine " + ARITHMETIC[1]
                + " " + two + " in one run\")";
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

    /**
     * Whether one engine's printed answer decided its run's command
     * ({@code suffix}): sat or unsat, and -- where z3 stopped at its cap
     * after the verdict -- the payload the command asked for printed before
     * the cap: the model's values of a {@code (get-value ...)}, the core of a
     * {@code (get-unsat-core)}.
     */
    static boolean decided(String printed, String suffix) {
        String verdict = firstLine(printed);
        if (!"sat".equals(verdict) && !"unsat".equals(verdict)) return false;
        if (!memoryOut(printed)) return true;
        if (suffix.contains("(get-unsat-core)")) {
            return "unsat".equals(verdict) && payload(printed);
        }
        if (suffix.contains("(get-value")) {
            return "sat".equals(verdict) && payload(printed);
        }
        return true;
    }

    /** Whether z3 printed its cap's {@link #OUT_OF_MEMORY} anywhere. */
    static boolean memoryOut(String printed) {
        if (printed == null) return false;
        for (String line : printed.split("\n", -1)) {
            if (OUT_OF_MEMORY.equals(line.trim())) return true;
        }
        return false;
    }

    /** Whether the line after the verdict is a payload: a list, no error. */
    static boolean payload(String printed) {
        String[] lines = printed.split("\n", -1);
        return lines.length > 1 && lines[1].trim().startsWith("(")
                && !lines[1].trim().startsWith(ERROR);
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

        /** Whatever it holds written, and the writer under it flushed, but
         *  not closed: the end of one text of several on one input. */
        void finish() throws IOException {
            release();
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
            ProcessBuilder builder = new ProcessBuilder(
                    command(z3, slotMb, budgetMillis));
            builder.redirectErrorStream(true);
            process = builder.start();
        } catch (IOException notLaunched) {
            read.set("error " + notLaunched.getMessage());
            readers.add(null);
            return null;
        }
        track(process);
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
     * line, which every reader here takes as the first), its cap's
     * {@link #OUT_OF_MEMORY} read as {@link #MEMOUT}, every other error line
     * remembered.
     */
    private String answerOf(String printed) {
        if (printed == null) return "";
        List<String> kept = new ArrayList<String>();
        for (String line : printed.split("\n", -1)) {
            if (line.startsWith("WARNING:")) continue;
            kept.add(OUT_OF_MEMORY.equals(line.trim()) ? MEMOUT : line);
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
    static String parseReason(String output) {
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
    static SExpression answerBlock(String output, boolean firstList) {
        int verdictEnd = output == null ? -1 : output.indexOf('\n');
        if (verdictEnd < 0) return null;
        int at = firstList ? output.indexOf('(', verdictEnd) : verdictEnd + 1;
        return at < 0 ? null : SExpression.parse(output, at);
    }
}
