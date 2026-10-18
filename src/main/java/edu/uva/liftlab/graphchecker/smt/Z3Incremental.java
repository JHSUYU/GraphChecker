package edu.uva.liftlab.graphchecker.smt;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.TimeUnit;

/**
 * MANY QUESTIONS OVER ONE SHARED PART, EACH A SCOPE OF ONE LONG-LIVED z3: a
 * composition's paths share most of their question ({@code
 * Composition#sharedQuery}; SGF6-bugs-snapshot-no-active 0001: 65 of each
 * path's 69 MB), and a z3 started per question read it again for every one
 * and every engine -- about 4 of a path's 5.5-8 s.  Here each arithmetic
 * engine ({@link Z3#ARITHMETIC}) keeps a z3 that read the shared part once,
 * and each question is one scope over it:
 *
 * <pre>
 *   (push 1) (set-option :timeout B) &lt;its own commands&gt; (echo began)
 *   (check-sat) (echo verdict)
 *   [(get-value (...)) | (get-unsat-core) | (get-info :reason-unknown)]
 *   (echo payload)   (pop 1) (echo popped)
 * </pre>
 *
 * <p>Every answer is what z3 printed up to its {@code echo} mark.  {@code
 * pop} takes back whatever the scope asserted, named or declared, so no
 * question sees another's, and a scope's answer is its question's: the
 * shared part and the scope are its commands.  A question's model or core
 * is read off its own check, before the pop.</p>
 *
 * <p>z3 answers a scope with an incremental core where it has a choice,
 * far slower than the tactic solver a lone question gets on some questions
 * (snapshot 0001: a sat path 73 s scoped, 8 s alone); after {@link
 * #SOLVER2_TIMEOUT_MS} it falls back to that solver ({@code
 * combined_solver.solver2_timeout}): that path 4 s, unsat ones 0.3-3 s, the
 * shared part read in 4 s once.</p>
 *
 * <p>The engines race as a run's do ({@code Z3#race}): each question goes
 * to both, the preferred engine's decided answer wins within its grace,
 * and the other engine's check still running is cancelled -- z3 ends a
 * {@code check-sat} on SIGINT and reads on (anywhere else SIGINT ends it:
 * a z3 that ended, started afresh).  A question whose asker stops (an ask
 * after a sat path) is cancelled so.  Undecided is never a verdict: a
 * timeout ({@code :timeout}, or no answer {@link #SILENCE_MARGIN_MS} past
 * it: that z3 ended), an {@code unknown}, a z3 at its cap ({@link
 * Z3#MEMOUT}).  A z3 that ends mid-question answers it nothing, and the
 * questions after it are asked of a fresh one.  A question is asked once
 * more where its z3 ended before reaching it, where it ran out of memory
 * after answering others, and where a SIGINT meant for an earlier check
 * was still to land -- one sent as that check ended cancels the next check
 * ("interrupted from keyboard") or, outside a check, ends z3.  A cancelled
 * check no verdict of which comes within {@link #SILENCE_MARGIN_MS} ends
 * its z3; a question's own silence is counted from when it is sent, or on
 * a fresh z3 from the end of its shared part's read, which never counts.  A sat whose
 * model its cap cut is undecided; an unsat whose core it cut stands, its
 * core unknown, as {@link Z3#ask}'s does.  Two decided answers to one
 * question that differ -- its engines', or its verdict's and its core's
 * -- are an error of the solver's, refusing the claim by name, and the
 * question undecided: a scope that leaked is never a verdict.</p>
 *
 * <p>A core needs z3 to track named assertions from its start, which slows
 * every question ({@link Z3#CORE_TRACKING}): a question that wants one is
 * asked whole of a pair started tracking -- its verdict, model and core of
 * one check -- the rest of pairs that track nothing.  The questions of each
 * kind wait in their lane, each pair of it asking the next.  The plain lane
 * has a pair for every {@link #PAIR_SLOT_MB} a z3 its solver's rooms on
 * other hosts hold ({@code Z3#hosts}), and as many as its own room holds
 * beside the tracking one -- at most as many in all as its asker puts
 * questions at once, the other hosts' placed first ({@link #placed}) --
 * each pair two slots of its room; a room here that holds no two pairs
 * runs one at a time, each holding the whole room, half each engine (a
 * question's z3 as {@link Z3#ask}'s alone).  A pair holds its slots while
 * it lives, and gives them back to whoever waits for room once it has no
 * question, or between questions once it held them {@link #YIELD_AFTER_MS}:
 * the pairs and the solver's one-shot asks take turns where the room holds
 * no more (SGF6-bugs-snapshot-no-active 0001 in 2269 MB: the recorded
 * valuation's core questions moved the room between the plain pair and the
 * tracking one 14 times, each move a fresh z3 reading 65 MB).</p>
 *
 * <p>A pair on another host runs its z3s over ssh ({@link #remote}): each
 * prints its pid first, which every SIGINT and its end are sent to on that
 * host, and reads the shared part from a file every host sees ({@link
 * SharedFiles}) before its input.  A pair there whose z3 has not read the
 * shared part -- ended first (ssh refused, the host gone) or not within
 * {@link #REMOTE_READ_MS} -- asks no more, and a question it left
 * undecided is the other pairs'.</p>
 */
public final class Z3Incremental implements AutoCloseable {

    /** How long z3's incremental core may run a scope before z3 falls back
     *  to its tactic solver (measured above). */
    static final int SOLVER2_TIMEOUT_MS = 1000;

    /** How long a pair keeps the room past another's asking for it, while
     *  questions of its own wait. */
    static final long YIELD_AFTER_MS = 30_000L;

    /** How long past a question's budget a z3 may stay silent before it is
     *  ended: z3 keeps the budget itself ({@code :timeout}). */
    static final long SILENCE_MARGIN_MS = 10_000L;

    /** A scoped z3's own clock ({@code Z3#hardTimeout}) where its solver
     *  names no deadline: one that runs out is started afresh. */
    static final long UNBOUNDED_LIFE_MS = 3_600_000L;

    /**
     * How long a check still running when its race ends -- or a cancelled
     * one whose start is read only later -- may still show its verdict
     * before it is signalled: one that ended just then is idle when the
     * signal comes, and the signal ends that z3 (the fixture of
     * {@code Z3IncrementalTest}: a loser's instant unknown not yet read).
     */
    static final long CANCEL_GRACE_MILLIS = 50L;

    /**
     * The slot a scoped z3 of a room that holds two pairs or more is given,
     * in MB: what one reading a large shared part takes, its questions
     * asked (snapshot 0001: 65 MB read, 420-560 MB held, 843 MB at peak).
     */
    static final int PAIR_SLOT_MB = 1024;

    /**
     * How long a z3 on another host may take to read the shared part, ssh
     * and all, before its pair asks no more there: a hung host or a stalled
     * file read holds no question to the decide's end (lift11: a 91 MB
     * composed query, SGF7-adhoc-10's, read in 7 s).
     */
    static final long REMOTE_READ_MS = 120_000L;

    /** What a remote z3's shell prints before its pid, first. */
    static final String PID = "@@graphchecker-pid ";

    /** How often a driver looks at a question's asker and at its room. */
    private static final long POLL_MILLIS = 200L;

    private static final String ERROR = "(error ";

    private final Z3 solver;
    private final ArtifactIO.Body shared;
    /** The slot each scoped z3 of its solver's own room holds, in MB. */
    private final int slotMb;
    private final Lane plain;
    private final Lane tracked;
    private final SharedFiles files;
    /** {@link System#nanoTime} past which no question of this view starts
     *  and every one running ends ({@link #until}); 0: the solver's. */
    private final long deadlineNanos;

    /**
     * Scopes over {@code shared}, asked of {@code solver}'s z3 in its rooms,
     * under its deadline ({@code Z3#until}), counted and their errors
     * noted as its runs' are; at most {@code questionsAtOnce} plain pairs,
     * as many questions as its asker puts at once ({@link #placed}).
     */
    public Z3Incremental(Z3 solver, ArtifactIO.Body shared,
                         int questionsAtOnce) {
        this.solver = solver;
        this.shared = shared;
        List<Z3.Room> placed = placed(solver, questionsAtOnce);
        int here = Collections.frequency(placed, solver.room());
        int room = solver.room().mb;
        this.slotMb = fit(room) >= 2
                ? room / (Z3.ARITHMETIC.length * (here + 1))
                : room / Z3.ARITHMETIC.length;
        this.plain = new Lane(false, placed);
        this.tracked = new Lane(true,
                Collections.singletonList(solver.room()));
        this.files = new SharedFiles(solver.visible(), shared);
        this.deadlineNanos = 0L;
        System.err.println("z3 scoped: " + placed.size()
                + " plain pair(s): " + where(placed) + "; the tracking one"
                + " here");
    }

    private Z3Incremental(Z3Incremental scopes, long deadlineNanos) {
        this.solver = scopes.solver;
        this.shared = scopes.shared;
        this.slotMb = scopes.slotMb;
        this.plain = scopes.plain;
        this.tracked = scopes.tracked;
        this.files = scopes.files;
        this.deadlineNanos = deadlineNanos;
    }

    /** How many pairs of {@link #PAIR_SLOT_MB} a z3 a room holds. */
    private static int fit(int roomMb) {
        return roomMb / (Z3.ARITHMETIC.length * PAIR_SLOT_MB);
    }

    /**
     * The room of each plain pair, at most {@code questionsAtOnce} of them:
     * on each other host as many as its room holds, {@link #PAIR_SLOT_MB}
     * a z3, placed first, so this host's room -- shared with the tracking
     * pair and the one-shot asks -- is not what the questions wait on;
     * then here as many as its room holds beside the tracking pair, or one
     * where it holds no two pairs.
     */
    static List<Z3.Room> placed(Z3 solver, int questionsAtOnce) {
        int most = Math.max(1, questionsAtOnce);
        List<Z3.Room> placed = new ArrayList<Z3.Room>();
        for (Z3.Room host : solver.hosts()) {
            for (int at = fit(host.mb); at > 0 && placed.size() < most;
                 at--) {
                placed.add(host);
            }
        }
        int fit = fit(solver.room().mb);
        for (int at = fit >= 2 ? fit - 1 : 1; at > 0 && placed.size() < most;
             at--) {
            placed.add(solver.room());
        }
        return placed;
    }

    /** How many plain pairs {@code solver}'s rooms place, as many
     *  questions put at once as they hold ({@link #placed}). */
    public static int placeable(Z3 solver) {
        return placed(solver, Integer.MAX_VALUE).size();
    }

    /** "k here, m on host, ...": how many pairs each room holds. */
    static String where(List<Z3.Room> placed) {
        StringBuilder said = new StringBuilder();
        for (Z3.Room room : new LinkedHashSet<Z3.Room>(placed)) {
            said.append(said.length() == 0 ? "" : ", ")
                    .append(Collections.frequency(placed, room))
                    .append(room.host == null ? " here" : " on " + room.host);
        }
        return said.toString();
    }

    /**
     * The same scoped z3s asked under a deadline of their asker's too
     * ({@link System#nanoTime}): past it a question is undecided --
     * {@link Z3#TIMEOUT}, never a verdict -- not started, or ended where it
     * runs (a named bound's: the decide's self-check cap,
     * {@code ClaimPolicy#SELF_CHECK_SHARE}).  Its owner closes the z3s.
     */
    public Z3Incremental until(long deadlineNanos) {
        return new Z3Incremental(this, deadlineNanos);
    }

    /**
     * One question, {@code scope} over the shared part, as {@link Z3#ask}
     * asks one: the values of {@code modelSymbols} on sat, a core on unsat
     * where {@code wantCore} -- asked whole tracking, verdict, model and
     * core of one check: a core that did not come with its unsat leaves it
     * unsat, its core unknown -- the verdict within {@code budgetMillis}
     * ({@code <= 0}: the solver's).
     */
    public Z3.Answer ask(ArtifactIO.Body scope, List<String> modelSymbols,
                         boolean wantCore, long budgetMillis) {
        List<String> symbols = modelSymbols == null
                ? Collections.<String>emptyList() : modelSymbols;
        return (wantCore ? tracked : plain).ask(scope, symbols,
                budgetMillis > 0L ? budgetMillis : solver.timeoutMillis(),
                deadlineNanos);
    }

    /** Every z3 ended, every question still open undecided, and what the
     *  remote z3s read first deleted. */
    @Override
    public void close() {
        plain.close();
        tracked.close();
        files.delete();
    }

    /**
     * What a plain or tracking z3 of {@code arithmetic} reads before the
     * shared part: its options.
     */
    private static String head(boolean tracking, int arithmetic) {
        return (tracking ? Z3.CORE_TRACKING : "")
                + "(set-option :combined_solver.solver2_timeout "
                + SOLVER2_TIMEOUT_MS + ")\n"
                + Z3.arithmeticOption(arithmetic) + "\n";
    }

    /**
     * The command that runs {@code z3} -- {@code Z3#command}'s words -- on
     * {@code room}'s host: its shell prints its pid after {@link #PID},
     * first, and execs z3, so the pid is z3's own; z3 reads {@code file},
     * then its input -- none where the file was not read: z3 ends at once,
     * never asked a scope over a shared part it lacks -- and says its
     * errors on its output, as a z3 here does (its memout is on stderr).
     * Its {@code setpriv --pdeathsig} ends it when that host's sshd goes,
     * the connection closed (lift11: a stand-in ended with its ssh); its
     * {@code -T} and memory cap bound it where the connection is lost
     * unseen.
     */
    static List<String> remote(Z3.Room room, List<String> z3, Path file) {
        StringBuilder line = new StringBuilder("echo " + PID + "$$; exec");
        for (String word : z3) line.append(' ').append(quoted(word));
        line.append(" < <(cat ").append(quoted(file.toString()))
                .append(" && cat -) 2>&1");
        // Its bash reads no rc file: ssh's variables would have it read
        // ~/.bashrc again (tools/onlift.sh; 0.1 s a start, lift11).
        List<String> command = new ArrayList<String>(room.reach);
        command.add("exec env -u BASH_ENV -u SSH_CLIENT -u SSH2_CLIENT"
                + " bash -c " + quoted(line.toString()));
        return command;
    }

    /** One word for a POSIX shell, whatever it holds. */
    private static String quoted(String word) {
        return "'" + word.replace("'", "'\\''") + "'";
    }

    /**
     * What a remote z3 reads first, by engine: a plain pair's head and the
     * shared part as that engine reads it ({@code Z3.EngineWriter}), written
     * once in a directory every host sees ({@code Z3#visible}) and deleted
     * when the scopes close (or the JVM ends).  Read from a file, never
     * piped through ssh: the lifts' links are 1 Gb/s, so SGF7-adhoc-10's 87
     * MB shared part piped to each of 48 remote z3s would cross the
     * composer's link ~4 GB, about 40 s serialized (87 MB: 0.6-0.8 s
     * through ssh, 0.82 s read from NFS uncached, lift11), where a host
     * reads the file from NFS for all its z3s.
     */
    private static final class SharedFiles {
        private final Path directory;
        private final ArtifactIO.Body shared;
        private final Map<Integer, Path> written =
                new HashMap<Integer, Path>();

        SharedFiles(Path directory, ArtifactIO.Body shared) {
            this.directory = directory;
            this.shared = shared;
        }

        /** The file of {@code arithmetic}, written by its first asker. */
        synchronized Path of(int arithmetic) throws IOException {
            Path file = written.get(arithmetic);
            if (file != null) return file;
            file = Files.createTempFile(directory,
                    "z3-shared-" + arithmetic + "-", ".smt2");
            file.toFile().deleteOnExit();
            try (BufferedWriter output = Files.newBufferedWriter(file,
                    StandardCharsets.UTF_8)) {
                output.write(head(false, arithmetic));
                Z3.EngineWriter engine = new Z3.EngineWriter(output,
                        arithmetic);
                BufferedWriter rewriting = new BufferedWriter(engine,
                        1 << 16);
                shared.writeTo(rewriting);
                rewriting.flush();
                engine.finish();
                output.write("\n");
            } catch (IOException | RuntimeException failed) {
                Files.deleteIfExists(file);
                throw failed;
            }
            written.put(arithmetic, file);
            return file;
        }

        synchronized void delete() {
            for (Path file : written.values()) {
                try {
                    Files.deleteIfExists(file);
                } catch (IOException kept) {
                    System.err.println("z3 scoped: " + file
                            + " not deleted: " + kept);
                }
            }
            written.clear();
        }
    }

    /**
     * Two decided answers to one question that differ: an error of the
     * solver's ({@code Z3#errors}, which refuses the claim by name) and an
     * undecided answer -- a scope leak or a solver fault is never a
     * verdict, let alone a refutation reused.
     */
    private Z3.Answer disagree(String how) {
        String error = Z3.DISAGREE + "a scoped question, " + how + "\")";
        solver.noteError(error);
        return bare(error, "");
    }

    private static Z3.Answer bare(String status, String reason) {
        return new Z3.Answer(status, Collections.<String, String>emptyMap(),
                Collections.<String>emptyList(), false, reason);
    }

    private static Z3.Answer memOut(int slotMb) {
        return bare(Z3.MEMOUT, "out of memory at its cap of "
                + (slotMb - Z3.MISSED_MB) + " MB (memory_max_size), scoped");
    }

    private static boolean memOut(List<String> lines) {
        for (String line : lines) {
            if (Z3.OUT_OF_MEMORY.equals(line.trim())) return true;
        }
        return false;
    }

    private static String echo(Mark mark) {
        return "(echo \"" + mark.text + "\")\n";
    }

    /**
     * A process's id, for SIGINT: {@code Process#pid} past Java 8, its
     * implementation's field on 8; -1 where neither is there (a cancel then
     * ends that z3).
     */
    static long pid(Process process) {
        try {
            return ((Number) Process.class.getMethod("pid").invoke(process))
                    .longValue();
        } catch (ReflectiveOperationException | RuntimeException none) {
            // Java 8: no such method.
        }
        try {
            Field field = process.getClass().getDeclaredField("pid");
            field.setAccessible(true);
            return field.getInt(process);
        } catch (ReflectiveOperationException | RuntimeException none) {
            return -1L;
        }
    }

    /** The pid a remote z3's shell printed; -1 where it is none (a cancel
     *  then ends that z3 by its silence). */
    private static long pidOf(String printed) {
        try {
            return Long.parseLong(printed.trim());
        } catch (NumberFormatException none) {
            return -1L;
        }
    }

    /** One question and its answer. */
    private static final class Question {
        final ArtifactIO.Body scope;
        final List<String> symbols;
        final long budgetMillis;
        /** Its asker's deadline ({@link #until}); 0: none. */
        final long deadlineNanos;
        private Z3.Answer answer;
        private boolean abandoned;

        Question(ArtifactIO.Body scope, List<String> symbols,
                 long budgetMillis, long deadlineNanos) {
            this.scope = scope;
            this.symbols = symbols;
            this.budgetMillis = budgetMillis;
            this.deadlineNanos = deadlineNanos;
        }

        /** {@code budget}, at most what its deadline leaves. */
        long left(long budget) {
            return deadlineNanos == 0L ? budget : Math.min(budget,
                    TimeUnit.NANOSECONDS.toMillis(deadlineNanos
                            - System.nanoTime()));
        }

        synchronized void answer(Z3.Answer given) {
            if (answer != null) return;
            answer = given;
            notifyAll();
        }

        synchronized boolean open() {
            return answer == null && !abandoned;
        }

        synchronized boolean abandoned() {
            return abandoned;
        }

        /** Its answer once given; undecided at once for an asker that
         *  stops, the question then cancelled. */
        synchronized Z3.Answer await() {
            while (answer == null) {
                try {
                    wait();
                } catch (InterruptedException stop) {
                    abandoned = true;
                    Thread.currentThread().interrupt();
                    return bare(Z3.TIMEOUT, "");
                }
            }
            return answer;
        }
    }

    /** What a pair's driver takes for "give the room back". */
    private static final Question YIELD = new Question(null, null, 0L, 0L);

    /** One line a scoped z3 printed; null text: its output ended. */
    private static final class Line {
        final Engine engine;
        final int generation;
        final String text;

        Line(Engine engine, int generation, String text) {
            this.engine = engine;
            this.generation = generation;
            this.text = text;
        }
    }

    /** What an echo mark closes. */
    private enum Role { STARTUP, BEGAN, VERDICT, PAYLOAD, POPPED }

    private static final class Mark {
        final String text;
        final Role role;
        final Turn turn;

        Mark(String text, Role role, Turn turn) {
            this.text = text;
            this.role = role;
            this.turn = turn;
        }
    }

    /** One engine's work on one question. */
    private static final class Turn {
        final Question question;
        final long budgetMillis;
        boolean cancelled;
        /** Between its began and verdict marks: in {@code check-sat}. */
        boolean solving;
        /** {@link System#nanoTime} past which its z3 is silent too long:
         *  its budget and a margin from when it was sent -- from the shared
         *  part read, on a fresh z3, and none while it is read (0) -- then
         *  from its check's start and from each payload asked. */
        long silentUntil;
        boolean retried;
        String verdict;
        Z3.Answer answer;
        /** Whether its answer decides the question, payload and all
         *  ({@code Z3#decided}). */
        boolean decided;

        Turn(Question question, long budgetMillis) {
            this.question = question;
            this.budgetMillis = budgetMillis;
        }

        boolean done() {
            return answer != null;
        }

        void end(Z3.Answer given, boolean decides) {
            if (answer != null) return;
            answer = given;
            decided = decides;
        }

        void bound() {
            silentUntil = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(
                    budgetMillis + SILENCE_MARGIN_MS);
        }
    }

    /**
     * The questions of one kind -- tracking named assertions or not -- in
     * the order they were put, and the pairs that ask them, each taking the
     * next open one.
     */
    private final class Lane {
        final boolean tracking;
        final List<Pair> pairs = new ArrayList<Pair>();
        private final Deque<Question> waiting = new ArrayDeque<Question>();
        private boolean started;
        private int driving;
        private volatile boolean closed;

        /** A pair in each of {@code rooms}. */
        Lane(boolean tracking, List<Z3.Room> rooms) {
            this.tracking = tracking;
            for (Z3.Room room : rooms) this.pairs.add(new Pair(this, room));
        }

        Z3.Answer ask(ArtifactIO.Body scope, List<String> symbols,
                      long budgetMillis, long deadlineNanos) {
            Question question = new Question(scope, symbols, budgetMillis,
                    deadlineNanos);
            // Past its deadline (Z3#until, #until) no question starts.
            if (solver.pastDeadline() || question.left(1L) <= 0L) {
                return bare(Z3.TIMEOUT, "");
            }
            synchronized (this) {
                if (closed) return bare(Z3.TIMEOUT, "");
                waiting.addLast(question);
                if (!started) {
                    started = true;
                    driving = pairs.size();
                    for (Pair pair : pairs) pair.start();
                }
                notifyAll();
            }
            return question.await();
        }

        /** The next open question for {@code pair}; {@link #YIELD} while
         *  none waits and another waits for the room the pair holds; null
         *  once closed. */
        synchronized Question next(Pair pair) throws InterruptedException {
            while (!closed) {
                Question head = waiting.pollFirst();
                if (head != null) {
                    if (head.open()) return head;
                    continue;
                }
                if (pair.holding && pair.room.contended()) return YIELD;
                wait(POLL_MILLIS);
            }
            return null;
        }

        /** A question a pair that asks no more left undecided, the next
         *  for the others. */
        synchronized void putBack(Question question) {
            waiting.addFirst(question);
            notifyAll();
        }

        /** A pair's driver stopped: the questions waiting are undecided
         *  where none drives any more, or the lane is closed. */
        List<Question> stopped() {
            List<Question> left = new ArrayList<Question>();
            synchronized (this) {
                if (--driving > 0 && !closed) return left;
                closed = true;
                left.addAll(waiting);
                waiting.clear();
            }
            return left;
        }

        /** Every driver told to stop at once, then waited for: a remote
         *  pair's end waits on ssh. */
        void close() {
            synchronized (this) {
                closed = true;
                notifyAll();
            }
            for (Pair pair : pairs) pair.stopDriving();
            for (Pair pair : pairs) pair.awaitDriver();
        }
    }

    /**
     * One z3 per engine over the shared part, of one lane, asking its
     * questions one at a time by one driver thread, the only one that
     * touches the z3s' state.
     */
    private final class Pair {
        final Lane lane;
        final boolean tracking;
        /** The room it holds its slots in: its z3s' host. */
        final Z3.Room room;
        /** The slot each of its z3s holds, in MB. */
        final int slotMb;
        private final Engine[] engines;
        private final BlockingQueue<Line> printed =
                new LinkedBlockingQueue<Line>();
        private Thread driver;
        /** The driver's own: whether it holds its slots, and since when;
         *  the engine whose answer the last race took (0: none); whether a
         *  z3 of it on another host never read the shared part, so it asks
         *  no more. */
        private boolean holding;
        private long heldSinceNanos;
        private int answeredBy;
        private boolean lost;

        Pair(Lane lane, Z3.Room room) {
            this.lane = lane;
            this.tracking = lane.tracking;
            this.room = room;
            this.slotMb = room.host == null ? Z3Incremental.this.slotMb
                    : PAIR_SLOT_MB;
            this.engines = new Engine[Z3.ARITHMETIC.length];
            for (int at = 0; at < engines.length; at++) {
                engines[at] = new Engine(this, Z3.ARITHMETIC[at]);
            }
        }

        private int need() {
            return Z3.ARITHMETIC.length * slotMb;
        }

        /** Its driver, started once by its lane. */
        void start() {
            driver = new Thread(this::drive, "graphchecker-z3-scopes"
                    + (tracking ? "-tracked" : ""));
            driver.setDaemon(true);
            driver.start();
        }

        private void drive() {
            Question question = null;
            try {
                while (true) {
                    question = lane.next(this);
                    if (question == null) return;
                    if (question == YIELD) {
                        release();
                        continue;
                    }
                    if (holding && room.contended()
                            && System.nanoTime() - heldSinceNanos
                            >= TimeUnit.MILLISECONDS.toNanos(YIELD_AFTER_MS)) {
                        release();
                    }
                    if (!holding) {
                        if (!room.take(need())) return;
                        holding = true;
                        heldSinceNanos = System.nanoTime();
                    }
                    Z3.Answer answer = asked(question);
                    // Its host gave it no z3: it asks no more, and what it
                    // left undecided the other pairs ask.
                    if (lost && !answer.decided()) {
                        lane.putBack(question);
                    } else {
                        question.answer(answer);
                    }
                    if (lost) {
                        question = null;
                        return;
                    }
                }
            } catch (InterruptedException closing) {
                // Closed: below.
            } catch (RuntimeException failed) {
                // Every question undecided from here on, and why said.
                System.err.println("scoped z3s stopped: " + failed);
                failed.printStackTrace();
            } finally {
                release();
                List<Question> left = lane.stopped();
                if (question != null && question != YIELD) left.add(question);
                for (Question each : left) each.answer(bare(Z3.TIMEOUT, ""));
            }
        }

        /** One question asked: counted and logged as a run is. */
        private Z3.Answer asked(Question question)
                throws InterruptedException {
            long budget = question.left(solver.budgetLeft(
                    question.budgetMillis));
            if (budget <= 0L) return bare(Z3.TIMEOUT, "");
            int run = solver.countRun();
            long started = System.nanoTime();
            Z3.Answer answer = race(question, budget, started);
            Z3.said(run, "check-sat, scoped" + (answeredBy == 0 ? ""
                    : " on " + answeredBy), answer.status(), started);
            return answer;
        }

        /**
         * Both engines on {@code question}, a z3 not running started first:
         * the preferred engine's decided answer; the other's once it has
         * decided and the preferred one has not within as long again as the
         * other took, at least {@link Z3#PREFERRED_GRACE_MILLIS} -- at once
         * where the question asks no model and no core, whose verdict is the
         * same whichever engine gives it ({@code Z3#race}); neither
         * deciding, the preferred one's.  Both decided and differing:
         * neither ({@link #disagree}).  Its turns still running are
         * cancelled, and every scope popped.
         */
        private Z3.Answer race(Question question, long budget, long started)
                throws InterruptedException {
            drain();
            answeredBy = 0;
            boolean payload = tracking || !question.symbols.isEmpty();
            Turn[] turns = new Turn[engines.length];
            for (int at = 0; at < engines.length; at++) {
                turns[at] = engines[at].ask(question, budget);
            }
            Turn winner = null;
            long otherDecided = 0L;
            try {
                while (true) {
                    long now = System.nanoTime();
                    if (turns[0].decided) {
                        winner = turns[0];
                        break;
                    }
                    if (turns[1].decided) {
                        if (otherDecided == 0L) otherDecided = now;
                        long grace = Math.max(otherDecided - started,
                                TimeUnit.MILLISECONDS.toNanos(
                                        Z3.PREFERRED_GRACE_MILLIS));
                        if (!payload || turns[0].done()
                                || now - otherDecided >= grace) {
                            winner = turns[1];
                            break;
                        }
                    }
                    if (turns[0].done() && turns[1].done()) {
                        winner = turns[0];
                        break;
                    }
                    if (question.abandoned() || lane.closed
                            || solver.pastDeadline()
                            || question.left(1L) <= 0L) {
                        break;
                    }
                    for (Engine engine : engines) engine.silent(now);
                    Line line = printed.poll(POLL_MILLIS,
                            TimeUnit.MILLISECONDS);
                    while (line != null) {
                        line.engine.take(line);
                        line = printed.poll();
                    }
                }
            } finally {
                // A verdict printed just now, or in a moment, is no check to
                // cancel.
                drain();
                long until = System.nanoTime() + TimeUnit.MILLISECONDS
                        .toNanos(CANCEL_GRACE_MILLIS);
                while (solving() && System.nanoTime() - until < 0L) {
                    Line line = printed.poll(5L, TimeUnit.MILLISECONDS);
                    if (line != null) line.engine.take(line);
                }
                for (Engine engine : engines) engine.endTurn();
            }
            if (winner == null) return bare(Z3.TIMEOUT, "");
            if (turns[0].decided && turns[1].decided && !turns[0].answer
                    .status().equals(turns[1].answer.status())) {
                return disagree("engine " + engines[0].arithmetic + " "
                        + turns[0].answer.status() + ", engine "
                        + engines[1].arithmetic + " "
                        + turns[1].answer.status());
            }
            answeredBy = winner == turns[0] ? engines[0].arithmetic
                    : engines[1].arithmetic;
            return winner.answer;
        }

        /** Whether an engine's turn is in its check, unanswered. */
        private boolean solving() {
            for (Engine engine : engines) {
                if (engine.turn != null && !engine.turn.done()
                        && engine.turn.solving) {
                    return true;
                }
            }
            return false;
        }

        /** Every line printed so far, taken. */
        private void drain() {
            Line line = printed.poll();
            while (line != null) {
                line.engine.take(line);
                line = printed.poll();
            }
        }

        /** Its z3s ended, and its room given back. */
        private void release() {
            for (Engine engine : engines) engine.stop();
            printed.clear();
            if (holding) {
                room.give(need());
                holding = false;
            }
        }

        void stopDriving() {
            Thread running = driver;
            if (running != null) running.interrupt();
        }

        void awaitDriver() {
            Thread running = driver;
            if (running == null) return;
            try {
                running.join(TimeUnit.SECONDS.toMillis(
                        2 * Z3.ORPHAN_MARGIN_SECONDS));
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }

    /** One engine's z3 of a pair, and the marks it is yet to print. */
    private final class Engine {
        private final Pair pair;
        private final int arithmetic;
        /** Whether its z3 runs on another host. */
        private final boolean remote;
        private Process process;
        /** Its z3's pid on its host: a remote one's once printed. */
        private long pid = -1L;
        /** {@link System#nanoTime} by which a remote z3 has read the shared
         *  part or its pair asks no more ({@link #REMOTE_READ_MS}). */
        private long readBy;
        /** Which of this engine's z3s runs: an earlier one's lines are
         *  dropped. */
        private int generation;
        private ExecutorService writer;
        private Writer input;
        private int marks;
        private final Deque<Mark> expected = new ArrayDeque<Mark>();
        /** What its z3 printed since the last mark. */
        private final List<String> collected = new ArrayList<String>();
        /** This question's turn, until the race ends. */
        private Turn turn;
        /** The checks its z3 ran to an answer: one that ran out of memory
         *  after some is asked again of a fresh z3, once. */
        private int answered;
        /**
         * A SIGINT sent for a cancelled check that may not have ended it:
         * one that ended before the signal came leaves the signal to a
         * later question -- whose check it cancels, or, landing outside a
         * check, the z3 -- so a question that dies or answers "canceled"
         * meanwhile is asked again, once.  Cleared once the signalled check
         * answers unknown, or a later one decides.
         */
        private boolean interruptOutstanding;
        private Turn signalled;
        /** The last check signalled and not yet answered, and when its z3
         *  is stopped if it has not answered by then. */
        private Turn cancelling;
        private long cancelDeadline;
        /** A cancelled check its z3 reached after its race ended, signalled
         *  at this time unless its verdict shows first
         *  ({@link #CANCEL_GRACE_MILLIS}); 0: none. */
        private Turn signalTurn;
        private long signalDue;

        Engine(Pair pair, int arithmetic) {
            this.pair = pair;
            this.arithmetic = arithmetic;
            this.remote = pair.room.host != null;
        }

        /** {@code question} put to its z3, one started first. */
        Turn ask(Question question, long budget) {
            Turn asked = new Turn(question, budget);
            turn = asked;
            if (process == null && !start()) {
                asked.end(bare("error a scoped z3 did not start", ""), false);
                return asked;
            }
            send(asked);
            return asked;
        }

        private void send(Turn asked) {
            // Behind a shared part still read, its silence counts from the
            // read's end (STARTUP), never the read itself.
            if (reading()) asked.silentUntil = 0L;
            else asked.bound();
            Mark began = mark(Role.BEGAN, asked);
            Mark verdict = mark(Role.VERDICT, asked);
            send("(push 1)\n(set-option :timeout " + asked.budgetMillis
                    + ")\n", asked.question.scope, "\n" + echo(began)
                    + "(check-sat)\n" + echo(verdict));
        }

        /** Its z3, started on the shared part: here, or on its host
         *  reading it from its file ({@link Z3Incremental#remote}). */
        private boolean start() {
            long life = solver.budgetLeft(UNBOUNDED_LIFE_MS);
            if (life <= 0L) return false;
            List<String> command = Z3.command(solver.executable(),
                    pair.slotMb, life);
            Process started;
            try {
                if (remote) {
                    command = remote(pair.room, command,
                            files.of(arithmetic));
                }
                ProcessBuilder builder = new ProcessBuilder(command);
                builder.redirectErrorStream(true);
                started = builder.start();
            } catch (IOException notLaunched) {
                if (remote) lose(notLaunched.toString());
                return false;
            }
            Z3.track(started);
            process = started;
            pid = remote ? -1L : pid(started);
            readBy = System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(
                    REMOTE_READ_MS);
            int born = ++generation;
            System.err.println("z3 scoped: engine " + arithmetic
                    + (pair.tracking ? " tracking" : "") + " started ("
                    + born + ")" + (remote ? " on " + pair.room.host : "")
                    + ", reading the shared part");
            expected.clear();
            collected.clear();
            answered = 0;
            interruptOutstanding = false;
            signalled = null;
            cancelling = null;
            cancelDeadline = 0L;
            signalTurn = null;
            signalDue = 0L;
            Thread reader = new Thread(() -> {
                try (BufferedReader output = new BufferedReader(
                        new InputStreamReader(started.getInputStream(),
                                StandardCharsets.UTF_8))) {
                    for (String line = output.readLine(); line != null;
                         line = output.readLine()) {
                        pair.printed.add(new Line(this, born, line));
                    }
                } catch (IOException ended) {
                    // Its end, below.
                }
                pair.printed.add(new Line(this, born, null));
            }, "graphchecker-z3-scope-reader");
            reader.setDaemon(true);
            reader.start();
            writer = Executors.newSingleThreadExecutor(work -> {
                Thread thread = new Thread(work,
                        "graphchecker-z3-scope-writer");
                thread.setDaemon(true);
                return thread;
            });
            input = new BufferedWriter(new OutputStreamWriter(
                    started.getOutputStream(), StandardCharsets.UTF_8),
                    1 << 16);
            Mark ready = mark(Role.STARTUP, null);
            // A remote z3 reads its head and the shared part from its file.
            if (remote) {
                send("", null, echo(ready));
            } else {
                send(head(pair.tracking, arithmetic), shared,
                        "\n" + echo(ready));
            }
            return true;
        }

        /** Whether its z3 is still reading the shared part. */
        private boolean reading() {
            for (Mark mark : expected) {
                if (mark.role == Role.STARTUP) return true;
            }
            return false;
        }

        private Mark mark(Role role, Turn of) {
            Mark mark = new Mark("@@graphchecker-" + (++marks), role, of);
            expected.addLast(mark);
            return mark;
        }

        /** Written in order by its writer thread: the driver never blocks
         *  on a z3 still reading. */
        private void send(String head, ArtifactIO.Body body, String tail) {
            Writer to = input;
            try {
                writer.execute(() -> {
                    try {
                        to.write(head);
                        if (body != null) {
                            Z3.EngineWriter engine =
                                    new Z3.EngineWriter(to, arithmetic);
                            BufferedWriter rewriting =
                                    new BufferedWriter(engine, 1 << 16);
                            body.writeTo(rewriting);
                            rewriting.flush();
                            engine.finish();
                        }
                        to.write(tail);
                        to.flush();
                    } catch (IOException ended) {
                        // Its z3 is gone: its reader says so.
                    }
                });
            } catch (RejectedExecutionException stopped) {
                // Its z3 ended already.
            }
        }

        /** One line its z3 printed. */
        void take(Line line) {
            if (line.generation != generation || process == null) return;
            if (line.text == null) {
                ended();
                return;
            }
            String text = line.text.trim();
            if (remote && pid <= 0L && text.startsWith(PID.trim())) {
                // Its shell's first line, before anything z3 prints.
                pid = pidOf(text.substring(PID.trim().length()));
                return;
            }
            Mark head = expected.peekFirst();
            if (head != null && text.equals(head.text)) {
                expected.pollFirst();
                reached(head);
                return;
            }
            if (text.startsWith(ERROR) && !Z3.OUT_OF_MEMORY.equals(text)) {
                solver.noteError(text);
            }
            collected.add(line.text);
        }

        private void reached(Mark mark) {
            List<String> lines = new ArrayList<String>(collected);
            collected.clear();
            Turn of = mark.turn;
            switch (mark.role) {
                case BEGAN:
                    of.solving = true;
                    of.bound();
                    if (of.cancelled) {
                        // Read late, its check may have ended already:
                        // signalled only if no verdict shows in its grace.
                        signalTurn = of;
                        signalDue = System.nanoTime() + TimeUnit.MILLISECONDS
                                .toNanos(CANCEL_GRACE_MILLIS);
                    }
                    return;
                case VERDICT:
                    of.solving = false;
                    if (of.cancelled) {
                        answered++;
                        if (of == cancelling) cancelDeadline = 0L;
                        if (of == signalTurn) signalDue = 0L;
                        // Unknown: the signal ended it; decided, it ended
                        // first and the signal is still to land.
                        if (of == signalled && !"sat".equals(first(lines))
                                && !"unsat".equals(first(lines))) {
                            interruptOutstanding = false;
                        }
                        return;
                    }
                    verdict(of, lines);
                    return;
                case PAYLOAD:
                    if (!of.cancelled) payload(of, lines);
                    return;
                case STARTUP:
                    // The shared part read: an open question sent behind
                    // it is silent from here, not from its send.
                    if (turn != null && !turn.done() && !turn.solving) {
                        turn.bound();
                    }
                    return;
                default:
            }
        }

        /** Its verdict, and the payload it calls for asked. */
        private void verdict(Turn of, List<String> lines) {
            String status = first(lines);
            of.verdict = status;
            // At its cap z3 ends: ended() answers, or asks again.
            if (Z3.MEMOUT.equals(status)) return;
            answered++;
            if ("sat".equals(status) || "unsat".equals(status)) {
                interruptOutstanding = false;
            }
            if ("sat".equals(status)) {
                if (of.question.symbols.isEmpty()) {
                    of.end(bare("sat", ""), true);
                } else {
                    request(of, Z3.getValue(of.question.symbols));
                }
            } else if ("unsat".equals(status)) {
                if (pair.tracking) request(of, "(get-unsat-core)\n");
                else of.end(bare("unsat", ""), true);
            } else {
                request(of, "(get-info :reason-unknown)\n");
            }
        }

        private void request(Turn of, String command) {
            Mark printed = mark(Role.PAYLOAD, of);
            of.bound();
            send(command, null, echo(printed));
        }

        /** A sat's model, an unsat's core, an undecided one's reason -- a
         *  timeout's ({@code :timeout}, a cancel) read as Z3's timeout. */
        private void payload(Turn of, List<String> lines) {
            String text = of.verdict + "\n" + String.join("\n", lines);
            if ("sat".equals(of.verdict)) {
                of.end(new Z3.Answer("sat", Z3.parseValues(text),
                        Collections.<String>emptyList(), false, ""), true);
            } else if ("unsat".equals(of.verdict)) {
                boolean known = Z3.payload(text)
                        && Z3.answerBlock(text, true) != null;
                of.end(new Z3.Answer("unsat",
                        Collections.<String, String>emptyMap(),
                        known ? Z3.parseCore(text)
                                : Collections.<String>emptyList(), known,
                        ""), true);
            } else {
                String reason = Z3.parseReason(text);
                if (interrupted(reason) && interruptOutstanding
                        && !of.retried) {
                    // A signal meant for a check before it.
                    again(of);
                    return;
                }
                of.end(reason.contains("timeout") || interrupted(reason)
                        ? bare(Z3.TIMEOUT, "")
                        : bare(of.verdict, reason), false);
            }
        }

        /** Whether z3 said its check was ended from outside: SIGINT under
         *  its tactic solver ("interrupted from keyboard", z3 4.14.1), or
         *  its incremental core's "canceled", which a timeout says too. */
        private boolean interrupted(String reason) {
            return reason.contains("interrupted") || reason.contains("canceled");
        }

        /** {@code of} asked once more: of this z3, its scope popped first,
         *  or of a fresh one. */
        private void again(Turn of) {
            of.retried = true;
            of.verdict = null;
            of.solving = false;
            interruptOutstanding = false;
            if (process != null) {
                Mark popped = mark(Role.POPPED, null);
                send("(pop 1)\n", null, echo(popped));
                send(of);
            } else if (start()) {
                send(of);
            } else {
                of.end(bare("error a scoped z3 did not start", ""), false);
            }
        }

        /** The first line no warning ({@code Z3#answerOf}), its cap's error
         *  read as {@link Z3#MEMOUT}. */
        private String first(List<String> lines) {
            for (String line : lines) {
                if (line.startsWith("WARNING:")) continue;
                String said = line.trim();
                return Z3.OUT_OF_MEMORY.equals(said) ? Z3.MEMOUT : said;
            }
            return "";
        }

        /**
         * Its z3 ended: its turn, open, answers nothing -- a memout where its
         * cap ended it, an unsat whose core it cut with its core unknown --
         * unless it is asked once more of a fresh z3: where its z3 ended
         * before reaching it, where a signal meant for an earlier check was
         * outstanding, or where its z3 ran out of memory after answering
         * others (one that ended reading the shared part would end again;
         * on another host its pair asks no more there, {@link #lose}).
         */
        private void ended() {
            Turn of = turn;
            boolean memOut = memOut(collected)
                    || (of != null && Z3.MEMOUT.equals(of.verdict));
            Mark head = expected.peekFirst();
            boolean stray = interruptOutstanding;
            boolean aged = answered > 0;
            boolean unread = head != null && head.role == Role.STARTUP;
            String said = String.join(" | ", collected);
            stop();
            if (remote && unread) lose("ended first, saying: " + said);
            if (of == null || of.done() || of.cancelled) return;
            boolean before = head != null && head.turn != of
                    && head.role != Role.STARTUP;
            if ((before || stray || (memOut && aged)) && !of.retried) {
                again(of);
                return;
            }
            if ("unsat".equals(of.verdict)) {
                of.end(new Z3.Answer("unsat",
                        Collections.<String, String>emptyMap(),
                        Collections.<String>emptyList(), false, ""), false);
            } else {
                of.end(memOut ? memOut(pair.slotMb)
                        : bare("", "its scoped z3 ended"), false);
            }
        }

        /**
         * Its pair on another host asks no more: its z3 did not read the
         * shared part ({@code why}).  Said once.
         */
        private void lose(String why) {
            if (pair.lost) return;
            pair.lost = true;
            System.err.println("z3 scoped: engine " + arithmetic + " on "
                    + pair.room.host + " did not read the shared part ("
                    + why + "): its pair asks no more");
        }

        /**
         * Its z3 ended where it is silent too long: a cancelled check no
         * verdict of which came within {@link #SILENCE_MARGIN_MS} -- the
         * open turn behind it asked once more of a fresh z3 -- or its own
         * turn past its budget and margin, a timeout; or a z3 on another
         * host that has not read the shared part by {@link #readBy}, its
         * pair then asking no more there.
         */
        void silent(long now) {
            Turn of = turn;
            if (process != null && remote && now - readBy >= 0L
                    && reading()) {
                lose("not within " + REMOTE_READ_MS + " ms");
                stop();
            }
            if (process == null) {
                // No z3 left to answer it (once asked again already).
                if (of != null && !of.done()) {
                    of.end(bare(Z3.TIMEOUT, ""), false);
                }
                return;
            }
            if (signalDue != 0L && now - signalDue >= 0L) {
                signalDue = 0L;
                if (signalTurn.solving) interrupt(signalTurn);
            }
            if (cancelDeadline != 0L && now - cancelDeadline >= 0L) {
                stop();
                if (of != null && !of.done()) {
                    if (of.retried) of.end(bare(Z3.TIMEOUT, ""), false);
                    else again(of);
                }
                return;
            }
            if (of == null || of.done() || process == null
                    || of.silentUntil == 0L || now - of.silentUntil < 0L) {
                return;
            }
            stop();
            of.end(bare(Z3.TIMEOUT, ""), false);
        }

        /** The race over: a check still running cancelled -- now, or once
         *  its z3 reaches it -- and the scope popped. */
        void endTurn() {
            Turn of = turn;
            turn = null;
            if (of == null) return;
            if (!of.done()) {
                of.cancelled = true;
                if (of.solving) interrupt(of);
            }
            if (process != null) {
                Mark popped = mark(Role.POPPED, null);
                send("(pop 1)\n", null, echo(popped));
            }
        }

        /**
         * SIGINT for {@code of}'s check: z3 ends the check it runs and reads
         * on.  Never its z3 ended here: what it printed after this check --
         * a later question's answer, its end -- is still to be read.  A z3
         * gone already ends by its own output; one no signal reached (no
         * process id) runs the check out to its {@code :timeout}, or is
         * stopped silent ({@link #silent}).
         *
         * <p>Sent only to a z3 that runs -- in its check, not waiting for
         * input -- so a check that ended while the signal was on its way
         * leaves its z3 reading on, its verdict still to come, where the
         * signal would end it: the kill takes 0.3-0.4 s over ssh (lift11)
         * where it took milliseconds here.  A signal sent is outstanding
         * until the check answers ({@link #interruptOutstanding}), and has
         * landed before anything more is sent to its z3: {@link #signal}
         * waits for it, so a later check that decides tells it landed
         * before.</p>
         */
        private void interrupt(Turn of) {
            if (pid <= 0L || process == null || !process.isAlive()) return;
            cancelling = of;
            if (signal("grep -qs '^State:.R' /proc/" + pid + "/status"
                    + " && kill -INT " + pid)) {
                interruptOutstanding = true;
                signalled = of;
            }
            cancelDeadline = System.nanoTime() + TimeUnit.MILLISECONDS
                    .toNanos(SILENCE_MARGIN_MS);
        }

        /**
         * A shell line run on its z3's host ({@code Z3.Room#reach}), here in
         * a shell of its own, and waited for -- at most {@link
         * Z3#ORPHAN_MARGIN_SECONDS} -- even by a driver told to close, which
         * is told again after: whether it may have done its work, false
         * where it said it did not.  Not sent, a SIGINT's check runs out to
         * its {@code :timeout}, a KILL's z3 ends with its ssh.
         */
        private boolean signal(String line) {
            List<String> command = new ArrayList<String>(pair.room.reach);
            if (command.isEmpty()) command.addAll(Arrays.asList("sh", "-c"));
            command.add(line);
            boolean closing = Thread.interrupted();
            try {
                Process kill = new ProcessBuilder(command)
                        .redirectErrorStream(true).start();
                kill.getOutputStream().close();
                if (!kill.waitFor(Z3.ORPHAN_MARGIN_SECONDS,
                        TimeUnit.SECONDS)) {
                    kill.destroyForcibly();
                    return true;
                }
                return kill.exitValue() == 0;
            } catch (IOException notSent) {
                return false;
            } catch (InterruptedException interrupted) {
                closing = true;
                return true;
            } finally {
                if (closing) Thread.currentThread().interrupt();
            }
        }

        /** Its z3 ended, if running, and what it printed dropped. */
        void stop() {
            Process ending = process;
            if (ending == null) return;
            long ended = pid;
            process = null;
            pid = -1L;
            generation++;
            expected.clear();
            collected.clear();
            // On another host, z3 first: its ssh's end reaches it only once
            // that host's sshd sees the connection closed.
            if (remote && ended > 0L && ending.isAlive()) {
                signal("kill -KILL " + ended);
            }
            // Its streams close with it: a write blocked on it fails.
            ending.destroyForcibly();
            writer.shutdownNow();
            try {
                ending.waitFor(Z3.ORPHAN_MARGIN_SECONDS, TimeUnit.SECONDS);
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
            Z3.untrack(ending);
        }
    }
}
