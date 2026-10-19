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
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

public final class Z3Incremental implements AutoCloseable {

    static final int SOLVER2_TIMEOUT_MS = 1000;

    static final long YIELD_AFTER_MS = 30_000L;

    static final long SILENCE_MARGIN_MS = 10_000L;

    static final long UNBOUNDED_LIFE_MS = 3_600_000L;

    static final long CANCEL_GRACE_MILLIS = 50L;

    static final int PAIR_SLOT_MB = 1024;

    static final long REMOTE_READ_MS = 120_000L;

    static final int SSH_STARTS_PER_HOST = 4;

    static final int SSH_ATTEMPTS = 3;

    static final long SSH_RETRY_MS = 1_000L;

    private static final Map<String, Semaphore> SSH_STARTS =
            new ConcurrentHashMap<String, Semaphore>();

    static final String PID = "@@graphchecker-pid ";

    private static final long POLL_MILLIS = 200L;

    private static final String ERROR = "(error ";

    private final Z3 solver;
    private final ArtifactIO.Body shared;
    private final int slotMb;
    private final AtomicInteger outgrownMb;
    private final Lane plain;
    private final Lane tracked;
    private final SharedFiles files;
    private final long deadlineNanos;

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
        this.outgrownMb = new AtomicInteger();
        this.plain = new Lane(false, placed);
        this.tracked = new Lane(true,
                Collections.singletonList(solver.room()));
        this.files = new SharedFiles(solver.visible(), shared);
        this.deadlineNanos = 0L;
        System.err.println("z3 scoped: " + placed.size()
                + " plain pair(s): " + where(placed) + "; the tracking one"
                + " here; an engine starts at " + PAIR_SLOT_MB + " MB on"
                + " another host, " + slotMb + " MB here");
    }

    private Z3Incremental(Z3Incremental scopes, long deadlineNanos) {
        this.solver = scopes.solver;
        this.shared = scopes.shared;
        this.slotMb = scopes.slotMb;
        this.outgrownMb = scopes.outgrownMb;
        this.plain = scopes.plain;
        this.tracked = scopes.tracked;
        this.files = scopes.files;
        this.deadlineNanos = deadlineNanos;
    }

    private static int fit(int roomMb) {
        return roomMb / (Z3.ARITHMETIC.length * PAIR_SLOT_MB);
    }

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

    public static int placeable(Z3 solver) {
        return placed(solver, Integer.MAX_VALUE).size();
    }

    static String where(List<Z3.Room> placed) {
        StringBuilder said = new StringBuilder();
        for (Z3.Room room : new LinkedHashSet<Z3.Room>(placed)) {
            said.append(said.length() == 0 ? "" : ", ")
                    .append(Collections.frequency(placed, room))
                    .append(room.host == null ? " here" : " on " + room.host);
        }
        return said.toString();
    }

    public Z3Incremental until(long deadlineNanos) {
        return new Z3Incremental(this, deadlineNanos);
    }

    public Z3.Answer ask(ArtifactIO.Body scope, List<String> modelSymbols,
                         boolean wantCore, long budgetMillis) {
        List<String> symbols = modelSymbols == null
                ? Collections.<String>emptyList() : modelSymbols;
        return (wantCore ? tracked : plain).ask(scope, symbols,
                budgetMillis > 0L ? budgetMillis : solver.timeoutMillis(),
                deadlineNanos);
    }

    @Override
    public void close() {
        plain.close();
        tracked.close();
        files.delete();
    }

    private static String head(boolean tracking, int arithmetic) {
        return (tracking ? Z3.CORE_TRACKING : "")
                + "(set-option :combined_solver.solver2_timeout "
                + SOLVER2_TIMEOUT_MS + ")\n"
                + Z3.arithmeticOption(arithmetic) + "\n";
    }

    static List<String> remote(Z3.Room room, List<String> z3, Path file) {
        StringBuilder line = new StringBuilder("echo " + PID + "$$; exec");
        for (String word : z3) line.append(' ').append(quoted(word));
        line.append(" < <(cat ").append(quoted(file.toString()))
                .append(" && cat -) 2>&1");
        List<String> command = new ArrayList<String>(room.reach);
        command.add("exec env -u BASH_ENV -u SSH_CLIENT -u SSH2_CLIENT"
                + " bash -c " + quoted(line.toString()));
        return command;
    }

    private static String quoted(String word) {
        return "'" + word.replace("'", "'\\''") + "'";
    }

    private static final class SharedFiles {
        private final Path directory;
        private final ArtifactIO.Body shared;
        private final Map<Integer, Path> written =
                new HashMap<Integer, Path>();

        SharedFiles(Path directory, ArtifactIO.Body shared) {
            this.directory = directory;
            this.shared = shared;
        }

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

    static long pid(Process process) {
        try {
            return ((Number) Process.class.getMethod("pid").invoke(process))
                    .longValue();
        } catch (ReflectiveOperationException | RuntimeException none) {
        }
        try {
            Field field = process.getClass().getDeclaredField("pid");
            field.setAccessible(true);
            return field.getInt(process);
        } catch (ReflectiveOperationException | RuntimeException none) {
            return -1L;
        }
    }

    private static long pidOf(String printed) {
        try {
            return Long.parseLong(printed.trim());
        } catch (NumberFormatException none) {
            return -1L;
        }
    }

    private static final class Question {
        final ArtifactIO.Body scope;
        final List<String> symbols;
        final long budgetMillis;
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

    private static final Question YIELD = new Question(null, null, 0L, 0L);

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

    private static final class Turn {
        final Question question;
        final long budgetMillis;
        boolean cancelled;
        boolean solving;
        long silentUntil;
        boolean retried;
        String verdict;
        Z3.Answer answer;
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

    private final class Lane {
        final boolean tracking;
        final List<Pair> pairs = new ArrayList<Pair>();
        private final Deque<Question> waiting = new ArrayDeque<Question>();
        private boolean started;
        private int driving;
        private volatile boolean closed;

        Lane(boolean tracking, List<Z3.Room> rooms) {
            this.tracking = tracking;
            for (Z3.Room room : rooms) this.pairs.add(new Pair(this, room));
        }

        Z3.Answer ask(ArtifactIO.Body scope, List<String> symbols,
                      long budgetMillis, long deadlineNanos) {
            Question question = new Question(scope, symbols, budgetMillis,
                    deadlineNanos);
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

        synchronized void putBack(Question question) {
            waiting.addFirst(question);
            notifyAll();
        }

        boolean holds(Pair asking, int slot) {
            for (Pair pair : pairs) {
                if (pair != asking && !pair.lost && pair.largest() >= slot) {
                    return true;
                }
            }
            return false;
        }

        boolean served(Pair asking) {
            for (Pair pair : pairs) {
                if (pair != asking && pair.holding) return true;
            }
            return false;
        }

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

        void close() {
            synchronized (this) {
                closed = true;
                notifyAll();
            }
            for (Pair pair : pairs) pair.stopDriving();
            for (Pair pair : pairs) pair.awaitDriver();
        }
    }

    private final class Pair {
        final Lane lane;
        final boolean tracking;
        final Z3.Room room;
        private int slotMb;
        private final Engine[] engines;
        private final BlockingQueue<Line> printed =
                new LinkedBlockingQueue<Line>();
        private Thread driver;
        private volatile boolean holding;
        private long heldSinceNanos;
        private int answeredBy;
        private volatile boolean lost;

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

        int largest() {
            return room.mb / Z3.ARITHMETIC.length;
        }

        private int wanted() {
            int slot = Math.max(slotMb, outgrownMb.get());
            if (slot <= largest()) return slot;
            return lane.holds(this, slot) ? 0 : largest();
        }

        private boolean outgrown(Z3.Answer answer) {
            int bigger = 2 * slotMb;
            if (!answer.memOut() || (slotMb >= largest()
                    && !lane.holds(this, bigger))) {
                return false;
            }
            if (outgrownMb.getAndAccumulate(bigger, Math::max) < bigger) {
                System.err.println("z3 scoped: an engine"
                        + (room.host == null ? "" : " on " + room.host)
                        + " ran out of memory at " + slotMb + " MB: the"
                        + " pairs run at " + bigger + " MB an engine");
            }
            return true;
        }

        private boolean hold() throws InterruptedException {
            int slot = wanted();
            if (slot == 0) {
                lost = true;
                System.err.println("z3 scoped: a pair"
                        + (room.host == null ? " here" : " on " + room.host)
                        + " holds no " + Math.max(slotMb, outgrownMb.get())
                        + " MB an engine, another pair does: it asks no"
                        + " more");
                return false;
            }
            if (slot != slotMb) {
                release();
                slotMb = slot;
            }
            if (holding) return true;
            if (!room.tryTake(need())) {
                if (lane.served(this)) {
                    room.await(POLL_MILLIS);
                    return false;
                }
                if (!room.take(need())) return false;
            }
            holding = true;
            heldSinceNanos = System.nanoTime();
            return true;
        }

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
                    if (!hold()) {
                        if (lost || lane.closed) return;
                        continue;
                    }
                    question = lane.next(this);
                    if (question == null) return;
                    if (question == YIELD) {
                        release();
                        continue;
                    }
                    if (wanted() != slotMb || (room.contended()
                            && System.nanoTime() - heldSinceNanos
                            >= TimeUnit.MILLISECONDS.toNanos(YIELD_AFTER_MS))) {
                        release();
                        lane.putBack(question);
                        question = null;
                        continue;
                    }
                    Z3.Answer answer = asked(question);
                    if ((lost && !answer.decided()) || outgrown(answer)) {
                        lane.putBack(question);
                    } else {
                        question.answer(answer);
                    }
                    question = null;
                    if (lost) return;
                }
            } catch (InterruptedException closing) {
            } catch (RuntimeException failed) {
                System.err.println("scoped z3s stopped: " + failed);
                failed.printStackTrace();
            } finally {
                release();
                List<Question> left = lane.stopped();
                if (question != null && question != YIELD) left.add(question);
                for (Question each : left) each.answer(bare(Z3.TIMEOUT, ""));
            }
        }

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

        private boolean solving() {
            for (Engine engine : engines) {
                if (engine.turn != null && !engine.turn.done()
                        && engine.turn.solving) {
                    return true;
                }
            }
            return false;
        }

        private void drain() {
            Line line = printed.poll();
            while (line != null) {
                line.engine.take(line);
                line = printed.poll();
            }
        }

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

    private final class Engine {
        private final Pair pair;
        private final int arithmetic;
        private final boolean remote;
        private Process process;
        private long pid = -1L;
        private long readBy;
        private int generation;
        private ExecutorService writer;
        private Writer input;
        private int marks;
        private final Deque<Mark> expected = new ArrayDeque<Mark>();
        private final List<String> collected = new ArrayList<String>();
        private Turn turn;
        private int answered;
        private boolean interruptOutstanding;
        private Turn signalled;
        private Turn cancelling;
        private long cancelDeadline;
        private Turn signalTurn;
        private long signalDue;
        private volatile AtomicBoolean handshaking = new AtomicBoolean();
        private int refusals;

        Engine(Pair pair, int arithmetic) {
            this.pair = pair;
            this.arithmetic = arithmetic;
            this.remote = pair.room.host != null;
        }

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
            if (reading()) asked.silentUntil = 0L;
            else asked.bound();
            Mark began = mark(Role.BEGAN, asked);
            Mark verdict = mark(Role.VERDICT, asked);
            send("(push 1)\n(set-option :timeout " + asked.budgetMillis
                    + ")\n", asked.question.scope, "\n" + echo(began)
                    + "(check-sat)\n" + echo(verdict));
        }

        private boolean start() {
            long life = solver.budgetLeft(UNBOUNDED_LIFE_MS);
            if (life <= 0L) return false;
            List<String> command = Z3.command(solver.executable(),
                    pair.slotMb, life);
            Process started;
            AtomicBoolean handshake = null;
            try {
                if (remote) {
                    command = remote(pair.room, command,
                            files.of(arithmetic));
                    handshake = handshake();
                }
                ProcessBuilder builder = new ProcessBuilder(command);
                builder.redirectErrorStream(true);
                started = builder.start();
            } catch (IOException notLaunched) {
                if (remote) {
                    handshook(handshake);
                    lose(notLaunched.toString());
                }
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
            AtomicBoolean shaking = handshake;
            Thread reader = new Thread(() -> {
                try (BufferedReader output = new BufferedReader(
                        new InputStreamReader(started.getInputStream(),
                                StandardCharsets.UTF_8))) {
                    for (String line = output.readLine(); line != null;
                         line = output.readLine()) {
                        if (line.trim().startsWith(PID.trim())) {
                            handshook(shaking);
                        }
                        pair.printed.add(new Line(this, born, line));
                    }
                } catch (IOException ended) {
                }
                handshook(shaking);
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
            if (remote) {
                send("", null, echo(ready));
            } else {
                send(head(pair.tracking, arithmetic), shared,
                        "\n" + echo(ready));
            }
            return true;
        }

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
                    }
                });
            } catch (RejectedExecutionException stopped) {
            }
        }

        void take(Line line) {
            if (line.generation != generation || process == null) return;
            if (line.text == null) {
                ended();
                return;
            }
            String text = line.text.trim();
            if (remote && pid <= 0L && text.startsWith(PID.trim())) {
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
                    if (turn != null && !turn.done() && !turn.solving) {
                        turn.bound();
                    }
                    return;
                default:
            }
        }

        private void verdict(Turn of, List<String> lines) {
            String status = first(lines);
            of.verdict = status;
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
                    again(of);
                    return;
                }
                of.end(reason.contains("timeout") || interrupted(reason)
                        ? bare(Z3.TIMEOUT, "")
                        : bare(of.verdict, reason), false);
            }
        }

        private boolean interrupted(String reason) {
            return reason.contains("interrupted") || reason.contains("canceled");
        }

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

        private String first(List<String> lines) {
            for (String line : lines) {
                if (line.startsWith("WARNING:")) continue;
                String said = line.trim();
                return Z3.OUT_OF_MEMORY.equals(said) ? Z3.MEMOUT : said;
            }
            return "";
        }

        private void ended() {
            Turn of = turn;
            boolean memOut = memOut(collected)
                    || (of != null && Z3.MEMOUT.equals(of.verdict));
            Mark head = expected.peekFirst();
            boolean stray = interruptOutstanding;
            boolean aged = answered > 0;
            boolean unread = head != null && head.role == Role.STARTUP;
            boolean refused = remote && unread && pid <= 0L
                    && ++refusals < SSH_ATTEMPTS;
            String said = String.join(" | ", collected);
            stop();
            if (remote && unread && !refused && !memOut) {
                lose("ended first, saying: " + said);
            }
            if (of == null || of.done() || of.cancelled) return;
            if (refused) {
                again(of);
                return;
            }
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

        private AtomicBoolean handshake() {
            if (refusals > 0) {
                try {
                    Thread.sleep(SSH_RETRY_MS * refusals);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
            SSH_STARTS.computeIfAbsent(pair.room.host,
                    host -> new Semaphore(SSH_STARTS_PER_HOST))
                    .acquireUninterruptibly();
            handshaking = new AtomicBoolean(true);
            return handshaking;
        }

        private void handshook(AtomicBoolean handshake) {
            if (handshake != null && handshake.compareAndSet(true, false)) {
                SSH_STARTS.get(pair.room.host).release();
            }
        }

        private void lose(String why) {
            if (pair.lost) return;
            pair.lost = true;
            System.err.println("z3 scoped: engine " + arithmetic + " on "
                    + pair.room.host + " did not read the shared part ("
                    + why + "): its pair asks no more");
        }

        void silent(long now) {
            Turn of = turn;
            if (process != null && remote && now - readBy >= 0L
                    && reading()) {
                lose("not within " + REMOTE_READ_MS + " ms");
                stop();
            }
            if (process == null) {
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

        void stop() {
            handshook(handshaking);
            Process ending = process;
            if (ending == null) return;
            long ended = pid;
            process = null;
            pid = -1L;
            generation++;
            expected.clear();
            collected.clear();
            if (remote && ended > 0L && ending.isAlive()) {
                signal("kill -KILL " + ended);
            }
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
