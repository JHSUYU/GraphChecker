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

public final class Z3 {

    public static final long DEFAULT_TIMEOUT_MILLIS = 20_000L;

    static final String CORE_TRACKING =
            "(set-option :produce-unsat-cores true)\n";

    private static final String ERROR = "(error ";

    static final String TIMEOUT = "timeout";

    static final String OUT_OF_MEMORY = "(error \"out of memory\")";
    static final String MEMOUT = "memout";

    static final int MISSED_MB = 64;

    static final int LEAST_SLOT_MB = 2 * MISSED_MB;

    static final int[] ARITHMETIC = {2, 6};

    static final String ARITHMETIC_OPENING = "(set-option :smt.arith.solver ";

    static final long PREFERRED_GRACE_MILLIS = 1000L;

    private static final long POLL_MILLIS = 20L;

    public static final class Answer {
        private final String status;
        private final Map<String, String> values;
        private final List<String> core;
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

        public static Answer decided(String status,
                                     Map<String, String> values) {
            if (!"sat".equals(status) && !"unsat".equals(status)) {
                throw new IllegalArgumentException("not a decided answer: "
                        + status);
            }
            return new Answer(status, values,
                    Collections.<String>emptyList(), false, "");
        }

        public String status() {
            return status;
        }

        public boolean sat() {
            return "sat".equals(status);
        }

        public boolean unsat() {
            return "unsat".equals(status);
        }

        public boolean decided() {
            return sat() || unsat();
        }

        public boolean timedOut() {
            return TIMEOUT.equals(status);
        }

        public boolean memOut() {
            return MEMOUT.equals(status);
        }

        public String reason() {
            return reason;
        }

        public Map<String, String> values() {
            return values;
        }

        public List<String> core() {
            return core;
        }

        public boolean coreKnown() {
            return coreKnown;
        }

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

    static final class Room {
        final int mb;
        final String host;
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

        private void pass() {
            while (abandoned.remove(serving)) serving++;
            notifyAll();
        }

        synchronized void give(int need) {
            held -= need;
            notifyAll();
        }

        synchronized boolean contended() {
            return issued > serving;
        }
    }

    private final Path z3;
    private final long timeoutMillis;
    private final AtomicInteger runs;
    private final Set<String> errors;
    private final Room room;
    private final List<Room> hosts;
    private final Path visible;
    private final int slotMb;
    private final int aloneMb;
    private final long deadlineNanos;

    public Z3(Path executable, long timeoutMillis, int roomMb) {
        this(executable, timeoutMillis, roomMb,
                Collections.<Room>emptyList(), null);
    }

    public static final class Rooms {
        private final Room room;

        public Rooms(int mb) {
            this.room = new Room(mb);
        }
    }

    public Z3(Path executable, long timeoutMillis, Rooms shared,
              int questionMb) {
        this(executable == null ? Paths.get("z3") : executable,
                timeoutMillis <= 0L ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis,
                new AtomicInteger(), new TreeSet<String>(), shared.room,
                Collections.<Room>emptyList(), null,
                Math.min(questionMb, shared.room.mb) / 2, 0L,
                Math.min(questionMb, shared.room.mb) / 2);
    }

    public Z3 alone(long timeoutMillis, int roomMb) {
        return new Z3(z3, timeoutMillis, roomMb);
    }


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

    public Z3 until(long deadlineNanos) {
        return new Z3(z3, timeoutMillis, runs, errors, room, hosts, visible,
                slotMb, deadlineNanos, aloneMb);
    }

    public boolean pastDeadline() {
        return deadlineNanos != 0L && System.nanoTime() - deadlineNanos >= 0L;
    }

    public Z3 slotted(int slotMb) {
        return new Z3(z3, timeoutMillis, runs, errors, room, hosts, visible,
                Math.max(LEAST_SLOT_MB, Math.min(slotMb, aloneMb)),
                deadlineNanos, aloneMb);
    }

    public Z3 shared(int asksAtOnce) {
        return slotted(2 * aloneMb / (ARITHMETIC.length * Math.max(1,
                asksAtOnce)));
    }

    public int capMb() {
        return slotMb - MISSED_MB;
    }

    Room room() {
        return room;
    }

    List<Room> hosts() {
        return hosts;
    }

    Path visible() {
        return visible;
    }

    Path executable() {
        return z3;
    }

    int countRun() {
        return runs.incrementAndGet();
    }

    void noteError(String line) {
        synchronized (errors) {
            errors.add(line.trim());
        }
    }

    long budgetLeft(long budgetMillis) {
        return deadlineNanos == 0L ? budgetMillis : Math.min(budgetMillis,
                TimeUnit.NANOSECONDS.toMillis(deadlineNanos
                        - System.nanoTime()));
    }

    public long timeoutMillis() {
        return timeoutMillis;
    }

    public int runs() {
        return runs.get();
    }

    public List<String> errors() {
        synchronized (errors) {
            return new ArrayList<String>(errors);
        }
    }

    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore) {
        return ask(query, modelSymbols, wantCore, 0L);
    }

    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        String text = query == null ? "" : query;
        return ask(output -> output.write(text), modelSymbols, wantCore,
                budgetMillis);
    }

    public Answer ask(ArtifactIO.Body query, List<String> modelSymbols,
                      boolean wantCore) {
        return ask(query, modelSymbols, wantCore, 0L);
    }

    public Answer ask(ArtifactIO.Body query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        long budget = budgetMillis > 0L ? budgetMillis : timeoutMillis;
        String status = firstLine(run("", query, "(check-sat)\n", budget));
        if (MEMOUT.equals(status)) {
            return new Answer(status, Collections.<String, String>emptyMap(),
                    Collections.<String>emptyList(), false, "out of memory at"
                    + " its cap of " + capMb() + " MB (memory_max_size)");
        }
        if (status.startsWith(DISAGREE)) return undecided(status);
        Map<String, String> values = Collections.emptyMap();
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
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
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)
                && !TIMEOUT.equals(status)) {
            reason = parseReason(run("", query,
                    "(check-sat)\n(get-info :reason-unknown)\n", budget));
        }
        return new Answer(status, values, core, coreKnown, reason);
    }

    static final String DISAGREE = "(error \"engines disagree: ";

    private Answer disagree(String how) {
        String error = DISAGREE + how + "\")";
        noteError(error);
        return undecided(error);
    }

    private static Answer undecided(String status) {
        return new Answer(status, Collections.<String, String>emptyMap(),
                Collections.<String>emptyList(), false, "");
    }

    private String payload(String prefix, ArtifactIO.Body query,
                           String suffix) {
        String printed = run(prefix, query, suffix, timeoutMillis);
        if (MEMOUT.equals(firstLine(printed)) && slotMb < aloneMb) {
            printed = slotted(aloneMb).run(prefix, query, suffix,
                    timeoutMillis);
        }
        return printed;
    }

    public static String modelQuery(String query, List<String> modelSymbols) {
        return (query == null ? "" : query) + valueCommand(modelSymbols);
    }

    private static String valueCommand(List<String> modelSymbols) {
        return "(check-sat)\n" + getValue(modelSymbols);
    }

    static String getValue(List<String> modelSymbols) {
        StringBuilder text = new StringBuilder("(get-value (");
        if (modelSymbols != null) {
            for (String symbol : modelSymbols) {
                text.append(' ').append(symbol);
            }
        }
        return text.append("))\n").toString();
    }


    static final long ORPHAN_MARGIN_SECONDS = 10L;

    private static final Set<Process> LIVE =
            Collections.newSetFromMap(new ConcurrentHashMap<Process, Boolean>());

    static final String[] DIES_WITH_ITS_DRIVER =
            {"setpriv", "--pdeathsig", "KILL", "--"};

    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            for (Process process : LIVE) process.destroyForcibly();
        }, "graphchecker-z3-reaper"));
    }

    static String hardTimeout(long budgetMillis) {
        return "-T:" + ((budgetMillis + 999L) / 1000L + ORPHAN_MARGIN_SECONDS);
    }

    static List<String> command(Path z3, int slotMb, long budgetMillis) {
        List<String> command = new ArrayList<String>(
                Arrays.asList(DIES_WITH_ITS_DRIVER));
        command.addAll(Arrays.asList(z3.toString(),
                "memory_max_size=" + (slotMb - MISSED_MB),
                hardTimeout(budgetMillis), "-in", "-smt2"));
        return command;
    }

    private String run(String prefix, ArtifactIO.Body query, String suffix,
                       long budgetMillis) {
        if (pastDeadline()) return TIMEOUT;
        int run = runs.incrementAndGet();
        long started = System.nanoTime();
        String answer = TIMEOUT;
        int slots = ARITHMETIC.length * slotMb;
        if (room.take(slots)) {
            try {
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

    static void said(int run, String command, String said,
                     long startedNanos) {
        System.err.println("z3 run " + run + " (" + command + "): "
                + (said.length() > 40 ? said.substring(0, 40) + "..." : said)
                + " in " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime()
                - startedNanos) / 1000.0 + " s");
    }

    static void track(Process process) {
        LIVE.add(process);
    }

    static void untrack(Process process) {
        LIVE.remove(process);
    }

    private static String command(String suffix) {
        String[] lines = suffix.trim().split("\n");
        String last = lines[lines.length - 1].replace("(", "").trim();
        int end = last.indexOf(' ');
        return (end < 0 ? last : last.substring(0, end)).replace(")", "");
    }

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
            return answerOf(memoryOut(printed) && !decided(printed, suffix)
                    ? OUT_OF_MEMORY : printed);
        } finally {
            for (Process engine : engines) {
                if (engine == null) continue;
                engine.destroyForcibly();
                try {
                    engine.waitFor(ORPHAN_MARGIN_SECONDS, TimeUnit.SECONDS);
                } catch (InterruptedException interrupted) {
                    Thread.currentThread().interrupt();
                }
                untrack(engine);
            }
        }
    }

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

    private static String agreed(String preferred, String other) {
        String one = firstLine(preferred);
        String two = firstLine(other);
        return one.equals(two) ? preferred : DISAGREE + "engine "
                + ARITHMETIC[0] + " " + one + ", engine " + ARITHMETIC[1]
                + " " + two + " in one run\")";
    }

    private static String finished(Process engine,
                                   AtomicReference<String> read,
                                   Thread reader)
            throws InterruptedException {
        if (engine == null) return read.get();
        if (engine.isAlive()) return null;
        reader.join(TimeUnit.SECONDS.toMillis(ORPHAN_MARGIN_SECONDS));
        return read.get() == null ? "" : read.get();
    }

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

    static boolean memoryOut(String printed) {
        if (printed == null) return false;
        for (String line : printed.split("\n", -1)) {
            if (OUT_OF_MEMORY.equals(line.trim())) return true;
        }
        return false;
    }

    static boolean payload(String printed) {
        String[] lines = printed.split("\n", -1);
        return lines.length > 1 && lines[1].trim().startsWith("(")
                && !lines[1].trim().startsWith(ERROR);
    }

    static String arithmeticOption(int engine) {
        return ARITHMETIC_OPENING + engine + ")";
    }

    static final class EngineWriter extends Writer {
        private final Writer out;
        private final String option;
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
            }
        }, "graphchecker-z3-writer");
        Thread reader = new Thread(() -> {
            try {
                read.set(readAll(process.getInputStream()));
            } catch (IOException truncated) {
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


    static Map<String, String> parseValues(String output) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        SExpression block = answerBlock(output, false);
        if (block == null || block.atom()) return values;
        for (SExpression pair : block.children()) {
            List<SExpression> parts = pair.children();
            if (parts.size() < 2) continue;
            values.put(unquoted(parts.get(0).text()), normalize(output
                    .substring(parts.get(1).start,
                            parts.get(parts.size() - 1).end)));
        }
        return values;
    }

    static String unquoted(String name) {
        String text = name == null ? "" : name.trim();
        return text.length() >= 2 && text.startsWith("|")
                && text.endsWith("|")
                ? text.substring(1, text.length() - 1) : text;
    }

    static String normalize(String value) {
        String text = value == null ? "" : value.trim();
        if (text.startsWith("(-") && text.endsWith(")")) {
            String digits = text.substring(2, text.length() - 1).trim();
            if (!digits.isEmpty()) return "-" + digits;
        }
        return text;
    }

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

    static String parseReason(String output) {
        if (output == null) return "";
        int at = output.indexOf(":reason-unknown");
        if (at < 0) return "";
        int open = output.indexOf('"', at);
        int close = open < 0 ? -1 : output.indexOf('"', open + 1);
        if (open < 0 || close < 0) return "";
        return output.substring(open + 1, close).trim();
    }

    static List<String> parseCore(String output) {
        List<String> names = new ArrayList<String>();
        SExpression block = answerBlock(output, true);
        if (block == null) return names;
        for (SExpression name : block.children()) names.add(name.text());
        return names;
    }

    static SExpression answerBlock(String output, boolean firstList) {
        int verdictEnd = output == null ? -1 : output.indexOf('\n');
        if (verdictEnd < 0) return null;
        int at = firstList ? output.indexOf('(', verdictEnd) : verdictEnd + 1;
        return at < 0 ? null : SExpression.parse(output, at);
    }
}
