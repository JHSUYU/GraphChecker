package edu.uva.liftlab.graphchecker.smt;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
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

    /** What one question answered. */
    public static final class Answer {
        private final String status;
        private final Map<String, String> values;
        private final List<String> core;
        private final String reason;

        private Answer(String status, Map<String, String> values,
                       List<String> core, String reason) {
            this.status = status;
            this.values = Collections.unmodifiableMap(values);
            this.core = Collections.unmodifiableList(core);
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

        /** The names of the conjuncts one unsat answer closed on. */
        public List<String> core() {
            return core;
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

    /**
     * The same ask under its own budget ({@code <= 0}: the instance's).
     * Same instance, so the run counter and error set stay whole.
     */
    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        long budget = budgetMillis > 0L ? budgetMillis : timeoutMillis;
        String text = query == null ? "" : query;
        String status = firstLine(run(text + "(check-sat)\n", budget));
        Map<String, String> values = Collections.emptyMap();
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
            values = parseValues(run(modelQuery(text, modelSymbols), budget));
        }
        List<String> core = Collections.emptyList();
        if (wantCore && "unsat".equals(status)) {
            core = parseCore(run(CORE_TRACKING + text
                    + "(check-sat)\n(get-unsat-core)\n", budget));
        }
        // Not after a timeout: it would spend the budget again for "".
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)
                && !TIMEOUT.equals(status)) {
            reason = parseReason(run(text
                    + "(check-sat)\n(get-info :reason-unknown)\n", budget));
        }
        return new Answer(status, values, core, reason);
    }

    /**
     * The exact text {@link #ask} sends for a model; published artifacts
     * must use it so the file is the question actually solved.
     */
    public static String modelQuery(String query, List<String> modelSymbols) {
        StringBuilder text = new StringBuilder(query == null ? "" : query);
        text.append("(check-sat)\n(get-value (");
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
     * One z3 process.  Each pipe direction has its own thread (else large
     * queries deadlock), and the timeout is enforced here, not by z3.
     */
    private String run(String input, long budgetMillis) {
        runs.incrementAndGet();
        long budget = TimeUnit.MILLISECONDS.toNanos(budgetMillis);
        Process process;
        try {
            ProcessBuilder builder = new ProcessBuilder(z3.toString(),
                    "-in", "-smt2");
            builder.redirectErrorStream(true);
            process = builder.start();
        } catch (IOException notLaunched) {
            // z3 never ran: undecided, not a z3 "(error ...)".
            return "error " + notLaunched.getMessage();
        }
        Process running = process;
        byte[] bytes = input.getBytes(StandardCharsets.UTF_8);
        AtomicReference<String> read = new AtomicReference<String>("");
        Thread writer = new Thread(() -> {
            try (OutputStream stream = running.getOutputStream()) {
                stream.write(bytes);
                stream.flush();
            } catch (IOException closed) {
                // z3 closed its input after answering.
            }
        }, "graphchecker-z3-writer");
        Thread reader = new Thread(() -> {
            try {
                read.set(readAll(running.getInputStream()));
            } catch (IOException truncated) {
                // A broken pipe answers nothing: "" is undecided.
            }
        }, "graphchecker-z3-reader");
        writer.setDaemon(true);
        reader.setDaemon(true);
        writer.start();
        reader.start();
        try {
            if (!process.waitFor(budget, TimeUnit.NANOSECONDS)) {
                process.destroyForcibly();
                writer.interrupt();
                reader.interrupt();
                return TIMEOUT;
            }
            reader.join(TimeUnit.NANOSECONDS.toMillis(budget));
            writer.join(TimeUnit.NANOSECONDS.toMillis(budget));
        } catch (InterruptedException interrupted) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
            return TIMEOUT;
        }
        return answerOf(read.get());
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
