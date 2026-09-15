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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/**
 * THE z3 driver: one query text in, one answer out.
 *
 * <p>Owns the four things running a solver is: launching the process,
 * enforcing the budget, reading both streams without deadlocking, and
 * reading the verdict, the model and the errors back out of what z3
 * printed.  Nothing here decides what an answer MEANS -- the composer turns
 * an undecided valuation or an error into its own named BLOCKING gap, and
 * the obligation solver refuses a model equal to the seed's -- because a
 * policy is about the campaign and this is about a process.</p>
 *
 * <p>An answer that is not {@code sat} or {@code unsat} is neither: a
 * timeout, an {@code unknown} or an {@code (error ...)} says the solver did
 * not decide, and a caller that reads one as a refutation is making a claim
 * about the solver.  {@link Answer#decided()} is the one test for that.</p>
 *
 * <p>The model is asked for in its OWN run, after the verdict is known, and
 * so are the unsat core and the reason: a script that appends
 * {@code (get-value ...)} to every question makes z3 answer
 * {@code "(error ... model is not available)"} on every unsat one, and an
 * error z3 prints as a matter of course is an error nobody reads -- which is
 * how a genuine "invalid bit-vector literal" once sat in a manifest as if it
 * were a verdict.</p>
 */
public final class Z3 {

    /** The budget one question gets when the campaign names none. */
    public static final long DEFAULT_TIMEOUT_MILLIS = 20_000L;

    /** How z3 says it could not read the query. */
    private static final String ERROR = "(error ";

    /** The status of an answer no process lived long enough to print. */
    private static final String TIMEOUT = "timeout";

    /** What one question answered. */
    public static final class Answer {
        private final String status;
        private final Map<String, String> values;
        private final List<String> core;
        private final String output;
        private final String reason;

        private Answer(String status, Map<String, String> values,
                       List<String> core, String output, String reason) {
            this.status = status;
            this.values = Collections.unmodifiableMap(values);
            this.core = Collections.unmodifiableList(core);
            this.output = output;
            this.reason = reason == null ? "" : reason;
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
         * Why the solver did not decide, in its own words, or "".
         *
         * <p>{@code (get-info :reason-unknown)}, asked only of an answer
         * that is neither sat nor unsat.  Without it an undecided valuation
         * reached the manifest as a bare {@code state=unknown}, which tells
         * a reader nothing about whether the query was too hard, in the
         * wrong fragment, or cut off -- 17960's moved valuation came back
         * {@code (incomplete quantifiers)}, and that named the two
         * {@code lambda} definitions it was about.</p>
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

        /** Everything z3 printed, for a reader of the run. */
        public String output() {
            return output;
        }

        @Override
        public String toString() {
            return status + (values.isEmpty() ? "" : " " + values)
                    + (core.isEmpty() ? "" : " core" + core);
        }
    }

    private final Path z3;
    private final long timeoutMillis;
    private int runs;
    private final Set<String> errors = new LinkedHashSet<String>();

    public Z3(Path executable, long timeoutMillis) {
        this.z3 = executable == null ? Paths.get("z3") : executable;
        this.timeoutMillis = timeoutMillis <= 0L
                ? DEFAULT_TIMEOUT_MILLIS : timeoutMillis;
    }

    /** How many times z3 was asked; the cost of one composition. */
    public int runs() {
        return runs;
    }

    /**
     * Every {@code (error ...)} z3 answered, over every ask.
     *
     * <p>An error is not a verdict and not an "undecided": it says the
     * solver could not READ the query this lowering wrote, so whatever it
     * printed afterwards is about a different formula.  It is collected
     * here, over the auxiliary asks (the unsat core, the pairing probes,
     * the clock probe) as well as the valuations, because one such answer
     * anywhere invalidates the claim a caller would otherwise read off the
     * others.</p>
     */
    public List<String> errors() {
        return new ArrayList<String>(errors);
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
        String text = query == null ? "" : query;
        String output = run(text + "(check-sat)\n");
        String status = firstLine(output);
        Map<String, String> values = Collections.emptyMap();
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
            values = parseValues(run(modelQuery(text, modelSymbols)));
        }
        List<String> core = Collections.emptyList();
        if (wantCore && "unsat".equals(status)) {
            core = parseCore(run(text + "(check-sat)\n(get-unsat-core)\n"));
        }
        // Why it did not decide, asked the same way: one more run, only
        // when there is something to ask for.  An undecided answer with no
        // reason is a silence, and a silence is not a verdict.  A timeout is
        // not asked: no process survived to print a reason, so a second run
        // would spend the whole budget again to read the same "".
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)
                && !TIMEOUT.equals(status)) {
            reason = parseReason(run(text
                    + "(check-sat)\n(get-info :reason-unknown)\n"));
        }
        return new Answer(status, values, core, output, reason);
    }

    /**
     * The exact text {@link #ask} sends when it asks for a model.
     *
     * <p>Public because a stage that publishes its query as an artifact
     * publishes the question that was asked, and there is one spelling of
     * that question: a file that says {@code (get-model)} while the run
     * asked {@code (get-value ...)} is a second query nobody solved.</p>
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
     * One z3 process, fed on stdin, read on a second thread.
     *
     * <p>Writing the whole query and only then reading deadlocks on the
     * pipe buffers as soon as a query or a model is larger than one: both
     * directions are therefore their own thread, and the timeout is
     * enforced here rather than handed to z3, so that a solver that ignores
     * it cannot hold the campaign open.</p>
     */
    private String run(String input) {
        runs++;
        long budget = TimeUnit.MILLISECONDS.toNanos(timeoutMillis);
        Process process;
        try {
            ProcessBuilder builder = new ProcessBuilder(z3.toString(),
                    "-in", "-smt2");
            builder.redirectErrorStream(true);
            process = builder.start();
        } catch (IOException notLaunched) {
            // Not an "(error ...)" z3 printed -- z3 never ran -- so it is
            // an undecided answer and not a query the solver could not read.
            return "error " + notLaunched.getMessage();
        }
        final Process running = process;
        final byte[] bytes = input.getBytes(StandardCharsets.UTF_8);
        final AtomicReference<String> read = new AtomicReference<String>("");
        Thread writer = new Thread(new Runnable() {
            @Override
            public void run() {
                OutputStream stream = running.getOutputStream();
                try {
                    stream.write(bytes);
                    stream.flush();
                } catch (IOException closed) {
                    // The solver answered and closed its input; that is an
                    // answer, not an error.
                } finally {
                    try {
                        stream.close();
                    } catch (IOException ignored) {
                        // Nothing further to say about a closed pipe.
                    }
                }
            }
        }, "graphchecker-z3-writer");
        Thread reader = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    read.set(readAll(running.getInputStream()));
                } catch (IOException truncated) {
                    read.set(read.get());
                }
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
        return errorsOf(read.get());
    }

    /** The same output, with every error line it names remembered. */
    private String errorsOf(String output) {
        if (output == null) return "";
        int at = output.indexOf(ERROR);
        while (at >= 0) {
            int end = output.indexOf('\n', at);
            errors.add((end < 0 ? output.substring(at)
                    : output.substring(at, end)).trim());
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
        if (output == null) return values;
        int start = output.indexOf('\n');
        if (start < 0) return values;
        String body = output.substring(start + 1).trim();
        if (!body.startsWith("(")) return values;
        for (String item : items(body.substring(1,
                Math.max(1, matching(body, 0))))) {
            String pair = item.trim();
            if (!pair.startsWith("(")) continue;
            String inner = pair.substring(1,
                    Math.max(1, matching(pair, 0))).trim();
            int split = inner.indexOf(' ');
            if (split < 0) continue;
            // z3 answers with the name as the query spelled it, quoted
            // bars and all; the caller asked about the name itself.
            values.put(unquoted(inner.substring(0, split).trim()),
                    normalize(inner.substring(split + 1).trim()));
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
        if (output == null) return names;
        int start = output.indexOf('\n');
        if (start < 0) return names;
        String body = output.substring(start + 1).trim();
        int open = body.indexOf('(');
        if (open < 0) return names;
        int close = matching(body, open);
        if (close < 0) return names;
        for (String name : body.substring(open + 1, close).trim()
                .split("\\s+")) {
            if (!name.isEmpty()) names.add(name);
        }
        return names;
    }

    /** The top-level items of one parenthesised body. */
    private static List<String> items(String body) {
        List<String> parts = new ArrayList<String>();
        int depth = 0;
        int start = -1;
        boolean quoted = false;
        for (int index = 0; index < body.length(); index++) {
            char value = body.charAt(index);
            if (value == '"') quoted = !quoted;
            if (quoted) continue;
            if (value == '(') {
                if (depth == 0) start = index;
                depth++;
            } else if (value == ')') {
                depth--;
                if (depth == 0 && start >= 0) {
                    parts.add(body.substring(start, index + 1));
                    start = -1;
                }
            }
        }
        return parts;
    }

    /** The index of the parenthesis closing the one at {@code open}. */
    private static int matching(String text, int open) {
        int depth = 0;
        boolean quoted = false;
        for (int index = open; index < text.length(); index++) {
            char value = text.charAt(index);
            if (value == '"') quoted = !quoted;
            if (quoted) continue;
            if (value == '(') depth++;
            else if (value == ')') {
                depth--;
                if (depth == 0) return index;
            }
        }
        return -1;
    }
}
