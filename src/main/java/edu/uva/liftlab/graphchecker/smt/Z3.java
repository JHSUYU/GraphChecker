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
 * THE z3 driver: one query text in, one answer out.  It launches the
 * process, enforces the budget, drains both streams, and parses verdict,
 * model and errors; what an answer MEANS is the caller's policy.
 *
 * <p>Only {@code sat}/{@code unsat} is decided ({@link Answer#decided()});
 * a timeout, {@code unknown} or {@code (error ...)} is not a refutation.</p>
 *
 * <p>Model, core and reason are each asked in their OWN run after the
 * verdict: {@code (get-value ...)} on an unsat query makes z3 print a
 * routine error that would hide real ones.</p>
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
     * Every {@code (error ...)} z3 answered, over every ask including the
     * auxiliary ones: an error means z3 could not read the query, and one
     * anywhere invalidates the claim.
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
        return ask(query, modelSymbols, wantCore, 0L);
    }

    /**
     * The same ask under its own budget ({@code <= 0}: the instance's).
     * Same instance, so the run counter and error set stay whole.
     */
    public Answer ask(String query, List<String> modelSymbols,
                      boolean wantCore, long budgetMillis) {
        long held = askBudgetMillis;
        askBudgetMillis = budgetMillis > 0L ? budgetMillis : 0L;
        try {
            return asked(query, modelSymbols, wantCore);
        } finally {
            askBudgetMillis = held;
        }
    }

    /** The budget the ask in flight states, or 0 for this solver's own. */
    private long askBudgetMillis;

    private Answer asked(String query, List<String> modelSymbols,
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
        // Not after a timeout: it would spend the budget again for "".
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)
                && !TIMEOUT.equals(status)) {
            reason = parseReason(run(text
                    + "(check-sat)\n(get-info :reason-unknown)\n"));
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
    private String run(String input) {
        runs++;
        long budget = TimeUnit.MILLISECONDS.toNanos(
                askBudgetMillis > 0L ? askBudgetMillis : timeoutMillis);
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
                    // z3 closed its input after answering.
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
            // Strip SMT-LIB |bars| from the name.
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
