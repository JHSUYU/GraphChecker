package edu.uva.liftlab.graphchecker.d3.compose;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
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
 * One z3 answer per valuation.
 *
 * <p>The composed body is asked once per valuation with that valuation's
 * root pins conjoined, because the pins are the question and the body is
 * the program: re-rendering the body per valuation would make sixteen
 * copies of one formula, and pinning inside the body would make the
 * enumeration a property of the artifact.</p>
 *
 * <p>An answer that is not {@code sat} or {@code unsat} is neither: a
 * timeout or an {@code unknown} says the solver did not decide, and a
 * claim that reads it as a refutation is a claim about the solver.</p>
 */
public final class Solver {

    /** What one z3 run answered. */
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

        /** Symbol -> the value the model gave it, for the symbols asked. */
        public Map<String, String> values() {
            return values;
        }

        /** The names of the conjuncts one unsat answer closed on. */
        public List<String> core() {
            return core;
        }

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

    public Solver(Path z3, long timeoutMillis) {
        this.z3 = z3 == null ? Paths.get("z3") : z3;
        this.timeoutMillis = timeoutMillis <= 0L ? 20000L : timeoutMillis;
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
     * anywhere invalidates the claim the composition would otherwise read
     * off the others.</p>
     */
    public List<String> errors() {
        return new ArrayList<String>(errors);
    }

    /**
     * One question: the body, these extra assertions, this model request.
     *
     * @param body          the composed query, declarations and assertions,
     *                      without a {@code check-sat}
     * @param assumptions   named assertions conjoined for this question only
     * @param modelSymbols  the constants whose value a sat answer must carry
     * @param wantCore      whether an unsat answer should name its core
     */
    public Answer ask(String body, List<String> assumptions,
                      List<String> modelSymbols, boolean wantCore) {
        StringBuilder query = new StringBuilder(body);
        if (assumptions != null) {
            for (String assumption : assumptions) {
                if (assumption == null || assumption.isEmpty()) continue;
                query.append(assumption).append('\n');
            }
        }
        String question = query.toString();
        query.append("(check-sat)\n");
        String output = run(SmtLowering.legalSymbols(query.toString()));
        String status = firstLine(output);
        Map<String, String> values = Collections.emptyMap();
        // The model is asked for in its OWN run, after the answer is known.
        // A script that appends (get-value ...) to every question makes z3
        // answer "(error ... model is not available)" on every unsat one --
        // and an error z3 prints as a matter of course is an error nobody
        // reads, which is how a genuine "invalid bit-vector literal" sat in
        // a manifest as if it were a verdict.  Same shape as the unsat core
        // below: one more run, only when there is something to ask for.
        if ("sat".equals(status) && modelSymbols != null
                && !modelSymbols.isEmpty()) {
            StringBuilder model = new StringBuilder(question);
            model.append("(check-sat)\n(get-value (");
            for (String symbol : modelSymbols) {
                model.append(' ').append(symbol);
            }
            model.append("))\n");
            values = parseValues(run(
                    SmtLowering.legalSymbols(model.toString())));
        }
        List<String> core = Collections.emptyList();
        if (wantCore && "unsat".equals(status)) {
            String coreOutput = run(SmtLowering.legalSymbols(body
                    + join(assumptions)
                    + "(check-sat)\n(get-unsat-core)\n"));
            core = parseCore(coreOutput);
        }
        // Why it did not decide, asked the same way: one more run, only
        // when there is something to ask for.  An undecided answer with no
        // reason is a silence, and a silence is not a verdict.
        String reason = "";
        if (!"sat".equals(status) && !"unsat".equals(status)) {
            reason = parseReason(run(SmtLowering.legalSymbols(question
                    + "(check-sat)\n(get-info :reason-unknown)\n")));
        }
        return new Answer(status, values, core, output, reason);
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

    private static String join(List<String> assumptions) {
        StringBuilder text = new StringBuilder();
        if (assumptions != null) {
            for (String assumption : assumptions) {
                if (assumption == null || assumption.isEmpty()) continue;
                text.append(assumption).append('\n');
            }
        }
        return text.toString();
    }

    /** Writes the query beside the artifacts, for a reader of the run. */
    public static void save(Path file, String query) throws IOException {
        if (file.getParent() != null) {
            Files.createDirectories(file.getParent());
        }
        Files.write(file, query.getBytes(StandardCharsets.UTF_8));
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
     * it cannot hold the composition open.</p>
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
        }, "graphchecker-d3-z3-writer");
        Thread reader = new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    read.set(readAll(running.getInputStream()));
                } catch (IOException truncated) {
                    read.set(read.get());
                }
            }
        }, "graphchecker-d3-z3-reader");
        writer.setDaemon(true);
        reader.setDaemon(true);
        writer.start();
        reader.start();
        try {
            if (!process.waitFor(budget, TimeUnit.NANOSECONDS)) {
                process.destroyForcibly();
                writer.interrupt();
                reader.interrupt();
                return "timeout";
            }
            reader.join(TimeUnit.NANOSECONDS.toMillis(budget));
            writer.join(TimeUnit.NANOSECONDS.toMillis(budget));
        } catch (InterruptedException interrupted) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
            return "timeout";
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

    /** How z3 says it could not read the query. */
    private static final String ERROR = "(error ";

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
