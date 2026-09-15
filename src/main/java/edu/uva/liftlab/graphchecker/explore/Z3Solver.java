package edu.uva.liftlab.graphchecker.explore;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

/** Runs one query through z3 and reads the model back. */
final class Z3Solver {
    private Z3Solver() {
    }

    /** One verdict, with the model when there is one. */
    static final class Answer {
        final boolean sat;
        final boolean timedOut;
        final Map<String, String> model;
        final String output;

        private Answer(boolean sat, boolean timedOut,
                       Map<String, String> model, String output) {
            this.sat = sat;
            this.timedOut = timedOut;
            this.model = Collections.unmodifiableMap(model);
            this.output = output;
        }
    }

    static Answer solve(Path executable, String query, long timeoutMillis)
            throws IOException, InterruptedException {
        String output = run(executable, query, timeoutMillis);
        if (output == null) {
            return new Answer(false, true,
                    new LinkedHashMap<String, String>(), "");
        }
        boolean sat = output.trim().startsWith("sat");
        return new Answer(sat, false,
                sat ? model(output) : new LinkedHashMap<String, String>(),
                output);
    }

    /** Every {@code define-fun} of a model, as variable to value. */
    static Map<String, String> model(String output) {
        Map<String, String> model = new LinkedHashMap<String, String>();
        int cursor = 0;
        while (true) {
            int at = output.indexOf("(define-fun ", cursor);
            if (at < 0) return model;
            int index = at + "(define-fun ".length();
            while (index < output.length()
                    && Character.isWhitespace(output.charAt(index))) {
                index++;
            }
            int nameEnd = index;
            while (nameEnd < output.length()
                    && !Character.isWhitespace(output.charAt(nameEnd))
                    && output.charAt(nameEnd) != '(') {
                nameEnd++;
            }
            String name = output.substring(index, nameEnd);
            // Skip the (empty) argument list and the sort.
            int arguments = output.indexOf('(', nameEnd);
            if (arguments < 0) return model;
            int close = output.indexOf(')', arguments);
            if (close < 0) return model;
            int sort = close + 1;
            while (sort < output.length()
                    && Character.isWhitespace(output.charAt(sort))) {
                sort++;
            }
            int sortEnd = sort;
            while (sortEnd < output.length()
                    && !Character.isWhitespace(output.charAt(sortEnd))) {
                sortEnd++;
            }
            int value = sortEnd;
            while (value < output.length()
                    && Character.isWhitespace(output.charAt(value))) {
                value++;
            }
            int end = value;
            if (end < output.length() && output.charAt(end) == '(') {
                int depth = 0;
                while (end < output.length()) {
                    char at2 = output.charAt(end);
                    if (at2 == '(') depth++;
                    if (at2 == ')') {
                        depth--;
                        if (depth == 0) {
                            end++;
                            break;
                        }
                    }
                    end++;
                }
            } else {
                while (end < output.length() && output.charAt(end) != ')'
                        && !Character.isWhitespace(output.charAt(end))) {
                    end++;
                }
            }
            model.put(name, normalize(output.substring(value, end).trim()));
            cursor = end;
        }
    }

    /** {@code (- 5)} is the integer minus five, and reads back as one. */
    private static String normalize(String value) {
        String text = value.trim();
        if (text.startsWith("(") && text.endsWith(")")) {
            String inner = text.substring(1, text.length() - 1).trim();
            if (inner.startsWith("-")) {
                return "-" + inner.substring(1).trim();
            }
        }
        return text;
    }

    /** The process run, with the timeout the campaign gives one obligation. */
    private static String run(Path executable, String query, long timeoutMillis)
            throws IOException, InterruptedException {
        byte[] encoded = query.getBytes(StandardCharsets.UTF_8);
        ProcessBuilder builder = new ProcessBuilder(executable.toString(),
                "-in", "-smt2");
        builder.redirectErrorStream(true);
        final Process process = builder.start();
        final AtomicReference<String> stdout = new AtomicReference<String>("");
        Thread writer = new Thread(new Runnable() {
            @Override public void run() {
                try {
                    OutputStream stream = process.getOutputStream();
                    try {
                        stream.write(encoded);
                    } finally {
                        stream.close();
                    }
                } catch (IOException ignored) {
                    // The reader below reports whatever z3 managed to say.
                }
            }
        }, "explore-z3-writer");
        Thread reader = new Thread(new Runnable() {
            @Override public void run() {
                try {
                    stdout.set(readAll(process.getInputStream()));
                } catch (IOException ignored) {
                    // Same: an unreadable stream is a timed-out solve.
                }
            }
        }, "explore-z3-reader");
        writer.setDaemon(true);
        reader.setDaemon(true);
        writer.start();
        reader.start();
        if (!process.waitFor(Math.max(1L, timeoutMillis),
                TimeUnit.MILLISECONDS)) {
            process.destroyForcibly();
            return null;
        }
        reader.join(Math.max(1L, timeoutMillis));
        return stdout.get();
    }

    private static String readAll(InputStream stream) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int read;
        while ((read = stream.read(buffer)) >= 0) {
            output.write(buffer, 0, read);
        }
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }
}
