package edu.uva.liftlab.graphchecker.launcher;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Reads a finished workload's own evidence and decides what it produced.
 *
 * <p>The evidence is the pair of files the trace recorder writes: the
 * streamed rows, and the manifest its shutdown hook closes. Both are read
 * back here with the same meaning the aggregation stage gives them - a
 * manifest that is not {@code CLOSED} marks a run the aggregator will refuse -
 * so the launcher's verdict and the next stage's cannot disagree.</p>
 *
 * <p>Nothing here consults the child's exit status except to report it.</p>
 */
public final class TargetOutcomeCapture {

    /** Written into the launcher output directory after every run. */
    public static final String OUTCOME_FILE_NAME = "launcher-outcome.json";

    /** Streamed trace rows, written by the workload JVM. */
    public static final String TRACE_FILE_NAME = "runtime_trace.jsonl";

    /** Close manifest, written by the recorder's shutdown hook. */
    public static final String MANIFEST_FILE_NAME =
            "streaming_trace_manifest.json";

    private static final String MANIFEST_KIND = "STREAMING_RUNTIME_TRACE";

    /** How much of a workload's output the failure is looked for in. */
    private static final long TAIL_BYTES = 512L * 1024L;

    private static final Pattern STATUS =
            Pattern.compile("\"status\"\\s*:\\s*\"([A-Z_]+)\"");

    private static final Pattern KIND =
            Pattern.compile("\"kind\"\\s*:\\s*\"([A-Z_]+)\"");

    /**
     * A printed throwable's first line: qualified class, optional message.
     *
     * <p>The optional parenthesised group after the class is Hadoop's
     * {@code RemoteException(java.io.IOException)}, which names the class the
     * server threw. The throwable this JVM saw is still the outer one.</p>
     */
    private static final Pattern THROWABLE = Pattern.compile(
            "([a-zA-Z_$][\\w$]*(?:\\.[a-zA-Z_$][\\w$]*)+"
                    + "(?:Exception|Error|Throwable)[\\w$]*)"
                    + "(?:\\([^()]*\\))?"
                    + "(?::\\s?(.*))?");

    private TargetOutcomeCapture() {
    }

    public static TargetOutcome capture(Path traceDir, WorkloadTarget target,
                                        String traceTest, int junitExitCode,
                                        Path workloadOutput)
            throws LauncherException {
        List<String> gaps = new ArrayList<>();
        TargetOutcome.Trace trace = readManifest(
                traceDir.resolve(MANIFEST_FILE_NAME), gaps);

        long records = 0L;
        long targetRecords = 0L;
        long throwRecords = 0L;
        Path traceFile = traceDir.resolve(TRACE_FILE_NAME);
        if (!Files.isRegularFile(traceFile)) {
            gaps.add("no " + TRACE_FILE_NAME + " in " + traceDir);
        } else {
            try (BufferedReader reader = Files.newBufferedReader(traceFile,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    records++;
                    if (target.mentionedBy(line)) {
                        targetRecords++;
                        if (target.thrownBy(line)) {
                            throwRecords++;
                        }
                    }
                }
            } catch (IOException failure) {
                throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                        "cannot read " + traceFile, failure);
            }
        }
        if (targetRecords == 0L) {
            gaps.add("no streamed row belongs to " + target.methodKey());
        } else if (throwRecords == 0L) {
            // Say what was read, not what happened.  This record sees rows;
            // it does not see the method, and only the instrumentation knows
            // whether an exceptional exit would have written one.
            gaps.add("none of the " + targetRecords + " streamed rows for "
                    + target.methodKey() + " records it exiting with "
                    + target.site().exceptionClass()
                    + "; that is a missing row, and is evidence the throw did "
                    + "not happen only for a pass that records the target's "
                    + "exceptional exit (see skeletonTargetThrowRecorded in "
                    + "target_resolved.json); target-branch evidence is left "
                    + "to the aggregation stage");
        } else {
            gaps.add(throwRecords + " streamed row(s) record "
                    + target.methodKey() + " exiting with "
                    + target.site().exceptionClass()
                    + "; the annotated exception left the target method, "
                    + "which is reported and is not an acceptance criterion - "
                    + "acceptance is the composed candidate.smt2 and its Z3 "
                    + "result, and this run produced neither");
        }
        TargetOutcome.Failure failure = null;
        if (junitExitCode != 0) {
            failure = readFailure(workloadOutput);
            gaps.add("the enclosing JUnit method exited " + junitExitCode
                    + (failure == null ? "" : " with "
                    + failure.exceptionClass())
                    + "; this is reported, not an acceptance criterion");
            if (failure == null) {
                gaps.add("no throwable could be read back from "
                        + workloadOutput);
            }
        }
        return new TargetOutcome(traceTest, target.site().id(),
                target.methodKey(), target.site().exceptionClass(),
                junitExitCode, trace, records, targetRecords, throwRecords,
                workloadOutput == null ? null : workloadOutput.toString(),
                failure, gaps);
    }

    /**
     * Reads the last stack trace out of a finished workload's output.
     *
     * <p>The last one is the workload's own verdict: the runner catches what
     * the JUnit method threw, prints it, and exits. Everything a distributed
     * workload logged before that - the retried RPC, the remote exception the
     * client recovered from - is earlier in the file and is not what failed
     * the run.</p>
     *
     * <p>The walk back from the last frame stops at the first line that is
     * not part of that trace, and reports nothing if that line is not a
     * throwable. Reaching further would silently pair a stack with a header
     * belonging to some earlier failure with unrelated log lines in between,
     * which is precisely the confident wrong answer this record exists to
     * avoid. A {@code Caused by} chain is followed back to its outermost
     * throwable, because that is the one that left the method.</p>
     */
    static TargetOutcome.Failure readFailure(Path output)
            throws LauncherException {
        if (output == null || !Files.isRegularFile(output)) {
            return null;
        }
        List<String> lines = tail(output);
        int frame = -1;
        for (int index = lines.size() - 1; index >= 0; index--) {
            if (isFrame(lines.get(index))) {
                frame = index;
                break;
            }
        }
        if (frame < 0) {
            return null;
        }
        int header = aboveTrace(lines, frame);
        while (isNested(lines.get(header))) {
            int outer = aboveTrace(lines, header - 1);
            if (!isHeader(lines.get(outer))) {
                break;
            }
            header = outer;
        }
        if (!isHeader(lines.get(header))) {
            return null;
        }
        Matcher matcher = THROWABLE.matcher(stripNesting(lines.get(header)));
        if (!matcher.matches()) {
            return null;
        }
        List<String> frames = new ArrayList<>();
        for (int index = header + 1; index < lines.size()
                && frames.size() < TargetOutcome.Failure.FRAME_LIMIT; index++) {
            if (!isFrame(lines.get(index))) {
                break;
            }
            frames.add(lines.get(index).trim());
        }
        return new TargetOutcome.Failure(matcher.group(1), matcher.group(2),
                frames);
    }

    /**
     * The first line at or above {@code from} that is not trace continuation.
     *
     * <p>A blank line counts as continuation: a wrapped remote exception
     * prints the server's frames, a blank line, then the client's.</p>
     */
    private static int aboveTrace(List<String> lines, int from) {
        int index = Math.max(0, from);
        while (index > 0 && (isFrame(lines.get(index))
                || isElision(lines.get(index))
                || lines.get(index).trim().isEmpty())) {
            index--;
        }
        return index;
    }

    /** The last {@link #TAIL_BYTES} of a file, as lines. */
    private static List<String> tail(Path file) throws LauncherException {
        try (SeekableByteChannel channel = Files.newByteChannel(file)) {
            long size = channel.size();
            long from = Math.max(0L, size - TAIL_BYTES);
            channel.position(from);
            ByteBuffer buffer = ByteBuffer.allocate(
                    (int) Math.min(TAIL_BYTES, size - from));
            while (buffer.hasRemaining() && channel.read(buffer) >= 0) {
                continue;
            }
            String text = new String(buffer.array(), 0, buffer.position(),
                    StandardCharsets.UTF_8);
            List<String> lines = new ArrayList<>(
                    Arrays.asList(text.split("\n", -1)));
            if (from > 0 && !lines.isEmpty()) {
                // The first line was cut mid-way by the byte window.
                lines.remove(0);
            }
            return lines;
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot read " + file, failure);
        }
    }

    private static boolean isFrame(String line) {
        return line.startsWith("\tat ") || line.startsWith("    at ");
    }

    private static boolean isElision(String line) {
        return line.trim().startsWith("... ") && line.trim().endsWith("more");
    }

    private static boolean isNested(String line) {
        return line.startsWith("Caused by: ") || line.trim()
                .startsWith("Suppressed: ");
    }

    private static boolean isHeader(String line) {
        return THROWABLE.matcher(stripNesting(line)).matches();
    }

    private static String stripNesting(String line) {
        String trimmed = line.trim();
        if (trimmed.startsWith("Caused by: ")) {
            return trimmed.substring("Caused by: ".length());
        }
        if (trimmed.startsWith("Suppressed: ")) {
            return trimmed.substring("Suppressed: ".length());
        }
        return line;
    }

    /** Writes the outcome record and returns its path. */
    public static Path write(Path outputDir, TargetOutcome outcome)
            throws LauncherException {
        Path path = outputDir.resolve(OUTCOME_FILE_NAME);
        try {
            Files.createDirectories(outputDir);
            Files.write(path,
                    (outcome.toJson() + "\n").getBytes(StandardCharsets.UTF_8));
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot write " + path, failure);
        }
        return path;
    }

    private static TargetOutcome.Trace readManifest(Path manifest,
                                                    List<String> gaps)
            throws LauncherException {
        if (!Files.isRegularFile(manifest)) {
            gaps.add("no " + MANIFEST_FILE_NAME + " at " + manifest
                    + "; the workload JVM never closed a trace");
            return TargetOutcome.Trace.MISSING;
        }
        String text;
        try {
            text = new String(Files.readAllBytes(manifest),
                    StandardCharsets.UTF_8);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot read " + manifest, failure);
        }
        Matcher kind = KIND.matcher(text);
        if (!kind.find() || !MANIFEST_KIND.equals(kind.group(1))) {
            gaps.add(manifest + " is not a " + MANIFEST_KIND + " manifest");
            return TargetOutcome.Trace.MISSING;
        }
        Matcher status = STATUS.matcher(text);
        if (!status.find()) {
            gaps.add(manifest + " declares no status");
            return TargetOutcome.Trace.MISSING;
        }
        if (!"CLOSED".equals(status.group(1))) {
            gaps.add(manifest + " status is " + status.group(1));
            return TargetOutcome.Trace.INCOMPLETE;
        }
        return TargetOutcome.Trace.CLOSED;
    }
}
