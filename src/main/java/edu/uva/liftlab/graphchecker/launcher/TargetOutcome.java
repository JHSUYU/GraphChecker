package edu.uva.liftlab.graphchecker.launcher;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.JsonFields;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * What one workload run produced, read back from the run's own evidence and
 * judged without asking JUnit.  A balancer test can fail its own assertions,
 * time out or leak a thread and still have carried the value flow the target
 * needs, and can equally pass without the target method ever executing, so the
 * JUnit verdict is one reported field and {@link #usable()} is derived from the
 * trace evidence alone.  The streamed rows and the manifest the recorder's
 * shutdown hook closes are read with the same meaning the aggregation stage
 * gives them, so the launcher's verdict and the next stage's cannot disagree.
 */
public final class TargetOutcome {

    /** Written into the launcher output directory after every run. */
    public static final String OUTCOME_FILE_NAME = "launcher-outcome.json";

    /** Streamed trace rows, written by the workload JVM. */
    public static final String TRACE_FILE_NAME = "runtime_trace.jsonl";

    /** Close manifest, written by the recorder's shutdown hook. */
    public static final String MANIFEST_FILE_NAME =
            "streaming_trace_manifest.json";

    private static final String MANIFEST_KIND = "STREAMING_RUNTIME_TRACE";

    /** The row kind that answers "did this method run", counted for every
     *  method: it tells a silent instrument apart from a method that did not
     *  execute.  Matched as a substring because a discovery pass streams
     *  millions of rows and parsing each would dominate the run. */
    private static final String METHOD_ENVELOPE = "\"event\":\"METHOD_ENTER\"";

    /** State of the workload's streaming trace. */
    public enum Trace {
        /** No manifest: the recorder never initialized, or the JVM died hard. */
        MISSING,
        /** The recorder stopped early or lost writes; evidence is partial. */
        INCOMPLETE,
        /** The recorder closed cleanly; the aggregation stage will accept it. */
        CLOSED
    }

    private final String traceTest;
    private final String exceptionTargetId;
    private final String targetMethod;
    private final String targetExceptionClass;
    private final int junitExitCode;
    private final Trace trace;
    private final long traceRecords;
    private final long targetMethodRecords;
    private final long targetThrowRecords;
    private final long methodEnvelopeRecords;
    private final String workloadOutput;
    private final List<String> gaps;

    private TargetOutcome(String traceTest, String exceptionTargetId,
                          String targetMethod, String targetExceptionClass,
                          int junitExitCode, Trace trace, long traceRecords,
                          long targetMethodRecords, long targetThrowRecords,
                          long methodEnvelopeRecords, String workloadOutput,
                          List<String> gaps) {
        this.traceTest = traceTest;
        this.exceptionTargetId = exceptionTargetId;
        this.targetMethod = targetMethod;
        this.targetExceptionClass = targetExceptionClass;
        this.junitExitCode = junitExitCode;
        this.trace = trace;
        this.traceRecords = traceRecords;
        this.targetMethodRecords = targetMethodRecords;
        this.targetThrowRecords = targetThrowRecords;
        this.methodEnvelopeRecords = methodEnvelopeRecords;
        this.workloadOutput = workloadOutput;
        this.gaps = Collections.unmodifiableList(new ArrayList<>(gaps));
    }

    public String targetMethod() { return targetMethod; }

    public int junitExitCode() { return junitExitCode; }

    public Trace trace() { return trace; }

    public long traceRecords() { return traceRecords; }

    /** Streamed rows attributed to the target method. */
    public long targetMethodRecords() { return targetMethodRecords; }

    /** Rows where the target method exited with the annotated exception. */
    public long targetThrowRecords() { return targetThrowRecords; }

    /** Streamed rows that are a method envelope, for any method: the
     *  denominator of the reach question.  A discovery pass records millions;
     *  a concolic replay tree publishes region results instead, and zero here
     *  means this trace could not have carried the answer. */
    public long methodEnvelopeRecords() { return methodEnvelopeRecords; }

    /** Whether this run's trace can answer the reach question at all.  Read
     *  {@link #targetMethodReached()} only when true: otherwise an absent
     *  target row is an absent instrument, not an absent call. */
    public boolean recordsMethodEnvelopes() {
        return methodEnvelopeRecords > 0L;
    }

    public boolean targetMethodReached() { return targetMethodRecords > 0L; }

    /** File holding the workload JVM's merged output, or null. */
    public String workloadOutput() { return workloadOutput; }

    /** Named evidence the run did not produce. */
    public List<String> gaps() { return gaps; }

    /**
     * Whether this run's evidence may be used.
     *
     * <p>A closed trace that carries no method envelope at all did not answer
     * the reach question "no": it did not observe the question.  The concolic
     * replay tree installs region hooks instead of trace-recorder hooks and
     * answers reach with its region results, so calling such a run unusable
     * turns {@link LauncherDiagnostic#TARGET_REACH_UNRECORDED} into a failed
     * process exit -- the same false negative in the exit code that the
     * diagnostic exists to avoid in the report.  {@link #diagnostic()} still
     * names it, and {@link #gaps()} still states what the pass could not
     * say.</p>
     */
    public boolean usable() {
        return trace == Trace.CLOSED
                && (targetMethodReached() || !recordsMethodEnvelopes());
    }

    /** How this run's reach evidence is classified, or null when it reached. */
    public LauncherDiagnostic diagnostic() {
        if (trace == Trace.MISSING) {
            return LauncherDiagnostic.TRACE_MANIFEST_MISSING;
        }
        if (trace == Trace.INCOMPLETE) {
            return LauncherDiagnostic.TRACE_INCOMPLETE;
        }
        if (!targetMethodReached()) {
            // Absence of a target row is evidence the target did not run only
            // when some method envelope was recorded. A pass that recorded
            // none did not observe the question.
            return recordsMethodEnvelopes()
                    ? LauncherDiagnostic.TARGET_NOT_REACHED
                    : LauncherDiagnostic.TARGET_REACH_UNRECORDED;
        }
        return null;
    }

    public String toJson() {
        return JsonFields.objectWithoutNulls(
                "schemaVersion", 1,
                "kind", "SOURCE_FIRST_LAUNCHER_OUTCOME",
                "traceTest", traceTest,
                "exceptionTargetId", exceptionTargetId,
                "targetMethod", targetMethod,
                "targetExceptionClass", targetExceptionClass,
                "junitExitCode", junitExitCode,
                "trace", trace.name(),
                "traceRecords", traceRecords,
                "targetMethodRecords", targetMethodRecords,
                "targetThrowRecords", targetThrowRecords,
                "methodEnvelopeRecords", methodEnvelopeRecords,
                "gaps", gaps);
    }

    public static TargetOutcome capture(Path traceDir, WorkloadTarget target,
                                        String traceTest, int junitExitCode,
                                        Path workloadOutput)
            throws LauncherException {
        List<String> gaps = new ArrayList<>();
        Trace trace = readManifest(traceDir.resolve(MANIFEST_FILE_NAME), gaps);

        long records = 0L;
        long targetRecords = 0L;
        long throwRecords = 0L;
        long envelopeRecords = 0L;
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
                    if (line.contains(METHOD_ENVELOPE)) {
                        envelopeRecords++;
                    }
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
        if (targetRecords == 0L && envelopeRecords == 0L) {
            // Not "the target did not run". This pass rewrote no method with
            // an envelope hook, so no row in it could have said either way.
            gaps.add("none of the " + records + " streamed rows is a method "
                    + "envelope, so this pass records no method entry for any "
                    + "method and cannot say whether " + target.methodKey()
                    + " was entered; reach for a pass instrumented this way is "
                    + "answered by its region results, not by this trace");
        } else if (targetRecords == 0L) {
            gaps.add("no streamed row belongs to " + target.methodKey()
                    + "; " + envelopeRecords + " method envelope row(s) were "
                    + "recorded for other methods, so this pass did observe "
                    + "the question");
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
        if (junitExitCode != 0) {
            gaps.add("the enclosing JUnit method exited " + junitExitCode
                    + "; this is reported, not an acceptance criterion. The"
                    + " throwable it printed is in " + workloadOutput);
        }
        return new TargetOutcome(traceTest, target.site().id(),
                target.methodKey(), target.site().exceptionClass(),
                junitExitCode, trace, records, targetRecords, throwRecords,
                envelopeRecords,
                workloadOutput == null ? null : workloadOutput.toString(),
                gaps);
    }

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

    private static Trace readManifest(Path manifest, List<String> gaps)
            throws LauncherException {
        if (!Files.isRegularFile(manifest)) {
            gaps.add("no " + MANIFEST_FILE_NAME + " at " + manifest
                    + "; the workload JVM never closed a trace");
            return Trace.MISSING;
        }
        String text;
        try {
            text = new String(Files.readAllBytes(manifest),
                    StandardCharsets.UTF_8);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot read " + manifest, failure);
        }
        JsonObject row;
        try {
            JsonElement parsed = JsonParser.parseString(text);
            row = parsed.isJsonObject() ? parsed.getAsJsonObject() : null;
        } catch (RuntimeException malformed) {
            row = null;
        }
        if (row == null || !MANIFEST_KIND.equals(string(row, "kind"))) {
            gaps.add(manifest + " is not a " + MANIFEST_KIND + " manifest");
            return Trace.MISSING;
        }
        String status = string(row, "status");
        if (status.isEmpty()) {
            gaps.add(manifest + " declares no status");
            return Trace.MISSING;
        }
        if (!"CLOSED".equals(status)) {
            gaps.add(manifest + " status is " + status);
            return Trace.INCOMPLETE;
        }
        return Trace.CLOSED;
    }
}
