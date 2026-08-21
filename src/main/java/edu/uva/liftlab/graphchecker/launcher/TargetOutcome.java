package edu.uva.liftlab.graphchecker.launcher;

import edu.uva.liftlab.graphchecker.causynth.CausynthJson;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What one workload run produced, judged without asking JUnit.
 *
 * <p>The enclosing JUnit method is not the experiment. A balancer test can
 * fail its own assertions, time out, or leak a thread and still have carried
 * the value flow the target needs; it can equally pass without the target
 * method ever executing. This record therefore keeps the JUnit verdict as one
 * reported field among several and derives {@link #usable()} from the trace
 * evidence alone.</p>
 */
public final class TargetOutcome {

    /** State of the workload's streaming trace. */
    public enum Trace {
        /** No manifest: the recorder never initialized, or the JVM died hard. */
        MISSING,
        /** The recorder stopped early or lost writes; evidence is partial. */
        INCOMPLETE,
        /** The recorder closed cleanly; the aggregation stage will accept it. */
        CLOSED
    }

    /**
     * The throwable that ended a failing workload, read back from its output.
     *
     * <p>The frames are the top of the stack only. What this record has to
     * answer is which failure the run hit, so the next reader knows whether it
     * is the target's, the workload's own, or the launcher's doing; the whole
     * trace is in the captured output for whoever needs it.</p>
     */
    public static final class Failure {

        /** Frames kept: enough to name the failing operation, not the stack. */
        public static final int FRAME_LIMIT = 8;

        private final String exceptionClass;
        private final String message;
        private final List<String> frames;

        public Failure(String exceptionClass, String message,
                       List<String> frames) {
            this.exceptionClass = exceptionClass;
            this.message = message;
            this.frames = Collections.unmodifiableList(
                    new ArrayList<>(frames));
        }

        public String exceptionClass() {
            return exceptionClass;
        }

        /** The throwable's message, or null when it had none. */
        public String message() {
            return message;
        }

        public List<String> frames() {
            return frames;
        }

        Map<String, Object> toMap() {
            Map<String, Object> encoded = new LinkedHashMap<>();
            encoded.put("exceptionClass", exceptionClass);
            if (message != null) {
                encoded.put("message", message);
            }
            encoded.put("frames", frames);
            return encoded;
        }
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
    private final String workloadOutput;
    private final Failure junitFailure;
    private final List<String> gaps;

    TargetOutcome(String traceTest, String exceptionTargetId,
                  String targetMethod, String targetExceptionClass,
                  int junitExitCode, Trace trace, long traceRecords,
                  long targetMethodRecords, long targetThrowRecords,
                  String workloadOutput, Failure junitFailure,
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
        this.workloadOutput = workloadOutput;
        this.junitFailure = junitFailure;
        this.gaps = Collections.unmodifiableList(new ArrayList<>(gaps));
    }

    public String traceTest() {
        return traceTest;
    }

    public String exceptionTargetId() {
        return exceptionTargetId;
    }

    public String targetMethod() {
        return targetMethod;
    }

    public String targetExceptionClass() {
        return targetExceptionClass;
    }

    public int junitExitCode() {
        return junitExitCode;
    }

    /** Reported, never used to decide {@link #usable()}. */
    public boolean junitPassed() {
        return junitExitCode == 0;
    }

    public Trace trace() {
        return trace;
    }

    public long traceRecords() {
        return traceRecords;
    }

    /** Streamed rows attributed to the target method. */
    public long targetMethodRecords() {
        return targetMethodRecords;
    }

    /** Rows where the target method exited with the annotated exception. */
    public long targetThrowRecords() {
        return targetThrowRecords;
    }

    /** Whether the target method executed at all during this run. */
    public boolean targetMethodReached() {
        return targetMethodRecords > 0L;
    }

    /**
     * Whether the annotated exception left the target method.
     *
     * <p>Stronger than {@link #targetMethodReached()} and still weaker than a
     * branch-level verdict: it says the annotated exception type propagated
     * out of the target method, not that the solver's selected branch was the
     * one taken. The branch verdict belongs to the aggregation and composition
     * stages that consume the same trace.</p>
     *
     * <p>Neither reach nor an observed target throw is acceptance, which is
     * why {@link #usable()} does not consult this: acceptance is the composed
     * {@code candidate.smt2} and its Z3 result. A {@code false} here is also
     * not symmetric with a {@code true} - it means no row said so, which is
     * an observation only for a pass that records the target's exceptional
     * exit. Both readings are named in {@link #gaps()}.</p>
     */
    public boolean targetExceptionObserved() {
        return targetThrowRecords > 0L;
    }

    /** File holding the workload JVM's merged output, or null. */
    public String workloadOutput() {
        return workloadOutput;
    }

    /**
     * The throwable that ended the workload, or null when it exited zero.
     *
     * <p>Reported for the same reason {@link #junitExitCode()} is, and with
     * the same standing: it says what the enclosing workload did, never
     * whether the run is usable.</p>
     */
    public Failure junitFailure() {
        return junitFailure;
    }

    /** Named evidence the run did not produce. */
    public List<String> gaps() {
        return gaps;
    }

    /** Whether downstream stages can use this run. */
    public boolean usable() {
        return trace == Trace.CLOSED && targetMethodReached();
    }

    /** The diagnostic that explains an unusable run, or null. */
    public LauncherDiagnostic diagnostic() {
        if (trace == Trace.MISSING) {
            return LauncherDiagnostic.TRACE_MANIFEST_MISSING;
        }
        if (trace == Trace.INCOMPLETE) {
            return LauncherDiagnostic.TRACE_INCOMPLETE;
        }
        if (!targetMethodReached()) {
            return LauncherDiagnostic.TARGET_NOT_REACHED;
        }
        return null;
    }

    public String toJson() {
        return CausynthJson.objectWithoutNulls(
                "schemaVersion", 1,
                "kind", "SOURCE_FIRST_LAUNCHER_OUTCOME",
                "traceTest", traceTest,
                "exceptionTargetId", exceptionTargetId,
                "targetMethod", targetMethod,
                "targetExceptionClass", targetExceptionClass,
                "junitExitCode", junitExitCode,
                "junitPassed", junitPassed(),
                "trace", trace.name(),
                "traceRecords", traceRecords,
                "targetMethodRecords", targetMethodRecords,
                "targetThrowRecords", targetThrowRecords,
                "targetMethodReached", targetMethodReached(),
                "targetExceptionObserved", targetExceptionObserved(),
                "workloadOutput", workloadOutput,
                "junitFailure", junitFailure == null
                        ? null : junitFailure.toMap(),
                "usable", usable(),
                "diagnostic", diagnostic() == null ? null
                        : diagnostic().name(),
                "gaps", gaps);
    }
}
