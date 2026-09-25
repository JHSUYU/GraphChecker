package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

import java.util.Locale;

/**
 * Which pass this JVM is: the one key that says so.
 *
 * <p>The weaver reads it to choose the evidence level, and the recorder
 * reads it to know whether it publishes a trace at all.  {@link
 * #REPLAY_CONTEXT} is the concolic replay: it keeps the exact method and
 * call-site stacks every accessor invocation needs and writes no trace,
 * because the trace of that workload is the seed's.  Declared and never
 * inferred -- the pass is a fact about how the campaign started this JVM,
 * not something to read off which unrelated keys happen to be set.</p>
 */
public enum RuntimeTraceMode {
    /** Static discovery: the weaver analyses and weaves nothing. */
    DISCOVERY,
    /** The recording: rich hooks over every candidate region. */
    REGION_STATE,
    REPLAY_CONTEXT;

    public static RuntimeTraceMode configured() {
        String value = firstNonBlank(
                System.getProperty("causynth.trace.mode"),
                System.getenv("CAUSYNTH_TRACE_MODE"), "discovery");
        String normalized = value.trim().toLowerCase(Locale.ROOT)
                .replace('_', '-');
        if ("discovery".equals(normalized)) {
            return DISCOVERY;
        }
        if ("region-state".equals(normalized)) {
            return REGION_STATE;
        }
        if ("replay-context".equals(normalized)) {
            return REPLAY_CONTEXT;
        }
        throw new IllegalArgumentException(
                "Unknown causynth trace mode: " + value);
    }

}
