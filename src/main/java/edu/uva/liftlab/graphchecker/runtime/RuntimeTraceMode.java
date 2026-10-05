package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.setting;

import java.util.Locale;

/**
 * Which pass this JVM is.  Declared, never inferred from other keys.
 *
 * <p>{@link #REPLAY_CONTEXT} keeps the exact stacks accessors need and
 * writes no trace: that workload's trace is the seed's.</p>
 */
public enum RuntimeTraceMode {
    DISCOVERY,
    /** The recording: rich hooks over every candidate region. */
    REGION_STATE,
    REPLAY_CONTEXT;

    public static RuntimeTraceMode configured() {
        String value = firstNonBlank(
                setting("causynth.trace.mode", "CAUSYNTH_TRACE_MODE"),
                "discovery");
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
