package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.setting;

import java.util.Locale;

public enum RuntimeTraceMode {
    DISCOVERY,
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
