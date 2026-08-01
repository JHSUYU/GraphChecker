package edu.uva.liftlab.graphchecker.runtime;

import java.util.Locale;

/** Runtime evidence level selected before bytecode instrumentation. */
public enum RuntimeTraceMode {
    REGION_SKELETON,
    REGION_STATE;

    public static RuntimeTraceMode configured() {
        String value = firstNonBlank(
                System.getProperty("causynth.trace.mode"),
                System.getenv("CAUSYNTH_TRACE_MODE"), "region-skeleton");
        String normalized = value.trim().toLowerCase(Locale.ROOT)
                .replace('_', '-');
        if ("region-skeleton".equals(normalized)) {
            return REGION_SKELETON;
        }
        if ("region-state".equals(normalized)) {
            return REGION_STATE;
        }
        throw new IllegalArgumentException(
                "Unknown causynth trace mode: " + value);
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value;
            }
        }
        return "";
    }
}
