package edu.uva.liftlab.graphchecker;

/**
 * Environment values supplied directly by the customized VM.
 */
public final class SymbolicEnvironment {
    public static final String CURRENT_TIME_MILLIS_RETURN =
            "<java.lang.System: long currentTimeMillis()>.return";

    private SymbolicEnvironment() {
    }

    public static boolean isCurrentTimeMillisReturn(String cell) {
        return CURRENT_TIME_MILLIS_RETURN.equals(cell);
    }
}
