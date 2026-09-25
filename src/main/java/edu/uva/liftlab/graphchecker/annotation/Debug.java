package edu.uva.liftlab.graphchecker.annotation;

import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime;

/** Explicit symbolic inputs understood by GraphChecker's selective replay. */
public final class Debug {
    private static final String BOOLEAN_MARKER_SIGNATURE =
            "<edu.uva.liftlab.graphchecker.annotation.Debug: "
                    + "boolean makeSymbolicBoolean(java.lang.String)>";

    private Debug() {
    }

    public static boolean makeSymbolicBoolean(String name) {
        return ConcolicRegionRuntime.materializeSymbolicBoolean(name);
    }

    /** Soot quotes Java-keyword package segments in rendered signatures. */
    public static boolean isBooleanMarkerSignature(String signature) {
        return signature != null && BOOLEAN_MARKER_SIGNATURE.equals(
                signature.replace("'", ""));
    }
}
