package edu.uva.liftlab.graphchecker.annotation;

/**
 * Explicit fault input understood by GraphChecker's selective replay.
 *
 * <p>The ordinary JVM value is {@code false}, so adding a marker does not
 * change a concrete workload.  When the returned value reaches a demanded
 * branch, GraphChecker materializes that exact call return as a symbolic
 * boolean during concolic replay.</p>
 */
public final class CausynthFault {
    public static final String BOOLEAN_MARKER_SIGNATURE =
            "<edu.uva.liftlab.graphchecker.annotation.CausynthFault: "
                    + "boolean makeSymbolicBoolean(java.lang.String)>";

    private CausynthFault() {
    }

    public static boolean makeSymbolicBoolean(String name) {
        return false;
    }

    /** Soot quotes Java-keyword package segments in rendered signatures. */
    public static boolean isBooleanMarkerSignature(String signature) {
        return signature != null && BOOLEAN_MARKER_SIGNATURE.equals(
                signature.replace("'", ""));
    }
}
