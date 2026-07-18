package edu.uva.liftlab.graphchecker;

/**
 * Exact application-level aliases for environment values supplied by the
 * customized VM.  An alias is admitted only when its implementation is a
 * transparent wrapper around the named JDK intrinsic; arbitrary methods
 * called {@code now} remain ordinary call returns.
 */
public final class SymbolicEnvironment {
    public static final String CURRENT_TIME_MILLIS_RETURN =
            "<java.lang.System: long currentTimeMillis()>.return";
    public static final String HADOOP_TIME_NOW_RETURN =
            "<org.apache.hadoop.util.Time: long now()>.return";
    public static final String CURRENT_TIME_MILLIS_PLACEHOLDER =
            "currentTimeMills";

    private SymbolicEnvironment() {
    }

    /**
     * Hadoop {@code Time.now()} is a transparent call to
     * {@code System.currentTimeMillis()} in the analyzed pre-HDFS-11741 tree.
     * The symbolic value produced by the customized JDK therefore reaches the
     * wrapper's return unchanged.
     */
    public static boolean isCurrentTimeMillisReturn(String cell) {
        return CURRENT_TIME_MILLIS_RETURN.equals(cell)
                || HADOOP_TIME_NOW_RETURN.equals(cell);
    }
}
