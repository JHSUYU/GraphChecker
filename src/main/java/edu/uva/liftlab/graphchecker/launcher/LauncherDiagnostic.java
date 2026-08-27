package edu.uva.liftlab.graphchecker.launcher;

/**
 * Named failure of one source-first launcher prerequisite or step, so an
 * absent prerequisite is reported as itself instead of as a stack trace from
 * deep inside Maven, the JVM, or the workload.  The codes are part of the
 * launcher's contract: a caller may branch on them.
 */
public enum LauncherDiagnostic {
    USAGE,
    HADOOP_HOME_MISSING,
    HADOOP_MODULE_MISSING,
    MAVEN_MISSING,
    /** Hadoop 3.0.0-alpha4 refuses to generate Protobuf sources without one. */
    PROTOC_MISSING,
    PROTOC_VERSION_MISMATCH,
    HADOOP_BUILD_FAILED,
    TEST_CLASSPATH_MISSING,
    MODULE_OUTPUT_MISSING,
    CLASSPATH_ENTRY_MISSING,
    JDK_MISSING,
    /** No {@code @CausynthExceptionTarget} with the requested id exists in the
     *  scanned class inputs, or more than one does. */
    TARGET_SITE_UNRESOLVED,
    WORKLOAD_JVM_FAILED,
    TRACE_MANIFEST_MISSING,
    /** The workload's streaming trace manifest is not {@code CLOSED}. */
    TRACE_INCOMPLETE,
    /** The workload produced a closed trace that never entered the target. */
    TARGET_NOT_REACHED,
    /**
     * The closed trace carries no method envelope at all, so it cannot say
     * whether the target method was entered.  Not {@link #TARGET_NOT_REACHED}:
     * the concolic replay tree installs region hooks rather than
     * trace-recorder hooks and has no row that could carry the answer.
     * Reporting the first as the second is a false negative that already cost
     * this experiment an investigation into a correct workload.
     */
    TARGET_REACH_UNRECORDED,
    IO_FAILED
}
