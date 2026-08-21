package edu.uva.liftlab.graphchecker.launcher;

/**
 * Named failure of one source-first launcher prerequisite or step.
 *
 * <p>Every launcher failure carries one of these codes so an absent
 * prerequisite is reported as itself instead of as a stack trace from deep
 * inside Maven, the JVM, or the workload. The codes are part of the
 * launcher's contract: a caller may branch on them, and the report of a
 * blocked run names them literally.</p>
 */
public enum LauncherDiagnostic {
    /** The command line is not a valid launcher invocation. */
    USAGE,

    /** {@code --hadoop-home} is absent, or is not a directory. */
    HADOOP_HOME_MISSING,

    /** One required Hadoop module directory or its {@code pom.xml} is absent. */
    HADOOP_MODULE_MISSING,

    /** The Maven executable cannot be found or is not executable. */
    MAVEN_MISSING,

    /**
     * No protoc executable was supplied and none is on {@code PATH}.
     *
     * <p>Hadoop 3.0.0-alpha4 pins {@code protobuf.version} and refuses to
     * generate its Protobuf sources without a matching {@code protoc}, so the
     * launcher refuses first and names it.</p>
     */
    PROTOC_MISSING,

    /** A protoc executable was found, but it is not the pinned version. */
    PROTOC_VERSION_MISMATCH,

    /** The Hadoop Maven build ran and exited non-zero. */
    HADOOP_BUILD_FAILED,

    /** The build did not leave a readable test-scope classpath file behind. */
    TEST_CLASSPATH_MISSING,

    /** A Hadoop module output directory expected on the classpath is absent. */
    MODULE_OUTPUT_MISSING,

    /** An entry named by the test-scope classpath file does not exist. */
    CLASSPATH_ENTRY_MISSING,

    /** The custom JDK image or its {@code bin/java} is absent. */
    JDK_MISSING,

    /**
     * No {@code @CausynthExceptionTarget} with the requested id exists in the
     * scanned class inputs, or more than one does.
     */
    TARGET_SITE_UNRESOLVED,

    /** The workload JVM could not be started, or the launcher was interrupted. */
    WORKLOAD_JVM_FAILED,

    /** The workload wrote no streaming trace manifest. */
    TRACE_MANIFEST_MISSING,

    /** The workload's streaming trace manifest is not {@code CLOSED}. */
    TRACE_INCOMPLETE,

    /** The workload produced a closed trace that never entered the target method. */
    TARGET_NOT_REACHED,

    /** A launcher input or output file could not be read or written. */
    IO_FAILED
}
