package edu.uva.liftlab.graphchecker.launcher;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Runs one Hadoop source test under the concolic JDK, and says what it
 * produced.
 *
 * <p>This is the source-first launcher: it drives the workload that exists in
 * the Hadoop checkout, with the configuration the experiment needs supplied
 * from outside the test, and it judges the run by the evidence the run wrote
 * rather than by the test's own verdict.</p>
 *
 * <h3>Two commands</h3>
 *
 * <p>{@code build} validates the checkout's toolchain and compiles it;
 * {@code run} executes the workload against what {@code build} left behind.
 * They are separate because only the first needs a Hadoop toolchain: the
 * checkout pins the {@code protoc} that generates its Protobuf sources, and a
 * machine without it can still run a workload against an existing build
 * rather than being stopped by a toolchain it does not need.</p>
 *
 * <h3>One pass</h3>
 *
 * <p>A run is one workload pass, not a campaign. The instrumentation mode,
 * the trace directory and the repetition that turns two passes into a
 * skeleton-then-state protocol belong to the stage above; this launcher takes
 * the instrumented classes it is given, forwards the {@code causynth.*}
 * properties it was started with, and can therefore be invoked once per pass
 * without knowing the protocol exists.</p>
 *
 * <h3>Exit status</h3>
 *
 * <p>Zero when the run produced a usable target outcome. A failing JUnit
 * method does not by itself make a run unusable, and a passing one does not
 * make it usable: the criterion is a closed trace that entered the target
 * method.</p>
 */
public final class SourceTestLauncher {

    private static final int EXIT_UNUSABLE_RUN = 1;
    private static final int EXIT_PREREQUISITE = 2;

    private SourceTestLauncher() {
    }

    public static void main(String[] args) {
        int status;
        try {
            status = run(args);
        } catch (LauncherException failure) {
            System.err.println("[launcher] " + failure.getMessage());
            if (failure.diagnostic() == LauncherDiagnostic.USAGE) {
                SourceTestLauncherOptions.printUsage(
                        new PrintWriter(System.err));
            }
            status = EXIT_PREREQUISITE;
        }
        System.exit(status);
    }

    /** Runs one invocation and returns its exit status. */
    public static int run(String[] args) throws LauncherException {
        SourceTestLauncherOptions options =
                SourceTestLauncherOptions.parse(args);
        if (options.command() == SourceTestLauncherOptions.Command.BUILD) {
            return build(options);
        }
        return runWorkload(options);
    }

    private static int build(SourceTestLauncherOptions options)
            throws LauncherException {
        Path classpathFile = HadoopSourceBuild.build(options.hadoopHome(),
                options.maven(), options.protoc(), options.outputDir());
        System.out.println("[launcher] test-scope classpath: " + classpathFile);
        return 0;
    }

    private static int runWorkload(SourceTestLauncherOptions options)
            throws LauncherException {
        // Resolving the target first turns "the source declares no such
        // target" into a prerequisite failure instead of a wasted workload.
        WorkloadTarget target = WorkloadTarget.resolve(
                options.exceptionTargetId(), targetClasses(options));

        Path targetSpec = TargetSpecFile.write(options.outputDir(),
                options.exceptionTargetId());

        WorkloadConfiguration configuration =
                WorkloadConfiguration.of(options.conf());
        Path confDir = configuration.writeTo(options.outputDir()
                .resolve("conf"));

        List<String> classpath = WorkloadClasspath.assemble(
                options.hadoopHome(), options.instrumented(), confDir,
                options.graphCheckerLibs(),
                WorkloadClasspath.graphCheckerCodeSource(),
                options.classpathFile());

        HadoopTestProperties.createDirectories(options.outputDir());
        createTraceDirectory(options.traceDir());

        Map<String, String> owned =
                new LinkedHashMap<>(HadoopTestProperties.of(
                        options.outputDir()));
        owned.put("causynth.trace.output.dir", options.traceDir().toString());
        owned.put("causynth.trace.test", options.traceTest());
        owned.put("causynth.target.spec", targetSpec.toString());
        if (!configuration.isEmpty()) {
            owned.put(WorkloadEntryPoint.CONFIG_RESOURCE_PROPERTY,
                    WorkloadConfiguration.RESOURCE_NAME);
            if (!options.confDefaultsClasses().isEmpty()) {
                owned.put(WorkloadEntryPoint.CONFIG_DEFAULTS_CLASSES_PROPERTY,
                        String.join(",", options.confDefaultsClasses()));
            }
        }
        // The workload's @Test timeout is a wall-clock budget for a compiled
        // JVM; interpreted and instrumented it is not reachable, and its
        // watchdog thread would abandon the cluster mid-run.
        owned.put("causynth.junit.ignore.timeout", "true");
        // MiniDFSCluster leaves non-daemon threads behind, so the workload JVM
        // has to be told to leave once the trace is flushed.
        owned.put("causynth.junit.exit.after.run", "true");

        Path javaBinary = WorkloadJvm.javaBinary(options.jdkHome());
        List<String> command = WorkloadJvm.command(javaBinary,
                WorkloadJvm.jvmOptions(options.jdkHome()),
                WorkloadJvm.systemProperties(owned, System.getProperties()),
                classpath, WorkloadEntryPoint.class.getName(),
                Arrays.asList(options.testClass(), options.testMethod()));

        Path workloadOutput = options.outputDir()
                .resolve(WorkloadJvm.OUTPUT_FILE_NAME);
        System.out.println("[launcher] " + String.join(" ", command));
        int junitExitCode = WorkloadJvm.run(command, options.outputDir(),
                WorkloadJvm.nativeLibraryDirectory(options.jdkHome()),
                workloadOutput);

        TargetOutcome outcome = TargetOutcomeCapture.capture(
                options.traceDir(), target, options.traceTest(),
                junitExitCode, workloadOutput);
        Path record = TargetOutcomeCapture.write(options.outputDir(), outcome);
        report(outcome, record);
        return outcome.usable() ? 0 : EXIT_UNUSABLE_RUN;
    }

    private static List<Path> targetClasses(
            SourceTestLauncherOptions options) {
        if (!options.targetClasses().isEmpty()) {
            return options.targetClasses();
        }
        List<Path> inputs = new ArrayList<>(options.instrumented());
        for (String output : WorkloadClasspath.MODULE_OUTPUTS) {
            inputs.add(options.hadoopHome().resolve(output));
        }
        return inputs;
    }

    private static void createTraceDirectory(Path traceDir)
            throws LauncherException {
        try {
            Files.createDirectories(traceDir);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot create " + traceDir, failure);
        }
    }

    private static void report(TargetOutcome outcome, Path record) {
        System.out.println("[launcher] outcome: " + record);
        System.out.println("[launcher] junit exit " + outcome.junitExitCode()
                + ", trace " + outcome.trace()
                + " (" + outcome.traceRecords() + " rows), "
                + outcome.targetMethodRecords() + " on "
                + outcome.targetMethod());
        if (outcome.workloadOutput() != null) {
            System.out.println("[launcher] workload output: "
                    + outcome.workloadOutput());
        }
        if (outcome.junitFailure() != null) {
            System.out.println("[launcher] workload threw "
                    + outcome.junitFailure().exceptionClass()
                    + (outcome.junitFailure().message() == null ? ""
                    : ": " + outcome.junitFailure().message()));
            for (String frame : outcome.junitFailure().frames()) {
                System.out.println("[launcher]   " + frame);
            }
        }
        for (String gap : outcome.gaps()) {
            System.out.println("[launcher] gap: " + gap);
        }
        if (!outcome.usable()) {
            System.err.println("[launcher] " + outcome.diagnostic());
        }
    }
}
