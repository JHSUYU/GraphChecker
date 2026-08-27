package edu.uva.liftlab.graphchecker.launcher;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * Runs one Hadoop source test under the concolic JDK, and says what it
 * produced: it drives the workload that exists in the Hadoop checkout, with
 * the configuration the experiment needs supplied from outside the test, and
 * judges the run by the evidence the run wrote rather than by the test's own
 * verdict.
 *
 * <p>{@code build} validates the checkout's toolchain and compiles it;
 * {@code run} executes the workload against what {@code build} left behind.
 * They are separate because only the first needs a Hadoop toolchain.  A run is
 * one workload pass, not a campaign; the instrumentation mode, the trace
 * directory and the two-pass protocol belong to the stage above.  Exit status
 * is zero when the run produced a usable target outcome: a closed trace that
 * entered the target method, whatever JUnit said.</p>
 *
 * <p>Argument handling is pure - no file, process or environment beyond the
 * documented protoc variable - so it stays testable with no Hadoop checkout;
 * whether a path exists is a question for {@link HadoopSourceBuild} and
 * {@link WorkloadClasspath}.  There is deliberately no properties grammar.</p>
 */
public final class SourceTestLauncher {

    /** Environment variable Hadoop's own build uses to locate protoc. */
    public static final String PROTOC_ENVIRONMENT_VARIABLE =
            "HADOOP_PROTOC_PATH";

    /**
     * Resource name the workload JVM registers for the {@code --conf}
     * overrides; not a Hadoop site file.  The unique name is load-bearing: an
     * {@code hdfs-site.xml} first on the classpath would hide the checkout's
     * own test {@code hdfs-site.xml}, which sets
     * {@code dfs.namenode.fs-limits.min-block-size} to zero - without it the
     * balancer test's 100-byte block size is rejected.  Being registered
     * <em>later</em> than the site files is what makes it win: see
     * {@link WorkloadEntryPoint#CONFIG_DEFAULTS_CLASSES_PROPERTY}.
     */
    public static final String CONFIG_RESOURCE_NAME =
            "graphchecker-workload-site.xml";

    /**
     * The target specification {@code CausynthTargetResolver} loads.  The
     * launcher introduces no naming mechanism of its own: a target is named by
     * {@code @CausynthExceptionTarget("<id>")} in the analyzed source and by
     * {@code exception_target_id} here, and the launcher's job is to make the
     * two agree.  One unindented {@code key: value} line, comments allowed.
     */
    public static final String TARGET_SPEC_FILE_NAME = "target.yaml";

    /** Scratch subdirectory of the launcher output directory. */
    private static final String SCRATCH_DIRECTORY = "workload";

    /** Options the build command has no use for. */
    private static final List<String> RUN_ONLY_OPTIONS = Arrays.asList(
            "test-class", "test-method", "jdk-home", "instrumented",
            "target-classes", "conf-defaults-class", "graphchecker-lib");

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
                printUsage(new PrintWriter(System.err));
            }
            status = EXIT_PREREQUISITE;
        }
        System.exit(status);
    }

    public static int run(String[] args) throws LauncherException {
        if (args == null || args.length == 0) {
            throw usage("expected a command: build|run");
        }
        String command = args[0] == null
                ? "" : args[0].trim().toLowerCase(Locale.ROOT);
        if (!"build".equals(command) && !"run".equals(command)) {
            throw usage("unknown command: " + args[0]);
        }
        CommandLine parsed;
        try {
            parsed = new DefaultParser().parse(options(),
                    Arrays.copyOfRange(args, 1, args.length));
        } catch (ParseException failure) {
            throw usage(failure.getMessage());
        }
        if (!parsed.getArgList().isEmpty()) {
            throw usage("unexpected argument: " + parsed.getArgList().get(0));
        }
        Path hadoopHome = requiredPath(parsed, "hadoop-home");
        Path outputDir = requiredPath(parsed, "output-dir");
        String targetId = required(parsed, "exception-target-id");
        Map<String, String> conf = parseConf(parsed.getOptionValues("conf"));
        if ("run".equals(command)) {
            return runWorkload(parsed, hadoopHome, outputDir, targetId, conf);
        }
        for (String name : RUN_ONLY_OPTIONS) {
            if (parsed.hasOption(name)) {
                throw usage("--" + name + " applies to the run command only");
            }
        }
        String protoc = optional(parsed, "protoc");
        if (protoc == null) {
            String environment = System.getenv(PROTOC_ENVIRONMENT_VARIABLE);
            protoc = environment == null || environment.trim().isEmpty()
                    ? null : environment.trim();
        }
        String maven = optional(parsed, "maven");
        System.out.println("[launcher] test-scope classpath: "
                + HadoopSourceBuild.build(hadoopHome,
                        maven == null ? "mvn" : maven, protoc, outputDir));
        return 0;
    }

    private static int runWorkload(CommandLine parsed, Path hadoopHome,
                                   Path outputDir, String targetId,
                                   Map<String, String> conf)
            throws LauncherException {
        String testClass = required(parsed, "test-class");
        String testMethod = required(parsed, "test-method");
        Path jdkHome = requiredPath(parsed, "jdk-home");
        List<Path> instrumented = paths(parsed, "instrumented");
        String traceDirValue = optional(parsed, "trace-dir");
        Path traceDir = traceDirValue == null
                ? outputDir.resolve("runtime") : absolute(traceDirValue);

        // Resolving the target first turns "the source declares no such
        // target" into a prerequisite failure instead of a wasted workload.
        // An empty --target-classes scans the workload classpath's own
        // outputs, which reads every compiled Hadoop class; naming the
        // declaring module keeps start-up proportional.
        List<Path> targetClasses = paths(parsed, "target-classes");
        if (targetClasses.isEmpty()) {
            targetClasses = new ArrayList<>(instrumented);
            for (String output : WorkloadClasspath.MODULE_OUTPUTS) {
                targetClasses.add(hadoopHome.resolve(output));
            }
        }
        WorkloadTarget target = WorkloadTarget.resolve(targetId, targetClasses);
        Path targetSpec = writeTargetSpec(outputDir, targetId);
        Path confDir = writeWorkloadConfiguration(outputDir.resolve("conf"),
                conf);

        // --graphchecker-lib names a library the recorder needs at a version
        // the workload does not provide; the flat classpath otherwise resolves
        // every shared library to the workload's version and the recorder
        // fails at its first call rather than degrading.
        List<String> classpath = WorkloadClasspath.assemble(hadoopHome,
                instrumented, confDir, paths(parsed, "graphchecker-lib"),
                WorkloadClasspath.graphCheckerCodeSource(),
                outputDir.resolve(HadoopSourceBuild.CLASSPATH_FILE_NAME));

        createDirectory(traceDir);
        Map<String, String> owned = hadoopTestProperties(outputDir);
        owned.put("causynth.trace.output.dir", traceDir.toString());
        owned.put("causynth.trace.test", testClass + "#" + testMethod);
        owned.put("causynth.target.spec", targetSpec.toString());
        if (!conf.isEmpty()) {
            owned.put(WorkloadEntryPoint.CONFIG_RESOURCE_PROPERTY,
                    CONFIG_RESOURCE_NAME);
            // Hadoop's own defaults come from static initializers and the last
            // registration wins, so the launcher's overrides survive only if
            // these are initialized first.
            List<String> defaults = names(parsed, "conf-defaults-class");
            if (!defaults.isEmpty()) {
                owned.put(WorkloadEntryPoint.CONFIG_DEFAULTS_CLASSES_PROPERTY,
                        String.join(",", defaults));
            }
        }
        // The workload's @Test timeout is a wall-clock budget for a compiled
        // JVM; interpreted and instrumented it is not reachable, and its
        // watchdog thread would abandon the cluster mid-run.
        owned.put("causynth.junit.ignore.timeout", "true");
        // MiniDFSCluster leaves non-daemon threads behind, so the workload JVM
        // has to be told to leave once the trace is flushed.
        owned.put("causynth.junit.exit.after.run", "true");

        List<String> command = WorkloadJvm.command(
                WorkloadJvm.javaBinary(jdkHome), WorkloadJvm.jvmOptions(jdkHome),
                WorkloadJvm.systemProperties(owned, System.getProperties()),
                classpath, WorkloadEntryPoint.class.getName(),
                Arrays.asList(testClass, testMethod));

        Path workloadOutput = outputDir.resolve(WorkloadJvm.OUTPUT_FILE_NAME);
        System.out.println("[launcher] " + String.join(" ", command));
        int junitExitCode = WorkloadJvm.run(command, outputDir,
                WorkloadJvm.nativeLibraryDirectory(jdkHome), workloadOutput);

        TargetOutcome outcome = TargetOutcome.capture(traceDir, target,
                testClass + "#" + testMethod, junitExitCode, workloadOutput);
        report(outcome, TargetOutcome.write(outputDir, outcome));
        return outcome.usable() ? 0 : EXIT_UNUSABLE_RUN;
    }

    private static void report(TargetOutcome outcome, Path record) {
        System.out.println("[launcher] outcome: " + record);
        System.out.println("[launcher] junit exit " + outcome.junitExitCode()
                + ", trace " + outcome.trace()
                + " (" + outcome.traceRecords() + " rows, "
                + outcome.methodEnvelopeRecords() + " method envelopes), "
                + outcome.targetMethodRecords() + " on "
                + outcome.targetMethod());
        if (outcome.workloadOutput() != null) {
            System.out.println("[launcher] workload output: "
                    + outcome.workloadOutput());
        }
        for (String gap : outcome.gaps()) {
            System.out.println("[launcher] gap: " + gap);
        }
        if (outcome.diagnostic() != null) {
            // Named whether or not it makes the run unusable: a pass that
            // could not observe the reach question still has to say so.
            System.err.println("[launcher] " + outcome.diagnostic());
        }
    }

    /**
     * The system properties Surefire would have set.  The workload runs the
     * JUnit method directly, so nothing else defines where a MiniDFSCluster
     * puts its storage directories or logs; without {@code test.build.data}
     * the cluster falls back to a relative {@code build/test/data} and two runs
     * quietly share one NameNode image.  The scratch tree is rooted in the
     * launcher's own output directory rather than the checkout's
     * {@code target/}, so a Maven build cannot delete a workload's evidence out
     * from under it.  {@code java.security.egd} matters more than it looks:
     * MiniDFSCluster seeds several {@code SecureRandom} instances during
     * startup, and on a machine with little entropy the blocking device turns
     * an interpreted run into a hang that resembles a workload deadlock.
     */
    private static Map<String, String> hadoopTestProperties(Path outputDir)
            throws LauncherException {
        Path scratch = outputDir.resolve(SCRATCH_DIRECTORY);
        Path testDir = scratch.resolve("test-dir");
        Path log = scratch.resolve("log");
        Path tmp = scratch.resolve("tmp");
        createDirectory(testDir);
        createDirectory(log);
        createDirectory(tmp);
        Map<String, String> properties = new LinkedHashMap<>();
        properties.put("test.build.dir", testDir.toString());
        properties.put("test.build.data", testDir.toString());
        properties.put("hadoop.log.dir", log.toString());
        properties.put("hadoop.tmp.dir", tmp.toString());
        properties.put("java.io.tmpdir", tmp.toString());
        properties.put("java.net.preferIPv4Stack", "true");
        properties.put("java.security.egd", "file:///dev/urandom");
        return properties;
    }

    private static Path writeTargetSpec(Path outputDir, String targetId)
            throws LauncherException {
        if (targetId.indexOf('\n') >= 0 || targetId.indexOf('\r') >= 0
                || targetId.indexOf('#') >= 0) {
            throw usage("exception target id is not a single plain token: "
                    + targetId);
        }
        Path path = outputDir.resolve(TARGET_SPEC_FILE_NAME);
        write(path, "# Generated by GraphChecker's source-first launcher.\n"
                + "exception_target_id: " + targetId + "\n");
        return path;
    }

    /**
     * Renders the {@code --conf} overrides into an ordinary Hadoop XML
     * resource and returns the directory the caller puts on the workload
     * classpath.  The workload's test builds its own {@code Configuration} and
     * the launcher must not edit it, so the overrides are registered by the
     * workload JVM instead.
     */
    private static Path writeWorkloadConfiguration(Path confDir,
                                                   Map<String, String> values)
            throws LauncherException {
        StringBuilder xml = new StringBuilder("<?xml version=\"1.0\"?>\n"
                + "<!-- Generated by GraphChecker's source-first launcher. "
                + "Registered with Configuration.addDefaultResource, so it "
                + "overrides the site files without hiding them. -->\n"
                + "<configuration>\n");
        for (Map.Entry<String, String> entry : values.entrySet()) {
            xml.append("  <property>\n    <name>")
                    .append(escape(entry.getKey()))
                    .append("</name>\n    <value>")
                    .append(escape(entry.getValue()))
                    .append("</value>\n  </property>\n");
        }
        write(confDir.resolve(CONFIG_RESOURCE_NAME),
                xml.append("</configuration>\n").toString());
        return confDir;
    }

    private static String escape(String value) {
        return value == null ? "" : value.replace("&", "&amp;")
                .replace("<", "&lt;").replace(">", "&gt;")
                .replace("\"", "&quot;");
    }

    private static void write(Path path, String text)
            throws LauncherException {
        try {
            Files.createDirectories(path.getParent());
            Files.write(path, text.getBytes(StandardCharsets.UTF_8));
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot write " + path, failure);
        }
    }

    private static void createDirectory(Path directory)
            throws LauncherException {
        try {
            Files.createDirectories(directory);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot create " + directory, failure);
        }
    }

    private static Map<String, String> parseConf(String[] values)
            throws LauncherException {
        Map<String, String> conf = new LinkedHashMap<>();
        if (values == null) {
            return conf;
        }
        for (String value : values) {
            int separator = value.indexOf('=');
            if (separator <= 0) {
                throw usage("--conf expects key=value, got: " + value);
            }
            String key = value.substring(0, separator).trim();
            if (key.isEmpty()) {
                throw usage("--conf expects a non-blank key, got: " + value);
            }
            if (conf.put(key, value.substring(separator + 1)) != null) {
                throw usage("--conf sets " + key + " more than once");
            }
        }
        return conf;
    }

    private static List<String> names(CommandLine parsed, String name)
            throws LauncherException {
        List<String> names = new ArrayList<>();
        String[] values = parsed.getOptionValues(name);
        if (values == null) {
            return names;
        }
        for (String value : values) {
            String trimmed = value.trim();
            if (trimmed.isEmpty()) {
                throw usage("--" + name + " expects a class name");
            }
            if (!names.contains(trimmed)) {
                names.add(trimmed);
            }
        }
        return names;
    }

    private static List<Path> paths(CommandLine parsed, String name) {
        List<Path> paths = new ArrayList<>();
        String[] values = parsed.getOptionValues(name);
        if (values != null) {
            for (String value : values) {
                paths.add(absolute(value));
            }
        }
        return paths;
    }

    private static String required(CommandLine parsed, String name)
            throws LauncherException {
        String value = optional(parsed, name);
        if (value == null) {
            throw usage("--" + name + " is required");
        }
        return value;
    }

    private static String optional(CommandLine parsed, String name) {
        String value = parsed.getOptionValue(name);
        return value == null || value.trim().isEmpty() ? null : value.trim();
    }

    private static Path requiredPath(CommandLine parsed, String name)
            throws LauncherException {
        return absolute(required(parsed, name));
    }

    private static Path absolute(String value) {
        return Paths.get(value).toAbsolutePath().normalize();
    }

    private static LauncherException usage(String detail) {
        return new LauncherException(LauncherDiagnostic.USAGE, detail);
    }

    static void printUsage(PrintWriter writer) {
        new HelpFormatter().printHelp(writer, 80,
                "SourceTestLauncher build|run [OPTIONS]",
                "Runs one Hadoop source test under the custom concolic JDK.",
                options(), 2, 2,
                "build validates the checkout, compiles it and writes "
                        + HadoopSourceBuild.CLASSPATH_FILE_NAME
                        + " into --output-dir; run executes the workload once "
                        + "and captures its target outcome.");
        writer.flush();
    }

    private static Options options() {
        Options options = new Options();
        options.addOption(one("hadoop-home", "dir",
                "Hadoop source checkout to build and run against"));
        options.addOption(one("output-dir", "dir",
                "Launcher output directory"));
        options.addOption(one("exception-target-id", "id",
                "@CausynthExceptionTarget value identifying the target"));
        options.addOption(one("test-class", "fqcn",
                "Hadoop source test class (run)"));
        options.addOption(one("test-method", "name",
                "Hadoop source test method (run)"));
        options.addOption(one("jdk-home", "dir",
                "Custom concolic JDK image (run)"));
        options.addOption(many("instrumented", "dir|jar",
                "Instrumented classes, prepended to the workload classpath"));
        options.addOption(many("target-classes", "dir|jar",
                "Where to look for @CausynthExceptionTarget; defaults to the "
                        + "workload's own class outputs"));
        options.addOption(many("graphchecker-lib", "dir|jar",
                "Library GraphChecker's runtime needs at a version the "
                        + "workload does not provide; prepended ahead of the "
                        + "workload's own dependencies"));
        options.addOption(many("conf", "key=value",
                "Hadoop Configuration override the launcher owns"));
        options.addOption(many("conf-defaults-class", "fqcn",
                "Class whose static initializer registers the workload's own "
                        + "default resources; initialized before the launcher "
                        + "registers its overrides"));
        options.addOption(one("maven", "path",
                "Maven executable; defaults to mvn (build)"));
        options.addOption(one("protoc", "path",
                "protoc executable; defaults to $"
                        + PROTOC_ENVIRONMENT_VARIABLE + " (build)"));
        options.addOption(one("trace-dir", "dir",
                "Runtime trace directory; defaults to <output-dir>/runtime"));
        return options;
    }

    private static Option one(String name, String argument, String help) {
        return Option.builder().longOpt(name).hasArg().argName(argument)
                .desc(help).build();
    }

    private static Option many(String name, String argument, String help) {
        return Option.builder().longOpt(name).hasArgs().argName(argument)
                .desc(help + "; repeatable").build();
    }
}
