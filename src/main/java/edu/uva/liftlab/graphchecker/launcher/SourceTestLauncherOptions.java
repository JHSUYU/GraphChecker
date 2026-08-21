package edu.uva.liftlab.graphchecker.launcher;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.PrintWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * The complete input of one source-first launcher invocation.
 *
 * <p>Parsing is pure: it touches no file, spawns no process, and reads no
 * environment beyond the two documented defaults. Whether a path exists is a
 * question for {@link HadoopSourceBuild} and {@link WorkloadClasspath}, which
 * answer it with a named {@link LauncherDiagnostic}. Keeping the split means
 * argument handling stays testable on a machine with no Hadoop checkout.</p>
 *
 * <p>There is deliberately no properties grammar. Everything the launcher
 * needs is one of the flags below, and everything the workload needs beyond
 * them is either a {@code --conf} entry (a Hadoop {@code Configuration} key)
 * or an inherited {@code causynth.*} system property.</p>
 */
public final class SourceTestLauncherOptions {

    /** Environment variable Hadoop's own build uses to locate protoc. */
    public static final String PROTOC_ENVIRONMENT_VARIABLE =
            "HADOOP_PROTOC_PATH";

    /** What the invocation asks the launcher to do. */
    public enum Command {
        /** Build the Hadoop checkout and emit its test-scope classpath. */
        BUILD,
        /** Run the Hadoop source test once against an existing build. */
        RUN
    }

    private final Command command;
    private final Path hadoopHome;
    private final Path outputDir;
    private final String exceptionTargetId;
    private final String testClass;
    private final String testMethod;
    private final String traceTest;
    private final Path jdkHome;
    private final List<Path> instrumented;
    private final List<Path> targetClasses;
    private final List<Path> graphCheckerLibs;
    private final Map<String, String> conf;
    private final List<String> confDefaultsClasses;
    private final String maven;
    private final String protoc;
    private final Path traceDir;

    private SourceTestLauncherOptions(Command command, Path hadoopHome,
                                      Path outputDir, String exceptionTargetId,
                                      String testClass, String testMethod,
                                      String traceTest, Path jdkHome,
                                      List<Path> instrumented,
                                      List<Path> targetClasses,
                                      List<Path> graphCheckerLibs,
                                      Map<String, String> conf,
                                      List<String> confDefaultsClasses,
                                      String maven,
                                      String protoc, Path traceDir) {
        this.command = command;
        this.hadoopHome = hadoopHome;
        this.outputDir = outputDir;
        this.exceptionTargetId = exceptionTargetId;
        this.testClass = testClass;
        this.testMethod = testMethod;
        this.traceTest = traceTest;
        this.jdkHome = jdkHome;
        this.instrumented = Collections.unmodifiableList(instrumented);
        this.targetClasses = Collections.unmodifiableList(targetClasses);
        this.graphCheckerLibs =
                Collections.unmodifiableList(graphCheckerLibs);
        this.conf = Collections.unmodifiableMap(conf);
        this.confDefaultsClasses =
                Collections.unmodifiableList(confDefaultsClasses);
        this.maven = maven;
        this.protoc = protoc;
        this.traceDir = traceDir;
    }

    public Command command() {
        return command;
    }

    public Path hadoopHome() {
        return hadoopHome;
    }

    public Path outputDir() {
        return outputDir;
    }

    public String exceptionTargetId() {
        return exceptionTargetId;
    }

    public String testClass() {
        return testClass;
    }

    public String testMethod() {
        return testMethod;
    }

    /** Logical workload name; the aggregation stage must be given the same. */
    public String traceTest() {
        return traceTest;
    }

    public Path jdkHome() {
        return jdkHome;
    }

    /** Instrumented class outputs, prepended to the workload classpath. */
    public List<Path> instrumented() {
        return instrumented;
    }

    /**
     * Class outputs scanned for the annotated target.
     *
     * <p>Empty means "scan the workload classpath's own class outputs", which
     * is correct but reads every compiled Hadoop class. Naming the one module
     * that declares the target keeps a run's start-up cost proportional to the
     * target rather than to the checkout.</p>
     */
    public List<Path> targetClasses() {
        return targetClasses;
    }

    /**
     * Libraries GraphChecker's runtime needs ahead of the workload's own.
     *
     * <p>The workload classpath is flat and otherwise resolves every shared
     * library to the workload's version, which is what keeps the workload
     * behaving like itself. A library listed here is the exception: the
     * recorder needs a newer one than the workload ships, and without it the
     * recorder fails at its first call rather than degrading.</p>
     */
    public List<Path> graphCheckerLibs() {
        return graphCheckerLibs;
    }

    /** Hadoop {@code Configuration} overrides the launcher owns. */
    public Map<String, String> conf() {
        return conf;
    }

    /**
     * Classes that register the workload's own default resources.
     *
     * <p>Hadoop's defaults are registered from static initializers, and the
     * last registration wins, so the launcher's overrides survive only if
     * those classes are initialized first. Which classes they are is a
     * property of the workload, not of the launcher: HDFS hides
     * {@code hdfs-default.xml} behind {@code HdfsConfiguration}, another
     * subsystem hides its own behind something else.</p>
     */
    public List<String> confDefaultsClasses() {
        return confDefaultsClasses;
    }

    public String maven() {
        return maven;
    }

    /** Protoc executable, or {@code null} when none was supplied. */
    public String protoc() {
        return protoc;
    }

    public Path traceDir() {
        return traceDir;
    }

    /** The file the build writes and the run reads. */
    public Path classpathFile() {
        return outputDir.resolve(HadoopSourceBuild.CLASSPATH_FILE_NAME);
    }

    public static SourceTestLauncherOptions parse(String[] args)
            throws LauncherException {
        return parse(args, System.getenv(PROTOC_ENVIRONMENT_VARIABLE));
    }

    /**
     * Parses one command line.
     *
     * @param environmentProtoc value of {@code HADOOP_PROTOC_PATH}, used only
     *                          when {@code --protoc} is absent; may be null
     */
    public static SourceTestLauncherOptions parse(String[] args,
                                                  String environmentProtoc)
            throws LauncherException {
        if (args == null || args.length == 0) {
            throw new LauncherException(LauncherDiagnostic.USAGE,
                    "expected a command: build|run");
        }
        Command command = parseCommand(args[0]);
        String[] rest = new String[args.length - 1];
        System.arraycopy(args, 1, rest, 0, rest.length);

        CommandLine parsed;
        try {
            parsed = new DefaultParser().parse(options(), rest);
        } catch (ParseException failure) {
            throw new LauncherException(LauncherDiagnostic.USAGE,
                    failure.getMessage());
        }
        if (!parsed.getArgList().isEmpty()) {
            throw new LauncherException(LauncherDiagnostic.USAGE,
                    "unexpected argument: " + parsed.getArgList().get(0));
        }

        Path hadoopHome = requiredPath(parsed, "hadoop-home");
        Path outputDir = requiredPath(parsed, "output-dir");
        String exceptionTargetId = required(parsed, "exception-target-id");

        String testClass = null;
        String testMethod = null;
        String traceTest = null;
        Path jdkHome = null;
        if (command == Command.RUN) {
            testClass = required(parsed, "test-class");
            testMethod = required(parsed, "test-method");
            jdkHome = requiredPath(parsed, "jdk-home");
            traceTest = optional(parsed, "trace-test");
            if (traceTest == null) {
                traceTest = testClass + "#" + testMethod;
            }
        } else {
            rejectRunOnly(parsed, "test-class", "test-method", "jdk-home",
                    "trace-test", "instrumented", "target-classes",
                    "conf-defaults-class", "graphchecker-lib");
        }

        List<Path> instrumented = paths(parsed, "instrumented");
        List<Path> targetClasses = paths(parsed, "target-classes");
        List<Path> graphCheckerLibs = paths(parsed, "graphchecker-lib");
        Map<String, String> conf = parseConf(parsed.getOptionValues("conf"));
        List<String> confDefaultsClasses =
                names(parsed, "conf-defaults-class");

        String maven = optional(parsed, "maven");
        if (maven == null) {
            maven = "mvn";
        }
        String protoc = optional(parsed, "protoc");
        if (protoc == null && environmentProtoc != null
                && !environmentProtoc.trim().isEmpty()) {
            protoc = environmentProtoc.trim();
        }

        String traceDirValue = optional(parsed, "trace-dir");
        Path traceDir = traceDirValue == null
                ? outputDir.resolve("runtime") : absolute(traceDirValue);

        return new SourceTestLauncherOptions(command, hadoopHome, outputDir,
                exceptionTargetId, testClass, testMethod, traceTest, jdkHome,
                instrumented, targetClasses, graphCheckerLibs, conf,
                confDefaultsClasses, maven, protoc, traceDir);
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
                throw new LauncherException(LauncherDiagnostic.USAGE,
                        "--" + name + " expects a class name");
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

    public static void printUsage(PrintWriter writer) {
        HelpFormatter formatter = new HelpFormatter();
        formatter.printHelp(writer, 80,
                "SourceTestLauncher build|run [OPTIONS]",
                "Runs one Hadoop source test under the custom concolic JDK.",
                options(), 2, 2,
                "build validates the checkout, compiles it and writes "
                        + HadoopSourceBuild.CLASSPATH_FILE_NAME
                        + " into --output-dir; run executes the workload once "
                        + "and captures its target outcome.");
        writer.flush();
    }

    private static Command parseCommand(String value)
            throws LauncherException {
        String normalized = value == null
                ? "" : value.trim().toLowerCase(Locale.ROOT);
        if ("build".equals(normalized)) {
            return Command.BUILD;
        }
        if ("run".equals(normalized)) {
            return Command.RUN;
        }
        throw new LauncherException(LauncherDiagnostic.USAGE,
                "unknown command: " + value);
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
                throw new LauncherException(LauncherDiagnostic.USAGE,
                        "--conf expects key=value, got: " + value);
            }
            String key = value.substring(0, separator).trim();
            if (key.isEmpty()) {
                throw new LauncherException(LauncherDiagnostic.USAGE,
                        "--conf expects a non-blank key, got: " + value);
            }
            if (conf.put(key, value.substring(separator + 1)) != null) {
                throw new LauncherException(LauncherDiagnostic.USAGE,
                        "--conf sets " + key + " more than once");
            }
        }
        return conf;
    }

    private static void rejectRunOnly(CommandLine parsed, String... names)
            throws LauncherException {
        for (String name : names) {
            if (parsed.hasOption(name)) {
                throw new LauncherException(LauncherDiagnostic.USAGE,
                        "--" + name + " applies to the run command only");
            }
        }
    }

    private static String required(CommandLine parsed, String name)
            throws LauncherException {
        String value = optional(parsed, name);
        if (value == null) {
            throw new LauncherException(LauncherDiagnostic.USAGE,
                    "--" + name + " is required");
        }
        return value;
    }

    private static String optional(CommandLine parsed, String name) {
        String value = parsed.getOptionValue(name);
        if (value == null || value.trim().isEmpty()) {
            return null;
        }
        return value.trim();
    }

    private static Path requiredPath(CommandLine parsed, String name)
            throws LauncherException {
        return absolute(required(parsed, name));
    }

    private static Path absolute(String value) {
        return Paths.get(value).toAbsolutePath().normalize();
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
        options.addOption(one("trace-test", "name",
                "Logical workload name; defaults to <class>#<method> (run)"));
        options.addOption(one("jdk-home", "dir",
                "Custom concolic JDK image (run)"));
        options.addOption(Option.builder().longOpt("instrumented")
                .hasArgs().argName("dir|jar")
                .desc("Instrumented classes, prepended to the workload "
                        + "classpath; repeatable (run)").build());
        options.addOption(Option.builder().longOpt("target-classes")
                .hasArgs().argName("dir|jar")
                .desc("Where to look for @CausynthExceptionTarget; defaults "
                        + "to the workload's own class outputs; "
                        + "repeatable (run)").build());
        options.addOption(Option.builder().longOpt("graphchecker-lib")
                .hasArgs().argName("dir|jar")
                .desc("Library GraphChecker's runtime needs at a version the "
                        + "workload does not provide; prepended ahead of the "
                        + "workload's own dependencies; repeatable (run)")
                .build());
        options.addOption(Option.builder().longOpt("conf")
                .hasArgs().argName("key=value")
                .desc("Hadoop Configuration override the launcher owns; "
                        + "repeatable").build());
        options.addOption(Option.builder().longOpt("conf-defaults-class")
                .hasArgs().argName("fqcn")
                .desc("Class whose static initializer registers the "
                        + "workload's own default resources; initialized "
                        + "before the launcher registers its overrides so "
                        + "they are not overridden by a *-default.xml; "
                        + "repeatable (run)").build());
        options.addOption(one("maven", "path",
                "Maven executable; defaults to mvn (build)"));
        options.addOption(one("protoc", "path",
                "protoc executable; defaults to $"
                        + PROTOC_ENVIRONMENT_VARIABLE + " (build)"));
        options.addOption(one("trace-dir", "dir",
                "Runtime trace directory; defaults to <output-dir>/runtime"));
        return options;
    }

    private static Option one(String name, String argument,
                              String description) {
        return Option.builder().longOpt(name).hasArg().argName(argument)
                .desc(description).build();
    }
}
