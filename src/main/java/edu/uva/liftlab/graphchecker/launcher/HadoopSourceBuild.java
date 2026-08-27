package edu.uva.liftlab.graphchecker.launcher;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Builds the Hadoop checkout and emits its test-scope classpath.  The only
 * launcher step needing a Hadoop toolchain - 3.0.0-alpha4 generates its
 * Protobuf sources with a pinned {@code protoc} - so it is separated: a
 * missing one is a named {@link LauncherDiagnostic} before Maven starts rather
 * than a stack trace mid-run, and the rest of the launcher stays testable
 * without Hadoop.  {@link #mavenCommands} is pure.
 */
public final class HadoopSourceBuild {

    /**
     * The file the build writes into the launcher output directory and
     * {@link WorkloadClasspath} reads back.
     */
    public static final String CLASSPATH_FILE_NAME =
            "hadoop-test-classpath.txt";

    /**
     * Modules the workload needs compiled, in reactor dependency order.
     * {@code hadoop-hdfs} is last on purpose: the classpath command below
     * relies on it being the final module of the {@code -am} reactor.
     */
    public static final List<String> MODULES =
            Collections.unmodifiableList(Arrays.asList(
                    "hadoop-common-project/hadoop-common",
                    "hadoop-hdfs-project/hadoop-hdfs-client",
                    "hadoop-hdfs-project/hadoop-hdfs"));

    /** Module whose test-scope classpath the workload runs against. */
    public static final String WORKLOAD_MODULE =
            "hadoop-hdfs-project/hadoop-hdfs";

    private static final String VERSION_POM = "hadoop-project/pom.xml";

    private static final Pattern PROTOBUF_VERSION = Pattern.compile(
            "<protobuf\\.version>\\s*([^<\\s]+)\\s*</protobuf\\.version>");

    private static final Pattern PROTOC_VERSION = Pattern.compile(
            "^libprotoc\\s+(\\S+)\\s*$");

    private HadoopSourceBuild() {
    }

    public static void requireHadoopHome(Path hadoopHome)
            throws LauncherException {
        if (hadoopHome == null || !Files.isDirectory(hadoopHome)) {
            throw new LauncherException(LauncherDiagnostic.HADOOP_HOME_MISSING,
                    "not a directory: " + hadoopHome);
        }
        for (String module : MODULES) {
            Path pom = hadoopHome.resolve(module).resolve("pom.xml");
            if (!Files.isRegularFile(pom)) {
                throw new LauncherException(
                        LauncherDiagnostic.HADOOP_MODULE_MISSING,
                        "missing " + pom);
            }
        }
    }

    /**
     * The two Maven invocations the build issues: the first compiles the
     * reactor {@code hadoop-hdfs} needs including test sources, the second
     * asks that reactor for the module's test-scope classpath.  Because
     * {@code hadoop-hdfs} is the reactor's last module its classpath is the
     * one left in {@code outputFile}.  Both are offline: the machine has no
     * network, and a silent remote fetch would not be reproducible.
     */
    public static List<List<String>> mavenCommands(String maven, Path protoc,
                                                   Path outputFile) {
        List<String> compile = new ArrayList<>(Arrays.asList(
                maven, "-o", "-B",
                "-pl", String.join(",", MODULES),
                "-am",
                "-DskipTests",
                "-Dmaven.javadoc.skip=true",
                "-Dprotoc.path=" + protoc,
                "test-compile"));
        List<String> classpath = new ArrayList<>(Arrays.asList(
                maven, "-o", "-B",
                "-pl", WORKLOAD_MODULE,
                "-am",
                "-Dprotoc.path=" + protoc,
                "-Dmdep.includeScope=test",
                "-Dmdep.outputFile=" + outputFile,
                "dependency:build-classpath"));
        List<List<String>> commands = new ArrayList<>();
        commands.add(Collections.unmodifiableList(compile));
        commands.add(Collections.unmodifiableList(classpath));
        return Collections.unmodifiableList(commands);
    }

    /**
     * Validates every prerequisite, then compiles and writes the classpath
     * file.  The pinned protoc version is read from the checkout rather than
     * hardcoded, because a different Hadoop revision pins a different one and
     * a constant would silently accept the wrong toolchain.
     *
     * @param protoc the configured protoc path, or null to search {@code PATH}
     */
    public static Path build(Path hadoopHome, String maven, String protoc,
                             Path outputDir) throws LauncherException {
        requireHadoopHome(hadoopHome);
        resolveExecutable(maven, LauncherDiagnostic.MAVEN_MISSING,
                "Maven executable");
        Path resolvedProtoc = resolveExecutable(protoc == null
                        ? "protoc" : protoc,
                LauncherDiagnostic.PROTOC_MISSING, "protoc executable");
        Path pom = hadoopHome.resolve(VERSION_POM);
        String pomText;
        try {
            pomText = new String(Files.readAllBytes(pom),
                    StandardCharsets.UTF_8);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.HADOOP_HOME_MISSING,
                    "cannot read " + pom, failure);
        }
        Matcher pinned = PROTOBUF_VERSION.matcher(pomText);
        if (!pinned.find()) {
            throw new LauncherException(LauncherDiagnostic.HADOOP_HOME_MISSING,
                    pom + " declares no <protobuf.version>");
        }
        String actual = protocVersion(resolvedProtoc);
        if (!pinned.group(1).equals(actual)) {
            throw new LauncherException(
                    LauncherDiagnostic.PROTOC_VERSION_MISMATCH,
                    resolvedProtoc + " reports " + actual + ", but " + hadoopHome
                            + " pins protobuf.version " + pinned.group(1));
        }

        Path classpathFile = outputDir.resolve(CLASSPATH_FILE_NAME);
        try {
            Files.createDirectories(outputDir);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot create " + outputDir, failure);
        }
        for (List<String> command
                : mavenCommands(maven, resolvedProtoc, classpathFile)) {
            int status = execute(command, hadoopHome);
            if (status != 0) {
                throw new LauncherException(
                        LauncherDiagnostic.HADOOP_BUILD_FAILED,
                        "exit " + status + " from " + String.join(" ",
                                command));
            }
        }
        if (!Files.isRegularFile(classpathFile)) {
            throw new LauncherException(
                    LauncherDiagnostic.TEST_CLASSPATH_MISSING,
                    "the build wrote no " + classpathFile);
        }
        return classpathFile;
    }

    private static int execute(List<String> command, Path directory)
            throws LauncherException {
        try {
            return new ProcessBuilder(command)
                    .directory(directory.toFile())
                    .inheritIO()
                    .start()
                    .waitFor();
        } catch (IOException failure) {
            throw new LauncherException(
                    LauncherDiagnostic.HADOOP_BUILD_FAILED,
                    "cannot run " + String.join(" ", command), failure);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new LauncherException(
                    LauncherDiagnostic.HADOOP_BUILD_FAILED,
                    "interrupted while running " + String.join(" ", command),
                    interrupted);
        }
    }

    private static String protocVersion(Path protoc)
            throws LauncherException {
        List<String> command = Arrays.asList(protoc.toString(), "--version");
        try {
            Process process = new ProcessBuilder(command)
                    .redirectErrorStream(true).start();
            String first;
            try (BufferedReader reader = new BufferedReader(
                    new InputStreamReader(process.getInputStream(),
                            StandardCharsets.UTF_8))) {
                first = reader.readLine();
            }
            int status = process.waitFor();
            if (status != 0 || first == null) {
                throw new LauncherException(
                        LauncherDiagnostic.PROTOC_VERSION_MISMATCH,
                        protoc + " --version exited " + status);
            }
            Matcher matcher = PROTOC_VERSION.matcher(first.trim());
            if (!matcher.matches()) {
                throw new LauncherException(
                        LauncherDiagnostic.PROTOC_VERSION_MISMATCH,
                        protoc + " --version printed: " + first.trim());
            }
            return matcher.group(1);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.PROTOC_MISSING,
                    "cannot run " + protoc + " --version", failure);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new LauncherException(
                    LauncherDiagnostic.PROTOC_MISSING,
                    "interrupted running " + protoc + " --version",
                    interrupted);
        }
    }

    /** Resolves a command that is either a path or a bare name on PATH. */
    private static Path resolveExecutable(String command,
                                          LauncherDiagnostic absent,
                                          String description)
            throws LauncherException {
        if (command == null || command.trim().isEmpty()) {
            throw new LauncherException(absent, description + " is not set");
        }
        String value = command.trim();
        if (value.indexOf('/') >= 0) {
            Path path = Paths.get(value).toAbsolutePath().normalize();
            if (!Files.isExecutable(path)) {
                throw new LauncherException(absent,
                        description + " is not executable: " + path);
            }
            return path;
        }
        String search = System.getenv("PATH");
        if (search != null) {
            for (String element : search.split(java.io.File.pathSeparator)) {
                if (element.isEmpty()) {
                    continue;
                }
                Path candidate = Paths.get(element).resolve(value);
                if (Files.isExecutable(candidate)) {
                    return candidate.toAbsolutePath().normalize();
                }
            }
        }
        throw new LauncherException(absent,
                description + " " + value + " is not on PATH");
    }
}
