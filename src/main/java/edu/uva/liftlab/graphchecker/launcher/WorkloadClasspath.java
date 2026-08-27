package edu.uva.liftlab.graphchecker.launcher;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.CodeSource;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Assembles the workload JVM classpath from an existing Hadoop build.  Order
 * is the whole point, so it is fixed here: instrumented outputs first so a
 * rewritten class shadows its original, then the configuration directory, the
 * named GraphChecker libraries, the Hadoop module outputs (tests before
 * main), the module's test-scope dependencies, and GraphChecker last.
 *
 * <p>GraphChecker's last position is load-bearing.  It ships as a
 * jar-with-dependencies, so putting it first also puts Guava 31, Protobuf 3
 * and Gson 2.10 ahead of the versions Hadoop pins and the workload dies
 * inside Hadoop - {@code NoSuchMethodError: Futures.addCallback}, because
 * Hadoop 3.0.0-alpha4 compiles against Guava 11.  Tracing needs GraphChecker
 * <em>present</em>, not winning a version conflict.  Where the recorder does
 * require a newer library the caller names it and it is prepended: Hadoop's
 * Gson 2.2.4 turns the first traced RPC into a {@code NoSuchMethodError} and
 * every later one into silence.</p>
 */
public final class WorkloadClasspath {

    /** Hadoop module outputs, in classpath order relative to the checkout. */
    public static final List<String> MODULE_OUTPUTS =
            Collections.unmodifiableList(Arrays.asList(
                    "hadoop-hdfs-project/hadoop-hdfs/target/test-classes",
                    "hadoop-hdfs-project/hadoop-hdfs/target/classes",
                    "hadoop-hdfs-project/hadoop-hdfs-client/target/classes",
                    "hadoop-common-project/hadoop-common/target/test-classes",
                    "hadoop-common-project/hadoop-common/target/classes"));

    private WorkloadClasspath() {
    }

    /**
     * @param confDir generated configuration directory, or null
     * @param graphCheckerLibs libraries the recorder needs at a version the
     *                         workload does not provide
     * @param graphCheckerCode GraphChecker's own classes directory or jar
     */
    public static List<String> assemble(Path hadoopHome,
                                        List<Path> instrumented,
                                        Path confDir,
                                        List<Path> graphCheckerLibs,
                                        Path graphCheckerCode,
                                        Path classpathFile)
            throws LauncherException {
        Set<String> entries = new LinkedHashSet<>();
        if (instrumented != null) {
            for (Path entry : instrumented) {
                if (!Files.exists(entry)) {
                    throw new LauncherException(
                            LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                            "instrumented classpath entry does not exist: "
                                    + entry);
                }
                entries.add(entry.toString());
            }
        }
        if (confDir != null) {
            entries.add(confDir.toString());
        }
        if (graphCheckerLibs != null) {
            for (Path entry : graphCheckerLibs) {
                if (!Files.exists(entry)) {
                    throw new LauncherException(
                            LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                            "GraphChecker library does not exist: " + entry);
                }
                entries.add(entry.toString());
            }
        }
        if (graphCheckerCode == null || !Files.exists(graphCheckerCode)) {
            throw new LauncherException(
                    LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                    "GraphChecker classes do not exist: " + graphCheckerCode);
        }

        HadoopSourceBuild.requireHadoopHome(hadoopHome);
        for (String output : MODULE_OUTPUTS) {
            Path directory = hadoopHome.resolve(output);
            if (!Files.isDirectory(directory)) {
                throw new LauncherException(
                        LauncherDiagnostic.MODULE_OUTPUT_MISSING,
                        "no compiled output at " + directory
                                + "; run the launcher's build command first");
            }
            entries.add(directory.toString());
        }

        if (classpathFile == null || !Files.isRegularFile(classpathFile)) {
            throw new LauncherException(
                    LauncherDiagnostic.TEST_CLASSPATH_MISSING,
                    "no test-scope classpath file at " + classpathFile
                            + "; run the launcher's build command first");
        }
        String text;
        try {
            text = new String(Files.readAllBytes(classpathFile),
                    StandardCharsets.UTF_8);
        } catch (IOException failure) {
            throw new LauncherException(
                    LauncherDiagnostic.TEST_CLASSPATH_MISSING,
                    "cannot read " + classpathFile, failure);
        }
        int dependencies = 0;
        for (String line : text.split("\\R")) {
            for (String entry : line.split(File.pathSeparator)) {
                String trimmed = entry.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                if (!Files.exists(Paths.get(trimmed))) {
                    throw new LauncherException(
                            LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                            classpathFile + " names a missing entry: "
                                    + trimmed);
                }
                entries.add(trimmed);
                dependencies++;
            }
        }
        if (dependencies == 0) {
            throw new LauncherException(
                    LauncherDiagnostic.TEST_CLASSPATH_MISSING,
                    classpathFile + " is empty");
        }
        entries.add(graphCheckerCode.toString());
        return Collections.unmodifiableList(new ArrayList<>(entries));
    }

    /** Locates the classes or jar this launcher itself was loaded from. */
    public static Path graphCheckerCodeSource() throws LauncherException {
        CodeSource source = WorkloadClasspath.class.getProtectionDomain()
                .getCodeSource();
        URL location = source == null ? null : source.getLocation();
        if (location == null) {
            throw new LauncherException(
                    LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                    "cannot locate GraphChecker's own code source");
        }
        try {
            return Paths.get(location.toURI()).toAbsolutePath().normalize();
        } catch (URISyntaxException | IllegalArgumentException failure) {
            throw new LauncherException(
                    LauncherDiagnostic.CLASSPATH_ENTRY_MISSING,
                    "unusable GraphChecker code source: " + location, failure);
        }
    }
}
