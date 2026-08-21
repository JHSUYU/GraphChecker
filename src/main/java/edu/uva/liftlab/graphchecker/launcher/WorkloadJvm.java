package edu.uva.liftlab.graphchecker.launcher;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.TreeMap;

/**
 * Builds and runs the child JVM that executes the workload.
 *
 * <p>The workload runs in the custom concolic JDK, interpreted. Its location
 * is an input, never a constant: the image is rebuilt out of band, may live
 * anywhere, and a launcher that hardcoded one path would silently run the
 * stock JVM the moment that assumption broke - producing a green run with no
 * symbolic state at all.</p>
 *
 * <p>Command assembly is separated from execution so the exact invocation can
 * be asserted without a JDK image present.</p>
 */
public final class WorkloadJvm {

    /** Prefix of the properties the launcher forwards from its own JVM. */
    public static final String INHERITED_PROPERTY_PREFIX = "causynth.";

    /** Interpreted execution; the concolic VM has no compiled path. */
    public static final List<String> INTERPRETED_JVM_OPTIONS =
            Collections.singletonList("-Xint");

    /**
     * What the concolic image calls itself in its own {@code -version} banner.
     *
     * <p>The engine is built from the {@code zero} OpenJDK configuration, so
     * the image reports {@code OpenJDK 64-Bit Zero VM ... interpreted mode}
     * where a stock JDK reports {@code Server VM ... mixed mode}. Asking the
     * JVM is the honest test: the image's location is an input and may be any
     * path, a name check would pass for a symlink to the stock JDK, and the
     * banner is the VM's own statement about whether it has a compiled path
     * at all - which is the only reason {@code -Xint} exists here.</p>
     */
    public static final String CONCOLIC_VM_MARKER = "Zero VM";

    /** Written into the launcher output directory by {@link #run}. */
    public static final String OUTPUT_FILE_NAME = "workload-output.log";

    private WorkloadJvm() {
    }

    /**
     * The JVM options the launcher owns for a workload on {@code jdkHome}.
     *
     * <p>{@code -Xint} belongs to the concolic image and to nothing else. A
     * tracing pass executes rewritten bytecode on a stock JVM and needs no
     * symbolic interpreter; forcing that JVM to interpret slows the workload
     * by more than an order of magnitude, and a distributed workload whose
     * own timeouts are wall-clock does not merely take longer under it - it
     * changes outcome. Applying the flag unconditionally therefore turned a
     * 112-second balancer test into a 30-minute run whose DataNodes were
     * declared dead faster than they could re-register.</p>
     */
    public static List<String> jvmOptions(Path jdkHome)
            throws LauncherException {
        return isConcolicImage(jdkHome) ? INTERPRETED_JVM_OPTIONS
                : Collections.<String>emptyList();
    }

    /**
     * Whether {@code jdkHome} is the concolic image, asked of the image.
     *
     * <p>A JDK whose {@code -version} cannot be read is a prerequisite
     * failure, not a default: guessing either way is silent, and the two
     * mistakes are a workload with no symbolic path and a tracing pass that
     * takes half an hour.</p>
     */
    public static boolean isConcolicImage(Path jdkHome)
            throws LauncherException {
        Path java = javaBinary(jdkHome);
        ProcessBuilder builder = new ProcessBuilder(java.toString(),
                "-version").redirectErrorStream(true);
        try {
            Process process = builder.start();
            String banner = read(process.getInputStream());
            int status = process.waitFor();
            if (status != 0) {
                throw new LauncherException(LauncherDiagnostic.JDK_MISSING,
                        java + " -version exited " + status + ": " + banner);
            }
            return banner.contains(CONCOLIC_VM_MARKER);
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.JDK_MISSING,
                    "cannot run " + java + " -version", failure);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new LauncherException(LauncherDiagnostic.JDK_MISSING,
                    "interrupted while probing " + java, interrupted);
        }
    }

    private static String read(InputStream input) throws IOException {
        ByteArrayOutputStream collected = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = input.read(buffer)) >= 0) {
            collected.write(buffer, 0, count);
        }
        input.close();
        return new String(collected.toByteArray(), StandardCharsets.UTF_8);
    }

    /** Locates {@code bin/java} inside a JDK image. */
    public static Path javaBinary(Path jdkHome) throws LauncherException {
        if (jdkHome == null || !Files.isDirectory(jdkHome)) {
            throw new LauncherException(LauncherDiagnostic.JDK_MISSING,
                    "not a directory: " + jdkHome);
        }
        Path java = jdkHome.resolve("bin").resolve("java");
        if (!Files.isExecutable(java)) {
            throw new LauncherException(LauncherDiagnostic.JDK_MISSING,
                    "not executable: " + java);
        }
        return java;
    }

    /**
     * The JDK image's native library directory, or null when it has none.
     */
    public static Path nativeLibraryDirectory(Path jdkHome) {
        for (String candidate
                : Arrays.asList("jre/lib/amd64", "lib/amd64", "lib/server")) {
            Path directory = jdkHome.resolve(candidate);
            if (Files.isDirectory(directory)) {
                return directory;
            }
        }
        return null;
    }

    /**
     * Merges the properties the launcher owns with the {@code causynth.*}
     * properties set on the launcher's own JVM.
     *
     * <p>Forwarding the rest is what keeps the input list short: knobs such as
     * the trace event cap or a concolic task selection reach the workload
     * without the launcher growing a flag - and without a configuration
     * grammar - while the handful of properties the launcher must control
     * cannot be overridden from outside.</p>
     */
    public static Map<String, String> systemProperties(
            Map<String, String> owned, Properties inherited) {
        Map<String, String> merged = new LinkedHashMap<>(owned);
        if (inherited != null) {
            Map<String, String> sorted = new TreeMap<>();
            for (String name : inherited.stringPropertyNames()) {
                if (name.startsWith(INHERITED_PROPERTY_PREFIX)
                        && !owned.containsKey(name)) {
                    sorted.put(name, inherited.getProperty(name));
                }
            }
            merged.putAll(sorted);
        }
        return Collections.unmodifiableMap(merged);
    }

    /** The complete child command line. */
    public static List<String> command(Path javaBinary,
                                       List<String> jvmOptions,
                                       Map<String, String> systemProperties,
                                       List<String> classpath,
                                       String mainClass,
                                       List<String> mainArguments) {
        List<String> command = new ArrayList<>();
        command.add(javaBinary.toString());
        command.addAll(jvmOptions);
        for (Map.Entry<String, String> property : systemProperties.entrySet()) {
            command.add("-D" + property.getKey() + "=" + property.getValue());
        }
        command.add("-cp");
        command.add(String.join(File.pathSeparator, classpath));
        command.add(mainClass);
        command.addAll(mainArguments);
        return Collections.unmodifiableList(command);
    }

    /**
     * Runs the child to completion, copying its output to {@code outputLog},
     * and returns its exit status.
     *
     * <p>A non-zero status is returned, not thrown: the JUnit verdict is an
     * observation the outcome record carries, and refusing to look at the
     * trace because a test assertion failed would throw away the run.</p>
     *
     * <p>The output is captured rather than inherited because the exit status
     * alone is a dead end. {@code junitExitCode: 1} in the outcome record says
     * only that something failed; the exception that failed it lives in the
     * child's stderr, and with {@code inheritIO} that text belonged to
     * whatever shell happened to be watching. Both streams are merged so the
     * failure keeps its position relative to the workload's own log, and the
     * copy is a tee so an interactive run still shows progress.</p>
     */
    public static int run(List<String> command, Path workingDirectory,
                          Path nativeLibraryDirectory, Path outputLog)
            throws LauncherException {
        ProcessBuilder builder = new ProcessBuilder(command)
                .redirectErrorStream(true);
        builder.redirectInput(ProcessBuilder.Redirect.INHERIT);
        if (workingDirectory != null) {
            builder.directory(workingDirectory.toFile());
        }
        if (nativeLibraryDirectory != null) {
            String existing = builder.environment().get("LD_LIBRARY_PATH");
            builder.environment().put("LD_LIBRARY_PATH",
                    existing == null || existing.isEmpty()
                            ? nativeLibraryDirectory.toString()
                            : nativeLibraryDirectory + File.pathSeparator
                            + existing);
        }
        try {
            if (outputLog.getParent() != null) {
                Files.createDirectories(outputLog.getParent());
            }
            Process process = builder.start();
            try (InputStream output = process.getInputStream();
                 OutputStream log = Files.newOutputStream(outputLog)) {
                byte[] buffer = new byte[8192];
                int count;
                while ((count = output.read(buffer)) >= 0) {
                    log.write(buffer, 0, count);
                    System.out.write(buffer, 0, count);
                    System.out.flush();
                }
            }
            return process.waitFor();
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.WORKLOAD_JVM_FAILED,
                    "cannot start " + command.get(0), failure);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new LauncherException(LauncherDiagnostic.WORKLOAD_JVM_FAILED,
                    "interrupted while running the workload", interrupted);
        }
    }
}
