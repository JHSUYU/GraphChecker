package edu.uva.liftlab.graphchecker.launcher;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The system properties Surefire would have set, supplied by the launcher.
 *
 * <p>The workload runs the JUnit method directly rather than through
 * Surefire, so nothing else defines where a MiniDFSCluster puts its storage
 * directories or logs. Without {@code test.build.data} the cluster falls back
 * to a relative {@code build/test/data} under whatever directory the launcher
 * happened to start in, and two runs quietly share one NameNode image.</p>
 *
 * <p>The scratch tree is rooted in the launcher's own output directory
 * instead of the checkout's {@code target/}, so a run is self-contained and a
 * Maven build cannot delete a workload's evidence out from under it.</p>
 *
 * <p>{@code java.security.egd} matters more than it looks: MiniDFSCluster
 * seeds several {@code SecureRandom} instances during startup, and on a
 * machine with little entropy the blocking device turns an interpreted run
 * into a hang that resembles a deadlock in the workload.</p>
 */
public final class HadoopTestProperties {

    /** Scratch subdirectory of the launcher output directory. */
    public static final String SCRATCH_DIRECTORY = "workload";

    private HadoopTestProperties() {
    }

    /** The scratch root a run uses. */
    public static Path scratchRoot(Path outputDir) {
        return outputDir.resolve(SCRATCH_DIRECTORY);
    }

    /** Property values for a run rooted at {@code outputDir}. */
    public static Map<String, String> of(Path outputDir) {
        Path scratch = scratchRoot(outputDir);
        Path testDir = scratch.resolve("test-dir");
        Map<String, String> properties = new LinkedHashMap<>();
        properties.put("test.build.dir", testDir.toString());
        properties.put("test.build.data", testDir.toString());
        properties.put("hadoop.log.dir", scratch.resolve("log").toString());
        properties.put("hadoop.tmp.dir", scratch.resolve("tmp").toString());
        properties.put("java.io.tmpdir", scratch.resolve("tmp").toString());
        properties.put("java.net.preferIPv4Stack", "true");
        properties.put("java.security.egd", "file:///dev/urandom");
        return Collections.unmodifiableMap(properties);
    }

    /** Creates the scratch directories the properties above name. */
    public static void createDirectories(Path outputDir)
            throws LauncherException {
        Path scratch = scratchRoot(outputDir);
        try {
            Files.createDirectories(scratch.resolve("test-dir"));
            Files.createDirectories(scratch.resolve("log"));
            Files.createDirectories(scratch.resolve("tmp"));
        } catch (IOException failure) {
            throw new LauncherException(LauncherDiagnostic.IO_FAILED,
                    "cannot create workload scratch under " + scratch,
                    failure);
        }
    }
}
