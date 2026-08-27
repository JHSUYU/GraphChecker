package edu.uva.liftlab.graphchecker.launcher;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class WorkloadClasspathTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private Path hadoop;
    private Path graphChecker;
    private Path gsonLib;
    private Path classpathFile;
    private Path dependency;

    @Before
    public void setUp() throws Exception {
        hadoop = folder.newFolder("hadoop").toPath();
        for (String module : HadoopSourceBuild.MODULES) {
            Path pom = hadoop.resolve(module).resolve("pom.xml");
            Files.createDirectories(pom.getParent());
            Files.write(pom, "<project/>".getBytes(StandardCharsets.UTF_8));
        }
        for (String output : WorkloadClasspath.MODULE_OUTPUTS) {
            Files.createDirectories(hadoop.resolve(output));
        }
        graphChecker = folder.newFolder("graphchecker-classes").toPath();
        gsonLib = folder.newFile("gson-2.10.1.jar").toPath();
        dependency = folder.newFile("guava.jar").toPath();
        classpathFile = folder.getRoot().toPath()
                .resolve(HadoopSourceBuild.CLASSPATH_FILE_NAME);
        writeClasspath(dependency.toString());
    }

    @Test
    public void instrumentedClassesShadowTheBuildAndGraphCheckerFollowsHadoop()
            throws Exception {
        Path instrumented = folder.newFolder("instrumented").toPath();
        Path conf = folder.newFolder("conf").toPath();

        List<String> classpath = WorkloadClasspath.assemble(hadoop,
                Collections.singletonList(instrumented), conf,
                Collections.singletonList(gsonLib), graphChecker,
                classpathFile);

        assertEquals(instrumented.toString(), classpath.get(0));
        assertEquals(conf.toString(), classpath.get(1));
        // The named library is the one thing that outranks the workload's own
        // dependencies; everything else GraphChecker carries does not.
        assertEquals(gsonLib.toString(), classpath.get(2));
        for (int index = 0; index < WorkloadClasspath.MODULE_OUTPUTS.size();
             index++) {
            assertEquals(hadoop.resolve(
                            WorkloadClasspath.MODULE_OUTPUTS.get(index))
                            .toString(),
                    classpath.get(3 + index));
        }
        assertEquals(dependency.toString(),
                classpath.get(classpath.size() - 2));
        assertTrue("the workload's own test classes must precede the "
                        + "production classes",
                WorkloadClasspath.MODULE_OUTPUTS.get(0).endsWith(
                        "hadoop-hdfs/target/test-classes"));

        List<String> bare = WorkloadClasspath.assemble(hadoop,
                Collections.<Path>emptyList(), null,
                Collections.<Path>emptyList(), graphChecker,
                classpathFile);

        // GraphChecker ships as a jar-with-dependencies: ahead of Hadoop it
        // would replace the Guava and Protobuf versions the workload is
        // compiled against.  Tracing only requires that it be reachable.
        assertEquals(graphChecker.toString(),
                bare.get(bare.size() - 1));
        assertTrue(bare.indexOf(dependency.toString())
                < bare.indexOf(graphChecker.toString()));

        Path protoc = folder.newFile("protoc").toPath();

        List<List<String>> commands = HadoopSourceBuild.mavenCommands(
                "/usr/bin/mvn", protoc, classpathFile);

        assertEquals(2, commands.size());
        for (List<String> command : commands) {
            assertEquals("/usr/bin/mvn", command.get(0));
            assertTrue(command.contains("-o"));
            assertTrue(command.contains("-Dprotoc.path=" + protoc));
            assertTrue(command.contains("-am"));
        }
        assertEquals("hadoop-hdfs is expected to be the last reactor module",
                HadoopSourceBuild.WORKLOAD_MODULE,
                HadoopSourceBuild.MODULES.get(
                        HadoopSourceBuild.MODULES.size() - 1));

        // Naming it hdfs-site.xml would hide the checkout's own test
        // hdfs-site.xml, which is what allows the balancer test's 100-byte
        // block size.
        assertFalse(SourceTestLauncher.CONFIG_RESOURCE_NAME.equals(
                "hdfs-site.xml"));
        assertFalse(SourceTestLauncher.CONFIG_RESOURCE_NAME.equals(
                "core-site.xml"));
        assertTrue(SourceTestLauncher.CONFIG_RESOURCE_NAME.endsWith(".xml"));

        // -Xint belongs to the concolic image.  Forcing a stock JVM to
        // interpret does not merely slow a tracing pass down; it moves the
        // workload's own wall-clock deadlines out of reach.
        List<String> stock = WorkloadJvm.command(
                Paths.get("/usr/lib/jvm/java-8/bin/java"),
                WorkloadJvm.jvmOptions(Paths.get(System.getProperty(
                        "java.home"))),
                Collections.singletonMap("causynth.trace.test", "t"),
                bare, "Main", Collections.<String>emptyList());
        assertFalse("a stock JDK must not be forced to interpret",
                stock.contains("-Xint"));
        assertEquals("-Dcausynth.trace.test=t", stock.get(1));
        assertEquals(WorkloadJvm.INTERPRETED_JVM_OPTIONS,
                Collections.singletonList("-Xint"));

    }

    private void writeClasspath(String text) throws IOException {
        Files.write(classpathFile, text.getBytes(StandardCharsets.UTF_8));
    }
}
