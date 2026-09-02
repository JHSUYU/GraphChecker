package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import soot.Scene;
import soot.SootMethod;
import soot.options.Options;

import java.io.File;
import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * The seed slice must recover its writers, its backed-collection mutations and
 * its callers from compiled bytecode, not only from a Scene built in memory.
 *
 * <p>This pins the rows the writer/caller index publishes for one demanded
 * field and one demanded callee.  Those rows are what a future narrowing of
 * the index - README {@code PERF-1}'s demanded-field/callee reverse lookup -
 * would have to reproduce exactly: a missing writer or caller silently
 * shortens the failure slice instead of failing.</p>
 */
public class CompiledBytecodeSliceTest {
    private static final String FIXTURES =
            "edu.uva.liftlab.graphchecker.causynth."
                    + "CompiledBytecodeSliceFixtures";
    private static final String STATE = FIXTURES + "$State";
    private static final String WRITER = FIXTURES + "$Writer";
    private static final String CONSUMER = FIXTURES + "$Consumer";
    private static final String CALLER = FIXTURES + "$Caller";
    private static final String FAILURE = FIXTURES + "$Failure";
    private static final List<String> FIXTURE_CLASSES = Arrays.asList(
            STATE, WRITER, CONSUMER, CALLER, FAILURE);

    private Path processDir;

    @Before
    public void resetBefore() {
        soot.G.reset();
        System.clearProperty(WireFlowCatalog.PROPERTY);
        System.clearProperty("causynth.trace.test");
    }

    @After
    public void resetAfter() throws IOException {
        System.clearProperty(WireFlowCatalog.PROPERTY);
        System.clearProperty("causynth.trace.test");
        soot.G.reset();
        if (processDir != null) {
            deleteRecursively(processDir);
            processDir = null;
        }
    }

    @Test
    public void writersMutatorsAndCallersResolveFromClassFiles()
            throws Exception {
        processDir = copyFixturesToProcessDirectory();
        loadScene(processDir);

        StaticProgram program = analyzeConsumer();

        assertTrue(program.traceMethods.contains(
                methodSignature(WRITER, "setValues")));
        assertTrue(program.traceMethods.contains(
                methodSignature(WRITER, "clearValues")));
        assertTrue(program.traceMethods.contains(
                methodSignature(CALLER, "callConsume")));
        String values = Scene.v().getSootClass(STATE)
                .getFieldByName("values").getSignature();
        assertTrue(hasEdgeInto(program, "field_write", values));
        assertTrue(hasEdgeInto(program, "field_mutation", values));
        assertTrue(program.edges.stream().anyMatch(edge ->
                "caller_argument".equals(edge.get("kind"))
                        && String.valueOf(edge.get("toCell")).startsWith(
                        methodSignature(CONSUMER, "consume") + ".param0:")));
    }

    private StaticProgram analyzeConsumer() throws IOException {
        String consume = methodSignature(CONSUMER, "consume");
        ExceptionTargetSite site = new ExceptionTargetSite(
                "compiled-bytecode-slice", CONSUMER, "consume",
                "(L" + STATE.replace('.', '/') + ";)V", consume, FAILURE, 0);
        return new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, site.id, site,
                        "TEST")).analyze();
    }

    private static void loadScene(Path processDir) {
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_prepend_classpath(true);
        // The analyzed output tree goes ahead of the test classpath, exactly
        // as GraphCheckerMain prepends its process directories.
        Options.v().set_soot_classpath(processDir + File.pathSeparator
                + System.getProperty("java.class.path"));
        Options.v().set_process_dir(new ArrayList<>(
                Collections.singletonList(processDir.toString())));
        Scene.v().loadNecessaryClasses();
    }

    /**
     * Copies only the fixtures, so the process directory holds the analyzed
     * classes and nothing else.
     */
    private static Path copyFixturesToProcessDirectory() throws Exception {
        Path compiled = new File(CompiledBytecodeSliceFixtures.class
                .getProtectionDomain().getCodeSource().getLocation().toURI())
                .toPath();
        Assume.assumeTrue("compiled test classes are not a directory",
                Files.isDirectory(compiled));
        String packageName = FIXTURES.substring(0, FIXTURES.lastIndexOf('.'));
        Path root = Files.createTempDirectory("graphchecker-slice");
        Path packageDir = root.resolve(
                packageName.replace('.', File.separatorChar));
        Files.createDirectories(packageDir);
        for (String name : FIXTURE_CLASSES) {
            String simple = name.substring(name.lastIndexOf('.') + 1)
                    + ".class";
            Files.copy(compiled.resolve(
                    packageName.replace('.', File.separatorChar))
                    .resolve(simple), packageDir.resolve(simple));
        }
        return root;
    }

    private static String methodSignature(String className, String name) {
        SootMethod method = Scene.v().getSootClass(className)
                .getMethodByName(name);
        assertNotNull(method);
        return method.getSignature();
    }

    private static boolean hasEdgeInto(StaticProgram program, String kind,
                                       String toCell) {
        return program.edges.stream().anyMatch(edge ->
                kind.equals(edge.get("kind"))
                        && toCell.equals(edge.get("toCell")));
    }

    private static void deleteRecursively(Path root) throws IOException {
        if (!Files.exists(root)) {
            return;
        }
        Files.walkFileTree(root, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file,
                                             BasicFileAttributes attributes)
                    throws IOException {
                Files.delete(file);
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult postVisitDirectory(Path directory,
                                                      IOException failure)
                    throws IOException {
                Files.delete(directory);
                return FileVisitResult.CONTINUE;
            }
        });
    }
}
