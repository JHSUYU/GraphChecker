package edu.uva.liftlab.graphchecker;

import edu.uva.liftlab.graphchecker.causynth.LineageScope;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import edu.uva.liftlab.graphchecker.transformer.GraphCheckerTransformer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.PackManager;
import soot.PhaseOptions;
import soot.Scene;
import soot.SootClass;
import soot.Transform;
import soot.options.Options;
import soot.util.Chain;

import java.io.File;
import java.io.PrintStream;
import java.util.Date;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static soot.SootClass.SIGNATURES;

public class GraphCheckerMain {
    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerMain.class);

    private final GraphCheckerOptions options;
    private final List<String> productionProcessDirs = new ArrayList<>();

    public GraphCheckerMain(GraphCheckerOptions options) {
        this.options = options;
    }

    public void initialize() {
        IndexedSourceLocator.install();
        Transform phase = new Transform(GraphCheckerTransformer.PHASE_NAME,
                new GraphCheckerTransformer(options));
        phase.setDeclaredOptions("enabled");
        phase.setDefaultOptions("enabled:false");
        PackManager.v().getPack(GraphCheckerTransformer.PHASE_PACK).add(phase);
        configureSoot();
        // One whole-program phase, no call graph: the pipeline builds its own.
        PhaseOptions.v().setPhaseOption(
                GraphCheckerTransformer.PHASE_NAME, "enabled:true");
        PhaseOptions.v().setPhaseOption("cg", "off");
        loadClasses();
    }

    public boolean run() {
        Options.v().warnNonexistentPhase();
        try {
            Date start = new Date();
            LOG.info("GraphChecker started on {}", start);
            Scene.v().loadNecessaryClasses();
            orderClassesByName();
            LambdaClassNames.install();
            PackManager.v().runPacks();
            PackManager.v().writeOutput();

            Date finish = new Date();
            long runtime = finish.getTime() - start.getTime();
            LOG.info("GraphChecker finished on {}", finish);
            LOG.info("GraphChecker ran for {} ms", runtime);
            return true;
        } catch (StackOverflowError exception) {
            LOG.error("Soot ran out of stack memory", exception);
            return false;
        } catch (OutOfMemoryError exception) {
            LOG.error("Soot ran out of heap memory", exception);
            return false;
        } catch (RuntimeException exception) {
            LOG.error("Unexpected exception encountered", exception);
            return false;
        }
    }

    private void configureSoot() {
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_prepend_classpath(true);
        List<String> processDirs = expandProcessDirs(options.getInputList());
        List<String> configuredTestDirs = new ArrayList<>();
        splitProcessDirs(processDirs, productionProcessDirs,
                configuredTestDirs);
        Options.v().set_soot_classpath(expandClassPath(
                prependClasspathEntries(processDirs, options.getClassPath())));
        Options.v().set_keep_line_number(true);
        Options.v().set_whole_program(true);
        // Identity must not depend on the host or the run.  Soot runs on one
        // thread, over the classes by name (orderClassesByName); each lambda
        // class is named by what it is (LambdaClassNames, installed once the
        // classes are loaded); jb.sils, which handed a split local's uses to
        // its copies in identity-hash order, takes them in body order
        // (SharedInitializationSplitter); and a body's locals are numbered
        // by type and first definition, not in the order the phases left
        // them (Balancer.runOneIteration's z6..z8 and
        // FileChecksumHelper.checksumBlock's z1, z2 swapped between runs).
        Options.v().set_num_threads(1);
        SharedInitializationSplitter.install();
        PhaseOptions.v().setPhaseOption("jb.lns", "sort-locals:true");
        boolean concolicInstrumentation = ConcolicInstrumentationSelections
                .instrumentationRequested();
        if (!configuredTestDirs.isEmpty()) {
            LOG.info("Static discovery keeps {} test output(s) on the "
                            + "classpath but excludes every test class "
                            + "from application scope; {} production "
                            + "root(s) remain",
                    configuredTestDirs.size(),
                    productionProcessDirs.size());
        }
        // ONE application scope for every pass: PackManager writes only
        // application classes, so a narrower scope drops woven bodies and
        // shifts every index below them (IDENTITY §10).
        Options.v().set_process_dir(productionProcessDirs);
        LOG.info("Soot application scope is the case's {} production "
                        + "root(s){}", productionProcessDirs.size(),
                concolicInstrumentation
                        ? ", campaign instrumentation included" : "");
        if (options.getOutputDir() != null) {
            Options.v().set_output_dir(options.getOutputDir());
        }
        Options.v().set_output_format(Options.output_format_class);
    }

    /**
     * Soot lists the classes it loaded in the order the process dirs'
     * listings returned them, which is the filesystem's; every pass after
     * this one (the bodies Soot builds first, lambda classes included, and
     * each walk of ours over the Scene) meets them by name instead.
     */
    private static void orderClassesByName() {
        Scene scene = Scene.v();
        for (Chain<SootClass> chain : Arrays.asList(scene.getClasses(),
                scene.getApplicationClasses(), scene.getLibraryClasses(),
                scene.getPhantomClasses())) {
            List<SootClass> named = new ArrayList<>(chain);
            named.sort(Comparator.comparing(SootClass::getName));
            chain.clear();
            chain.addAll(named);
        }
    }

    private void loadClasses() {
        Class<?>[] basicClasses = {PrintStream.class, System.class, Thread.class, Throwable.class};
        for (Class<?> cls : basicClasses) {
            Scene.v().addBasicClass(cls.getCanonicalName(), SIGNATURES);
            for (Class<?> innerCls : cls.getDeclaredClasses()) {
                Scene.v().addBasicClass(innerCls.getName(), SIGNATURES);
            }
        }
        Scene.v().addBasicClass(
                "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder",
                SIGNATURES);
        Scene.v().addBasicClass("java.lang.Object[]", SootClass.HIERARCHY);
        Scene.v().addBasicClass("java.lang.String[]", SootClass.HIERARCHY);
    }

    private static void splitProcessDirs(Collection<String> processDirs,
                                         List<String> productionDirs,
                                         List<String> testDirs) {
        for (String directory : processDirs) {
            File path = new File(directory);
            if ("test-classes".equals(path.getName())) {
                testDirs.add(path.getAbsolutePath());
            } else {
                productionDirs.add(path.getAbsolutePath());
            }
        }
    }

    private static String expandClassPath(String classPath) {
        if (classPath == null || classPath.trim().isEmpty()) {
            return classPath;
        }

        Set<String> expanded = new LinkedHashSet<>();
        for (String entry : classPath.split(File.pathSeparator)) {
            if (entry == null || entry.trim().isEmpty()) {
                continue;
            }
            if (entry.endsWith(File.separator + "*") || entry.endsWith("/*")) {
                String dir = entry.substring(0, entry.length() - 2);
                File[] jars = new File(dir).listFiles(file -> file.getName().endsWith(".jar"));
                if (jars != null) {
                    Arrays.sort(jars, Comparator.comparing(File::getAbsolutePath));
                    for (File jar : jars) {
                        expanded.add(jar.getAbsolutePath());
                    }
                }
                continue;
            }
            expanded.add(entry);
        }
        return String.join(File.pathSeparator, expanded);
    }

    /** Input dirs plus {@code causynth.process.dirs} and the lineage dirs. */
    private List<String> expandProcessDirs(List<String> inputDirs) {
        LinkedHashSet<String> dirs = new LinkedHashSet<>();
        for (String inputDir : inputDirs) {
            dirs.add(new File(inputDir).getAbsolutePath());
        }
        dirs.addAll(LineageScope.dirs("causynth.process.dirs",
                "Configured Soot process directory"));
        dirs.addAll(LineageScope.dirs());
        if (dirs.size() > inputDirs.size()) {
            LOG.info("Expanded Soot process dirs to {}", dirs);
        }
        return new ArrayList<>(dirs);
    }

    /** Put the authoritative project outputs ahead of dependency jars. */
    private static String prependClasspathEntries(
            List<String> entries, String classPath) {
        StringBuilder builder = new StringBuilder();
        List<String> ordered = new ArrayList<>(entries);
        ordered.add(classPath);
        for (String entry : ordered) {
            if (entry == null || entry.isEmpty()) continue;
            if (builder.length() > 0) builder.append(File.pathSeparator);
            builder.append(entry);
        }
        return builder.toString();
    }

    public static void main(String[] args) {
        GraphCheckerMain main = new GraphCheckerMain(
                GraphCheckerOptions.parse(args));
        main.initialize();
        if (!main.run()) {
            System.exit(1);
        }
    }
}
