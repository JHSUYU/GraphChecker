package edu.uva.liftlab.graphchecker;

import edu.uva.liftlab.graphchecker.causynth.LineageScope;
import edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import edu.uva.liftlab.graphchecker.option.OptionError;
import edu.uva.liftlab.graphchecker.option.OptionParser;
import edu.uva.liftlab.graphchecker.transformer.GraphCheckerTransformer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.PackManager;
import soot.PhaseOptions;
import soot.Scene;
import soot.SootClass;
import soot.Timers;
import soot.Transform;
import soot.options.Options;

import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Date;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import static soot.SootClass.SIGNATURES;

public class GraphCheckerMain {
    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerMain.class);

    private final GraphCheckerOptions options;
    private final List<String> productionProcessDirs = new ArrayList<>();
    private final Set<String> testClassOutputDirs = new LinkedHashSet<>();
    private boolean concolicInstrumentation;

    public GraphCheckerMain(GraphCheckerOptions options) {
        this.options = options;
    }

    public void initialize() {
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
        if (!Options.v().parse(options.getArgs())) {
            System.err.println("Error in parsing Soot options");
            return false;
        }
        enforceProductionApplicationScope();

        Options.v().warnNonexistentPhase();
        if (Options.v().phase_list()) {
            System.out.println(Options.v().getPhaseList());
            return true;
        }
        if (!Options.v().phase_help().isEmpty()) {
            for (String phase : Options.v().phase_help()) {
                System.out.println(Options.v().getPhaseHelp(phase));
            }
            return true;
        }

        try {
            Date start = new Date();
            LOG.info("GraphChecker started on {}", start);
            Timers.v().totalTimer.start();

            Scene.v().loadNecessaryClasses();
            PackManager.v().runPacks();
            PackManager.v().writeOutput();

            Timers.v().totalTimer.end();
            if (Options.v().time()) {
                Timers.v().printProfilingInformation();
            }

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
        testClassOutputDirs.addAll(configuredTestDirs);
        String classPath = expandClassPath(prependClasspathEntries(
                processDirs, options.getClassPath()));
        collectTestClassOutputs(classPath, testClassOutputDirs);
        Options.v().set_soot_classpath(classPath);
        Options.v().set_keep_line_number(true);
        Options.v().set_whole_program(true);
        concolicInstrumentation = ConcolicInstrumentationSelections
                .instrumentationRequested();
        if (!configuredTestDirs.isEmpty()) {
            LOG.info("Static discovery keeps {} test output(s) on the "
                            + "classpath but excludes every test class "
                            + "from application scope; {} production "
                            + "root(s) remain",
                    configuredTestDirs.size(),
                    productionProcessDirs.size());
        }
        // ONE application scope, whatever this run is for: the case's own
        // process dirs.  The concolic pass used to narrow it to the owners of
        // the campaign envelope, which silently dropped every woven body
        // outside them -- PackManager writes application classes and nothing
        // else -- so a work start (G9) or a skeleton region entry in an
        // unselected class was woven in the recording and absent from the
        // replay's class tree, and every index below it drifted.  The scope
        // is the same in both passes or the two passes are not comparable.
        Options.v().set_process_dir(productionProcessDirs);
        LOG.info("Soot application scope is the case's {} production "
                        + "root(s){}", productionProcessDirs.size(),
                concolicInstrumentation
                        ? ", campaign instrumentation included" : "");
        if (options.getOutputDir() != null) {
            Options.v().set_output_dir(options.getOutputDir());
        }

        if (options.isOutputJar()) {
            Options.v().set_output_jar(true);
        } else {
            Options.v().set_output_format(Options.output_format_class);
        }

        if (options.getArgs().length == 0) {
            Options.v().set_unfriendly_mode(true);
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

    static void splitProcessDirs(Collection<String> processDirs,
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

    private static void collectTestClassOutputs(
            String classPath, Collection<String> testDirs) {
        if (classPath == null || classPath.trim().isEmpty()) {
            return;
        }
        for (String entry : classPath.split(Pattern.quote(
                File.pathSeparator))) {
            File path = new File(entry);
            if ("test-classes".equals(path.getName())
                    && path.isDirectory()) {
                testDirs.add(path.getAbsolutePath());
            }
        }
    }

    /** Raw Soot arguments are parsed after GraphChecker's own options. */
    private void enforceProductionApplicationScope() {
        // Soot parses a trailing -cp after configureSoot().
        collectTestClassOutputs(Options.v().soot_classpath(),
                testClassOutputDirs);
        Options.v().set_process_dir(productionProcessDirs);
        for (String className : new ArrayList<>(Options.v().classes())) {
            if (classComesFromTestOutput(className)) {
                throw new IllegalStateException("Test class cannot enter "
                        + "GraphChecker application scope: " + className);
            }
        }
        String mainClass = Options.v().main_class();
        if (classComesFromTestOutput(mainClass)) {
            throw new IllegalStateException("Test main class cannot enter "
                    + "GraphChecker application scope: " + mainClass);
        }
    }

    private boolean classComesFromTestOutput(String className) {
        if (className == null || className.trim().isEmpty()) {
            return false;
        }
        String relative = className.replace('.', File.separatorChar)
                + ".class";
        for (String directory : testClassOutputDirs) {
            if (Files.isRegularFile(Paths.get(directory, relative))) {
                return true;
            }
        }
        return false;
    }

    static String expandClassPath(String classPath) {
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

    /** The input directories plus the roots {@code causynth.process.dirs}
     *  names.  {@code run_engine.sh} resolves that list from the workflow
     *  configuration, so this is the one place it is read. */
    private List<String> expandProcessDirs(List<String> inputDirs) {
        LinkedHashSet<String> dirs = new LinkedHashSet<>();
        for (String inputDir : inputDirs) {
            dirs.add(new File(inputDir).getAbsolutePath());
        }
        String configured = System.getProperty("causynth.process.dirs");
        if (configured != null && !configured.trim().isEmpty()) {
            for (String dir : configured.split(
                    Pattern.quote(File.pathSeparator))) {
                File file = new File(dir.trim());
                if (!file.isDirectory()) {
                    throw new IllegalStateException(
                            "Configured Soot process directory not found: "
                                    + dir);
                }
                dirs.add(file.getAbsolutePath());
            }
        }
        // The lineage scope, on the two weave runs that name it: application
        // classes of the run, woven for their lineage alone (LineageScope).
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
        OptionParser parser = new OptionParser();
        GraphCheckerOptions options;
        try {
            options = parser.parse(args);
        } catch (OptionError optionError) {
            System.out.println("Error in parsing options: " + optionError.getMessage() + "\n");
            parser.printHelp();
            System.exit(1);
            return;
        }

        if (options.isHelp()) {
            parser.printHelp();
            System.exit(0);
        }
        if (options.getInputList().isEmpty()) {
            System.out.println("Must set an input jar or input directory.");
            parser.printHelp();
            System.exit(1);
        }

        GraphCheckerMain main = new GraphCheckerMain(options);
        main.initialize();
        if (!main.run()) {
            System.exit(1);
        }
    }
}
