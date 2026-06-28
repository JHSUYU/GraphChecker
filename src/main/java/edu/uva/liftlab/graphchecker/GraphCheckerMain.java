package edu.uva.liftlab.graphchecker;

import edu.uva.liftlab.graphchecker.analysis.AnalysisManager;
import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.option.GraphCheckerOptions;
import edu.uva.liftlab.graphchecker.option.OptionError;
import edu.uva.liftlab.graphchecker.option.OptionParser;
import edu.uva.liftlab.graphchecker.transformer.GraphCheckerTransformer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.G;
import soot.PackManager;
import soot.PhaseOptions;
import soot.Scene;
import soot.SootClass;
import soot.Timers;
import soot.options.Options;

import java.io.File;
import java.io.PrintStream;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static soot.SootClass.SIGNATURES;

public class GraphCheckerMain {
    private static final Logger LOG = LoggerFactory.getLogger(GraphCheckerMain.class);

    private final GraphCheckerOptions options;
    private boolean initialized;

    public GraphCheckerMain(GraphCheckerOptions options) {
        this.options = options;
    }

    public boolean initialize() {
        registerAnalyses();
        configureSoot();
        enableAnalyses();
        loadClasses();
        initialized = true;
        return true;
    }

    public boolean run() {
        if (!initialized) {
            System.err.println("GraphChecker is not initialized");
            return false;
        }

        if (!Options.v().parse(options.getArgs())) {
            System.err.println("Error in parsing Soot options");
            return false;
        }

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
            if (!options.noOutput()) {
                PackManager.v().writeOutput();
            }

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

    public void reset() {
        G.reset();
        initialized = false;
    }

    private void registerAnalyses() {
        GraphCheckerTransformer transformer = new GraphCheckerTransformer();
        AnalysisManager.getInstance().registerAnalysis(transformer, GraphCheckerTransformer.PHASE_INFO);
    }

    private void configureSoot() {
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_prepend_classpath(true);
        Options.v().set_soot_classpath(expandClassPath(options.getClassPath()));
        Options.v().set_keep_line_number(options.keepDebug());
        Options.v().set_whole_program(options.isWholeProgram());

        if (options.getMainClass() != null) {
            Options.v().set_main_class(options.getMainClass());
        }
        if (!options.isInputListEmpty()) {
            Options.v().set_process_dir(options.getInputList());
        }
        if (options.getOutputDir() != null) {
            Options.v().set_output_dir(options.getOutputDir());
        }

        if (options.noOutput()) {
            Options.v().set_output_format(Options.output_format_none);
        } else if (options.isOutputJar()) {
            Options.v().set_output_jar(true);
        } else {
            Options.v().set_output_format(Options.output_format_class);
        }

        if (options.getArgs().length == 0) {
            Options.v().set_unfriendly_mode(true);
        }
    }

    private void enableAnalyses() {
        String[] analyses = options.getAnalyses();
        if (analyses == null || analyses.length == 0) {
            analyses = new String[] {GraphCheckerTransformer.PHASE_INFO.getFullName()};
        }

        boolean needCallGraph = false;
        Set<String> enabledFromCommandLine = new HashSet<>();
        for (String analysis : analyses) {
            AnalysisManager.getInstance().enableAnalysis(analysis);
            PhaseInfo phaseInfo = AnalysisManager.getInstance().getPhaseInfo(analysis);
            if (phaseInfo != null && phaseInfo.needCallGraph()) {
                needCallGraph = true;
            }
        }

        Map<String, List<String>> phaseOptions = options.getPhaseOptions();
        if (phaseOptions != null) {
            for (Map.Entry<String, List<String>> entry : phaseOptions.entrySet()) {
                String phase = entry.getKey();
                if (AnalysisManager.getInstance().isAnalysisEnabled(phase)) {
                    enabledFromCommandLine.add(phase);
                    PhaseOptions.v().setPhaseOption(phase, "enabled:true");
                }
                for (String option : entry.getValue()) {
                    if (!PhaseOptions.v().setPhaseOption(phase, option)) {
                        System.err.println("Failed to set Soot phase option: " + phase + " " + option);
                    }
                }
            }
        }

        for (String analysis : analyses) {
            if (!enabledFromCommandLine.contains(analysis)) {
                PhaseOptions.v().setPhaseOption(analysis, "enabled:true");
            }
        }

        if (!needCallGraph) {
            PhaseOptions.v().setPhaseOption("cg", "off");
        }
    }

    private void loadClasses() {
        String[] classes = options.getClasses();
        if (classes != null) {
            for (String className : classes) {
                LOG.info("Adding input class {}", className);
                Options.v().classes().add(className);
            }
        }

        Class<?>[] basicClasses = {PrintStream.class, System.class, Thread.class, Throwable.class};
        for (Class<?> cls : basicClasses) {
            Scene.v().addBasicClass(cls.getCanonicalName(), SIGNATURES);
            for (Class<?> innerCls : cls.getDeclaredClasses()) {
                Scene.v().addBasicClass(innerCls.getName(), SIGNATURES);
            }
        }
        Scene.v().addBasicClass("java.lang.Object[]", SootClass.HIERARCHY);
        Scene.v().addBasicClass("java.lang.String[]", SootClass.HIERARCHY);
    }

    private static String expandClassPath(String classPath) {
        if (classPath == null || classPath.trim().isEmpty()) {
            return classPath;
        }

        StringBuilder expanded = new StringBuilder();
        for (String entry : classPath.split(File.pathSeparator)) {
            if (entry.endsWith(File.separator + "*") || entry.endsWith("/*")) {
                String dir = entry.substring(0, entry.length() - 2);
                File[] jars = new File(dir).listFiles(file -> file.getName().endsWith(".jar"));
                if (jars != null) {
                    for (File jar : jars) {
                        appendClasspathEntry(expanded, jar.getAbsolutePath());
                    }
                    continue;
                }
            }
            appendClasspathEntry(expanded, entry);
        }
        return expanded.toString();
    }

    private static void appendClasspathEntry(StringBuilder classPath, String entry) {
        if (entry == null || entry.isEmpty()) {
            return;
        }
        if (classPath.length() > 0) {
            classPath.append(File.pathSeparator);
        }
        classPath.append(entry);
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

        if (options.isSootHelp()) {
            parser.printHelp();
            System.out.println("\nSoot OPTIONS:\n");
            System.out.println(Options.v().getUsage());
            System.exit(0);
        }
        if (options.isHelp()) {
            parser.printHelp();
            System.exit(0);
        }
        if (options.listAnalysis()) {
            parser.listAnalyses();
            System.exit(0);
        }
        if (options.isInputListEmpty() && options.getClasses() == null) {
            System.out.println("Must set either an input jar/input directory or a list of classes.");
            parser.printHelp();
            System.exit(1);
        }

        GraphCheckerMain main = new GraphCheckerMain(options);
        if (!main.initialize() || !main.run()) {
            System.exit(1);
        }
    }
}
