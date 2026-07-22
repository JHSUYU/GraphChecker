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
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Date;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.regex.Pattern;

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
        List<String> processDirs = expandProcessDirs(options.getInputList());
        Options.v().set_soot_classpath(expandClassPath(appendClasspathEntries(
                options.getClassPath(), processDirs)));
        Options.v().set_keep_line_number(options.keepDebug());
        Options.v().set_whole_program(options.isWholeProgram());

        if (options.getMainClass() != null) {
            Options.v().set_main_class(options.getMainClass());
        }
        if (!processDirs.isEmpty()) {
            Options.v().set_process_dir(processDirs);
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
        Scene.v().addBasicClass(
                "edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder",
                SIGNATURES);
        Scene.v().addBasicClass("java.lang.Object[]", SootClass.HIERARCHY);
        Scene.v().addBasicClass("java.lang.String[]", SootClass.HIERARCHY);
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

    private List<String> expandProcessDirs(List<String> inputDirs) {
        LinkedHashSet<String> dirs = new LinkedHashSet<>();
        if (inputDirs != null) {
            for (String inputDir : inputDirs) {
                addExistingDirectory(dirs, inputDir);
            }
        }

        Properties config = loadGraphCheckerConfig();
        addConfiguredProcessDirs(dirs, firstNonBlank(
                System.getProperty("causynth.process.dirs"),
                config.getProperty("causynth_process_dirs")));

        if (dirs.size() > (inputDirs == null ? 0 : inputDirs.size())) {
            LOG.info("Expanded Soot process dirs to {}", dirs);
        }
        return new ArrayList<>(dirs);
    }

    private void addConfiguredProcessDirs(Set<String> dirs, String configuredDirs) {
        if (configuredDirs == null || configuredDirs.trim().isEmpty()) {
            return;
        }
        String normalized = configuredDirs.replace(';', File.pathSeparatorChar);
        for (String dir : normalized.split(Pattern.quote(File.pathSeparator))) {
            addExistingDirectory(dirs, dir);
        }
    }

    private Properties loadGraphCheckerConfig() {
        Properties properties = new Properties();
        String configPath = options.getConfigFilePath();
        if (configPath == null || configPath.trim().isEmpty()) {
            return properties;
        }
        Path path = Paths.get(configPath);
        if (!Files.isRegularFile(path)) {
            return properties;
        }
        try {
            for (String rawLine : Files.readAllLines(path, StandardCharsets.UTF_8)) {
                String line = rawLine.trim();
                if (line.isEmpty() || line.startsWith("#")) {
                    continue;
                }
                int eq = line.indexOf('=');
                if (eq <= 0) {
                    continue;
                }
                String key = line.substring(0, eq).trim();
                String value = line.substring(eq + 1).trim();
                if ((value.startsWith("\"") && value.endsWith("\""))
                        || (value.startsWith("'") && value.endsWith("'"))) {
                    value = value.substring(1, value.length() - 1);
                }
                properties.setProperty(key, value);
            }
        } catch (IOException exception) {
            LOG.warn("Unable to read GraphChecker config {}", configPath, exception);
        }
        return properties;
    }

    private void addExistingDirectory(Set<String> dirs, String path) {
        if (path == null || path.trim().isEmpty()) {
            return;
        }
        File file = new File(path.trim());
        if (file.isDirectory()) {
            dirs.add(file.getAbsolutePath());
        }
    }

    private static String appendClasspathEntries(String classPath, List<String> entries) {
        StringBuilder builder = new StringBuilder();
        if (classPath != null && !classPath.trim().isEmpty()) {
            builder.append(classPath);
        }
        if (entries != null) {
            for (String entry : entries) {
                appendClasspathEntry(builder, entry);
            }
        }
        return builder.toString();
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

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
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
