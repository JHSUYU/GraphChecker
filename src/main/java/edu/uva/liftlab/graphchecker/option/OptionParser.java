package edu.uva.liftlab.graphchecker.option;

import edu.uva.liftlab.graphchecker.GraphCheckerMain;
import edu.uva.liftlab.graphchecker.analysis.AnalysisManager;
import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class OptionParser {
    private final Options options = new Options();

    public OptionParser() {
        add("a", true, "name name ...", "Analysis phase names to run");
        add("p", true, "phase key:value,key:value ...",
                "Soot phase options");
        add("i", true, "directory directory ...",
                "Input directories containing class files");
        add("j", true, "file file ...", "Input jar files");
        add("x", true, "classpath classpath ...",
                "Additional classpath entries");
        add("c", true, "class class ...",
                "Class names to process from the classpath");
        addOne("m", "class", "Main class");
        addOne("o", "directory", "Output directory");
        options.addOption(Option.builder("n")
                .desc("Do not write Soot output").build());
        options.addOption(Option.builder().longOpt("no-debug")
                .desc("Do not keep line numbers").build());
        options.addOption(Option.builder().longOpt("list")
                .desc("List available GraphChecker analyses").build());
        options.addOption(Option.builder("h")
                .desc("Print this help message").build());
        options.addOption(Option.builder("H")
                .desc("Print this help message and Soot help").build());
        addOne("C", "file", "Workflow configuration file");
    }

    public GraphCheckerOptions parse(String[] args) throws OptionError {
        try {
            CommandLine cmd = new DefaultParser().parse(options, args);
            GraphCheckerOptions parsed = new GraphCheckerOptions();

            List<String> inputList = parseInputs(cmd);
            parsed.inputList = inputList;
            parsed.outputJar = cmd.hasOption("j");
            String[] classes = cmd.getOptionValues("c");
            parsed.classes = classes == null ? new String[0] : classes;
            parsed.mainClass = cmd.getOptionValue("m");
            parsed.outputDir = cmd.getOptionValue("o");
            parsed.noOutput = cmd.hasOption("n");
            parsed.keepDebug = !cmd.hasOption("no-debug");
            parsed.listAnalysis = cmd.hasOption("list");
            parsed.help = cmd.hasOption("h");
            parsed.sootHelp = cmd.hasOption("H");
            parsed.configFilePath = cmd.getOptionValue("C");
            parsed.args = cmd.getArgs();
            parsed.classPath = buildClassPath(cmd, inputList);
            parsed.analyses = parseAnalyses(cmd);
            parsed.phaseOptions = parsePhaseOptions(cmd);
            return parsed;
        } catch (ParseException exception) {
            throw new OptionError(exception.getMessage());
        }
    }

    public void printHelp() {
        HelpFormatter formatter = new HelpFormatter();
        formatter.printHelp(80, "GraphChecker.jar [OPTIONS] -- [SOOT OPTIONS]",
                null, options, null, false);
    }

    public void listAnalyses() {
        System.out.println("Available GraphChecker analyses:");
        Iterator<PhaseInfo> infoIterator = AnalysisManager.getInstance().phaseInfoIterator();
        while (infoIterator.hasNext()) {
            PhaseInfo info = infoIterator.next();
            System.out.println("\t" + info.getFullName() + " - " + info.getHelp());
        }
    }

    private void add(String name, boolean many, String argument,
                     String description) {
        Option.Builder builder = Option.builder(name).argName(argument)
                .desc(description);
        options.addOption(many ? builder.hasArgs().build()
                : builder.hasArg().build());
    }

    private void addOne(String name, String argument, String description) {
        add(name, false, argument, description);
    }

    private List<String> parseInputs(CommandLine cmd) throws OptionError {
        String[] jars = cmd.getOptionValues("j");
        String[] directories = cmd.getOptionValues("i");
        if (jars != null && directories != null) {
            throw new OptionError("Can only accept either jar inputs or directory inputs.");
        }

        List<String> inputs = new ArrayList<>();
        if (jars != null) {
            for (String jar : jars) {
                if (!new File(jar).isFile()) {
                    throw new OptionError(jar + " does not exist or is not a file");
                }
                inputs.add(jar);
            }
        }
        if (directories != null) {
            for (String directory : directories) {
                if (!new File(directory).isDirectory()) {
                    throw new OptionError(directory + " does not exist or is not a directory");
                }
                inputs.add(directory);
            }
        }
        return inputs;
    }

    private String buildClassPath(CommandLine cmd, List<String> inputList) {
        List<String> entries = new ArrayList<>();
        String toolPath = GraphCheckerMain.class.getProtectionDomain().getCodeSource().getLocation().getPath();
        entries.add(toolPath);

        String[] extraClassPath = cmd.getOptionValues("x");
        if (extraClassPath != null) {
            for (String entry : extraClassPath) {
                entries.add(entry);
            }
        }
        entries.addAll(inputList);

        String javaClassPath = System.getProperty("java.class.path");
        if (javaClassPath != null && !javaClassPath.isEmpty()) {
            entries.add(javaClassPath);
        }
        return String.join(File.pathSeparator, entries);
    }

    private String[] parseAnalyses(CommandLine cmd) throws OptionError {
        String[] analyses = cmd.getOptionValues("a");
        if (analyses == null) {
            return new String[0];
        }
        for (String analysis : analyses) {
            if (AnalysisManager.getInstance().getPhaseInfo(analysis) == null) {
                throw new OptionError(analysis + " is not a recognized analysis");
            }
        }
        return analyses;
    }

    private Map<String, List<String>> parsePhaseOptions(CommandLine cmd) throws OptionError {
        String[] phaseOptionValues = cmd.getOptionValues("p");
        Map<String, List<String>> allPhaseOptions = new LinkedHashMap<>();
        if (phaseOptionValues == null) {
            return allPhaseOptions;
        }

        String phaseName = null;
        boolean lastWasOption = false;
        for (String phaseOptionValue : phaseOptionValues) {
            String[] components = phaseOptionValue.split(",");
            for (String component : components) {
                String[] parts = component.split(":", 2);
                if (parts.length == 1) {
                    if (phaseName != null && !lastWasOption) {
                        throw new OptionError("Missing phase option for " + phaseName);
                    }
                    phaseName = component;
                    lastWasOption = false;
                } else {
                    if (phaseName == null || phaseName.isEmpty()) {
                        throw new OptionError("Missing phase name for phase option " + component);
                    }
                    allPhaseOptions.computeIfAbsent(phaseName,
                            ignored -> new ArrayList<>()).add(component);
                    lastWasOption = true;
                }
            }
        }
        if (phaseName != null && !lastWasOption) {
            throw new OptionError("Missing phase option for " + phaseName);
        }
        return allPhaseOptions;
    }
}
