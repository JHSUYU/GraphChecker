package edu.uva.liftlab.graphchecker.option;

import edu.uva.liftlab.graphchecker.GraphCheckerMain;
import edu.uva.liftlab.graphchecker.analysis.AnalysisManager;
import edu.uva.liftlab.graphchecker.analysis.PhaseInfo;
import edu.uva.liftlab.graphchecker.util.StringUtils;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class OptionParser {
    private final Option analysisList = Option.builder("a").longOpt("analysis").hasArgs()
            .argName("name name ...")
            .desc("Analysis phase names to run").build();
    private final Option phaseOptions = Option.builder("p").longOpt("phase_option").hasArgs()
            .argName("phase key:value,key:value ...")
            .desc("Soot phase options").build();
    private final Option inputDirectoryList = Option.builder("i").longOpt("indir").hasArgs()
            .argName("directory directory ...")
            .desc("Input directories containing class files").build();
    private final Option inputJarList = Option.builder("j").longOpt("jar").hasArgs()
            .argName("file file ...")
            .desc("Input jar files").build();
    private final Option classPathList = Option.builder("x").longOpt("extra_classpath").hasArgs()
            .argName("classpath classpath ...")
            .desc("Additional classpath entries").build();
    private final Option classList = Option.builder("c").longOpt("class").hasArgs()
            .argName("class class ...")
            .desc("Class names to process from the classpath").build();
    private final Option mainClass = Option.builder("m").longOpt("main").hasArg()
            .argName("class")
            .desc("Main class").build();
    private final Option outputDirectory = Option.builder("o").longOpt("outdir").hasArg()
            .argName("directory")
            .desc("Output directory").build();
    private final Option noOutput = Option.builder("n").longOpt("no_output")
            .desc("Do not write Soot output").build();
    private final Option wholeProgram = Option.builder("w").longOpt("whole")
            .desc("Enable whole-program mode").build();
    private final Option noDebugInfo = Option.builder().longOpt("no_debug")
            .desc("Do not keep line numbers").build();
    private final Option listAnalysis = Option.builder().longOpt("list")
            .desc("List available GraphChecker analyses").build();
    private final Option help = Option.builder("h").longOpt("help")
            .desc("Print this help message").build();
    private final Option helpWithSootHelp = Option.builder("H").longOpt("Help")
            .desc("Print this help message and Soot help").build();
    private final Option configFile = Option.builder("C").longOpt("systemConfigFile").hasArg()
            .argName("file")
            .desc("Reserved configuration file path for future transformers").build();

    private final Options options = new Options();

    public OptionParser() {
        options.addOption(analysisList);
        options.addOption(phaseOptions);
        options.addOption(inputDirectoryList);
        options.addOption(inputJarList);
        options.addOption(classPathList);
        options.addOption(classList);
        options.addOption(mainClass);
        options.addOption(outputDirectory);
        options.addOption(noOutput);
        options.addOption(wholeProgram);
        options.addOption(noDebugInfo);
        options.addOption(listAnalysis);
        options.addOption(help);
        options.addOption(helpWithSootHelp);
        options.addOption(configFile);
    }

    public GraphCheckerOptions parse(String[] args) throws OptionError {
        try {
            CommandLine cmd = new DefaultParser().parse(options, args);
            GraphCheckerOptions parsed = GraphCheckerOptions.getInstance();

            List<String> inputList = parseInputs(cmd);
            parsed.setInputList(inputList);
            parsed.setOutputJar(cmd.getOptionValues(inputJarList.getOpt()) != null);
            parsed.setClasses(cmd.getOptionValues(classList.getLongOpt()));
            parsed.setMainClass(cmd.getOptionValue(mainClass.getLongOpt()));
            parsed.setOutputDir(cmd.getOptionValue(outputDirectory.getLongOpt()));
            parsed.setNoOutput(cmd.hasOption(noOutput.getLongOpt()));
            parsed.setWholeProgram(true);
            parsed.setKeepDebug(!cmd.hasOption(noDebugInfo.getLongOpt()));
            parsed.setListAnalysis(cmd.hasOption(listAnalysis.getLongOpt()));
            parsed.setHelp(cmd.hasOption(help.getLongOpt()));
            parsed.setSootHelp(cmd.hasOption(helpWithSootHelp.getLongOpt()));
            parsed.setConfigFilePath(cmd.getOptionValue(configFile.getLongOpt()));
            parsed.setArgs(cmd.getArgs());

            parsed.setClassPath(buildClassPath(cmd, inputList));
            parsed.setAnalyses(parseAnalyses(cmd));
            parsed.setPhaseOptions(parsePhaseOptions(cmd));
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

    private List<String> parseInputs(CommandLine cmd) throws OptionError {
        String[] jars = cmd.getOptionValues(inputJarList.getOpt());
        String[] directories = cmd.getOptionValues(inputDirectoryList.getOpt());
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

        String[] extraClassPath = cmd.getOptionValues(classPathList.getLongOpt());
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
        return StringUtils.join(File.pathSeparator, entries);
    }

    private String[] parseAnalyses(CommandLine cmd) throws OptionError {
        String[] analyses = cmd.getOptionValues(analysisList.getLongOpt());
        if (analyses == null) {
            return null;
        }
        for (String analysis : analyses) {
            if (AnalysisManager.getInstance().getPhaseInfo(analysis) == null) {
                throw new OptionError(analysis + " is not a recognized analysis");
            }
        }
        return analyses;
    }

    private Map<String, List<String>> parsePhaseOptions(CommandLine cmd) throws OptionError {
        String[] phaseOptionValues = cmd.getOptionValues(phaseOptions.getLongOpt());
        Map<String, List<String>> allPhaseOptions = new HashMap<>();
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
                    List<String> optionList = allPhaseOptions.get(phaseName);
                    if (optionList == null) {
                        optionList = new ArrayList<>();
                        allPhaseOptions.put(phaseName, optionList);
                    }
                    optionList.add(component);
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
