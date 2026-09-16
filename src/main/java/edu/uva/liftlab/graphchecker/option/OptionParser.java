package edu.uva.liftlab.graphchecker.option;

import edu.uva.liftlab.graphchecker.GraphCheckerMain;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

/** Parses the five flags run_engine.sh passes; the rest are raw Soot args. */
public class OptionParser {
    private final Options options = new Options();

    public OptionParser() {
        many("i", "directory directory ...", "Input directories of classes");
        many("j", "file file ...", "Input jar files");
        many("x", "classpath classpath ...", "Extra classpath entries");
        one("o", "directory", "Output directory");
        options.addOption(Option.builder("h")
                .desc("Print this help message").build());
    }

    public GraphCheckerOptions parse(String[] args) throws OptionError {
        try {
            CommandLine cmd = new DefaultParser().parse(options, args);
            GraphCheckerOptions parsed = new GraphCheckerOptions();
            parsed.inputList = parseInputs(cmd);
            parsed.outputJar = cmd.hasOption("j");
            parsed.outputDir = cmd.getOptionValue("o");
            parsed.help = cmd.hasOption("h");
            parsed.args = cmd.getArgs();
            parsed.classPath = buildClassPath(cmd, parsed.inputList);
            return parsed;
        } catch (ParseException exception) {
            throw new OptionError(exception.getMessage());
        }
    }

    public void printHelp() {
        new HelpFormatter().printHelp(80,
                "GraphChecker.jar [OPTIONS] -- [SOOT OPTIONS]",
                null, options, null, false);
    }

    private void many(String name, String argument, String description) {
        options.addOption(Option.builder(name).argName(argument)
                .desc(description).hasArgs().build());
    }

    private void one(String name, String argument, String description) {
        options.addOption(Option.builder(name).argName(argument)
                .desc(description).hasArg().build());
    }

    private List<String> parseInputs(CommandLine cmd) throws OptionError {
        String[] jars = cmd.getOptionValues("j");
        String[] directories = cmd.getOptionValues("i");
        if (jars != null && directories != null) {
            throw new OptionError("Can only accept either jar inputs or "
                    + "directory inputs.");
        }
        List<String> inputs = new ArrayList<>();
        if (jars != null) {
            for (String jar : jars) {
                if (!new File(jar).isFile()) {
                    throw new OptionError(jar
                            + " does not exist or is not a file");
                }
                inputs.add(jar);
            }
        }
        if (directories != null) {
            for (String directory : directories) {
                if (!new File(directory).isDirectory()) {
                    throw new OptionError(directory
                            + " does not exist or is not a directory");
                }
                inputs.add(directory);
            }
        }
        return inputs;
    }

    private String buildClassPath(CommandLine cmd, List<String> inputList) {
        List<String> entries = new ArrayList<>();
        entries.add(GraphCheckerMain.class.getProtectionDomain()
                .getCodeSource().getLocation().getPath());
        String[] extra = cmd.getOptionValues("x");
        if (extra != null) {
            for (String entry : extra) entries.add(entry);
        }
        entries.addAll(inputList);
        String javaClassPath = System.getProperty("java.class.path");
        if (javaClassPath != null && !javaClassPath.isEmpty()) {
            entries.add(javaClassPath);
        }
        return String.join(File.pathSeparator, entries);
    }
}
