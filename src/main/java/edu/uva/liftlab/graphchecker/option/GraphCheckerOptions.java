package edu.uva.liftlab.graphchecker.option;

import edu.uva.liftlab.graphchecker.GraphCheckerMain;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * The static pass's options, as run_engine.sh ({@code do_analyze}) and the
 * offline gate ({@code tools/regress/offline-ab.sh}) pass them: {@code -i
 * <classes directory>} (one or more), {@code -x <classpath>} and {@code -o
 * <output directory>}, each flag followed by its value.  Anything else is
 * refused by name.
 */
public final class GraphCheckerOptions {
    private final List<String> inputList;
    private final String classPath;
    private final String outputDir;

    private GraphCheckerOptions(List<String> inputList, String classPath,
                                String outputDir) {
        this.inputList = Collections.unmodifiableList(inputList);
        this.classPath = classPath;
        this.outputDir = outputDir;
    }

    public static GraphCheckerOptions parse(String[] args) {
        List<String> inputs = new ArrayList<>();
        List<String> extra = new ArrayList<>();
        String output = null;
        for (int index = 0; index < args.length; index += 2) {
            String flag = args[index];
            if (index + 1 >= args.length) {
                throw new IllegalArgumentException(flag + " takes a value");
            }
            String value = args[index + 1];
            switch (flag) {
                case "-i":
                    if (!new File(value).isDirectory()) {
                        throw new IllegalArgumentException("-i " + value
                                + ": not a directory");
                    }
                    inputs.add(value);
                    break;
                case "-x":
                    extra.add(value);
                    break;
                case "-o":
                    output = value;
                    break;
                default:
                    throw new IllegalArgumentException("unknown option "
                            + flag + "; GraphCheckerMain takes -i <classes "
                            + "directory>, -x <classpath> and -o <output "
                            + "directory>");
            }
        }
        if (inputs.isEmpty()) {
            throw new IllegalArgumentException("GraphCheckerMain states no "
                    + "-i <classes directory>");
        }
        // Soot's classpath: GraphChecker's own classes (the runtime a weave
        // calls), the analysed classpath, the inputs.  The pass's own JVM
        // runs on GraphChecker's jar alone (run_engine.sh do_analyze).
        List<String> entries = new ArrayList<>();
        entries.add(GraphCheckerMain.class.getProtectionDomain()
                .getCodeSource().getLocation().getPath());
        entries.addAll(extra);
        entries.addAll(inputs);
        return new GraphCheckerOptions(inputs,
                String.join(File.pathSeparator, entries), output);
    }

    public String getClassPath() { return classPath; }

    public List<String> getInputList() { return inputList; }

    /** The output directory, or null when none was given. */
    public String getOutputDir() { return outputDir; }
}
