package edu.uva.liftlab.graphchecker.option;

import edu.uva.liftlab.graphchecker.GraphCheckerMain;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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

    public String getOutputDir() { return outputDir; }
}
