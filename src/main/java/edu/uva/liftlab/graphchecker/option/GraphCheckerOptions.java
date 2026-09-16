package edu.uva.liftlab.graphchecker.option;

import java.util.Collections;
import java.util.List;

public final class GraphCheckerOptions {
    boolean help;
    boolean outputJar;

    String classPath;
    List<String> inputList = Collections.emptyList();
    String outputDir;
    String[] args = new String[0];

    GraphCheckerOptions() {
    }

    public boolean isHelp() { return help; }

    public boolean isOutputJar() { return outputJar; }

    public String getClassPath() { return classPath; }

    public List<String> getInputList() { return inputList; }

    public String getOutputDir() { return outputDir; }


    public String[] getArgs() { return args; }
}
