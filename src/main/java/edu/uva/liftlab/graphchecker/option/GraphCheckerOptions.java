package edu.uva.liftlab.graphchecker.option;

import java.util.Collections;
import java.util.List;
import java.util.Map;

public final class GraphCheckerOptions {
    boolean help;
    boolean sootHelp;
    boolean keepDebug = true;
    boolean noOutput;
    boolean outputJar;
    boolean listAnalysis;

    String classPath;
    List<String> inputList = Collections.emptyList();
    String mainClass;
    String outputDir;
    String configFilePath;
    String[] analyses = new String[0];
    String[] classes = new String[0];
    Map<String, List<String>> phaseOptions = Collections.emptyMap();
    String[] args = new String[0];

    GraphCheckerOptions() {
    }

    public boolean isHelp() {
        return help;
    }

    public boolean isSootHelp() {
        return sootHelp;
    }

    public boolean keepDebug() {
        return keepDebug;
    }

    public boolean noOutput() {
        return noOutput;
    }

    public boolean isOutputJar() {
        return outputJar;
    }

    public boolean listAnalysis() {
        return listAnalysis;
    }

    public String getClassPath() {
        return classPath;
    }

    public List<String> getInputList() {
        return inputList;
    }

    public boolean isInputListEmpty() {
        return inputList.isEmpty();
    }

    public String getMainClass() {
        return mainClass;
    }

    public String getOutputDir() {
        return outputDir;
    }

    public String getConfigFilePath() {
        return configFilePath;
    }

    public String[] getAnalyses() {
        return analyses;
    }

    public String[] getClasses() {
        return classes;
    }

    public Map<String, List<String>> getPhaseOptions() {
        return phaseOptions;
    }

    public String[] getArgs() {
        return args;
    }

}
