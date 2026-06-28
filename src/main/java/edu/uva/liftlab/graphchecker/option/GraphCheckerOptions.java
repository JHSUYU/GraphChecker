package edu.uva.liftlab.graphchecker.option;

import java.util.Collections;
import java.util.List;
import java.util.Map;

public class GraphCheckerOptions {
    private boolean help;
    private boolean sootHelp;
    private boolean keepDebug = true;
    private boolean wholeProgram = true;
    private boolean noOutput;
    private boolean outputJar;
    private boolean listAnalysis;

    private String classPath;
    private List<String> inputList = Collections.emptyList();
    private String mainClass;
    private String outputDir;
    private String configFilePath;
    private String[] analyses;
    private String[] classes;
    private Map<String, List<String>> phaseOptions = Collections.emptyMap();
    private String[] args = new String[0];

    private static final GraphCheckerOptions INSTANCE = new GraphCheckerOptions();

    public static GraphCheckerOptions getInstance() {
        return INSTANCE;
    }

    private GraphCheckerOptions() {
    }

    public boolean isHelp() {
        return help;
    }

    void setHelp(boolean help) {
        this.help = help;
    }

    public boolean isSootHelp() {
        return sootHelp;
    }

    void setSootHelp(boolean sootHelp) {
        this.sootHelp = sootHelp;
    }

    public boolean keepDebug() {
        return keepDebug;
    }

    void setKeepDebug(boolean keepDebug) {
        this.keepDebug = keepDebug;
    }

    public boolean isWholeProgram() {
        return wholeProgram;
    }

    void setWholeProgram(boolean wholeProgram) {
        this.wholeProgram = wholeProgram;
    }

    public boolean noOutput() {
        return noOutput;
    }

    void setNoOutput(boolean noOutput) {
        this.noOutput = noOutput;
    }

    public boolean isOutputJar() {
        return outputJar;
    }

    void setOutputJar(boolean outputJar) {
        this.outputJar = outputJar;
    }

    public boolean listAnalysis() {
        return listAnalysis;
    }

    void setListAnalysis(boolean listAnalysis) {
        this.listAnalysis = listAnalysis;
    }

    public String getClassPath() {
        return classPath;
    }

    void setClassPath(String classPath) {
        this.classPath = classPath;
    }

    public List<String> getInputList() {
        return inputList;
    }

    void setInputList(List<String> inputList) {
        this.inputList = inputList == null ? Collections.emptyList() : inputList;
    }

    public boolean isInputListEmpty() {
        return inputList == null || inputList.isEmpty();
    }

    public String getMainClass() {
        return mainClass;
    }

    void setMainClass(String mainClass) {
        this.mainClass = mainClass;
    }

    public String getOutputDir() {
        return outputDir;
    }

    void setOutputDir(String outputDir) {
        this.outputDir = outputDir;
    }

    public String getConfigFilePath() {
        return configFilePath;
    }

    void setConfigFilePath(String configFilePath) {
        this.configFilePath = configFilePath;
    }

    public String[] getAnalyses() {
        return analyses;
    }

    void setAnalyses(String[] analyses) {
        this.analyses = analyses;
    }

    public String[] getClasses() {
        return classes;
    }

    void setClasses(String[] classes) {
        this.classes = classes;
    }

    public Map<String, List<String>> getPhaseOptions() {
        return phaseOptions;
    }

    void setPhaseOptions(Map<String, List<String>> phaseOptions) {
        this.phaseOptions = phaseOptions == null ? Collections.emptyMap() : phaseOptions;
    }

    public String[] getArgs() {
        return args == null ? new String[0] : args;
    }

    void setArgs(String[] args) {
        this.args = args == null ? new String[0] : args;
    }
}
