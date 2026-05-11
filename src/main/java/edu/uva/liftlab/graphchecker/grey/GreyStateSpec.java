package edu.uva.liftlab.graphchecker.grey;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class GreyStateSpec {
    private final List<FatalSeed> fatalSeeds;
    private final List<String> analysisClasses;
    private final String outputDir;
    private final int bound;

    public GreyStateSpec(
            List<FatalSeed> fatalSeeds,
            List<String> analysisClasses,
            String outputDir,
            int bound) {
        if (fatalSeeds == null || fatalSeeds.isEmpty()) {
            throw new IllegalArgumentException("grey-state config requires at least one fatal seed");
        }
        this.fatalSeeds = Collections.unmodifiableList(new ArrayList<FatalSeed>(fatalSeeds));
        this.analysisClasses = analysisClasses == null
                ? Collections.<String>emptyList()
                : Collections.unmodifiableList(new ArrayList<String>(analysisClasses));
        this.outputDir = outputDir == null || outputDir.trim().isEmpty() ? "grey-output" : outputDir.trim();
        this.bound = bound > 0 ? bound : 4;
    }

    public List<FatalSeed> getFatalSeeds() {
        return fatalSeeds;
    }

    public List<String> getAnalysisClasses() {
        return analysisClasses;
    }

    public String getOutputDir() {
        return outputDir;
    }

    public int getBound() {
        return bound;
    }

    public static final class FatalSeed {
        private final String id;
        private final String className;
        private final String methodName;
        private final String exceptionClass;

        public FatalSeed(String id, String className, String methodName, String exceptionClass) {
            this.id = isBlank(id) ? "fatal_seed" : id.trim();
            this.className = require(className, "fatal seed class");
            this.methodName = require(methodName, "fatal seed method");
            this.exceptionClass = exceptionClass == null ? "" : exceptionClass.trim();
        }

        public String getId() {
            return id;
        }

        public String getClassName() {
            return className;
        }

        public String getMethodName() {
            return methodName;
        }

        public String getExceptionClass() {
            return exceptionClass;
        }

        private static String require(String value, String name) {
            if (isBlank(value)) {
                throw new IllegalArgumentException("Missing " + name);
            }
            return value.trim();
        }

        private static boolean isBlank(String value) {
            return value == null || value.trim().isEmpty();
        }
    }
}
