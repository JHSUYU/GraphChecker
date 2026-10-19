package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

public final class LineageScope {
    public static final String PROPERTY = "causynth.lineage.dirs";

    private static Set<String> classes;

    private LineageScope() {
    }

    public static List<String> dirs() {
        return dirs(PROPERTY, "lineage class directory");
    }

    public static List<String> dirs(String property, String what) {
        String configured = System.getProperty(property);
        List<String> dirs = new ArrayList<>();
        if (configured == null || configured.trim().isEmpty()) return dirs;
        for (String dir : configured.split(Pattern.quote(File.pathSeparator))) {
            File file = new File(dir.trim());
            if (!file.isDirectory()) {
                throw new IllegalStateException(
                        what + " not found: " + dir);
            }
            dirs.add(file.getAbsolutePath());
        }
        return dirs;
    }

    public static synchronized boolean lineageOnly(String className) {
        if (classes == null) classes = read();
        return classes.contains(className);
    }

    private static Set<String> read() {
        Set<String> names = new LinkedHashSet<>();
        for (String dir : dirs()) {
            Path root = Paths.get(dir);
            try {
                for (Path file : ArtifactIO.classFiles(root)) {
                    names.add(VerifyWovenClasses.binaryName(root, file));
                }
            } catch (IOException failure) {
                throw new UncheckedIOException(failure);
            }
        }
        return Collections.unmodifiableSet(names);
    }
}
