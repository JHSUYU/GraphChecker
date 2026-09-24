package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * The classes a weave run holds for their lineage alone
 * ({@code plan.LineageScan}): the process dirs {@value #PROPERTY} names.
 *
 * <p>They are application classes of the run, so the weave writes them, and
 * {@code CausynthPipeline.instrumentApplicationScope} gives them the
 * work-start, work-claim and queue-claim hooks and nothing else: no
 * calling-context level, so every occurrence of the analysis scope keeps its
 * index, and no timed-wait stand-in, so no daemon loop outside the analysis
 * scope changes how it waits.  Discovery never names the property, so no
 * static analysis sees them.</p>
 */
public final class LineageScope {
    /** The system property run_engine.sh sets on the two weave runs. */
    public static final String PROPERTY = "causynth.lineage.dirs";

    private static Set<String> classes;

    private LineageScope() {
    }

    /** The lineage dirs of this run, or none. */
    public static List<String> dirs() {
        String configured = System.getProperty(PROPERTY);
        List<String> dirs = new ArrayList<>();
        if (configured == null || configured.trim().isEmpty()) return dirs;
        for (String dir : configured.split(Pattern.quote(File.pathSeparator))) {
            File file = new File(dir.trim());
            if (!file.isDirectory()) {
                throw new IllegalStateException(
                        "lineage class directory not found: " + dir);
            }
            dirs.add(file.getAbsolutePath());
        }
        return dirs;
    }

    /** Whether this class is in the run for its lineage alone. */
    public static synchronized boolean lineageOnly(String className) {
        if (classes == null) classes = read();
        return classes.contains(className);
    }

    private static Set<String> read() {
        Set<String> names = new LinkedHashSet<>();
        for (String dir : dirs()) {
            Path root = Paths.get(dir);
            try (Stream<Path> walk = Files.walk(root)) {
                walk.filter(path -> path.toString().endsWith(".class"))
                        .forEach(path -> {
                            String relative = root.relativize(path).toString();
                            names.add(relative.substring(0,
                                    relative.length() - ".class".length())
                                    .replace(File.separatorChar, '.'));
                        });
            } catch (IOException failure) {
                throw new UncheckedIOException(failure);
            }
        }
        return Collections.unmodifiableSet(names);
    }
}
