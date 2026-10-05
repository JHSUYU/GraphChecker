package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/**
 * The candidate region skeletons every weave opens its regions from: a static
 * fact, since the recording is woven before it runs and the replay must stand
 * on the same frames.
 */
final class RegionSkeletonInstrumentationSelection {
    private RegionSkeletonInstrumentationSelection() {
    }

    /**
     * The region each ROOT method opens: the recording pushes an index frame
     * where the replay does (IDENTITY §10), from the same file.
     */
    static Map<String, String> regionRootsFromEnvironment() {
        Map<String, String> roots = new LinkedHashMap<>();
        for (StaticProgram.RegionRow region : skeletonsFromEnvironment()) {
            if (region.rootMethod.isEmpty()) continue;
            roots.putIfAbsent(region.rootMethod, region.regionId);
        }
        return roots;
    }

    static Set<String> methodsFromEnvironment() {
        Set<String> methods = new LinkedHashSet<>();
        for (StaticProgram.RegionRow region : skeletonsFromEnvironment()) {
            methods.addAll(region.sourcePhaseTraceMethods);
            methods.addAll(region.methods);
        }
        if (methods.isEmpty()) {
            throw new IllegalStateException(
                    "Runtime region skeletons selected no methods: "
                            + configuredFile());
        }
        return methods;
    }

    /** The candidate skeletons' file every weave opens its regions from. */
    static File skeletonFile() {
        return new File(configuredFile());
    }

    /** The candidate skeletons every weave opens its regions from. */
    static List<StaticProgram.RegionRow> skeletonsFromEnvironment() {
        File file = skeletonFile();
        try {
            List<StaticProgram.RegionRow> regions = StaticProgram.regionRows(
                    MapFields.readRows(file),
                    RuntimeSelectedRegionFinalizer.SKELETON_KIND, file);
            for (StaticProgram.RegionRow region : regions) {
                if (region.anchorMethod.isEmpty()) {
                    throw new IllegalArgumentException("REGION_SKELETON "
                            + region.regionId + " states no anchor");
                }
            }
            return regions;
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException(
                    "Cannot read runtime region skeletons from " + file,
                    exception);
        }
    }

    private static String configuredFile() {
        String configured = firstNonBlank(
                System.getProperty("causynth.region.skeletons"));
        if (configured.isEmpty()) {
            throw new IllegalStateException("REGION_STATE requires "
                    + "causynth.region.skeletons");
        }
        return configured;
    }
}
