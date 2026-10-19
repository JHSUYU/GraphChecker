package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

final class RegionSkeletonInstrumentationSelection {
    private RegionSkeletonInstrumentationSelection() {
    }

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

    static File skeletonFile() {
        return new File(configuredFile());
    }

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
