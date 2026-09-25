package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/**
 * The candidate region skeletons every weave opens its regions from.
 *
 * <p>Candidates, not the regions a run turned out to exercise: the recording
 * is woven before it runs, and the replay has to stand on the same frame
 * stack, so the frame set is a static fact.  Which candidates the recording
 * exercised is read off its trace afterwards and decides only which regions
 * are planned.</p>
 */
final class RegionSkeletonInstrumentationSelection {
    private RegionSkeletonInstrumentationSelection() {
    }

    /**
     * The region each selected ROOT method opens, for the recording's
     * execution index.
     *
     * <p>The recording pushes an index frame where the replay pushes one --
     * at a region activation (IDENTITY-IMPL B; {@code
     * ConcolicRegionRuntime.enterRegionFrame}) -- so the trace has to know
     * which of the methods it traces is a root.  It is the same file the
     * concolic pass reads its roots from, so the two passes cannot select
     * different roots.</p>
     */
    static Map<String, String> regionRootsFromEnvironment() {
        Map<String, String> roots = new LinkedHashMap<>();
        for (StaticProgram.RegionRow region : selectedSkeletons()) {
            if (region.rootMethod.isEmpty()) continue;
            roots.putIfAbsent(region.rootMethod, region.regionId);
        }
        return roots;
    }

    static Set<String> methodsFromEnvironment() {
        Set<String> methods = new LinkedHashSet<>();
        for (StaticProgram.RegionRow region : selectedSkeletons()) {
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

    /** The selected skeletons of the configured file. */
    private static List<StaticProgram.RegionRow> selectedSkeletons() {
        File file = new File(configuredFile());
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
                System.getProperty("causynth.region.skeletons"),
                System.getenv("CAUSYNTH_REGION_SKELETONS"), "");
        if (configured.isEmpty()) {
            throw new IllegalStateException("REGION_STATE requires "
                    + "causynth.region.skeletons or "
                    + "CAUSYNTH_REGION_SKELETONS");
        }
        return configured;
    }
}
