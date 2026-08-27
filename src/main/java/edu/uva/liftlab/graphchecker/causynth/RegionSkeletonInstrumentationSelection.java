package edu.uva.liftlab.graphchecker.causynth;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/** Methods selected by the runtime region-discovery pass. */
final class RegionSkeletonInstrumentationSelection {
    private RegionSkeletonInstrumentationSelection() {
    }

    static Set<String> methodsFromEnvironment() {
        String configured = firstNonBlank(
                System.getProperty("causynth.region.skeletons"),
                System.getenv("CAUSYNTH_REGION_SKELETONS"), "");
        if (configured.isEmpty()) {
            throw new IllegalStateException("REGION_STATE requires "
                    + "causynth.region.skeletons or "
                    + "CAUSYNTH_REGION_SKELETONS");
        }
        File file = new File(configured);
        Set<String> methods = new LinkedHashSet<>();
        try {
            for (StaticProgram.RegionRow region : StaticProgram.regionRows(
                    MapFields.readRows(file),
                    RuntimeSelectedRegionFinalizer.SKELETON_KIND, file)) {
                if (region.anchorMethod.isEmpty()) {
                    throw new IllegalArgumentException("REGION_SKELETON "
                            + region.regionId + " states no anchor; this "
                            + "reads selected skeletons, not candidates");
                }
                methods.addAll(region.sourcePhaseTraceMethods);
                methods.addAll(region.methods);
            }
        } catch (IOException | RuntimeException exception) {
            throw new IllegalStateException(
                    "Cannot read runtime region skeletons from " + file,
                    exception);
        }
        if (methods.isEmpty()) {
            throw new IllegalStateException(
                    "Runtime region skeletons selected no methods: " + file);
        }
        return methods;
    }
}
