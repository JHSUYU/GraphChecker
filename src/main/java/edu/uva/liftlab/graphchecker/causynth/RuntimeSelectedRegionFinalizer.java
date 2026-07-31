package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * Completes symbolic regions after a discovery trace has selected their
 * concrete roots.
 */
public final class RuntimeSelectedRegionFinalizer {
    private static final Type ROW_TYPE =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();

    private RuntimeSelectedRegionFinalizer() {
    }

    public static void finalizeRegions(
            File staticGraph, File regions, File regionEdges,
            Collection<String> observedMethods) throws IOException {
        finalizeRegions(staticGraph, regions, regionEdges, observedMethods,
                false, false);
    }

    /**
     * Emits runtime-selectable regions with cheap, incomplete REGION.IN
     * candidates, without constructing concolic output slices or
     * materialization metadata.
     */
    public static void finalizeInventory(
            File staticGraph, File regions, File regionEdges,
            Collection<String> observedMethods) throws IOException {
        finalizeRegions(staticGraph, regions, regionEdges, observedMethods,
                true, false);
    }

    /**
     * Emits only selected region roots and member methods.  REGION.IN/OUT and
     * region edges are deferred until concrete runtime activations are known.
     */
    public static void finalizeSkeletons(
            File staticGraph, File regions, File regionEdges,
            Collection<String> observedMethods) throws IOException {
        finalizeRegions(staticGraph, regions, regionEdges, observedMethods,
                true, true);
    }

    private static void finalizeRegions(
            File staticGraph, File regions, File regionEdges,
            Collection<String> observedMethods,
            boolean inventoryOnly, boolean skeletonOnly) throws IOException {
        StaticProgram program = new StaticProgram();
        program.edges.addAll(readJsonl(staticGraph));
        try {
            if (skeletonOnly) {
                SymbolicRegionPlanner.planSelectedSkeleton(program,
                        observedMethods);
            } else if (inventoryOnly) {
                SymbolicRegionPlanner.planSelectedInventory(program,
                        observedMethods);
            } else {
                SymbolicRegionPlanner.planSelected(program, observedMethods);
            }
        } catch (IllegalArgumentException invalidPlan) {
            throw new IOException("Invalid runtime-selected region plan",
                    invalidPlan);
        }
        CausynthArtifactWriter.writeRegions(regions.toPath(),
                regionEdges.toPath(), program);
    }

    private static List<Map<String, Object>> readJsonl(File input)
            throws IOException {
        List<Map<String, Object>> rows = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(input.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                try {
                    Map<String, Object> row = GSON.fromJson(trimmed,
                            ROW_TYPE);
                    if (row == null) {
                        throw new IllegalArgumentException("null row");
                    }
                    rows.add(row);
                } catch (RuntimeException malformed) {
                    throw new IOException("Malformed static graph "
                            + input + ":" + lineNumber, malformed);
                }
            }
        }
        return rows;
    }
}
