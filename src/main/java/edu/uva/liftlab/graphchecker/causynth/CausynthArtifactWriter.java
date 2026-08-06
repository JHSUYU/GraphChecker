package edu.uva.liftlab.graphchecker.causynth;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.GZIPOutputStream;

/** Writes the stable JSON/JSONL artifact set for one static analysis run. */
final class CausynthArtifactWriter {
    private CausynthArtifactWriter() {
    }

    static void writeDiscoveryArtifacts(Path outputDir,
                                        StaticProgram program)
            throws IOException {
        Files.createDirectories(outputDir);
        writeJson(outputDir.resolve("target_resolved.json"),
                program.targetResolved);
        writeJsonl(outputDir.resolve("candidate_dataflow_edges.jsonl"),
                program.edges);
        Files.deleteIfExists(outputDir.resolve("region_skeletons.jsonl"));
        writeGzipJsonl(outputDir.resolve("region_skeletons.jsonl.gz"),
                program.regions);
        // A fresh discovery run invalidates any regions selected by an older
        // trace. The current trace will repopulate both files during
        // finalization.
        writeJsonl(outputDir.resolve("symbolic_regions.jsonl"),
                Collections.emptyList());
        writeJsonl(outputDir.resolve("symbolic_region_edges.jsonl"),
                Collections.emptyList());
    }

    static void writeRegions(Path regions, Path regionEdges,
                             StaticProgram program) throws IOException {
        Path regionParent = regions.getParent();
        if (regionParent != null) {
            Files.createDirectories(regionParent);
        }
        Path edgeParent = regionEdges.getParent();
        if (edgeParent != null) {
            Files.createDirectories(edgeParent);
        }
        List<Map<String, Object>> canonicalEdges = canonicalRegionEdges(
                program.regionEdges);
        program.regionEdges.clear();
        program.regionEdges.addAll(canonicalEdges);
        writeJsonl(regions, program.regions);
        writeJsonl(regionEdges, program.regionEdges);
    }

    /**
     * The edge id is the canonical semantic identity. Repeated identical
     * payloads are harmless aggregation duplicates; two different payloads
     * under one id are an ambiguous artifact and must fail closed.
     */
    private static List<Map<String, Object>> canonicalRegionEdges(
            List<Map<String, Object>> edges) throws IOException {
        Map<String, Map<String, Object>> byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            String edgeId = edge.get("edgeId") == null ? ""
                    : String.valueOf(edge.get("edgeId"));
            if (edgeId.isEmpty()) {
                throw new IOException("runtime region edge has no edgeId");
            }
            Map<String, Object> previous = byId.putIfAbsent(edgeId, edge);
            if (previous != null && !previous.equals(edge)) {
                throw new IOException("conflicting runtime region edge "
                        + "payload for edgeId " + edgeId);
            }
        }
        return new java.util.ArrayList<>(byId.values());
    }

    private static void writeJson(Path output, Object value)
            throws IOException {
        Files.write(output,
                CausynthJson.write(value).getBytes(StandardCharsets.UTF_8));
    }

    private static void writeJsonl(Path output,
                                   List<?> values)
            throws IOException {
        try (BufferedWriter writer = Files.newBufferedWriter(output,
                StandardCharsets.UTF_8)) {
            for (Object value : values) {
                writer.write(CausynthJson.write(value));
                // Keep artifact hashes stable across host platforms.
                writer.write('\n');
            }
        }
    }

    private static void writeGzipJsonl(Path output, List<?> values)
            throws IOException {
        try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(new GZIPOutputStream(
                        Files.newOutputStream(output)),
                        StandardCharsets.UTF_8))) {
            for (Object value : values) {
                writer.write(CausynthJson.write(value));
                writer.write('\n');
            }
        }
    }
}
