package edu.uva.liftlab.graphchecker.causynth;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/** Writes the stable JSON/JSONL artifact set for one static analysis run. */
final class CausynthArtifactWriter {
    private CausynthArtifactWriter() {
    }

    static void write(Path outputDir, StaticProgram program)
            throws IOException {
        Files.createDirectories(outputDir);
        writeJson(outputDir.resolve("target_resolved.json"),
                program.targetResolved);
        writeJsonl(outputDir.resolve("static_dataflow_edges.jsonl"),
                program.edges);
        writeRegions(outputDir.resolve("symbolic_regions.jsonl"),
                outputDir.resolve("symbolic_region_edges.jsonl"), program);
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
        writeJsonl(regions, program.regions);
        writeJsonl(regionEdges, program.regionEdges);
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
}
