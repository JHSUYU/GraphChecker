package edu.uva.liftlab.graphchecker.causynth;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.List;
import java.util.Map;

/** Writes the stable JSON/JSONL artifact set for one static analysis run. */
final class CausynthArtifactWriter {
    private final Path outputDir;
    private final CausynthAnalysisResult result;

    CausynthArtifactWriter(Path outputDir, CausynthAnalysisResult result) {
        this.outputDir = outputDir;
        this.result = result;
    }

    void writeAll() throws IOException {
        Files.createDirectories(outputDir);
        writeJson("target_resolved.json", result.targetResolved);
        writeJsonl("static_dataflow_edges.jsonl", result.edges);
        writeJsonl("symbolic_regions.jsonl", result.symbolicRegions);
        writeJsonl("symbolic_region_edges.jsonl", result.symbolicRegionEdges);
    }

    private void writeJson(String fileName, Object value) throws IOException {
        Files.write(outputDir.resolve(fileName),
                CausynthJson.write(value).getBytes(StandardCharsets.UTF_8));
    }

    private void writeJsonl(String fileName,
                            List<Map<String, Object>> values)
            throws IOException {
        Path output = outputDir.resolve(fileName);
        try (BufferedWriter writer = Files.newBufferedWriter(output,
                StandardCharsets.UTF_8,
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE)) {
            for (Object value : values) {
                writer.write(CausynthJson.write(value));
                // Keep artifact hashes stable across host platforms.
                writer.write('\n');
            }
        }
    }
}
