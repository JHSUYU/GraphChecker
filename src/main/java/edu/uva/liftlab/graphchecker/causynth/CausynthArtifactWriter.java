package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.d3.smt.JsonFields;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.zip.Deflater;
import java.util.zip.GZIPOutputStream;

/** Writes the stable discovery artifact set for one static analysis run. */
final class CausynthArtifactWriter {
    private CausynthArtifactWriter() {
    }

    static void writeDiscoveryArtifacts(Path outputDir,
                                        StaticProgram program)
            throws IOException {
        Files.createDirectories(outputDir);
        Files.write(outputDir.resolve("target_resolved.json"),
                JsonFields.WRITER.toJson(program.targetResolved)
                        .getBytes(StandardCharsets.UTF_8));
        writeGzipJsonl(outputDir.resolve(
                "candidate_dataflow_edges.jsonl.gz"), program.edges);
        writeGzipJsonl(outputDir.resolve("region_skeletons.jsonl.gz"),
                program.regions);
        // Static communication and loop discovery.
        writeGzipJsonl(outputDir.resolve(
                        "communication_call_sites.jsonl.gz"),
                program.communicationCallSites);
        writeGzipJsonl(outputDir.resolve("retained_loops.jsonl.gz"),
                program.retainedLoops);
        writeGzipJsonl(outputDir.resolve("communication_gaps.jsonl.gz"),
                program.communicationGaps);
    }

    private static void writeGzipJsonl(Path output, List<?> values)
            throws IOException {
        try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(new FastGzipOutputStream(
                        Files.newOutputStream(output)),
                        StandardCharsets.UTF_8))) {
            for (Object value : values) {
                writer.write(JsonFields.WRITER.toJson(value));
                // Keep artifact hashes stable across host platforms.
                writer.write('\n');
            }
        }
    }

    /** Discovery artifacts favor iteration speed over maximum compression. */
    private static final class FastGzipOutputStream
            extends GZIPOutputStream {
        private FastGzipOutputStream(OutputStream output)
                throws IOException {
            super(output, 64 * 1024);
            def.setLevel(Deflater.BEST_SPEED);
        }
    }
}
