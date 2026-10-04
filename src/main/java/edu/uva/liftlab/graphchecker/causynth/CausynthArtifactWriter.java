package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.plan.ScopeFrontier;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

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

/**
 * Writes the discovery artifact set of one static analysis run.  Target,
 * call-site and loop rows are not published on their own: they travel in the
 * scope map and {@code region_skeletons}.
 */
final class CausynthArtifactWriter {
    /** The candidate dataflow graph's file in the campaign's output. */
    static final String CANDIDATE_GRAPH = "candidate_dataflow_edges.jsonl.gz";

    private CausynthArtifactWriter() {
    }

    static void writeDiscoveryArtifacts(Path outputDir,
                                        StaticProgram program,
                                        List<JsonObject> staticScopeMap,
                                        List<JsonObject> scopeFrontier,
                                        List<JsonObject> rootDemand)
            throws IOException {
        Files.createDirectories(outputDir);
        writeGzipJsonl(outputDir.resolve(CANDIDATE_GRAPH), program.edges);
        writeGzipJsonl(outputDir.resolve("region_skeletons.jsonl.gz"),
                program.regions);
        writeGzipJsonl(outputDir.resolve("communication_gaps.jsonl.gz"),
                program.communicationGaps);
        // SYMBOL-SCOPE §2.3: plain JSONL for EXPLORE.  Built over the
        // door-woven bodies before any hook is woven, so guard ids share the
        // woven branch sites' numbering.
        ArtifactIO.replaceJsonl(outputDir.resolve(StaticScopeMap.FILE),
                staticScopeMap);
        ArtifactIO.replaceJsonl(outputDir.resolve(ScopeFrontier.FILE),
                scopeFrontier);
        ArtifactIO.replaceJsonl(outputDir.resolve(RootDemand.FILE),
                rootDemand);
    }

    private static void writeGzipJsonl(Path output, List<?> values)
            throws IOException {
        try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(new FastGzipOutputStream(
                        Files.newOutputStream(output)),
                        StandardCharsets.UTF_8))) {
            for (Object value : values) {
                writer.write(JsonFields.WRITER.toJson(value));
                // Not the platform newline: stable hashes.
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
