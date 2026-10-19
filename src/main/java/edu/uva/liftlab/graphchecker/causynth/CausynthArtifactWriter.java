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

final class CausynthArtifactWriter {
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
                writer.write('\n');
            }
        }
    }

    private static final class FastGzipOutputStream
            extends GZIPOutputStream {
        private FastGzipOutputStream(OutputStream output)
                throws IOException {
            super(output, 64 * 1024);
            def.setLevel(Deflater.BEST_SPEED);
        }
    }
}
