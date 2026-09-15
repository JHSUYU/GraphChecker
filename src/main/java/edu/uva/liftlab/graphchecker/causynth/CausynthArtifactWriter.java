package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;

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
 * Writes the stable discovery artifact set for one static analysis run.
 *
 * <p>Three files it used to write are gone, because nothing read their
 * CONTENT: {@code target_resolved.json} (the declared target method, which
 * the static scope map's TARGET_SITE row already names),
 * {@code communication_call_sites.jsonl.gz} (20 bytes and 0 rows on 17960)
 * and {@code retained_loops.jsonl.gz} (whose rows travel inside
 * {@code region_skeletons}).  The in-process data behind all three is
 * untouched -- {@code StaticProgram.targetResolved} feeds
 * {@code SymbolicRegionPlanner:78} and {@code CausynthPipeline:308,373},
 * {@code communicationCallSites} feeds {@code SymbolicRegionPlanner:227,358}
 * and {@code retainedLoops} feeds {@code SymbolicRegionPlanner:158-163} --
 * only the publication is.</p>
 */
final class CausynthArtifactWriter {
    private CausynthArtifactWriter() {
    }

    static void writeDiscoveryArtifacts(Path outputDir,
                                        StaticProgram program,
                                        List<JsonObject> staticScopeMap)
            throws IOException {
        Files.createDirectories(outputDir);
        writeGzipJsonl(outputDir.resolve(
                "candidate_dataflow_edges.jsonl.gz"), program.edges);
        writeGzipJsonl(outputDir.resolve("region_skeletons.jsonl.gz"),
                program.regions);
        writeGzipJsonl(outputDir.resolve("communication_gaps.jsonl.gz"),
                program.communicationGaps);
        // CLOSURE-V2 SS4: what the slice knows about the sites the target's
        // demand can reach, for EXPLORE to join the recording against.  Plain
        // JSONL and small (one row per site), because the stage that reads it
        // reads nothing else of the static analysis.  Built by the caller,
        // BEFORE any weaving: a guard id has to be in the same unit numbering
        // as the branch site the instrumentation wove.
        ArtifactIO.replaceJsonl(outputDir.resolve(StaticScopeMap.FILE),
                staticScopeMap);
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
