package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.TracedRows;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A recording whose rows the weave pruned is aggregated only over the static
 * artifacts the weave decided them on, and by the row rule it traced by:
 * over others, a site or port they add would find no rows and say nothing,
 * and an older rule's recording lacks rows the aggregation reads.
 */
public class TracedRowsDigestTest {
    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void aPrunedRecordingIsAggregatedOverItsOwnArtifactsOnly()
            throws IOException {
        File scopeMap = file("static_scope_map.jsonl", "{\"kind\":\"A\"}\n");
        File graph = file("candidate_dataflow_edges.jsonl.gz", "g");
        File skeletons = file("region_skeletons.jsonl.gz", "s");
        String own = TracedRows.inputsDigest(scopeMap, graph, skeletons);
        File other = file("other_scope_map.jsonl", "{\"kind\":\"B\"}\n");
        String others = TracedRows.inputsDigest(other, graph, skeletons);
        assertTrue("another scope map is another digest", !own.equals(others));
        // A recording traced before the rule was part of the digest (before
        // the storing calls' argument rows): its artifacts alone.
        String unruled = ArtifactIO.sha256(ArtifactIO.sha256(
                scopeMap.toPath()) + "\n" + ArtifactIO.sha256(graph.toPath())
                + "\n" + ArtifactIO.sha256(skeletons.toPath()));
        Object[][] rows = {
            // manifest schema, its tracedRows, refused
            {1, null, false},     // a recording that wrote every row
            {2, own, false},
            {2, others, true},
            {2, "", true},        // a pruned recording stating no digest
            {2, unruled, true},   // traced by an older row rule
        };
        for (Object[] row : rows) {
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", (Integer) row[0]);
            if (row[1] != null) manifest.addProperty("tracedRows",
                    (String) row[1]);
            try {
                CausynthTraceRecorder.requireTracedOver(manifest, scopeMap,
                        graph, skeletons);
                assertEquals(manifest.toString(), false, row[2]);
            } catch (IOException refused) {
                assertTrue(manifest + ": " + refused.getMessage(),
                        (Boolean) row[2] && refused.getMessage()
                                .startsWith("TRACED_ROWS_MISMATCH"));
            }
        }
    }

    private File file(String name, String text) throws IOException {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), text.getBytes(StandardCharsets.UTF_8));
        return file;
    }
}
