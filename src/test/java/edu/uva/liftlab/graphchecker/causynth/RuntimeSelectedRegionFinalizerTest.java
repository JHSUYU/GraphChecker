package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeSelectedRegionFinalizerTest {
    @Test
    public void finalizeSkeletonsWritesNoStateInterfaceOrRegionEdges()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            String method = "<example.Box: int compute()>";
            Path graph = folder.getRoot().toPath().resolve("graph.jsonl");
            Path regions = folder.getRoot().toPath().resolve("regions.jsonl");
            Path edges = folder.getRoot().toPath().resolve("edges.jsonl");
            String row = "{"
                    + "\"schemaVersion\":2,"
                    + "\"id\":\"DF.0\","
                    + "\"kind\":\"exception_guard\","
                    + "\"transferKind\":\"GUARD\","
                    + "\"semanticMode\":\"ASSERTABLE\","
                    + "\"relation\":\"taint_depends_on\","
                    + "\"fromCell\":\"" + method + ".param0:int\","
                    + "\"toCell\":\"" + method
                    + "#u9#exception:example.Failure\","
                    + "\"method\":\"" + method + "\","
                    + "\"siteId\":\"" + method + "#u9\","
                    + "\"unitIndex\":9,"
                    + "\"unit\":\"if p0 == 0 goto return\"}"
                    + System.lineSeparator();
            Files.write(graph, row.getBytes(StandardCharsets.UTF_8));

            RuntimeSelectedRegionFinalizer.finalizeSkeletons(
                    graph.toFile(), regions.toFile(), edges.toFile(),
                    Collections.singleton(method));

            String output = new String(Files.readAllBytes(regions),
                    StandardCharsets.UTF_8);
            assertTrue(output.contains("\"kind\":\"REGION_SKELETON\""));
            assertTrue(output.contains(
                    "\"planningMode\":\"REGION_SKELETON_ONLY\""));
            assertFalse(output.contains("symbolicInputs"));
            assertEquals(0, Files.size(edges));
        } finally {
            folder.delete();
        }
    }

}
