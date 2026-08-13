package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.zip.GZIPInputStream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CausynthArtifactWriterTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void discoveryWritesLargeGraphsAsGzipWithoutPlaceholders()
            throws Exception {
        Path output = temporary.newFolder("artifacts").toPath();
        StaticProgram program = new StaticProgram();
        Map<String, Object> skeleton = new LinkedHashMap<>();
        skeleton.put("schemaVersion", 3);
        skeleton.put("kind", "REGION_SKELETON");
        skeleton.put("regionId", "REGION.0");
        program.regions.add(skeleton);
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("id", "DF.0");
        program.edges.add(edge);

        CausynthArtifactWriter.writeDiscoveryArtifacts(output, program);

        Path skeletonGzip = output.resolve("region_skeletons.jsonl.gz");
        Path candidateGzip = output.resolve(
                "candidate_dataflow_edges.jsonl.gz");
        assertTrue(Files.isRegularFile(candidateGzip));
        assertFalse(Files.exists(output.resolve(
                "candidate_dataflow_edges.jsonl")));
        assertTrue(Files.isRegularFile(skeletonGzip));
        assertFalse(Files.exists(output.resolve("region_skeletons.jsonl")));
        assertFalse(Files.exists(output.resolve("symbolic_regions.jsonl")));
        assertFalse(Files.exists(output.resolve(
                "symbolic_region_edges.jsonl")));
        try (BufferedReader reader = new BufferedReader(
                new InputStreamReader(new GZIPInputStream(
                        Files.newInputStream(skeletonGzip)),
                        StandardCharsets.UTF_8))) {
            assertEquals(CausynthJson.write(skeleton), reader.readLine());
            assertEquals(null, reader.readLine());
        }
        try (BufferedReader reader = new BufferedReader(
                new InputStreamReader(new GZIPInputStream(
                        Files.newInputStream(candidateGzip)),
                        StandardCharsets.UTF_8))) {
            assertEquals(CausynthJson.write(edge), reader.readLine());
            assertEquals(null, reader.readLine());
        }
    }

    @Test
    public void regionWriterDeduplicatesIdenticalCanonicalEdges()
            throws Exception {
        Path output = temporary.newFolder("region-edges").toPath();
        StaticProgram program = new StaticProgram();
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("edgeId", "EDGE.1");
        edge.put("fromPort", "REGION.a.out.1");
        edge.put("toPort", "REGION.b.in.1");
        program.regionEdges.add(edge);
        program.regionEdges.add(new LinkedHashMap<>(edge));

        Path regions = output.resolve("regions.jsonl");
        Path edges = output.resolve("edges.jsonl");
        CausynthArtifactWriter.writeRegions(regions, edges, program);

        assertEquals(1, Files.readAllLines(edges,
                StandardCharsets.UTF_8).size());
        assertEquals(1, program.regionEdges.size());
    }

    @Test
    public void regionWriterRejectsConflictingCanonicalEdgePayloads()
            throws Exception {
        Path output = temporary.newFolder("conflicting-edges").toPath();
        StaticProgram program = new StaticProgram();
        Map<String, Object> first = new LinkedHashMap<>();
        first.put("edgeId", "EDGE.1");
        first.put("writerOccurrence", 1);
        Map<String, Object> conflicting = new LinkedHashMap<>(first);
        conflicting.put("writerOccurrence", 2);
        program.regionEdges.add(first);
        program.regionEdges.add(conflicting);

        try {
            CausynthArtifactWriter.writeRegions(
                    output.resolve("regions.jsonl"),
                    output.resolve("edges.jsonl"), program);
            throw new AssertionError("conflicting edge must fail closed");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("EDGE.1"));
        }
    }
}
