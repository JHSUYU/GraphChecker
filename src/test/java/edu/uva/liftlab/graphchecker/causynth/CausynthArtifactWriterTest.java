package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.BufferedReader;
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
    public void discoveryWritesCandidateSkeletonsAsGzip() throws Exception {
        Path output = temporary.newFolder("artifacts").toPath();
        StaticProgram program = new StaticProgram();
        Map<String, Object> skeleton = new LinkedHashMap<>();
        skeleton.put("schemaVersion", 2);
        skeleton.put("kind", "REGION_SKELETON");
        skeleton.put("regionId", "REGION.0");
        program.regions.add(skeleton);

        CausynthArtifactWriter.writeDiscoveryArtifacts(output, program);

        Path gzip = output.resolve("region_skeletons.jsonl.gz");
        assertTrue(Files.isRegularFile(gzip));
        assertFalse(Files.exists(output.resolve("region_skeletons.jsonl")));
        try (BufferedReader reader = new BufferedReader(
                new InputStreamReader(new GZIPInputStream(
                        Files.newInputStream(gzip)),
                        StandardCharsets.UTF_8))) {
            assertEquals(CausynthJson.write(skeleton), reader.readLine());
            assertEquals(null, reader.readLine());
        }
    }
}
