package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.Gson;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class RegionSkeletonInstrumentationSelectionTest {
    private static final Gson GSON = new Gson();

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void configuredSourcePhaseHelperJoinsRichTraceScope()
            throws Exception {
        String root = "<example.Root: void run()>";
        String anchor = "<example.Target: void fail()>";
        String phaseHelper = "<example.Keys: void rotate()>";
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 3);
        row.put("kind", "REGION_SKELETON");
        row.put("regionId", "REGION.1");
        row.put("rootMethod", root);
        row.put("anchorMethod", anchor);
        row.put("methods", Arrays.asList(root, anchor));
        row.put(ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD,
                Arrays.asList(phaseHelper));
        File skeletons = folder.newFile("region-skeletons.jsonl");
        Files.write(skeletons.toPath(), Arrays.asList(GSON.toJson(row)),
                StandardCharsets.UTF_8);

        String property = "causynth.region.skeletons";
        String prior = System.getProperty(property);
        try {
            System.setProperty(property, skeletons.getAbsolutePath());
            Set<String> methods = RegionSkeletonInstrumentationSelection
                    .methodsFromEnvironment();
            assertEquals(3, methods.size());
            assertTrue(methods.contains(root));
            assertTrue(methods.contains(anchor));
            assertTrue(methods.contains(phaseHelper));
        } finally {
            if (prior == null) System.clearProperty(property);
            else System.setProperty(property, prior);
        }
    }
}
