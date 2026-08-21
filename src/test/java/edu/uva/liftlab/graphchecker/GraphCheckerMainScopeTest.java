package edu.uva.liftlab.graphchecker;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class GraphCheckerMainScopeTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void staticScopeExcludesEveryTestClassOutput()
            throws Exception {
        Path production = folder.newFolder("target", "classes").toPath();
        Path tests = folder.newFolder("target", "test-classes").toPath();

        List<String> productionDirs = new ArrayList<>();
        List<String> testDirs = new ArrayList<>();
        GraphCheckerMain.splitProcessDirs(Arrays.asList(
                production.toString(), tests.toString()),
                productionDirs, testDirs);
        assertEquals(Arrays.asList(production.toFile().getAbsolutePath()),
                productionDirs);
        assertEquals(Arrays.asList(tests.toFile().getAbsolutePath()),
                testDirs);
    }
}
