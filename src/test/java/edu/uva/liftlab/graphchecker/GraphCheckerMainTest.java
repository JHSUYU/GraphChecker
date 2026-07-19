package edu.uva.liftlab.graphchecker;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;

public class GraphCheckerMainTest {
    @Rule
    public final TemporaryFolder temporaryFolder = new TemporaryFolder();

    @Test
    public void wildcardClasspathIsSortedAndDuplicateEntriesAreRemoved()
            throws Exception {
        Path jars = temporaryFolder.newFolder("jars").toPath();
        Path second = Files.createFile(jars.resolve("b.jar"));
        Path first = Files.createFile(jars.resolve("a.jar"));
        String wildcard = jars + File.separator + "*";
        String input = wildcard + File.pathSeparator + second
                + File.pathSeparator + first;

        String expanded = GraphCheckerMain.expandClassPath(input);

        assertEquals(first.toAbsolutePath() + File.pathSeparator
                + second.toAbsolutePath(), expanded);
    }
}
