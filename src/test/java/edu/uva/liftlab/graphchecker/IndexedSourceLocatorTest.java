package edu.uva.liftlab.graphchecker;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;
import soot.IFoundFile;
import soot.Singletons;
import soot.SourceLocator;

import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

/** A directory lookup answers as Soot's own does, from its folder's listing. */
public class IndexedSourceLocatorTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @After
    public void reset() {
        G.reset();
    }

    @Test
    public void answersAsSootDoes() throws Exception {
        Path dir = folder.getRoot().toPath();
        Files.createDirectories(dir.resolve("a/b"));
        Files.write(dir.resolve("a/b/C.class"), new byte[]{1});
        Files.write(dir.resolve("a.b.D.jimple"), new byte[]{1});
        Files.createSymbolicLink(dir.resolve("a/b/L.class"),
                dir.resolve("a/b/C.class"));
        Files.createSymbolicLink(dir.resolve("a/b/Gone.class"),
                dir.resolve("a/b/Missing.class"));
        G.reset();
        IndexedSourceLocator.install();
        IndexedSourceLocator indexed = (IndexedSourceLocator) SourceLocator.v();
        SootOwn own = new SootOwn(global());
        String root = dir.toString();
        for (String name : new String[]{"a/b/C.class", "a/b/L.class",
                "a.b.D.jimple", "a/b/Missing.class", "a/b/Gone.class",
                "java/lang/String.class", "C.class", "a/b"}) {
            assertEquals(name, path(own.at(root, name)),
                    path(indexed.lookupInDir(root, name)));
        }
        assertSame(indexed, SourceLocator.v());
    }

    private static String path(IFoundFile found) {
        return found == null ? null : found.getFile().getPath();
    }

    private static Singletons.Global global() throws Exception {
        Field g = Singletons.class.getDeclaredField("g");
        g.setAccessible(true);
        return (Singletons.Global) g.get(G.v());
    }

    /** Soot's own directory lookup. */
    private static final class SootOwn extends SourceLocator {
        SootOwn(Singletons.Global global) {
            super(global);
        }

        IFoundFile at(String dir, String name) {
            return lookupInDir(dir, name);
        }
    }
}
