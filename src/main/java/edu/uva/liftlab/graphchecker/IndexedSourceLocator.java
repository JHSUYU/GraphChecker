package edu.uva.liftlab.graphchecker;

import soot.FoundFile;
import soot.G;
import soot.IFoundFile;
import soot.Singletons;
import soot.SourceLocator;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.file.FileVisitOption;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Soot's source locator, with each classpath directory listed once.
 *
 * <p>Soot looks a class up along its classpath in order, and in a directory
 * by asking whether {@code <dir>/<name>} exists: every class costs one stat
 * in each directory ahead of the entry that holds it, and a JDK or library
 * class misses in every class directory of the case.  On NFS one static pass
 * of an HDFS case made ~197K such failed stats.  This locator walks a
 * directory the first time Soot looks into it and answers every later
 * lookup there from that listing.  The rest is Soot's own: the classpath
 * order, the archives, the class providers, and the {@code FoundFile} a hit
 * returns.</p>
 */
final class IndexedSourceLocator extends SourceLocator {
    /** Each directory's files, by their path under it ({@code /}-separated). */
    private final Map<String, Set<String>> listings = new ConcurrentHashMap<>();

    IndexedSourceLocator(Singletons.Global global) {
        super(global);
    }

    /** Makes this Soot's source locator, before anything looks a class up. */
    static void install() {
        Field locator = field("instance_soot_SourceLocator");
        Field global = field("g");
        try {
            if (locator.get(G.v()) != null) {
                throw new IllegalStateException("Soot's own source locator "
                        + "ran before the indexed one was installed");
            }
            locator.set(G.v(), new IndexedSourceLocator(
                    (Singletons.Global) global.get(G.v())));
        } catch (IllegalAccessException refused) {
            throw new IllegalStateException(
                    "cannot install the indexed source locator", refused);
        }
    }

    @Override
    protected IFoundFile lookupInDir(String dir, String fileName) {
        return listings.computeIfAbsent(dir, IndexedSourceLocator::list)
                .contains(fileName)
                ? new FoundFile(new File(dir, fileName)) : null;
    }

    /**
     * Every file under {@code dir}, as Soot's {@code File#exists} sees it:
     * links followed, a link whose target is gone left out.  A directory that
     * cannot be walked stops the pass by name.
     */
    private static Set<String> list(String dir) {
        Path root = Paths.get(dir);
        Set<String> files = new HashSet<>();
        try {
            Files.walkFileTree(root, EnumSet.of(FileVisitOption.FOLLOW_LINKS),
                    Integer.MAX_VALUE, new SimpleFileVisitor<Path>() {
                        @Override
                        public FileVisitResult visitFile(Path file,
                                                         BasicFileAttributes attributes) {
                            if (!attributes.isSymbolicLink()) {
                                files.add(root.relativize(file).toString()
                                        .replace(File.separatorChar, '/'));
                            }
                            return FileVisitResult.CONTINUE;
                        }
                    });
        } catch (IOException failure) {
            throw new IllegalStateException("cannot list the classpath "
                    + "directory " + dir, failure);
        }
        return Collections.unmodifiableSet(files);
    }

    private static Field field(String name) {
        try {
            Field field = Singletons.class.getDeclaredField(name);
            field.setAccessible(true);
            return field;
        } catch (NoSuchFieldException missing) {
            throw new IllegalStateException("this Soot has no Singletons."
                    + name, missing);
        }
    }
}
