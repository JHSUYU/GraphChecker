package edu.uva.liftlab.graphchecker;

import soot.G;
import soot.IFoundFile;
import soot.Singletons;
import soot.SourceLocator;

import java.io.File;
import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Soot's source locator, with each directory of the classpath listed once.
 *
 * <p>Soot looks a class up along its classpath in order, and in a directory
 * by asking whether {@code <dir>/<name>} exists: every class costs one stat
 * in each directory ahead of the entry that holds it, and a JDK or library
 * class misses in every class directory of the case.  On NFS one static pass
 * of an HDFS case made ~197K such failed stats.  Here a lookup first reads
 * the listing of the name's folder ({@code <dir>/a/b} for {@code
 * a/b/C.class}), read once per JVM; a name the listing does not hold is no
 * file there, and one it holds is Soot's own lookup, so a hit is the same
 * {@code FoundFile}.  The classpath order, the archives and the class
 * providers are Soot's.</p>
 */
final class IndexedSourceLocator extends SourceLocator {
    /** The names in each folder looked into, by {@code dir \0 folder}. */
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
        int slash = fileName.lastIndexOf('/');
        String folder = slash < 0 ? "" : fileName.substring(0, slash);
        return listings.computeIfAbsent(dir + '\0' + folder,
                key -> list(new File(dir, folder)))
                .contains(fileName.substring(slash + 1))
                ? super.lookupInDir(dir, fileName) : null;
    }

    /** The names {@code folder} holds; none when it is no directory. */
    private static Set<String> list(File folder) {
        String[] names = folder.list();
        return names == null ? Collections.<String>emptySet()
                : new HashSet<>(Arrays.asList(names));
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
