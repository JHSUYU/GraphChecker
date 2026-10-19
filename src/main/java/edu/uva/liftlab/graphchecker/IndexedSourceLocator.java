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

final class IndexedSourceLocator extends SourceLocator {
    private final Map<String, Set<String>> listings = new ConcurrentHashMap<>();

    IndexedSourceLocator(Singletons.Global global) {
        super(global);
    }

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
