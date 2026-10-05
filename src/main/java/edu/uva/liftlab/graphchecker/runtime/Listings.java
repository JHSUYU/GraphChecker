package edu.uva.liftlab.graphchecker.runtime;

import java.io.File;
import java.io.FileFilter;
import java.io.FilenameFilter;
import java.util.Arrays;

/**
 * A directory listing in one order in every run (SYMBOL-SCOPE §4.5): the weave
 * calls these in place of {@code java.io.File}'s listings ({@code
 * CausynthPipeline#replaceListing}), in both passes, and each returns the
 * listing sorted by name.  The JDK leaves the order unspecified and a file
 * system lists in its own (ext4: hash order, which differs per file system
 * and per directory name), so a recording in one host's /tmp and its replay in
 * another's /localtmp walked a copied tree in different orders: the shell
 * commands each copied file issued, and so the start counts of the threads
 * they started, moved between the two runs (hdfs-adhoc-24/26/37, round HG7R:
 * 72-89 schedule give-ups where HG5A, recorded and replayed on one file
 * system, had 8-32).
 */
public final class Listings {
    private Listings() {
    }

    public static String[] list(File directory) {
        return sorted(directory.list());
    }

    public static String[] list(File directory, FilenameFilter filter) {
        return sorted(directory.list(filter));
    }

    public static File[] listFiles(File directory) {
        return sorted(directory.listFiles());
    }

    public static File[] listFiles(File directory, FileFilter filter) {
        return sorted(directory.listFiles(filter));
    }

    public static File[] listFiles(File directory, FilenameFilter filter) {
        return sorted(directory.listFiles(filter));
    }

    /** A listing is null when the directory cannot be read: as listed. */
    private static <T extends Comparable<? super T>> T[] sorted(T[] entries) {
        if (entries != null) Arrays.sort(entries);
        return entries;
    }
}
