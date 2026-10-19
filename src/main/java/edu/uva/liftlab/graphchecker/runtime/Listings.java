package edu.uva.liftlab.graphchecker.runtime;

import java.io.File;
import java.io.FileFilter;
import java.io.FilenameFilter;
import java.util.Arrays;

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

    private static <T extends Comparable<? super T>> T[] sorted(T[] entries) {
        if (entries != null) Arrays.sort(entries);
        return entries;
    }
}
