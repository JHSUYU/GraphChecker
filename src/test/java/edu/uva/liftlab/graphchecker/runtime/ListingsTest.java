package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import org.junit.Test;

/** A listing comes back sorted by name, whatever order the file system
 *  keeps (SYMBOL-SCOPE §4.5); a directory that cannot be listed stays null. */
public class ListingsTest {
    @Test
    public void everyListingIsSortedByName() throws IOException {
        File directory = Files.createTempDirectory("listings").toFile();
        try {
            for (String name : new String[] {"VERSION", "BP-9-127.0.0.1-7",
                    "BP-10-127.0.0.1-3", "current"}) {
                new File(directory, name).createNewFile();
            }
            String[] names = {"BP-10-127.0.0.1-3", "BP-9-127.0.0.1-7",
                    "VERSION", "current"};
            assertArrayEquals(names, Listings.list(directory));
            assertArrayEquals(names, Listings.list(directory, (d, n) -> true));
            File[] files = new File[names.length];
            for (int i = 0; i < names.length; i++) {
                files[i] = new File(directory, names[i]);
            }
            assertArrayEquals(files, Listings.listFiles(directory));
            assertArrayEquals(files, Listings.listFiles(directory,
                    (java.io.FileFilter) f -> true));
            assertArrayEquals(files, Listings.listFiles(directory,
                    (java.io.FilenameFilter) (d, n) -> true));
            assertNull(Listings.list(new File(directory, "missing")));
        } finally {
            for (File file : directory.listFiles()) file.delete();
            directory.delete();
        }
    }
}
