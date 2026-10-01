package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * SYMBOL-SCOPE §4.2: the engine's library catalog -- its doors, one
 * transport direction's library lines as one door method -- and the rows it
 * refuses by name.
 */
public class LibraryCatalogTest {
    private static final String IPC = "<org.apache.hadoop.ipc.Client: "
            + "org.apache.hadoop.io.Writable getRpcResponse(";
    private static final String DOOR = "{\"schemaVersion\": 1, \"kind\": "
            + "\"DOOR\", \"transport\": \"T\", \"direction\": \"SEND\", "
            + "\"method\": \"<a.B: void send(int)>\", \"before\": "
            + "\"<a.C: void flush()>\", \"faults\": [\"java.io.IOException\"]";
    private static final String CONFIG = "{\"schemaVersion\": 1, \"kind\": "
            + "\"CONFIG_SOURCE\", \"method\": \"<a.Conf: int getInt("
            + "java.lang.String,int)>\"";

    @Test
    public void theShippedCatalogNamesEachLibraryDoorOnce() {
        List<String> transports = new ArrayList<>(LibraryCatalog.transports());
        assertEquals(Arrays.asList("HADOOP_IPC", "HDFS_SASL",
                "HDFS_DATA_TRANSFER", "SOLR_HTTP", "SOLR_HTTP2", "ZOOKEEPER"),
                transports);
        LinkedHashSet<String> response = new LinkedHashSet<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.method.startsWith(IPC)) {
                response.add(door.doorMethod());
                assertEquals("org.apache.hadoop.ipc.Client", door.family());
            }
        }
        // trunk's and 3.4's signatures are one door method.
        assertEquals(Arrays.asList("FAULT:HADOOP_IPC:RESPONSE at "
                        + "org.apache.hadoop.ipc.Client#getRpcResponse"),
                new ArrayList<>(response));
    }

    /**
     * A system's own doors replace the catalog's of their transport and
     * direction, and only those: each system file names catalog doors, and
     * parses as the catalog does.
     */
    @Test
    public void aSystemsDoorsReplaceTheCatalogsOfTheirTransport()
            throws Exception {
        List<LibraryCatalog.Door> catalog = LibraryCatalog.doors();
        for (String system : new String[]{"hadoop", "solr"}) {
            java.nio.file.Path file = java.nio.file.Paths.get("experiments",
                    system, "doors.jsonl");
            List<LibraryCatalog.Door> own;
            try (BufferedReader reader = java.nio.file.Files
                    .newBufferedReader(file)) {
                own = LibraryCatalog.doors(LibraryCatalog.rows(reader,
                        "doors.jsonl"));
            }
            LinkedHashSet<String> named = new LinkedHashSet<>();
            for (LibraryCatalog.Door door : own) named.add(door.name());
            List<LibraryCatalog.Door> woven =
                    LibraryCatalog.overridden(catalog, own);
            for (LibraryCatalog.Door door : catalog) {
                assertEquals(system + " " + door.method,
                        !named.contains(door.name()), woven.contains(door));
            }
            for (String name : named) {
                boolean known = false;
                for (LibraryCatalog.Door door : catalog) {
                    known |= door.name().equals(name);
                }
                assertTrue(system + " overrides no catalog door " + name,
                        known);
            }
            assertTrue(woven.containsAll(own));
        }
    }

    @Test
    public void aMalformedRowIsRefusedByName() {
        String[][] refused = {
            {DOOR + ", \"schemaVersion\": 2}", "states schemaVersion 2"},
            {"{\"schemaVersion\": 1, \"kind\": \"CODEC\"}", "kind CODEC"},
            {DOOR + ", \"library\": \"a.B\"}", "DOOR has no member library"},
            {DOOR + ", \"after\": \"<a.C: void flush()>\"}",
                    "one of before and after"},
            {DOOR.replace("[\"java.io.IOException\"]", "[]") + "}",
                    "faults lists"},
            {DOOR.replace("\"T\"", "\"t\"") + "}", "transport is no"},
            {CONFIG + ", \"keyArg\": 1}", "keyArg names the String"},
            {CONFIG + ", \"keyArg\": 2}", "keyArg is an argument index"},
            {CONFIG + ", \"keyArg\": 0, \"defaultArg\": 0}", "defaultArg"},
            {CONFIG + ", \"keyArg\": 0}\n" + CONFIG + ", \"keyArg\": 0}",
                    "is stated again; first at t.jsonl:1"},
        };
        for (String[] row : refused) {
            try {
                LibraryCatalog.doors(rows(row[0]));
                fail("accepted " + row[0]);
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .startsWith("library catalog at t.jsonl:")
                        && expected.getMessage().contains(row[1]));
            }
        }
        assertEquals(1, LibraryCatalog.doors(rows(DOOR + "}\n" + CONFIG
                + ", \"keyArg\": 0, \"defaultArg\": 1}")).size());
    }

    private static Map<String, JsonObject> rows(String text) {
        try {
            return LibraryCatalog.rows(new BufferedReader(
                    new StringReader(text)), "t.jsonl");
        } catch (java.io.IOException impossible) {
            throw new AssertionError(impossible);
        }
    }
}
