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
     * A system states only where its own hook sits relative to a catalog
     * door: each door a hook names is woven after the hook, with the
     * catalog's kinds, and no door is added or dropped; a hook naming no
     * catalog door, or a door row in a system's file, is refused.
     */
    @Test
    public void aSystemsHooksPlaceCatalogDoorsAndAddNone() throws Exception {
        List<LibraryCatalog.Door> catalog = LibraryCatalog.doors();
        for (String system : new String[]{"hadoop", "solr"}) {
            java.nio.file.Path file = java.nio.file.Paths.get("experiments",
                    system, "doors.jsonl");
            List<LibraryCatalog.Hook> hooks;
            try (BufferedReader reader = java.nio.file.Files
                    .newBufferedReader(file)) {
                hooks = LibraryCatalog.hooks(LibraryCatalog.rows(reader,
                        "doors.jsonl"));
            }
            List<LibraryCatalog.Door> woven =
                    LibraryCatalog.placed(catalog, hooks);
            assertEquals(system, catalog.size(), woven.size());
            for (int at = 0; at < catalog.size(); at++) {
                LibraryCatalog.Door door = catalog.get(at);
                LibraryCatalog.Door placed = woven.get(at);
                LibraryCatalog.Hook hook = null;
                for (LibraryCatalog.Hook each : hooks) {
                    if (each.places(door)) hook = each;
                }
                assertEquals(system + " " + door.method,
                        hook == null ? door.method : hook.method,
                        placed.method);
                assertEquals(door.name(), placed.name());
                assertEquals(door.faults, placed.faults);
            }
        }
        String[][] refused = {
            {"{\"schemaVersion\": 1, \"kind\": \"HOOK\", \"transport\": "
                    + "\"T\", \"direction\": \"SEND\", \"door\": "
                    + "\"<a.B: void none(int)>\", \"method\": \"<a.B: void "
                    + "send(int)>\", \"after\": \"<a.C: void hook()>\"}",
                    "names no catalog door"},
            {DOOR + "}", "never a door"}};
        for (String[] row : refused) {
            try {
                LibraryCatalog.placed(catalog,
                        LibraryCatalog.hooks(rows(row[0])));
                fail("accepted " + row[0]);
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage(),
                        expected.getMessage().contains(row[1]));
            }
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
