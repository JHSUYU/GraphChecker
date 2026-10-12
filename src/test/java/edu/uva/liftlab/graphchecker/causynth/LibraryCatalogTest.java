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
    /** A door at every call of its anchor: no method. */
    private static final String AT_CALLS = DOOR.replace(
            "\"method\": \"<a.B: void send(int)>\", ", "");
    private static final String CONFIG = "{\"schemaVersion\": 1, \"kind\": "
            + "\"CONFIG_SOURCE\", \"method\": \"<a.Conf: int getInt("
            + "java.lang.String,int)>\"";

    @Test
    public void theShippedCatalogNamesEachLibraryDoorOnce() {
        List<String> transports = new ArrayList<>(LibraryCatalog.transports());
        assertEquals(Arrays.asList("HADOOP_IPC", "HDFS_SASL",
                "HDFS_DATA_TRANSFER", "SOLR_HTTP", "SOLR_HTTP2", "ZOOKEEPER",
                "LOCAL_IO", "TIMED_WAIT"), transports);
        // A local file operation is a door only at the calls the root
        // demand chose, before the call; it throws the kind the JDK call
        // declares, or returns its failing result.
        LibraryCatalog.Door open = LibraryCatalog.demandedDoor(
                "<java.io.FileOutputStream: void <init>(java.io.File)>");
        LibraryCatalog.Door rename = LibraryCatalog.demandedDoor(
                "<java.io.File: boolean renameTo(java.io.File)>");
        assertEquals("FAULT:LOCAL_IO:OPEN [java.io.FileNotFoundException] "
                        + "NONE false; FAULT:LOCAL_IO:NAMESPACE [] FALSE",
                open.name() + " " + open.faults + " " + open.result + " "
                        + open.after + "; " + rename.name() + " "
                        + rename.faults + " " + rename.result);
        assertEquals(null, LibraryCatalog.demandedDoor(
                "<java.io.File: boolean exists()>"));
        // A timed wait whose result the slice reads returns its timeout at
        // once on the fault arm; a future's throws it.
        String unit = "long,java.util.concurrent.TimeUnit)>";
        Object[][] waits = {
            {"<java.util.concurrent.CountDownLatch: boolean await(" + unit,
                    "FAULT:TIMED_WAIT:AWAIT [] FALSE"},
            {"<java.util.concurrent.locks.Condition: long awaitNanos(long)>",
                    "FAULT:TIMED_WAIT:AWAIT [] ZERO"},
            {"<java.util.concurrent.BlockingQueue: java.lang.Object poll("
                    + unit, "FAULT:TIMED_WAIT:POLL [] NULL"},
            {"<java.util.concurrent.Future: java.lang.Object get(" + unit,
                    "FAULT:TIMED_WAIT:GET "
                            + "[java.util.concurrent.TimeoutException] NONE"},
            {"<java.util.concurrent.locks.Lock: boolean tryLock(" + unit,
                    "FAULT:TIMED_WAIT:ACQUIRE [] FALSE"},
        };
        for (Object[] wait : waits) {
            LibraryCatalog.Door door =
                    LibraryCatalog.demandedDoor((String) wait[0]);
            assertEquals(wait[1], door.name() + " " + door.faults + " "
                    + door.result);
        }
        assertTrue(LibraryCatalog.rootsNothing("FAULT:TIMED_WAIT:AWAIT"));
        // A store read is a door at its method, before its request (a
        // failed read registers no watch), asked only on the data flow; it
        // roots no region, as a demanded door does not.
        List<String> reads = new ArrayList<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.dataFlow) {
                reads.add(door.name() + " " + door.method.substring(
                        door.method.indexOf(' ') + 1) + " " + door.after);
            }
        }
        assertEquals(Arrays.asList(
                "FAULT:ZOOKEEPER:READ byte[] getData(java.lang.String,org."
                        + "apache.zookeeper.Watcher,org.apache.zookeeper.data."
                        + "Stat)> false",
                "FAULT:ZOOKEEPER:READ org.apache.zookeeper.data.Stat exists("
                        + "java.lang.String,org.apache.zookeeper.Watcher)> false",
                "FAULT:ZOOKEEPER:READ java.util.List getChildren(java.lang."
                        + "String,org.apache.zookeeper.Watcher)> false",
                "FAULT:ZOOKEEPER:READ java.util.List getChildren(java.lang."
                        + "String,org.apache.zookeeper.Watcher,org.apache."
                        + "zookeeper.data.Stat)> false"), reads);
        String[][] markers = {
            {"FAULT:ZOOKEEPER:READ:ConnectionLossException", "true true"},
            {"FAULT:ZOOKEEPER:WRITE:ConnectionLossException", "false false"},
            {"FAULT:LOCAL_IO:OPEN:FileNotFoundException", "false true"},
            {"FAULT:SOLR_HTTP:REQUEST", "false false"},
        };
        for (String[] marker : markers) {
            assertEquals(marker[0], marker[1],
                    LibraryCatalog.dataFlowMarker(marker[0]) + " "
                            + LibraryCatalog.rootsNothing(marker[0]));
        }
        LinkedHashSet<String> response = new LinkedHashSet<>();
        List<String> dataTransfer = new ArrayList<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (!door.atCalls() && door.method.startsWith(IPC)) {
                response.add(door.doorMethod());
                assertEquals("org.apache.hadoop.ipc.Client", door.family());
            }
            if (door.transport.equals("HDFS_DATA_TRANSFER")) {
                dataTransfer.add(door.direction + " " + door.place());
            }
        }
        // trunk's and 3.4's signatures are one door method.
        assertEquals(Arrays.asList("FAULT:HADOOP_IPC:RESPONSE at "
                        + "org.apache.hadoop.ipc.Client#getRpcResponse"),
                new ArrayList<>(response));
        // An op leaves in Sender#send; each side that sent one reads its
        // response or ack where it calls the parse.
        String proto = "org.apache.hadoop.hdfs.protocol.proto."
                + "DataTransferProtos$";
        assertEquals(Arrays.asList("REQUEST <org.apache.hadoop.hdfs.protocol."
                        + "datatransfer.Sender: void send(java.io."
                        + "DataOutputStream,org.apache.hadoop.hdfs.protocol."
                        + "datatransfer.Op,org.apache.hadoop.thirdparty."
                        + "protobuf.Message)>",
                "RESPONSE every call of <" + proto + "BlockOpResponseProto: "
                        + proto + "BlockOpResponseProto parseFrom(java.io."
                        + "InputStream)>",
                "RESPONSE every call of <" + proto + "DNTransferAckProto: "
                        + proto + "DNTransferAckProto parseFrom(java.io."
                        + "InputStream)>",
                "RESPONSE every call of <org.apache.hadoop.hdfs.protocol."
                        + "datatransfer.PipelineAck: void readFields(java.io."
                        + "InputStream)>"), dataTransfer);
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
                assertEquals(door.dataFlow, placed.dataFlow);
                if (hook != null) {
                    assertEquals(hook.anchor, placed.anchor);
                    assertEquals(hook.after, placed.after);
                }
                // Solr's store reads go before its read turn's hook; a
                // data read's after its reply, where a notification's
                // occurrence is named: a reply lost.
                if (system.equals("solr") && door.dataFlow) {
                    assertEquals(door.method, door.method.contains("getData")
                            ? "<org.apache.solr.common.cloud.SolrZkClient: "
                            + "void causynthReplied()> false"
                            : "<org.apache.solr.common.cloud.SolrZkClient: "
                            + "void causynthReading(java.lang.String)> false",
                            placed.anchor + " " + placed.after);
                }
            }
        }
        String[][] refused = {
            {"{\"schemaVersion\": 1, \"kind\": \"HOOK\", \"transport\": "
                    + "\"T\", \"direction\": \"SEND\", \"door\": "
                    + "\"<a.B: void none(int)>\", \"method\": \"<a.B: void "
                    + "send(int)>\", \"after\": \"<a.C: void hook()>\"}",
                    "names no catalog door"},
            {DOOR + "}", "never a door"},
            {"{\"schemaVersion\": 1, \"kind\": \"HOOK\", \"transport\": "
                    + "\"T\", \"direction\": \"SEND\", \"door\": "
                    + "\"<a.B: void send(int)>\", \"method\": \"<a.B: void "
                    + "send(int)>\", \"after\": \"<a.C: void hook()>\", "
                    + "\"before\": \"<a.C: void hook()>\"}",
                    "one of before and after"}};
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
            {"{\"schemaVersion\": 1, \"kind\": \"WIRE_FLOW\"}", "kind WIRE_FLOW"},
            {"{\"schemaVersion\": 1, \"kind\": \"CODEC\", \"codec\": \"X\", \"classes\": []}", "classes lists"},
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
            {"{\"schemaVersion\": 1, \"kind\": \"CONFIG_FIELD_OWNER\", "
                    + "\"class\": \"Settings\"}", "class is no"},
            {AT_CALLS + "}\n" + AT_CALLS + "}",
                    "FAULT:T:SEND every call of <a.C: void flush()> is "
                            + "stated again"},
            {DOOR + ", \"sites\": \"DEMANDED\"}", "no method, before"},
            {AT_CALLS.replace("before", "after")
                    + ", \"sites\": \"DEMANDED\"}", "no method, before"},
            {AT_CALLS + ", \"result\": false}", "a failing result"},
            {AT_CALLS + ", \"sites\": \"DATA_FLOW\"}", "a door at a method"},
            {DOOR.replace("before", "after") + ", \"sites\": \"DATA_FLOW\"}",
                    "a door at a method"},
            {DOOR + ", \"sites\": \"SOME\"}", "sites is DEMANDED or"},
            {AT_CALLS.replace(", \"faults\": [\"java.io.IOException\"]",
                    "") + ", \"sites\": \"DEMANDED\", \"result\": true}",
                    "result is false, null or 0"},
            {AT_CALLS.replace(", \"faults\": [\"java.io.IOException\"]",
                    "") + ", \"sites\": \"DEMANDED\", \"result\": 1}",
                    "result is false, null or 0"},
        };
        for (String[] row : refused) {
            try {
                LibraryCatalog.read(rows(row[0]));
                fail("accepted " + row[0]);
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage(), expected.getMessage()
                        .startsWith("library catalog at t.jsonl:")
                        && expected.getMessage().contains(row[1]));
            }
        }
        LibraryCatalog.Contents read = LibraryCatalog.read(rows(DOOR
                + "}\n" + CONFIG + ", \"keyArg\": 0, \"defaultArg\": 1}\n"
                + "{\"schemaVersion\": 1, \"kind\": \"CONFIG_FIELD_OWNER\", "
                + "\"class\": \"a.Settings\"}"));
        assertEquals(1, read.doors.size());
        assertEquals("<a.Conf: int getInt(java.lang.String,int)> 0 1",
                read.configSources.get(0).method + " "
                        + read.configSources.get(0).keyArg + " "
                        + read.configSources.get(0).defaultArg);
        assertEquals("[a.Settings]", read.configFieldOwners.toString());
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
