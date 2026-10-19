package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class LibraryCatalogTest {
    private static final String IPC = "<org.apache.hadoop.ipc.Client: "
            + "org.apache.hadoop.io.Writable getRpcResponse(";

    @Test
    public void theShippedCatalogNamesEachLibraryDoorOnce() {
        List<String> transports = new ArrayList<>(LibraryCatalog.transports());
        assertEquals(Arrays.asList("HADOOP_IPC", "HDFS_SASL",
                "HDFS_DATA_TRANSFER", "SOLR_HTTP", "SOLR_HTTP2", "ZOOKEEPER",
                "LOCAL_IO", "TIMED_WAIT"), transports);
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
        assertEquals(Arrays.asList("FAULT:HADOOP_IPC:RESPONSE at "
                        + "org.apache.hadoop.ipc.Client#getRpcResponse"),
                new ArrayList<>(response));
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
}
