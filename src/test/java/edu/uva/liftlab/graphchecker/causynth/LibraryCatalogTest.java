package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import org.junit.Test;
import soot.G;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class LibraryCatalogTest {
    private static final String IPC = "<org.apache.hadoop.ipc.Client: "
            + "org.apache.hadoop.io.Writable getRpcResponse(";

    @Test
    public void theShippedCatalogNamesEachLibraryDoorOnce() {
        List<String> transports = new ArrayList<>(LibraryCatalog.transports());
        assertEquals(Arrays.asList("HADOOP_IPC", "HDFS_SASL",
                "HDFS_DATA_TRANSFER", "SOLR_HTTP", "SOLR_HTTP2", "HBASE_RPC",
                "ZOOKEEPER", "ZK_QUORUM", "LOCAL_IO", "TIMED_WAIT"),
                transports);
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
        List<String> learnerStream = new ArrayList<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.transport.equals("ZK_QUORUM")) {
                learnerStream.add(door.doorMethod() + " " + door.anchor + " "
                        + door.after + " " + door.faults);
            }
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
        String quorum = "org.apache.zookeeper.server.quorum.";
        assertEquals(Arrays.asList("FAULT:ZK_QUORUM:READ at " + quorum
                        + "Learner#syncWithLeader <" + quorum + "Learner: void "
                        + "readPacket(" + quorum + "QuorumPacket)> false "
                        + "[java.net.SocketTimeoutException]"), learnerStream);
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

    @Test
    public void aListedMessageCrossesAsAGeneratedOneAndItsSettersExportIt() {
        String header = "org.apache.zookeeper.txn.TxnHeader";
        assertEquals(Arrays.asList(header),
                new ArrayList<>(LibraryCatalog.messageClasses()));
        String proto = "a.Protos$Ack";
        String[][] table = {
            {header, "Zxid", "long", "true",
                    "<" + header + ": void setZxid(long)>"},
            {proto, "Seq", "int", "false", "<" + proto + "$Builder: " + proto
                    + "$Builder setSeq(int)>"},
        };
        for (String[] row : table) {
            assertEquals(row[0], row[4], SeedBackwardStaticAnalyzer
                    .producerSetter(row[0], row[1], row[2],
                            Boolean.parseBoolean(row[3])));
        }
    }

    @Test
    public void theHBaseClientsDoorsAreItsCallsRequestAndCompletion() {
        List<String> hbase = new ArrayList<>();
        for (LibraryCatalog.Door door : LibraryCatalog.doors()) {
            if (door.transport.equals("HBASE_RPC")) {
                hbase.add(door.doorMethod() + " " + door.after + " "
                        + door.faults + " " + door.family());
            }
        }
        String ipc = "org.apache.hadoop.hbase.ipc.";
        assertEquals(Arrays.asList("FAULT:HBASE_RPC:REQUEST at " + ipc
                        + "AbstractRpcClient#callMethod false [java.io."
                        + "IOException, org.apache.hadoop.hbase.exceptions."
                        + "ConnectionClosedException] " + ipc
                        + "AbstractRpcClient",
                "FAULT:HBASE_RPC:RESPONSE at " + ipc + "RpcConnection"
                        + "#finishCall false [java.io.IOException, " + ipc
                        + "CallTimeoutException, org.apache.hadoop.hbase."
                        + "exceptions.ConnectionClosedException] " + ipc
                        + "RpcConnection"), hbase);
        assertTrue(LibraryCatalog.exchangeMarker(
                "FAULT:HBASE_RPC:RESPONSE:CallTimeoutException"));
        assertFalse(LibraryCatalog.rootsNothing("FAULT:HBASE_RPC:REQUEST"));
    }

    @Test
    public void aHookInItsDoorsOwnMethodMovesTheDoorNowhere()
            throws IOException {
        String rpc = "<a.Rpc: void ";
        String body = "{ a.Rpc r0; r0 := @this: a.Rpc; ";
        String hook = "staticinvoke <a.Hook: void sent()>(); ";
        String call = "virtualinvoke r0.<a.Rpc: void call()>(); ";
        JimpleScene.load(JimpleScene.OBJECT, "application public class a.Rpc"
                + " extends java.lang.Object { public void call() " + body
                + hook + "staticinvoke <a.Net: void send()>(); return; }"
                + " public void wrapped() " + body + call + hook + "return; }"
                + " public void blocking() " + body + call + hook
                + "return; } }");
        try {
            List<SootClass> analysed = Arrays.asList(
                    Scene.v().getSootClass("a.Rpc"));
            String door = "{\"schemaVersion\": 1, \"kind\": \"DOOR\", "
                    + "\"transport\": \"RPC\", \"direction\": \"REQUEST\", "
                    + "\"method\": \"" + rpc + "call()>\", \"before\": "
                    + "\"<a.Net: void send()>\", \"faults\": "
                    + "[\"java.io.IOException\"]}";
            String[][] table = {
                {"call", "[]"},
                {"wrapped", "[" + rpc + "blocking()>]"},
            };
            for (String[] row : table) {
                List<LibraryCatalog.Door> placed = LibraryCatalog.placed(
                        LibraryCatalog.read(rows(door)).doors,
                        LibraryCatalog.hooks(rows("{\"schemaVersion\": 1, "
                                + "\"kind\": \"HOOK\", \"transport\": "
                                + "\"RPC\", \"direction\": \"REQUEST\", "
                                + "\"door\": \"" + rpc + "call()>\", "
                                + "\"method\": \"" + rpc + row[0] + "()>\","
                                + " \"after\": \"<a.Hook: void sent()>\"}")));
                Set<String> moved = new TreeSet<>();
                for (SootMethod method : DoorWeave.moved(placed.get(0),
                        analysed).keySet()) {
                    moved.add(method.getSignature());
                }
                assertEquals(row[0], row[1], moved.toString());
            }
        } finally {
            G.reset();
        }
    }

    private static Map<String, JsonObject> rows(String row)
            throws IOException {
        return LibraryCatalog.rows(new BufferedReader(new StringReader(row)),
                "test.jsonl");
    }
}
