package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import com.google.protobuf.Field;
import com.google.protobuf.Type;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.List;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * What a message door carries and where the message stands: the protobuf
 * message it walks (SYMBOL-SCOPE §6.3), a SASL message's half, and a
 * DataTransfer op taken into its turn.
 */
public class MessageDoorsTest {
    private static final String PORT = "XCH.0.wire.auto:Field.Number";
    private final List<JsonObject> written = new ArrayList<JsonObject>();

    @Before
    public void install() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
        ScheduleLog.resetForTests();
        RecordingWindow.open();
        ScheduleLog.install(written::add);
        JsonObject row = new JsonObject();
        row.addProperty("kind", StaticScopeMap.SITE_KIND);
        row.addProperty("role", StaticScopeMap.EXPORT_SITE);
        row.addProperty("cell", "<com.google.protobuf.Field: int number_>");
        row.addProperty("portId", PORT);
        MessageCodec.install(Collections.singletonList(row));
    }

    @After
    public void clear() {
        CausynthMessagePropagation.endInbound();
        SymbolicMessageEnvelope.clear();
        MessageCodec.install(Collections.<JsonObject>emptyList());
        ScheduleLog.resetForTests();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
        RecordingWindow.reset();
    }

    /**
     * A {@code Type} holding two {@code Field}s whose {@code number_} is a
     * port: a parse binds each element to the message object it was decoded
     * into, in the exchange it arrived in; a relay of the decoded message
     * hands on those elements, the one the decode carried none for counted
     * empty.  A message built here carries what its builder's setters
     * exported, and its getter attaches nothing.  No VM runs here, so only
     * decoded elements are staged.
     */
    @Test
    public void aDecodedMessageIsBoundAndRelayedWhole() {
        Type decoded = Type.newBuilder()
                .addFields(Field.newBuilder().setNumber(7))
                .addFields(Field.newBuilder().setNumber(9)).build();
        // The sender's message carried an element for the second field only.
        SymbolicMessageEnvelope.skip(PORT);
        SymbolicMessageEnvelope.stage(PORT, 42L, null);
        CausynthMessagePropagation.inbound("",
                SymbolicMessageEnvelope.takeOutbound(),
                CausynthMessagePropagation.IPC, "c-1", "0",
                MessageDoors.RESPONSE, null);
        CausynthMessagePropagation.received(decoded);
        CausynthMessagePropagation.endInbound();
        MessageCodec.Element first = MessageCodec.bound(decoded.getFields(0),
                PORT);
        MessageCodec.Element second = MessageCodec.bound(
                decoded.getFields(1), PORT);
        Field.Builder builder = Field.newBuilder().setNumber(7);
        MessageCodec.set(builder, PORT, 77L, null);
        Field built = builder.build();
        MessageCodec.built(builder, built);
        Object[][] rows = {
            {"a field its message carried no element for",
                SymbolicMessageEnvelope.ABSENT, first.handle},
            {"the element its message carried", 42L, second.handle},
            {"in the exchange it arrived in, whatever the thread serves now",
                "c-1 RESPONSE", second.correlationId + " " + second.half},
            {"a message no door decoded", null, MessageCodec.bound(
                    Field.newBuilder().setNumber(9).build(), PORT)},
            {"nor a class's JVM-wide default instance", null,
                MessageCodec.bound(Field.getDefaultInstance(), PORT)},
            // Relayed inside a new request (the response door unwraps the
            // RPC engine's wrapper): the second element under its original
            // handle at its own ordinal, the first counted empty.
            {"a relay hands on what it received", "CSE6;" + token() + ",42,1",
                relayed("c-2", decoded.getFields(0), decoded.getFields(1))},
            {"a message held twice is walked twice", "CSE6;" + token()
                    + ",42,0;" + token() + ",42,1", relayed("c-3",
                    decoded.getFields(1), decoded.getFields(1))},
            {"a built message's getter attaches nothing", null,
                MessageCodec.bound(built, PORT)},
            {"its door stages the setter's export", "CSE6;" + token()
                    + ",77,0", relayed("c-4", built)}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** The symbolic envelope a response wrapping {@code fields} sends. */
    private static String relayed(String correlation, Field... fields) {
        Type.Builder message = Type.newBuilder();
        for (Field field : fields) message.addFields(field);
        return CausynthMessagePropagation.outboundResponse(
                CausynthMessagePropagation.IPC, correlation, "0", null,
                new Wrapper(message.build())).symbolic;
    }

    /** The RPC engine's response wrapper ({@code ProtobufWrapper}). */
    private static final class Wrapper {
        @SuppressWarnings("unused")
        private final Object message;

        private Wrapper(Object message) {
            this.message = message;
        }
    }

    private static String token() {
        return Base64.getUrlEncoder().withoutPadding().encodeToString(
                PORT.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * A SASL message's half is its sender's role in the exchange.
     * hdfs-17967: a DataNode serving the source's transfer opens its own
     * handshake with the mirror; labelled as the RESPONSE of the request it
     * served, its messages left under the source's correlation and the key
     * id's export on the forwarding node was never stated.
     */
    @Test
    public void aClientHandshakeOpenedWhileServingSendsItsOwnRequests() {
        Object head = new Object();
        RuntimeTraceContext.registerSource(head, new SourceRef("CLUSTER_NODE",
                "DATANODE", "hdfs-17967/head-dn", 0));
        long upstream = RuntimeTraceContext.beginRequest(head, "transfer");
        String header = RuntimeTraceContext.outboundHeader(head, null);
        RuntimeTraceContext.endRequest(upstream);
        assertFalse("the upstream message carries a context",
                header.isEmpty());
        long serving = RuntimeTraceContext.beginRequest(head, "serve");
        // Serving the source's handshake: its answer is the RESPONSE of it.
        CausynthMessagePropagation.inboundSasl(header, "", "source-sasl", "1");
        assertEquals("source-sasl",
                CausynthMessagePropagation.outboundSasl().correlationId);
        // Still serving it, the thread opens its own handshake.
        CausynthMessagePropagation.inboundSasl(header, "", "source-sasl", "1");
        CausynthMessagePropagation.beginSasl();
        String own = CausynthMessagePropagation.outboundSasl().correlationId;
        assertTrue("the forwarding node's own exchange: " + own,
                own.startsWith("hdfs-sasl-"));
        CausynthMessagePropagation.inboundSasl(header, "", own, "1");
        assertEquals("the next request stays in it", own,
                CausynthMessagePropagation.outboundSasl().correlationId);
        CausynthMessagePropagation.endSasl();
        assertEquals("closed: the served exchange is the thread's again",
                "source-sasl",
                CausynthMessagePropagation.outboundSasl().correlationId);
        RuntimeTraceContext.endRequest(serving);
    }

    /**
     * A DataTransfer op is a message the DataNode's turn takes into its own
     * context: the turn keeps its address, and its RECV names the op's SEND.
     * b20h FsDatasetImpl-1749: the op crossed with no envelope, so its block
     * id paired with no export; standing on the sender instead, the turn's
     * tasks inherited an IPC chain the seed replays did not reproduce.
     */
    @Test
    public void aTurnTakesItsOpInAndKeepsItsAddress() {
        Object client = new Object();
        RuntimeTraceContext.registerSource(client, new SourceRef(
                "CLUSTER_NODE", "CLIENT", "adhoc/client0", 0));
        long writing = RuntimeTraceContext.beginRequest(client, "write");
        CausynthMessagePropagation.Outbound op =
                CausynthMessagePropagation.outboundOp(null);
        RuntimeTraceContext.endRequest(writing);
        assertTrue("an op is a request on a correlation of its own: "
                + op.correlationId, op.correlationId.startsWith("hdfs-dt-"));
        String sent = Interactions.sender(
                CausynthMessagePropagation.DATA_TRANSFER, op.correlationId,
                MessageDoors.REQUEST);
        assertFalse("its send filed a producer endpoint", sent.isEmpty());

        Object dataNode = new Object();
        RuntimeTraceContext.registerSource(dataNode, new SourceRef(
                "CLUSTER_NODE", "DATANODE", "adhoc/dn1", 0));
        long turn = MessageDoors.beginTick(dataNode, "DATA_XCEIVER");
        CausalContext before = Identity.contextHere();
        CausynthMessagePropagation.inboundOp(op.symbolic, op.correlationId);
        assertEquals("the turn keeps its address", before,
                Identity.contextHere());
        assertTrue(before instanceof CausalContext.Root);
        assertEquals("and serves the op it took in", op.correlationId,
                MessageDoors.current().correlationId);
        ScheduleEvent recv = null;
        for (JsonObject row : written) {
            if (!row.has("kind")) continue;
            ScheduleEvent event = RowCodec.readScheduleEvent(row);
            if (event.kind() == ScheduleEvent.Kind.RECV) recv = event;
        }
        assertTrue("the turn's RECV names the message that made it",
                recv != null && sent.equals(recv.received()));
        MessageDoors.endTick(turn);
        CausynthMessagePropagation.endInbound();
        assertTrue("and the turn's end ends it",
                MessageDoors.current() == null);
    }
}
