package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import com.google.gson.JsonObject;
import com.google.protobuf.Field;
import com.google.protobuf.Type;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.util.Collections;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * The door walks the protobuf message it carries (SYMBOL-SCOPE §6.3), here a
 * {@code Type} holding two {@code Field}s whose {@code number_} is a port:
 * a parse binds each element to the message object it was decoded into, in
 * the exchange it arrived in, and a relay of the decoded message hands on
 * those elements, the one the decode carried none for counted empty.  A
 * message built here is no wire value.  No concolic VM runs these tests,
 * so only decoded elements are staged.
 */
public class MessageCodecTest {
    private static final String PORT = "XCH.0.wire.auto:Field.Number";

    @Before
    public void install() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
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
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
        Interactions.resetForTests();
    }

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

        MessageCodec.Element first = MessageCodec.bound(
                decoded.getFields(0), PORT);
        MessageCodec.Element second = MessageCodec.bound(
                decoded.getFields(1), PORT);
        Object[][] rows = {
                {"a field its message carried no element for",
                        SymbolicMessageEnvelope.ABSENT, first.handle},
                {"the element its message carried", 42L, second.handle},
                {"in the exchange it arrived in, whatever the thread serves"
                        + " now", "c-1 RESPONSE",
                        second.correlationId + " " + second.half},
                // Built here: its field is the program's own value, and its
                // getter attaches nothing.
                {"a message no door decoded", null,
                        MessageCodec.bound(Field.newBuilder().setNumber(9)
                                .build(), PORT)},
                {"nor a class's JVM-wide default instance", null,
                        MessageCodec.bound(Field.getDefaultInstance(),
                                PORT)},
                // Relayed inside a new request (the response door unwraps
                // the RPC engine's wrapper): the second element under its
                // original handle at its own ordinal, the first counted
                // empty, nothing exported from either field.
                {"a relay hands on what it received",
                        "CSE6;" + token(PORT) + ",42,1",
                        CausynthMessagePropagation.outboundResponse(
                                CausynthMessagePropagation.IPC, "c-2", "0",
                                null, new Wrapper(Type.newBuilder()
                                        .addFields(decoded.getFields(0))
                                        .addFields(decoded.getFields(1))
                                        .build())).symbolic},
                // A message held twice is on the wire twice.
                {"a message held twice is walked twice",
                        "CSE6;" + token(PORT) + ",42,0;" + token(PORT)
                                + ",42,1",
                        CausynthMessagePropagation.outboundResponse(
                                CausynthMessagePropagation.IPC, "c-3", "0",
                                null, new Wrapper(Type.newBuilder()
                                        .addFields(decoded.getFields(1))
                                        .addFields(decoded.getFields(1))
                                        .build())).symbolic}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * A message built here carries what its builder's setters exported: the
     * door stages each element under its export, and the message's own
     * getter attaches nothing.
     */
    @Test
    public void aBuiltMessageCarriesItsSettersExports() {
        Field.Builder builder = Field.newBuilder().setNumber(7);
        MessageCodec.set(builder, PORT, 77L, null);
        Field built = builder.build();
        MessageCodec.built(builder, built);
        Object[][] rows = {
                {"its getter attaches nothing", null,
                        MessageCodec.bound(built, PORT)},
                {"its door stages the setter's export",
                        "CSE6;" + token(PORT) + ",77,0",
                        CausynthMessagePropagation.outboundResponse(
                                CausynthMessagePropagation.IPC, "c-4", "0",
                                null, new Wrapper(Type.newBuilder()
                                        .addFields(built).build()))
                                .symbolic}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** The RPC engine's response wrapper ({@code ProtobufWrapper}). */
    private static final class Wrapper {
        @SuppressWarnings("unused")
        private final Object message;

        private Wrapper(Object message) {
            this.message = message;
        }
    }

    private static String token(String value) {
        return java.util.Base64.getUrlEncoder().withoutPadding()
                .encodeToString(value.getBytes(
                        java.nio.charset.StandardCharsets.UTF_8));
    }
}
