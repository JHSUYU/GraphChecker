package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Test;
import soot.G;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * F3: a protobuf field the slice demands crosses the wire by rule, when an
 * RPC carries its message.  The scene is protobuf-shaped: a message {@code
 * KeyProto} whose hierarchy reaches {@code GeneratedMessageV3}, held by the
 * response of a service method {@code getKeys(RpcController, KeysRequest)},
 * its getter returning its field {@code keyId_}, its {@code
 * KeyProto$Builder.setKeyId}, two producers calling it, and an declared
 * throw deciding on two {@code getKeyId()} reads -- beside a third read
 * nothing demands -- and on the same field of {@code SectionProto}, a
 * message no service carries (an on-disk section) with its own setter call.
 */
public class WirePortDerivationTest {
    private static final String MESSAGE = "m.Protos$KeyProto";
    private static final String BUILDER = MESSAGE + "$Builder";
    private static final String GETTER = "<" + MESSAGE + ": int getKeyId()>";
    private static final String SETTER = "<" + BUILDER + ": " + BUILDER
            + " setKeyId(int)>";
    private static final String ENCODE_A = "<m.Codec: void encodeA("
            + BUILDER + ",int)>";
    private static final String ENCODE_B = "<m.Codec: void encodeB("
            + BUILDER + ",int)>";
    private static final String SECTION = "m.Protos$SectionProto";
    private static final String CHECK = "<m.Codec: void check(" + MESSAGE
            + "," + MESSAGE + "," + SECTION + ")>";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aDemandedFieldReadIsAPortOfItsMessageField() throws Exception {
        StaticProgram program = new SeedBackwardStaticAnalyzer(target())
                .analyze();
        assertEquals("one port: the RPC message's field, the on-disk"
                + " section's none", 1, program.communicationCallSites.size());
        Map<String, Object> port = program.communicationCallSites.get(0);
        String portId = MapFields.text(port.get(
                CommunicationCatalogContract.PORT_ID));
        Object[][] rows = {
                {"its name", "auto:KeyProto.KeyId", port.get(
                        CommunicationCatalogContract.PORT_NAME)},
                {"a direction-free declared port id", true,
                        CommunicationCatalogContract.declaredPortId(portId)
                                && portId.endsWith(
                                ".wire.auto:KeyProto.KeyId")},
                {"its type", "int", port.get(
                        CommunicationCatalogContract.PORT_JAVA_TYPE)},
                {"carried in the field its getter returns, which the door"
                        + " walks", "<" + MESSAGE + ": int keyId_>",
                        port.get(CommunicationCatalogContract
                                .PORT_CODEC_FIELD)},
                {"every setter call is a producer, argument 0",
                        Arrays.asList(
                                "CALL_ARGUMENT " + ENCODE_A + "#u2 0 "
                                        + SETTER,
                                "CALL_ARGUMENT " + ENCODE_B + "#u3 0 "
                                        + SETTER),
                        captures(port, CommunicationCatalogContract
                                .PORT_PRODUCERS)},
                {"every demanded getter read is a consumer, the idle one"
                        + " is none", Arrays.asList(
                        "CALL_RETURN " + CHECK + "#u3 null " + GETTER,
                        "CALL_RETURN " + CHECK + "#u4 null " + GETTER),
                        captures(port, CommunicationCatalogContract
                                .PORT_CONSUMERS)},
                {"each producer's value reaches each consumer",
                        new LinkedHashSet<>(Arrays.asList(
                                ENCODE_A + "::i0 -> " + CHECK + "::i0",
                                ENCODE_A + "::i0 -> " + CHECK + "::i1",
                                ENCODE_B + "::i1 -> " + CHECK + "::i0",
                                ENCODE_B + "::i1 -> " + CHECK + "::i1")),
                        edges(program, "wire_handoff")},
                {"and the slice goes on on the sending side",
                        true, edges(program, "local_def_use").containsAll(
                        Arrays.asList(
                                ENCODE_A + ".param1:int -> " + ENCODE_A
                                        + "::i0",
                                ENCODE_B + "::i0 -> " + ENCODE_B
                                        + "::i1"))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** A system's flow declaration applies to a program that holds every
     *  method it names; one side alone carries nothing. */
    @Test
    public void aFlowNamingAMethodTheProgramDoesNotHoldDoesNotApply() {
        assertFalse(WireFlowCatalog.applies(JsonParser.parseString(
                "{\"schemaVersion\":3,\"kind\":\"WIRE_FLOW\",\"id\":\"key-id\","
                        + "\"javaType\":\"int\","
                        + "\"producer\":{\"method\":\"<a.P: int p()>\"},"
                        + "\"consumer\":{\"method\":\"<a.C: void c(int)>\"}}")
                .getAsJsonObject(), Collections.emptyMap()));
    }

    private static List<String> captures(Map<String, Object> port,
                                         String side) {
        List<String> found = new ArrayList<>();
        for (Map<String, Object> capture : MapFields.rows(port.get(side))) {
            found.add(capture.get(CommunicationCatalogContract
                    .PORT_OUTPUT_CAPTURE_KIND) + " "
                    + capture.get(CommunicationCatalogContract.CALL_SITE_ID)
                    + " " + capture.get(
                    CommunicationCatalogContract.PORT_ARGUMENT_INDEX) + " "
                    + capture.get(
                    CommunicationCatalogContract.DECLARED_CALLEE));
        }
        return found;
    }

    private static Set<String> edges(StaticProgram program, String kind) {
        Set<String> found = new LinkedHashSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (kind.equals(edge.get("kind"))) {
                found.add(edge.get("fromCell") + " -> " + edge.get("toCell"));
            }
        }
        return found;
    }

    /** The scene, and the declared throw in {@code check}. */
    private static CausynthTargetContext target() {
        String runtime = "com.google.protobuf.GeneratedMessageV3";
        String getSection = "<" + SECTION + ": int getKeyId()>";
        JimpleScene.load(JimpleScene.OBJECT,
                "public class " + runtime + " extends java.lang.Object { }",
                "application " + keyIdField(MESSAGE, runtime),
                "application " + keyIdField(SECTION, runtime),
                // encodeA sets its parameter; encodeB a value it computed;
                // saveSection writes the on-disk section.
                "application public class m.Codec extends java.lang.Object {"
                        + encode("encodeA", BUILDER, "i0")
                        + encode("encodeB", BUILDER, "i1")
                        + encode("saveSection", SECTION + "$Builder", "i0")
                        + " public static void check(" + MESSAGE + ", "
                        + MESSAGE + ", " + SECTION + ") { " + MESSAGE + " r0,"
                        + " r1; " + SECTION + " r2; int i0, i1, i2, i3;"
                        + " java.lang.IllegalStateException r3;"
                        + " r0 := @parameter0: " + MESSAGE + ";"
                        + " r1 := @parameter1: " + MESSAGE + ";"
                        + " r2 := @parameter2: " + SECTION + ";"
                        + " i0 = virtualinvoke r0." + GETTER + "();"
                        + " i1 = virtualinvoke r1." + GETTER + "();"
                        + " i2 = virtualinvoke r0." + GETTER + "();"
                        + " i3 = virtualinvoke r2." + getSection + "();"
                        + " if i0 != i1 goto label1; if i3 == 0 goto label1;"
                        + " r3 = new java.lang.IllegalStateException;"
                        + " throw r3; label1: return; } }",
                JimpleScene.FAILURE,
                // The service: getKeys(RpcController, KeysRequest) answers a
                // KeysReply whose repeated field holds KeyProto.
                "public class m.Protos$KeysReply extends " + runtime
                        + " { public " + MESSAGE + " getKey(int) { } }",
                "public class m.Protos$KeyService$BlockingInterface extends"
                        + " java.lang.Object { public m.Protos$KeysReply"
                        + " getKeys(com.google.protobuf.RpcController,"
                        + " m.Protos$KeysRequest) { } }",
                "public class com.google.protobuf.RpcController extends"
                        + " java.lang.Object { }",
                "public class m.Protos$KeysRequest extends " + runtime
                        + " { }",
                "application " + builder(MESSAGE),
                "application " + builder(SECTION));
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", "m.Codec", "check",
                        "(Lm/Protos$KeyProto;Lm/Protos$KeyProto;"
                                + "Lm/Protos$SectionProto;)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }

    /** {@code static void name(Builder b, int k)}: {@code b.setKeyId(k)},
     *  or ({@code sent} i1) of {@code k + 1}. */
    private static String encode(String name, String builder, String sent) {
        return " public static void " + name + "(" + builder + ", int) { "
                + builder + " r0; int i0" + (sent.equals("i1") ? ", i1" : "")
                + "; r0 := @parameter0: " + builder + "; i0 := @parameter1:"
                + " int;" + (sent.equals("i1") ? " i1 = i0 + 1;" : "")
                + " virtualinvoke r0.<" + builder + ": " + builder
                + " setKeyId(int)>(" + sent + "); return; }";
    }

    /** The message: {@code int getKeyId()} returning its field {@code
     *  keyId_}. */
    private static String keyIdField(String message, String runtime) {
        return "public class " + message + " extends " + runtime + " {"
                + " private int keyId_; public int getKeyId() { " + message
                + " r0; int i0; r0 := @this: " + message + "; i0 = r0.<"
                + message + ": int keyId_>; return i0; } }";
    }

    /** Its {@code $Builder}: {@code setKeyId(int)}. */
    private static String builder(String message) {
        String builder = message + "$Builder";
        return "public class " + builder + " extends java.lang.Object {"
                + " public " + builder + " setKeyId(int) { " + builder
                + " r0; int i0; r0 := @this: " + builder + ";"
                + " i0 := @parameter0: int; return r0; } }";
    }
}
