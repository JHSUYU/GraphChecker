package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.ArrayType;
import soot.ByteType;
import soot.G;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

/** Focused ownership checks for the HDFS encrypted SASL cut. */
public class HadoopCommunicationAdapterTest {
    private static final String IO_STREAM_PAIR =
            "org.apache.hadoop.hdfs.protocol.datatransfer.IOStreamPair";
    private static final String DATA_ENCRYPTION_KEY =
            "org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey";

    @Before
    public void resetBefore() {
        G.reset();
        System.clearProperty("causynth.protocol.stubs");
    }

    @After
    public void resetAfter() {
        System.clearProperty("causynth.protocol.stubs");
        G.reset();
    }

    @Test
    public void onlyEncryptedStreamsPublishesTheEncryptionKeyHandoff()
            throws Exception {
        Map<String, SootMethod> methods = new LinkedHashMap<>();
        SootClass client = applicationClass(
                HadoopCommunicationAdapter.SASL_CLIENT_CLASS);
        SootClass server = applicationClass(
                HadoopCommunicationAdapter.SASL_SERVER_CLASS);

        SootMethod handshake = method(client,
                HadoopCommunicationAdapter.SASL_CLIENT_METHOD,
                Arrays.<Type>asList(
                        ref("java.net.InetAddress"),
                        ref("java.io.OutputStream"),
                        ref("java.io.InputStream"),
                        ref("java.lang.String"),
                        ref("java.util.Map"),
                        ref("javax.security.auth.callback.CallbackHandler")),
                ref(IO_STREAM_PAIR));
        SootMethod encrypted = method(client, "getEncryptedStreams",
                Arrays.<Type>asList(
                        ref("java.net.InetAddress"),
                        ref("java.io.OutputStream"),
                        ref("java.io.InputStream"),
                        ref(DATA_ENCRYPTION_KEY)),
                ref(IO_STREAM_PAIR));
        SootMethod ordinary = method(client, "getSaslStreams",
                Arrays.<Type>asList(
                        ref("java.net.InetAddress"),
                        ref("java.io.OutputStream"),
                        ref("java.io.InputStream"),
                        ref("org.apache.hadoop.security.token.Token")),
                ref(IO_STREAM_PAIR));
        SootMethod serverEntry = method(server,
                HadoopCommunicationAdapter.SASL_SERVER_METHOD,
                Collections.<Type>singletonList(ref("java.lang.String")),
                ArrayType.v(ByteType.v(), 1));
        for (SootMethod method : Arrays.asList(handshake, encrypted,
                ordinary, serverEntry)) {
            methods.put(method.getSignature(), method);
        }

        Path catalog = Files.createTempFile("hadoop-sasl-cuts", ".jsonl");
        try {
            Files.write(catalog,
                    Collections.singletonList(mapping(handshake, serverEntry)
                            .toString()), StandardCharsets.UTF_8);
            System.setProperty("causynth.protocol.stubs",
                    catalog.toString());
            HadoopCommunicationAdapter adapter =
                    new HadoopCommunicationAdapter(methods,
                            ConfiguredProtocolStubs.fromConfiguration(
                                    methods));

            CommunicationResolution accepted = adapter.resolve(
                    encrypted.getSignature(), 17, handshake.getSignature());
            assertNotNull(accepted.site);
            assertFalse(accepted.isGap());
            assertEquals(4, accepted.site.request.size());
            assertEquals("keyId", accepted.site.request.get(1).name);
            assertEquals("blockPoolId", accepted.site.request.get(2).name);
            assertEquals("nonce", accepted.site.request.get(3).name);
            assertEquals(DATA_ENCRYPTION_KEY,
                    accepted.site.request.get(1).exportCarrierClass);
            assertEquals("keyId",
                    accepted.site.request.get(1).exportCarrierField);
            assertEquals("I",
                    accepted.site.request.get(1).exportCarrierDescriptor);
            assertEquals(HadoopCommunicationAdapter.SASL_CONTROL_PLANE_CLASS
                            + "$Parsed",
                    accepted.site.request.get(1).attachCarrierClass);
            assertEquals(serverEntry.getSignature(),
                    accepted.site.serverEntryMethod);

            CommunicationResolution rejected = adapter.resolve(
                    ordinary.getSignature(), 11, handshake.getSignature());
            assertNull(rejected.site);
            assertFalse(rejected.isGap());
        } finally {
            Files.deleteIfExists(catalog);
        }
    }

    private static JsonObject mapping(SootMethod client,
                                      SootMethod server) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 2);
        row.addProperty("kind", "PROTOCOL_STUB_MAPPING");
        row.addProperty("id", "hdfs.data-transfer.encrypted-sasl");
        row.addProperty("transport", "SASL_HANDSHAKE");
        row.addProperty("clientStub", client.getSignature());
        row.addProperty("serverStub", server.getSignature());
        JsonObject port = new JsonObject();
        port.addProperty("name", "authenticationId");
        port.addProperty("clientArgument", 3);
        port.addProperty("serverParameter", 0);
        JsonArray request = new JsonArray();
        request.add(port);
        row.add("request", request);
        row.addProperty("response", false);
        return row;
    }

    private static SootClass applicationClass(String name) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        sootClass.setApplicationClass();
        Scene.v().addClass(sootClass);
        return sootClass;
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returns) {
        SootMethod method = new SootMethod(name, parameters, returns,
                Modifier.PUBLIC);
        owner.addMethod(method);
        return method;
    }

    private static RefType ref(String name) {
        return RefType.v(name);
    }
}
