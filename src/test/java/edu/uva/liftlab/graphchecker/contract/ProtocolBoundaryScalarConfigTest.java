package edu.uva.liftlab.graphchecker.contract;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ProtocolBoundaryScalarConfigTest {
    private static final String CLIENT =
            "<example.Client: example.Response fetch()>";
    private static final String SERVER =
            "<example.Server: example.Response fetch()>";

    public interface RuntimeClient {
        String fetch(String request);
    }

    public static final class RuntimeClientImplementation
            implements RuntimeClient {
        @Override
        public String fetch(String request) {
            return request;
        }
    }

    public static final class UnrelatedRuntimeClient {
        public String fetch(String request) {
            return request;
        }
    }

    public interface FirstRuntimeClient {
        String fetch(String request);
    }

    public interface SecondRuntimeClient {
        String fetch(String request);
    }

    public static final class AmbiguousRuntimeClient
            implements FirstRuntimeClient, SecondRuntimeClient {
        @Override
        public String fetch(String request) {
            return request;
        }
    }

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void nestedReferenceArrayLeafRetainsConfiguredIdentityAndBound()
            throws Exception {
        File mapping = mapping("nested.jsonl", "{"
                + "\"schemaVersion\":2,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"id\":\"example.fetch\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true,"
                + "\"boundaryScalarLeaves\":[{"
                + "\"leafId\":\"keys.id\","
                + "\"direction\":\"RESPONSE\","
                + "\"declaredPath\":["
                + "\"<example.Response: example.Key[] keys>\","
                + "\"[]\",\"<example.Key: int id>\"],"
                + "\"containerBound\":8}]}" );

        ProtocolBoundaryScalarConfig config =
                ProtocolBoundaryScalarConfig.read(mapping.toPath());
        List<ProtocolBoundaryScalarConfig.Leaf> leaves =
                config.clientLeaves(CLIENT, "RESPONSE", -1);

        assertEquals(1, leaves.size());
        ProtocolBoundaryScalarConfig.Leaf leaf = leaves.get(0);
        assertEquals("example.fetch", leaf.mappingId());
        assertEquals("keys.id", leaf.leafId());
        assertEquals("response", leaf.port());
        assertEquals("int", leaf.javaType());
        assertEquals(8, leaf.containerBound());
        assertEquals(3, leaf.declaredPath().size());
        assertEquals(leaf.declaredPath(),
                config.serverLeaves(SERVER, "RESPONSE", -1)
                        .get(0).declaredPath());
    }

    @Test
    public void requestLeafUsesNamedPortIndicesOnBothSides()
            throws Exception {
        String client = "<example.Client: void send(example.Request)>";
        String server = "<example.Server: void send(example.Request)>";
        File mapping = mapping("request.jsonl", "{"
                + "\"schemaVersion\":2,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"id\":\"example.send\","
                + "\"clientStub\":\"" + client + "\","
                + "\"serverStub\":\"" + server + "\","
                + "\"request\":[{\"name\":\"payload\","
                + "\"clientArgument\":0,\"serverParameter\":0}],"
                + "\"response\":false,\"boundaryScalarLeaves\":[{"
                + "\"leafId\":\"payload.epoch\","
                + "\"direction\":\"REQUEST\","
                + "\"port\":\"payload\","
                + "\"declaredPath\":["
                + "\"<example.Request: long epoch>\"]}]}" );

        ProtocolBoundaryScalarConfig config =
                ProtocolBoundaryScalarConfig.read(mapping.toPath());

        assertEquals(1, config.clientLeaves(client, "REQUEST", 0).size());
        assertEquals(1, config.serverLeaves(server, "REQUEST", 0).size());
        assertTrue(config.clientLeaves(client, "REQUEST", 1).isEmpty());
        assertEquals("payload", config.mappingLeaves("example.send")
                .get(0).port());
    }

    @Test
    public void clientInterfaceMatchesRuntimeImplementation()
            throws Exception {
        File mapping = mapping("client-implementation.jsonl",
                scalarResponseMapping("runtime.client",
                        fetchSignature(RuntimeClient.class),
                        "example.RuntimeServer"));
        ProtocolBoundaryScalarConfig config =
                ProtocolBoundaryScalarConfig.read(mapping.toPath());

        List<ProtocolBoundaryScalarConfig.Leaf> leaves =
                config.clientLeaves(fetchSignature(
                        RuntimeClientImplementation.class),
                        "RESPONSE", -1);

        assertEquals(1, leaves.size());
        assertEquals("runtime.client", leaves.get(0).mappingId());
        assertEquals(1, config.clientLeaves(fetchSignature(
                RuntimeClientImplementation.class), "RESPONSE", -1)
                .size());
    }

    @Test
    public void unrelatedClassWithSameSubSignatureDoesNotMatch()
            throws Exception {
        File mapping = mapping("unrelated-client.jsonl",
                scalarResponseMapping("runtime.client",
                        fetchSignature(RuntimeClient.class),
                        "example.RuntimeServer"));
        ProtocolBoundaryScalarConfig config =
                ProtocolBoundaryScalarConfig.read(mapping.toPath());
        String unrelated = fetchSignature(UnrelatedRuntimeClient.class);

        assertTrue(config.clientLeaves(unrelated, "RESPONSE", -1)
                .isEmpty());
        assertTrue(config.clientLeaves(unrelated, "RESPONSE", -1)
                .isEmpty());
    }

    @Test
    public void implementationMatchingTwoConfiguredInterfacesFailsClosed()
            throws Exception {
        File mapping = mapping("ambiguous-client.jsonl",
                scalarResponseMapping("runtime.first",
                        fetchSignature(FirstRuntimeClient.class),
                        "example.FirstRuntimeServer") + "\n"
                        + scalarResponseMapping("runtime.second",
                        fetchSignature(SecondRuntimeClient.class),
                        "example.SecondRuntimeServer"));
        ProtocolBoundaryScalarConfig config =
                ProtocolBoundaryScalarConfig.read(mapping.toPath());
        String implementation = fetchSignature(AmbiguousRuntimeClient.class);

        for (int attempt = 0; attempt < 2; attempt++) {
            try {
                config.clientLeaves(implementation, "RESPONSE", -1);
                fail("ambiguous runtime implementation must fail closed");
            } catch (IllegalArgumentException expected) {
                assertTrue(expected.getMessage().contains(
                        "ambiguous clientStub implementation"));
                assertTrue(expected.getMessage().contains(implementation));
            }
        }
    }

    @Test
    public void legacyMappingsWithoutIdsShareTheirHistoricalDerivedId()
            throws Exception {
        String legacy = "{"
                + "\"schemaVersion\":1,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true}";
        File mapping = mapping("legacy-no-id.jsonl",
                legacy + "\n" + legacy);
        try {
            ProtocolBoundaryScalarConfig.read(mapping.toPath());
            fail("derived historical mapping id must be globally unique");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    CLIENT + " -> " + SERVER));
        }
    }

    @Test
    public void retiredCarrierProjectionIsRejectedWithMigrationMessage()
            throws Exception {
        File mapping = mapping("retired.jsonl", "{"
                + "\"schemaVersion\":1,\"id\":\"example.fetch\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true,"
                + "\"carrierProjection\":"
                + "\"DECLARED_FIELDS_AND_ELEMENT_ORDER\"}" );

        try {
            ProtocolBoundaryScalarConfig.read(mapping.toPath());
            fail("retired carrier projection must be rejected");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains(
                    "boundaryScalarLeaves"));
        }
    }

    @Test
    public void referenceArrayLeafRequiresAnExplicitSupportedBound()
            throws Exception {
        File mapping = mapping("missing-bound.jsonl", "{"
                + "\"schemaVersion\":2,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"id\":\"example.fetch\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true,"
                + "\"boundaryScalarLeaves\":[{"
                + "\"leafId\":\"keys.id\","
                + "\"direction\":\"RESPONSE\","
                + "\"declaredPath\":["
                + "\"<example.Response: example.Key[] keys>\","
                + "\"[]\",\"<example.Key: int id>\"]}]}" );

        try {
            ProtocolBoundaryScalarConfig.read(mapping.toPath());
            fail("reference array path must declare a finite bound");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("containerBound"));
        }
    }

    @Test
    public void futureBoundarySchemaAndWrongKindAreRejected()
            throws Exception {
        for (String header : new String[]{
                "\"schemaVersion\":99,"
                        + "\"kind\":\"PROTOCOL_STUB_MAPPING\",",
                "\"schemaVersion\":2,\"kind\":\"OTHER\","}) {
            File mapping = mapping("invalid-header-"
                    + Math.abs(header.hashCode()) + ".jsonl", "{" + header
                    + "\"id\":\"example.fetch\","
                    + "\"clientStub\":\"" + CLIENT + "\","
                    + "\"serverStub\":\"" + SERVER + "\","
                    + "\"request\":[],\"response\":true,"
                    + "\"boundaryScalarLeaves\":[{"
                    + "\"leafId\":\"value\","
                    + "\"direction\":\"RESPONSE\","
                    + "\"declaredPath\":["
                    + "\"<example.Response: int value>\"]}]}" );
            try {
                ProtocolBoundaryScalarConfig.read(mapping.toPath());
                fail("invalid boundary mapping header must be rejected");
            } catch (IOException expected) {
                assertTrue(expected.getMessage().contains(
                        "boundaryScalarLeaves"));
            }
        }
    }

    @Test
    public void mappingIdIsGloballyUnique() throws Exception {
        File mapping = mapping("duplicate-id.jsonl", "{"
                + "\"schemaVersion\":1,\"id\":\"duplicate\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true}\n{"
                + "\"schemaVersion\":1,\"id\":\"duplicate\","
                + "\"clientStub\":\"<example.Other: void call()>\","
                + "\"serverStub\":\"<example.OtherServer: void call()>\","
                + "\"request\":[],\"response\":false}" );
        try {
            ProtocolBoundaryScalarConfig.read(mapping.toPath());
            fail("duplicate mapping id must be rejected");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("duplicate"));
        }
    }

    @Test
    public void semanticBoundaryPathCannotBeRelabeledTwice()
            throws Exception {
        File mapping = mapping("duplicate-semantic-leaf.jsonl", "{"
                + "\"schemaVersion\":2,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"id\":\"example.fetch\","
                + "\"clientStub\":\"" + CLIENT + "\","
                + "\"serverStub\":\"" + SERVER + "\","
                + "\"request\":[],\"response\":true,"
                + "\"boundaryScalarLeaves\":[{"
                + "\"leafId\":\"first\","
                + "\"direction\":\"RESPONSE\","
                + "\"declaredPath\":["
                + "\"<example.Response: int value>\"]},{"
                + "\"leafId\":\"relabeled\","
                + "\"direction\":\"RESPONSE\","
                + "\"declaredPath\":["
                + "\"<example.Response: int value>\"]}]}" );
        try {
            ProtocolBoundaryScalarConfig.read(mapping.toPath());
            fail("one semantic boundary path must have one identity");
        } catch (IOException expected) {
            assertTrue(expected.getMessage().contains("semantic path"));
        }
    }

    private File mapping(String name, String row) throws IOException {
        File file = folder.newFile(name);
        Files.write(file.toPath(), java.util.Collections.singletonList(row),
                StandardCharsets.UTF_8);
        return file;
    }

    private static String fetchSignature(Class<?> owner) {
        return "<" + owner.getName()
                + ": java.lang.String fetch(java.lang.String)>";
    }

    private static String scalarResponseMapping(String id, String client,
                                                String serverOwner) {
        return "{\"schemaVersion\":2,"
                + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                + "\"id\":\"" + id + "\","
                + "\"clientStub\":\"" + client + "\","
                + "\"serverStub\":\"<" + serverOwner
                + ": java.lang.String fetch(java.lang.String)>\","
                + "\"request\":[],\"response\":true,"
                + "\"boundaryScalarLeaves\":[{"
                + "\"leafId\":\"value\","
                + "\"direction\":\"RESPONSE\","
                + "\"declaredPath\":["
                + "\"<example.Response: int value>\"]}]}";
    }
}
