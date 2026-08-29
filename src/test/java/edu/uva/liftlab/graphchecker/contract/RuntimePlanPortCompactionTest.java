package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * What a region port is still allowed to say after plan compaction.
 *
 * <p>Compaction drops the trace history a published plan does not need, and
 * that is deliberate.  It must not drop what a port <em>means</em>: a cut's
 * REQUEST port is stamped with where its value is read - a
 * {@code CALL_ARGUMENT} capture, at one argument position, at one unit of the
 * client's own method - and that statement is why the client prefix can state
 * {@code Req_out} without the transport frame entering its definition scope
 * (README section 3).  The site is recoverable from
 * {@code callerMethod}/{@code unitIndex}, but re-deriving the semantics from a
 * position is exactly the guess the cut vocabulary exists to avoid.</p>
 */
public class RuntimePlanPortCompactionTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String CLIENT =
            "<example.ClientActivation: int execute(java.lang.Boolean)>";
    private static final String CALLEE =
            "<example.RpcChannel: int callServer(int)>";
    private static final String EXCHANGE =
            "XCH.00000000-0000-3000-8000-000000000001";

    /**
     * The four capture names survive one encode/read round trip of the
     * published plan, on the catalog the composer reads.
     */
    @Test
    public void theCutArgumentCaptureSurvivesPortCompaction()
            throws Exception {
        List<JsonObject> regions = roundTrip(requestPort());

        assertEquals(1, regions.size());
        JsonArray outputs = regions.get(0).getAsJsonArray("outputs");
        assertEquals(1, outputs.size());
        JsonObject port = outputs.get(0).getAsJsonObject();
        assertEquals(CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                port.get(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND)
                        .getAsString());
        assertEquals(0, port.get(
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX).getAsInt());
        assertEquals(CLIENT, port.get(
                CommunicationCatalogContract.PORT_DEFINITION_METHOD)
                .getAsString());
        assertEquals(14, port.get(
                        CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX)
                .getAsInt());
        // The site the capture is stated over is still the client's own
        // method one frame before the transport, under both spellings.
        assertEquals(CLIENT, port.get("callerMethod").getAsString());
        assertEquals(14, port.get("unitIndex").getAsInt());
        assertEquals(CALLEE, port.get("declaredCallee").getAsString());
    }

    /**
     * Compaction still drops what it is for: a port's recorded access history
     * is trace evidence and does not enter the published catalog.
     */
    @Test
    public void compactionStillDropsRecordedAccessHistory() throws Exception {
        JsonObject port = requestPort();
        JsonArray accesses = new JsonArray();
        JsonObject access = new JsonObject();
        access.addProperty("eventSeq", 7);
        access.addProperty("staticAccessSiteId", CALLEE + "#u2");
        accesses.add(access);
        port.add("runtimeAccesses", accesses);

        List<JsonObject> regions = roundTrip(port);

        JsonObject compacted = regions.get(0).getAsJsonArray("outputs")
                .get(0).getAsJsonObject();
        assertTrue(String.valueOf(compacted),
                !compacted.has("runtimeAccesses"));
    }

    /** The cut identity and server parameter survive compaction. */
    @Test
    public void theCutIdentitySurvivesCompaction()
            throws Exception {
        JsonObject port = requestPort();
        port.addProperty(
                CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX, 0);
        port.addProperty(CommunicationCatalogContract.PORT_DIRECTION,
                CommunicationCatalogContract.DIRECTION_REQUEST);
        port.addProperty("portRole", "SERVER");
        port.addProperty(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                EXCHANGE);
        port.addProperty(CommunicationCatalogContract.CALL_SITE_ID,
                CLIENT + "#u14");

        JsonObject compacted = roundTrip(port).get(0)
                .getAsJsonArray("outputs").get(0).getAsJsonObject();

        assertEquals(0, compacted.get(CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX).getAsInt());
        assertEquals(CommunicationCatalogContract.DIRECTION_REQUEST,
                compacted.get(CommunicationCatalogContract.PORT_DIRECTION)
                        .getAsString());
        assertEquals("SERVER",
                compacted.get("portRole")
                        .getAsString());
        assertEquals(EXCHANGE, compacted.get(
                CommunicationCatalogContract.EXCHANGE_SITE_KEY).getAsString());
        assertEquals(CLIENT + "#u14", compacted.get(
                CommunicationCatalogContract.CALL_SITE_ID).getAsString());
    }

    @Test
    public void manualComponentCarrierSurvivesCompaction() throws Exception {
        JsonObject port = requestPort();
        port.addProperty(CommunicationCatalogContract.PORT_COMPONENT_OF,
                "XCH.example.req.parent");
        port.addProperty(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                "TEST_ENCODING_V1");
        port.addProperty(
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                "WIRE/value");
        port.addProperty(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS,
                "example.Carrier");
        port.addProperty(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD,
                "value");
        port.addProperty(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR,
                "I");

        JsonObject compacted = roundTrip(port).get(0)
                .getAsJsonArray("outputs").get(0).getAsJsonObject();

        assertEquals("example.Carrier", compacted.get(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS)
                .getAsString());
        assertEquals("value", compacted.get(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD)
                .getAsString());
        assertEquals("I", compacted.get(
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR)
                .getAsString());
    }

    @Test
    public void staticSymbolicSourceDeclarationsSurviveCompaction()
            throws Exception {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        declaration.addProperty("kind",
                StaticSymbolicSourceDeclaration.KIND);
        declaration.addProperty("authority",
                StaticSymbolicSourceDeclaration.AUTHORITY);
        declaration.addProperty("sourceId", "RPC_COMPARE.VALUE");
        declaration.addProperty("fieldSignature", "<Node: long value>");
        declaration.addProperty("declarationMethod",
                "<Node: void symbolizeInputs()>");
        declaration.addProperty("declarationUnitIndex", 1);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);

        JsonObject region = region(new JsonArray());
        region.add(StaticSymbolicSourceDeclaration.FIELD, declarations);

        String encoded = RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(region));
        File file = new File(folder.getRoot(), "source-plan.jsonl");
        Files.write(file.toPath(), encoded.getBytes(StandardCharsets.UTF_8));
        JsonArray retained = RuntimePlanArtifact.read(file.toPath())
                .regions().get(0).getAsJsonArray(
                        StaticSymbolicSourceDeclaration.FIELD);

        assertEquals(1, retained.size());
        assertEquals(declaration, retained.get(0).getAsJsonObject());
    }

    @Test
    public void compactionRejectsRegionsOutsideTheCurrentSchema() {
        JsonObject current = region(new JsonArray());
        for (String field : new String[]{"schemaVersion", "kind"}) {
            JsonObject malformed = current.deepCopy();
            malformed.remove(field);
            assertRegionRejected(malformed);
        }
        JsonObject wrongVersion = current.deepCopy();
        wrongVersion.addProperty("schemaVersion", 2);
        assertRegionRejected(wrongVersion);
        JsonObject stringVersion = current.deepCopy();
        stringVersion.addProperty("schemaVersion", "3");
        assertRegionRejected(stringVersion);
        JsonObject wrongKind = current.deepCopy();
        wrongKind.addProperty("kind", "REGION_SKELETON");
        assertRegionRejected(wrongKind);
    }

    // ------------------------------------------------------------------
    // Fixture
    // ------------------------------------------------------------------

    private static JsonObject requestPort() {
        JsonObject port = new JsonObject();
        port.addProperty("portId", "XCH.example.req.p0");
        port.addProperty("javaType", "int");
        port.addProperty("sourceKind", "COMMUNICATION_SITE_PORT");
        port.addProperty(
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT);
        port.addProperty(CommunicationCatalogContract.PORT_ARGUMENT_INDEX, 0);
        port.addProperty(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                CLIENT);
        port.addProperty(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 14);
        port.addProperty("callerMethod", CLIENT);
        port.addProperty("unitIndex", 14);
        port.addProperty("declaredCallee", CALLEE);
        return port;
    }

    private List<JsonObject> roundTrip(JsonObject port) throws Exception {
        JsonArray outputs = new JsonArray();
        outputs.add(port);
        JsonObject region = region(outputs);

        String encoded = RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Collections.singletonList(region));
        File file = new File(folder.getRoot(), "concolic_region_plan.jsonl");
        Files.write(file.toPath(),
                encoded.getBytes(StandardCharsets.UTF_8));
        return RuntimePlanArtifact.read(file.toPath()).regions();
    }

    private static JsonObject region(JsonArray outputs) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", "REGION.1");
        region.add("symbolicInputs", new JsonArray());
        region.add("outputs", outputs);
        return region;
    }

    private static void assertRegionRejected(JsonObject region) {
        try {
            RuntimePlanArtifact.encode(
                    Collections.<JsonObject>emptyList(),
                    Collections.<JsonObject>emptyList(),
                    Collections.singletonList(region));
            throw new AssertionError("unsupported region schema was accepted");
        } catch (IllegalArgumentException expected) {
            assertTrue(expected.getMessage().contains("unsupported schema"));
        }
    }
}
