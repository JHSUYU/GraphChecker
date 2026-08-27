package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class Hdfs11741SymbolicInputConfigurationTest {
    /** The selector member that the field-only design retired. */
    private static final String SELECTOR_DECLARATIONS =
            "configuredSourceSelectorDeclarations";
    private static final String KEY_ID =
            "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                    + "int keyId>";
    private static final String EXPIRY =
            "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                    + "long expiryDate>";
    private static final String ALL_KEYS =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: java.util.Map allKeys>";
    private static final String NAMENODE_REGION =
            "REGION.2aed59dd-ef36-3105-96a8-99e03878bc89";
    private static final String DATANODE_REGION =
            "REGION.fe3fe30c-9f44-319f-8f3d-07e6bdb58fdb";

    @Test
    public void experimentDeclaresFieldsOnlyAndNeverAnOccurrence()
            throws Exception {
        Path config = Paths.get(System.getProperty("user.dir"),
                "experiments", "hdfs", "hdfs-11741",
                "symbolic-inputs.jsonl");
        List<JsonObject> rows = ArtifactIO.readJsonl(config);

        // Manual input names WHICH FIELDS only.  Every occurrence of a
        // declared field is its own symbolic variable, so the key-bearing
        // regions declare both DelegationKey fields and nothing else.
        assertEquals(Arrays.asList(KEY_ID, EXPIRY),
                fields(rows, NAMENODE_REGION));
        // The DataNode loop region now also symbolizes allKeys: its
        // removeExpiredKeys it.remove() is tracked as a conditional REMOVE_IF
        // (guarded by the symbolic expiry) so the target's allKeys.get(keyId)
        // read-from can flip the removal.
        assertEquals(Arrays.asList(KEY_ID, EXPIRY, ALL_KEYS),
                fields(rows, DATANODE_REGION));
        assertTrue(fields(rows,
                "REGION.ddd831dd-6a8e-3d72-94bc-e67d38797ce9")
                .contains(ALL_KEYS));
        assertTrue(fields(rows,
                "REGION.d842447f-37ce-3501-854b-9388704c804e")
                .contains(ALL_KEYS));
        for (JsonObject row : rows) {
            assertFalse("selector declaration survives on "
                            + row.get("regionId").getAsString(),
                    row.has(SELECTOR_DECLARATIONS));
            assertTrue("empty symbolic-input row: " + row,
                    row.getAsJsonArray("fieldSignatures").size() > 0
                            || row.getAsJsonArray("portIds").size() > 0
                            || row.getAsJsonArray("cells").size() > 0);
        }
    }

    @Test
    public void hookOwnedExpiryStaysConcreteWhileMapStateStaysSymbolic()
            throws Exception {
        Path config = Files.createTempFile("hdfs11741-sources", ".jsonl");
        try {
            String row = "{\"regionId\":\"REGION.NN\","
                    + "\"fieldSignatures\":[\"" + ALL_KEYS + "\"],"
                    + "\"portIds\":[],\"cells\":[]}\n";
            Files.write(config, row.getBytes(StandardCharsets.UTF_8));
            JsonObject region = new JsonObject();
            region.addProperty("regionId", "REGION.NN");
            JsonArray sources = new JsonArray();
            sources.add(source("HDFS11741.KEY_EXPIRY", EXPIRY));
            region.add(StaticSymbolicSourceDeclaration.FIELD, sources);
            ConcolicScheduler.SymbolicInputSelection selection =
                    ConcolicScheduler.SymbolicInputSelection.read(config,
                            Arrays.asList(region));
            JsonObject firstExpiry = action("expiry.1", EXPIRY);
            JsonObject secondExpiry = action("expiry.2", EXPIRY);
            JsonObject mapState = action("map.state", ALL_KEYS);
            JsonArray candidates = new JsonArray();
            candidates.add(firstExpiry);
            candidates.add(secondExpiry);
            candidates.add(mapState);

            JsonArray selected = selection.select("REGION.NN", candidates);

            // The application hook owns the expiry root at every occurrence,
            // so the scheduler must not also mint it as its own input.
            assertEquals("CONCRETE", selected.get(0).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals("CONCRETE", selected.get(1).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals("SYMBOLIC", selected.get(2).getAsJsonObject()
                    .get("mode").getAsString());
            assertFalse(selection.selectedForDiscovery("REGION.NN",
                    firstExpiry));
            assertFalse(selection.selectedForDiscovery("REGION.NN",
                    secondExpiry));
            assertTrue(selection.selectedForDiscovery("REGION.NN",
                    mapState));
        } finally {
            Files.deleteIfExists(config);
        }
    }

    private static JsonObject action(String portId, String field) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("portId", portId);
        action.addProperty("accessFieldSignature", field);
        return action;
    }

    private static JsonObject source(String sourceId, String field) {
        JsonObject source = new JsonObject();
        source.addProperty("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        source.addProperty("kind", StaticSymbolicSourceDeclaration.KIND);
        source.addProperty("authority",
                StaticSymbolicSourceDeclaration.AUTHORITY);
        source.addProperty("sourceId", sourceId);
        source.addProperty("fieldSignature", field);
        source.addProperty("declarationMethod", "<Node: void updateKeys()>");
        source.addProperty("declarationUnitIndex", 3);
        return source;
    }

    private static List<String> fields(
            List<JsonObject> rows, String regionId) {
        for (JsonObject row : rows) {
            if (regionId.equals(row.get("regionId").getAsString())) {
                return fields(row);
            }
        }
        throw new AssertionError("missing region " + regionId);
    }

    private static List<String> fields(JsonObject row) {
        java.util.ArrayList<String> result = new java.util.ArrayList<>();
        for (JsonElement field : row.getAsJsonArray("fieldSignatures")) {
            result.add(field.getAsString());
        }
        return result;
    }
}
