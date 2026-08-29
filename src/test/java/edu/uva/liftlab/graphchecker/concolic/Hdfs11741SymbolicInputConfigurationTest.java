package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class Hdfs11741SymbolicInputConfigurationTest {
    private static final String EXPIRY =
            "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                    + "long expiryDate>";
    private static final String ALL_KEYS =
            "<org.apache.hadoop.hdfs.security.token.block."
                    + "BlockTokenSecretManager: java.util.Map allKeys>";
    @Test
    public void experimentCarriesNoStaleRegionSpecificRoots()
            throws Exception {
        Path config = Paths.get(System.getProperty("user.dir"),
                "experiments", "hdfs", "hdfs-11741",
                "symbolic-inputs.jsonl");
        // Region ids and generic map/field roots are generation-local.  The
        // current experiment deliberately pins none: K and expiry are owned
        // by the explicit NameNode hooks, while Balancer/DataNode state must
        // receive those expressions through real propagation and handoff.
        assertTrue(ArtifactIO.readJsonl(config).isEmpty());
    }

    @Test
    public void emptySelectionLeavesGenericInputsConcrete()
            throws Exception {
        Path config = Files.createTempFile("hdfs11741-sources", ".jsonl");
        try {
            Files.write(config, new byte[0]);
            JsonObject region = new JsonObject();
            region.addProperty("regionId", "REGION.NN");
            JsonArray sources = new JsonArray();
            sources.add(source("HDFS11741.NAMENODE.KEY_EXPIRY", EXPIRY));
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

            // Explicit source hooks remain the sole root authority.  Empty
            // manual selection means the scheduler mints neither those fields
            // nor a free allKeys state in NN, Balancer, or DataNode regions.
            assertEquals("CONCRETE", selected.get(0).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals("CONCRETE", selected.get(1).getAsJsonObject()
                    .get("mode").getAsString());
            assertEquals("CONCRETE", selected.get(2).getAsJsonObject()
                    .get("mode").getAsString());
            assertFalse(selection.selectedForDiscovery("REGION.NN",
                    firstExpiry));
            assertFalse(selection.selectedForDiscovery("REGION.NN",
                    secondExpiry));
            assertFalse(selection.selectedForDiscovery("REGION.NN",
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

}
