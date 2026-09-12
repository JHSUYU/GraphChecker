package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * An indexed container field is declared as one whole-state location, and
 * never as both a whole state and a reference slot.
 */
public class IndexedCarrierDeclarationTest {

    @Test
    public void aBoundedListFieldIsDeclaredAsWholeState() {
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        Map<String, Object> snapshots = port("<org.apache.hadoop.hdfs.server"
                + ".namenode.snapshot.DirectorySnapshottableFeature:"
                + " java.util.List snapshotsByNames>");
        snapshots.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, snapshots, snapshots);

        // Declared as a reference slot it would publish one write for the
        // list's construction and nothing for any add or remove.
        String key = "MAP_STATE\norg.apache.hadoop.hdfs.server.namenode"
                + ".snapshot.DirectorySnapshottableFeature"
                + "#snapshotsByNames:Ljava/util/List;";
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                carriers.get(key).get("kind"));
    }

    @Test
    public void aBoundedMapFieldKeepsItsWholeStateDeclaration() {
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        Map<String, Object> entries = port(
                "<example.State: java.util.Map entries>");
        entries.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, entries, entries);
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                carriers.get("MAP_STATE\nexample.State#entries"
                        + ":Ljava/util/Map;").get("kind"));
    }

    @Test
    public void anArrayFieldKeepsItsElementAddressing() {
        // An array's elements already have their own locations; selecting the
        // array whole would name the same storage twice.
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        Map<String, Object> keys = port("<example.State: int[] keys>");
        keys.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(carriers, keys, keys);
        assertTrue(carriers.keySet().toString(), carriers.containsKey(
                "DECLARED_FIELD\nexample.State#keys:[I"));
    }

    @Test
    public void aFieldIsNeverBothAWholeStateAndAReferenceSlot() {
        String field = "<example.State: java.util.List rows>";
        List<SharedStateCapture.SharedCarrierRequest> conflicting =
                Arrays.asList(
                        request(SharedStateEvidence.LOCATION_KIND_MAP_STATE),
                        request("INSTANCE_FIELD"));
        assertTrue(SharedStateCapture.wholeStateAndPointerCarrier(
                conflicting, field));

        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                Collections.singletonList(request(
                        SharedStateEvidence.LOCATION_KIND_MAP_STATE)),
                field));
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                Collections.singletonList(request("INSTANCE_FIELD")), field));
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                new ArrayList<SharedStateCapture.SharedCarrierRequest>(),
                field));
        // A different field never conflicts with this one.
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                conflicting, "<example.State: java.util.List other>"));
    }

    private static SharedStateCapture.SharedCarrierRequest request(
            String kind) {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("kind", kind);
        declaration.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        declaration.addProperty("declaringClass", "example.State");
        declaration.addProperty("fieldName", "rows");
        declaration.addProperty("descriptor", "Ljava/util/List;");
        return new SharedStateCapture.SharedCarrierRequest(
                declaration, true);
    }

    private static Map<String, Object> port(String declaration) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("fieldPathDeclarations",
                Collections.singletonList(declaration));
        port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        return port;
    }
}
