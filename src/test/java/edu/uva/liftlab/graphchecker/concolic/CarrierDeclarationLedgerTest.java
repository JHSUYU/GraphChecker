package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** The manifest's audit of lowered families against declared carriers. */
public class CarrierDeclarationLedgerTest {

    @Test
    public void declaredLocationsAreTheCarriersAndTheSymbolicInputsFields() {
        JsonObject task = new JsonObject();
        JsonArray carriers = new JsonArray();
        carriers.add(carrier("S", "snapshotCounter"));
        task.add(ExecutionTask.SHARED_CARRIERS, carriers);
        JsonArray actions = new JsonArray();
        actions.add(action("SYMBOLIC", "<A: int value>"));
        actions.add(action("CONCRETE", "<L: long layoutVersion>"));
        task.add("inputActions", actions);

        Set<String> declared = CarrierDeclarationLedger.declaredLocations(
                Collections.singletonList(task));

        assertEquals(new java.util.LinkedHashSet<>(Arrays.asList(
                "S#snapshotCounter", "A#value")), declared);
    }

    @Test
    public void aFamilyOverAnUndeclaredLocationIsNamedNotRefused() {
        JsonObject task = new JsonObject();
        JsonArray carriers = new JsonArray();
        carriers.add(carrier("S", "snapshotCounter"));
        task.add(ExecutionTask.SHARED_CARRIERS, carriers);
        JsonObject model = new JsonObject();
        JsonArray reads = new JsonArray();
        reads.add(read("RFC.counter", "S#snapshotCounter", 3));
        reads.add(read("RFC.children", "D#children", 5));
        reads.add(read("RFC.unnamed", "", 2));
        model.add("reads", reads);

        JsonObject ledger = CarrierDeclarationLedger.of(
                Collections.singletonList(task), model, null);

        assertEquals(3, ledger.get("familyCount").getAsInt());
        assertEquals(1, ledger.get("unnamedFamilyCount").getAsInt());
        assertEquals(1, ledger.get("undeclaredFamilyCount").getAsInt());
        assertEquals(5, ledger.get("undeclaredArmCount").getAsInt());
        assertFalse(ledger.get("consistent").getAsBoolean());
        JsonObject row = ledger.getAsJsonArray("undeclaredFamilies")
                .get(0).getAsJsonObject();
        assertEquals("RFC.children", row.get("readIdentity").getAsString());
        assertEquals("D#children",
                row.getAsJsonArray("declaredField").get(0).getAsString());
        assertEquals(5, ledger.getAsJsonObject("undeclaredArmsByLocation")
                .get("D#children").getAsInt());
    }

    @Test
    public void aModelOverDeclaredLocationsOnlyIsConsistent() {
        JsonObject task = new JsonObject();
        JsonArray carriers = new JsonArray();
        carriers.add(carrier("S", "snapshotCounter"));
        task.add(ExecutionTask.SHARED_CARRIERS, carriers);
        JsonObject model = new JsonObject();
        JsonArray reads = new JsonArray();
        reads.add(read("RFC.counter", "S#snapshotCounter", 3));
        model.add("reads", reads);

        JsonObject ledger = CarrierDeclarationLedger.of(
                Collections.singletonList(task), model, null);

        assertTrue(ledger.get("consistent").getAsBoolean());
        assertEquals(0, ledger.get("undeclaredArmCount").getAsInt());
    }

    private static JsonObject carrier(String owner, String field) {
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind", "DECLARED_FIELD");
        carrier.addProperty("declaringClass", owner);
        carrier.addProperty("fieldName", field);
        carrier.addProperty("descriptor", "I");
        return carrier;
    }

    private static JsonObject action(String mode, String field) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", mode);
        action.addProperty("accessFieldSignature", field);
        return action;
    }

    private static JsonObject read(String identity, String field, int arms) {
        JsonObject read = new JsonObject();
        read.addProperty("readIdentity", identity);
        JsonArray rows = new JsonArray();
        for (int index = 0; index < arms; index++) {
            JsonObject arm = new JsonObject();
            arm.addProperty("selector", "read_selector__" + index);
            arm.addProperty("declaredField", field);
            rows.add(arm);
        }
        read.add("arms", rows);
        return read;
    }
}
