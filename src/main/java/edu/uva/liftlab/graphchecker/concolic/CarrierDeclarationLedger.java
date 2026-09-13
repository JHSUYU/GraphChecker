package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Whether every guarded-read family the composer lowered is over a location
 * the execution task plan declared.
 *
 * <p>The composer manufactures no family of its own: every arm comes from a
 * VM {@code ReadFromExpression}, and the VM versions a location only after
 * the replay selected it as a shared carrier -- from the task's
 * {@code sharedCarriers}, which {@link SharedCarrierSlice} narrows to the
 * root-dependence slice, or from a SYMBOLIC input's own field
 * ({@code ConcolicTaskPlan.declareSymbolicFieldCarriers}), which the root
 * policy narrows to the same slice.  So a family over an undeclared location
 * is not something to gate here; it is evidence the plan and the recording
 * disagree, and this ledger says so in the manifest.  Against a task plan
 * narrower than the one the recording ran under -- the offline way to ask
 * what a re-plan buys -- it names exactly the families that plan would not
 * have produced.</p>
 */
final class CarrierDeclarationLedger {
    static final String MANIFEST_FIELD = "carrierDeclarations";
    static final String KIND = "CARRIER_DECLARATION_LEDGER";

    private CarrierDeclarationLedger() {
    }

    /**
     * The {@code owner#field} keys the task plan declares as shared
     * carriers: every {@code sharedCarriers} row, and the field of every
     * SYMBOLIC input action, spelled as the replay declares them.
     */
    static Set<String> declaredLocations(Collection<JsonObject> taskRows) {
        Set<String> keys = new LinkedHashSet<>();
        for (JsonObject task : taskRows == null
                ? java.util.Collections.<JsonObject>emptyList() : taskRows) {
            for (JsonElement element : array(task,
                    ExecutionTask.SHARED_CARRIERS)) {
                if (!element.isJsonObject()) continue;
                String key = SharedCarrierSlice.location(
                        element.getAsJsonObject());
                if (!key.isEmpty()) keys.add(key);
            }
            for (JsonElement element : array(task,
                    InputActionCatalog.FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                if (!InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(action, "mode"))) {
                    continue;
                }
                JsonArray declarations = array(action,
                        "fieldPathDeclarations");
                String leaf = declarations.size() > 0
                        && declarations.get(declarations.size() - 1)
                        .isJsonPrimitive()
                        ? declarations.get(declarations.size() - 1)
                        .getAsString() : "";
                FieldPathSpec.DeclaredField field =
                        FieldPathSpec.declaredField(firstNonBlank(leaf,
                                optionalString(action, "leafFieldSignature"),
                                optionalString(action,
                                        "accessFieldSignature")));
                if (field == null) continue;
                String key = SharedFieldFlow.fieldKey(field.owner(),
                        field.name());
                if (!key.isEmpty()) keys.add(key);
            }
        }
        return keys;
    }

    /**
     * The ledger over one composed guarded-read model.
     *
     * <p>A read's location is the {@code declaredField} its arms carry
     * (the recorded carrier that versioned it); a read whose arms name none
     * is counted as unnamed rather than undeclared, because it states no
     * location the plan could have declared.</p>
     */
    static JsonObject of(Collection<JsonObject> taskRows,
                         JsonObject guardedReadModel,
                         JsonObject taskPlanArtifact) {
        Set<String> declared = declaredLocations(taskRows);
        JsonObject ledger = new JsonObject();
        ledger.addProperty("schemaVersion", 1);
        ledger.addProperty("kind", KIND);
        if (taskPlanArtifact != null) {
            ledger.add("taskPlanArtifact", taskPlanArtifact);
        }
        ledger.addProperty("declaredLocationCount", declared.size());
        ledger.add("declaredLocations", strings(declared));
        JsonArray undeclared = new JsonArray();
        Map<String, Integer> undeclaredArmsByLocation = new LinkedHashMap<>();
        int families = 0;
        int unnamed = 0;
        int undeclaredArms = 0;
        for (JsonElement element : array(guardedReadModel, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            families++;
            JsonArray arms = array(read, "arms");
            Set<String> fields = new LinkedHashSet<>();
            for (JsonElement arm : arms) {
                if (!arm.isJsonObject()) continue;
                String field = optionalString(arm.getAsJsonObject(),
                        "declaredField");
                if (!field.isEmpty()) fields.add(field);
            }
            if (fields.isEmpty()) {
                unnamed++;
                continue;
            }
            Set<String> missing = new LinkedHashSet<>();
            for (String field : fields) {
                if (!declared.contains(field)) missing.add(field);
            }
            if (missing.isEmpty()) continue;
            JsonObject row = new JsonObject();
            row.addProperty("readIdentity",
                    optionalString(read, "readIdentity"));
            row.add("declaredField", strings(missing));
            row.addProperty("armCount", arms.size());
            undeclared.add(row);
            undeclaredArms += arms.size();
            for (String field : missing) {
                undeclaredArmsByLocation.merge(field, arms.size(),
                        Integer::sum);
            }
        }
        ledger.addProperty("familyCount", families);
        ledger.addProperty("unnamedFamilyCount", unnamed);
        ledger.addProperty("undeclaredFamilyCount", undeclared.size());
        ledger.addProperty("undeclaredArmCount", undeclaredArms);
        JsonObject byLocation = new JsonObject();
        for (Map.Entry<String, Integer> entry
                : undeclaredArmsByLocation.entrySet()) {
            byLocation.addProperty(entry.getKey(), entry.getValue());
        }
        ledger.add("undeclaredArmsByLocation", byLocation);
        ledger.add("undeclaredFamilies", undeclared);
        ledger.addProperty("consistent", undeclared.size() == 0);
        return ledger;
    }

    /** The manifest's own read model, for a ledger computed after the fact. */
    static JsonObject readModel(JsonObject manifest) {
        return object(manifest, "guardedReadModel");
    }

    private static JsonArray strings(Collection<String> values) {
        JsonArray rows = new JsonArray();
        for (String value : values) rows.add(value);
        return rows;
    }
}
