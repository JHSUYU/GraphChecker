package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.LocalCaseIdentity;

import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** One imported region-local path observation. */
public final class RelationSummary {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "CONCOLIC_REGION_SUMMARY";
    public static final String INTERACTION_EVENTS = "interactionEvents";

    private final JsonObject row;

    private RelationSummary(JsonObject row) {
        this.row = row;
    }

    /**
     * Decodes a row already expanded by a shared expression-table resolver.
     * The caller and this value must treat the supplied expression DAG as
     * immutable.
     */
    public static RelationSummary decodeExpanded(JsonObject expanded) {
        if (expanded == null) expanded = new JsonObject();
        if (!KIND.equals(optionalString(expanded, "kind"))
                || !exactSchemaVersion(expanded)
                || optionalString(expanded, "regionId").isEmpty()
                || optionalString(expanded, "occurrenceId").isEmpty()
                || optionalString(expanded, "summaryId").isEmpty()
                || optionalString(expanded, LocalCaseIdentity.FIELD).isEmpty()) {
            throw new IllegalArgumentException(
                    "relation summary has an unsupported schema");
        }
        return new RelationSummary(expanded);
    }

    /** Read-only view which retains shared expression-node identity. */
    public JsonObject immutableJson() { return row; }
    public String summaryId() { return optionalString(row, "summaryId"); }
    public String localCaseId() {
        return optionalString(row, LocalCaseIdentity.FIELD);
    }
    public String sourceKey() { return optionalString(row, "sourceKey"); }
    public String occurrenceId() { return optionalString(row, "occurrenceId"); }
    public String regionId() { return optionalString(row, "regionId"); }

    /**
     * Shallow case carrier for DAG-aware passes.  Top-level fields may be
     * added to the returned object; nested values remain immutable views.
     */
    public JsonObject pathCaseView() {
        JsonObject path = new JsonObject();
        for (Map.Entry<String, JsonElement> field : row.entrySet()) {
            path.add(field.getKey(), field.getValue());
        }
        addCase(path, array(row, "pathCondition"));
        return path;
    }

    private void addCase(JsonObject path, JsonElement conditions) {
        path.addProperty("caseId", localCaseId());
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", conditions);
        path.add("guard", guard);
    }

    public boolean pathSetClosed() { return optionalBool(row, "pathSetClosed", false); }

    private static boolean exactSchemaVersion(JsonObject source) {
        JsonElement value = source.get("schemaVersion");
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isNumber()
                && Integer.toString(SCHEMA_VERSION).equals(
                value.getAsString());
    }
}
