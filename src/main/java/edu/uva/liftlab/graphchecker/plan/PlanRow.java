package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;

import java.util.List;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** The one plan row shape; {@link RegionInstancePlan} and {@link ExecutionTask}
 *  are views of it. {@link #json()} is the live object: read-only once decoded.
 */
public abstract class PlanRow {
    final JsonObject encoded;
    private final String label;
    private final List<ConfiguredSourcePhaseContract.Occurrence> phases;

    /** {@code source} is owned outright; a decoder copies before calling. */
    PlanRow(JsonObject source, String label) {
        this(source, label, null);
    }

    /** {@code decoded}: phases the caller already holds (one decode per row).
     */
    PlanRow(JsonObject source, String label,
            List<ConfiguredSourcePhaseContract.Occurrence> decoded) {
        this.encoded = source;
        this.label = label;
        require(sourceKey(), "sourceKey");
        require(occurrenceId(), "occurrenceId");
        require(relationKey(), "relationKey");
        require(regionId(), "regionId");
        if (decoded != null) {
            phases = decoded;
            return;
        }
        phases = ConfiguredSourcePhaseContract.occurrencesOf(
                encoded.get(ConfiguredSourcePhaseContract.PLAN_FIELD));
        for (ConfiguredSourcePhaseContract.Occurrence phase : phases) {
            if (!occurrenceId().equals(phase.sourceOccurrenceId())) {
                throw new IllegalArgumentException(
                        "configured source phase belongs to another "
                                + "occurrence: " + phase.phaseId());
            }
        }
    }

    public JsonObject json() { return encoded; }

    public String sourceKey() { return optionalString(encoded, "sourceKey"); }

    public String occurrenceId() { return optionalString(encoded, "occurrenceId"); }

    public String relationKey() { return optionalString(encoded, "relationKey"); }

    public String regionId() { return optionalString(encoded, "regionId"); }

    public List<ConfiguredSourcePhaseContract.Occurrence>
            configuredSourcePhases() {
        return phases;
    }

    final String require(String value, String field) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " requires " + field);
        }
        return result;
    }
}
