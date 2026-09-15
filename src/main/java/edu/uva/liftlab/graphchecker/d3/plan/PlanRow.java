package edu.uva.liftlab.graphchecker.d3.plan;

import com.google.gson.JsonObject;

import java.util.List;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * The one plan row shape.  {@link RegionInstancePlan} and {@link ExecutionTask}
 * are two views of it, so the region occurrence, its relation and the exact
 * mint sites it executed are decoded once, here, and consumers take the typed
 * values instead of re-reading the wire.
 *
 * <p>{@link #json()} is the live backing object, never a copy: a decoded row is
 * read-only, and the scheduler alone mutates a task row it has just created and
 * then drops the row it created it from.
 */
public abstract class PlanRow {
    final JsonObject encoded;
    private final String label;
    private final List<ConfiguredSourcePhaseContract.Occurrence> phases;

    /** {@code source} is owned outright; a decoder copies before calling. */
    PlanRow(JsonObject source, String label, boolean completeOccurrence) {
        this(source, label, completeOccurrence, null);
    }

    /** {@code decoded} are the phases a caller that built this row already
     *  holds: passing them keeps one decode per row. */
    PlanRow(JsonObject source, String label, boolean completeOccurrence,
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
                encoded.get(ConfiguredSourcePhaseContract.PLAN_FIELD),
                completeOccurrence);
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

    /** This occurrence's catalog of executed mint sites, decoded once. */
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
