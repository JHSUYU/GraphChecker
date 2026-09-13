package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Which shared carriers a scheduled task still declares.
 *
 * <p>{@code RuntimeRegionPlanner.declareSharedCarriers} publishes, on every
 * closure goal, every shared field its region reads or writes at an exact
 * runtime access; the task copies the list and the replay versions each of
 * them -- one guarded-read family per read, one arm per writer.  The root
 * policy meanwhile narrows the task's SYMBOLIC actions to the root-dependence
 * slice ({@link ConcolicScheduler.RootDependenceSlice}), so a task can carry
 * a field no root can move: HDFS-17960 declared ten locations, of which the
 * slice reaches three.  A carrier off the slice buys families over recorded
 * constants -- {@code INodeDirectory#children} alone was 11 reads and 31
 * arms in a formula the root never touches.</p>
 *
 * <p>A carrier is therefore kept only when the slice reaches its location
 * ({@link ConcolicScheduler.RootDependenceSlice#reachesLocation}): the root's
 * own field, every field on the forward closure from a root, and the field of
 * every action the slice carries -- which is what keeps the fatal read's own
 * location.  Everything else is recorded at its concrete value: no versions,
 * no families.  When the slice is withheld nothing is dropped, exactly as
 * nothing is narrowed or pruned then.</p>
 */
final class SharedCarrierSlice {
    /** The artifact beside the replay task slice: one telemetry row, then
     *  one decision per declared carrier of every scheduled task. */
    static final String ARTIFACT = "shared_carrier_slice.jsonl";
    static final String TELEMETRY = "SHARED_CARRIER_SLICE";
    static final String DECISION = "SHARED_CARRIER_DECISION";
    /** Decision reason of a carrier whose location no root reaches. */
    static final String DROPPED = "SHARED_CARRIER_NOT_ROOT_DEPENDENT";
    /** Decision reason of a carrier the task still declares. */
    static final String KEPT = "SHARED_CARRIER_KEPT";
    /** Decision reason when the slice narrowed nothing. */
    static final String WITHHELD = "SHARED_CARRIER_SLICE_WITHHELD";

    private final boolean applied;
    private final String sliceReason;
    private final List<JsonObject> decisions;
    private final Set<String> keptLocations;
    private final Set<String> droppedLocations;
    private final int kept;
    private final int dropped;

    private SharedCarrierSlice(boolean applied, String sliceReason,
                               List<JsonObject> decisions,
                               Set<String> keptLocations,
                               Set<String> droppedLocations,
                               int kept, int dropped) {
        this.applied = applied;
        this.sliceReason = sliceReason;
        this.decisions = decisions;
        this.keptLocations = keptLocations;
        this.droppedLocations = droppedLocations;
        this.kept = kept;
        this.dropped = dropped;
    }

    /**
     * Narrows the {@code sharedCarriers} of every task in place and records
     * one decision per declared carrier.
     *
     * <p>The task row is the live row ({@code ExecutionTask#json()}): the
     * scheduler annotates the task it has just created, and no typed member
     * the task decoded is derived from these carriers.  A task whose every
     * carrier is dropped loses the member rather than keeping an empty list,
     * which is how a goal that declared none is spelled.</p>
     */
    static SharedCarrierSlice apply(
            Collection<ExecutionTask> tasks,
            ConcolicScheduler.SymbolicInputSelection selection) {
        ConcolicScheduler.RootDependenceSlice slice =
                selection.carrierSlice();
        boolean applied = slice.usable();
        List<JsonObject> decisions = new ArrayList<>();
        Set<String> keptLocations = new LinkedHashSet<>();
        Set<String> droppedLocations = new LinkedHashSet<>();
        int kept = 0;
        int dropped = 0;
        for (ExecutionTask task : tasks) {
            JsonObject row = task.json();
            JsonArray declared = array(row, ExecutionTask.SHARED_CARRIERS);
            if (declared.size() == 0) continue;
            JsonArray retained = new JsonArray();
            for (JsonElement element : declared) {
                if (!element.isJsonObject()) {
                    retained.add(element);
                    continue;
                }
                JsonObject carrier = element.getAsJsonObject();
                String location = location(carrier);
                boolean keep = !applied
                        || slice.reachesLocation(location, null);
                if (keep) {
                    retained.add(carrier);
                    kept++;
                    keptLocations.add(location);
                } else {
                    dropped++;
                    droppedLocations.add(location);
                }
                decisions.add(decision(row, carrier, location, applied,
                        keep));
            }
            if (retained.size() == 0) {
                row.remove(ExecutionTask.SHARED_CARRIERS);
            } else if (retained.size() != declared.size()) {
                row.add(ExecutionTask.SHARED_CARRIERS, retained);
            }
        }
        return new SharedCarrierSlice(applied,
                applied ? "ROOT_DEPENDENT_CARRIERS"
                        : "NO_ROOT_CELL_IN_REFINED_GRAPH",
                decisions, keptLocations, droppedLocations, kept, dropped);
    }

    /** The {@code owner#field} key one carrier declaration names. */
    static String location(JsonObject carrier) {
        return SharedFieldFlow.fieldKey(
                optionalString(carrier, "declaringClass"),
                optionalString(carrier, "fieldName"));
    }

    private static JsonObject decision(JsonObject task, JsonObject carrier,
                                       String location, boolean applied,
                                       boolean keep) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", DECISION);
        row.addProperty("regionId", optionalString(task, "regionId"));
        row.addProperty("occurrenceId", optionalString(task, "occurrenceId"));
        row.addProperty("taskId", optionalString(task, "taskId"));
        row.addProperty("carrierKind", optionalString(carrier, "kind"));
        row.addProperty("declaringClass",
                optionalString(carrier, "declaringClass"));
        row.addProperty("fieldName", optionalString(carrier, "fieldName"));
        row.addProperty("descriptor", optionalString(carrier, "descriptor"));
        row.addProperty("location", location);
        row.addProperty("decision", keep ? "KEEP" : "DROP");
        row.addProperty("reason", !applied ? WITHHELD
                : keep ? KEPT : DROPPED);
        return row;
    }

    /** False when narrowing was withheld; then every carrier is kept. */
    boolean applied() {
        return applied;
    }

    int keptCarrierCount() {
        return kept;
    }

    int droppedCarrierCount() {
        return dropped;
    }

    /** The distinct locations no task declares any more. */
    Set<String> droppedLocations() {
        return droppedLocations;
    }

    /**
     * The artifact rows: a telemetry summary, then one decision per
     * declared carrier so "why does this task not version that field" is
     * answerable from one file.
     */
    List<JsonObject> rows() {
        List<JsonObject> rows = new ArrayList<>();
        rows.add(telemetry());
        rows.addAll(decisions);
        return rows;
    }

    /** The summary alone, for the schedule index. */
    JsonObject telemetry() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", TELEMETRY);
        row.addProperty("sharedCarrierSliceApplied", applied);
        row.addProperty("sharedCarrierSliceReason", sliceReason);
        row.addProperty("declaredCarrierCount", kept + dropped);
        row.addProperty("keptCarrierCount", kept);
        row.addProperty("droppedCarrierCount", dropped);
        row.addProperty("keptLocationCount", keptLocations.size());
        row.addProperty("droppedLocationCount", droppedLocations.size());
        row.add("keptLocations", strings(keptLocations));
        row.add("droppedLocations", strings(droppedLocations));
        JsonObject byOccurrence = new JsonObject();
        for (Map.Entry<String, Integer> entry
                : droppedByOccurrence().entrySet()) {
            byOccurrence.addProperty(entry.getKey(), entry.getValue());
        }
        row.add("droppedByOccurrence", byOccurrence);
        return row;
    }

    private Map<String, Integer> droppedByOccurrence() {
        Map<String, Integer> counts = new LinkedHashMap<>();
        for (JsonObject decision : decisions) {
            if (!"DROP".equals(optionalString(decision, "decision"))) continue;
            counts.merge(optionalString(decision, "occurrenceId"), 1,
                    Integer::sum);
        }
        return counts;
    }

    private static JsonArray strings(Collection<String> values) {
        JsonArray rows = new JsonArray();
        for (String value : values) rows.add(value);
        return rows;
    }
}
