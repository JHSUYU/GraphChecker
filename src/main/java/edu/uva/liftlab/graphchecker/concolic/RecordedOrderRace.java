package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.List;
import java.util.Map;

/**
 * The rotation race a witness names when it reads a container the program
 * had not finished writing.
 *
 * <p>A guarded read's candidate arms are exactly the writers the VM retained
 * <em>below</em> the read's own event id, so the arm a model picks is always
 * one of the read's recorded predecessors. That is not by itself interesting.
 * What is interesting -- and what HDFS-17899 is about -- is the arrangement
 * where the model picks the <em>last</em> of those predecessors, i.e. the
 * program's own last writer, and the same location is written again later in
 * the recorded order. The read then legitimately misses a value the program
 * installs a few events afterwards: the target datanode has not yet run its
 * {@code addKeys} for the key the wire is naming, so {@code allKeys.get(keyId)}
 * really does answer null. Upstream fixes exactly that with a retry.</p>
 *
 * <p>Everything here is read from typed rows the Composer publishes: each
 * guarded-read arm carries the {@code fieldVersionId} of the version it names
 * as {@code writerVersionId} and the {@code readEventId} of the read event
 * that published it. Both are session-monotonic, so "written after this read"
 * is the plain comparison {@code writerVersionId > readEventId} over arms of
 * the same {@code sessionLocationKey}. A manifest published before those rows
 * existed simply carries no race, which is the honest answer rather than a
 * guess.</p>
 */
public final class RecordedOrderRace {
    /** The mechanism kind a witness reports this as. */
    public static final String KIND = "ROTATION_RACE";
    /** What the finding rests on: the VM's own recorded write order. */
    public static final String AUTHORITY = "RECORDED_WRITER_ORDER_V1";
    /** The per-arm field naming the version a candidate writer published. */
    public static final String WRITER_VERSION = "writerVersionId";
    /** The per-arm field naming the read event that published the arm. */
    public static final String READ_EVENT = "readEventId";

    private RecordedOrderRace() {
    }

    /**
     * The race this model's fatal-arm choice evidences, or {@code null}.
     *
     * @param manifest the composition manifest, for the writes at the same
     *                 location that no arm of the fatal read could carry
     * @param fatalArms the fatal read's published arms
     * @param model the solver model, by solver term
     */
    public static JsonObject of(JsonObject manifest,
                                List<JsonObject> fatalArms,
                                Map<String, String> model) {
        if (manifest == null || fatalArms == null || model == null) {
            return null;
        }
        for (JsonObject arm : fatalArms) {
            if (!"true".equals(model.get(optionalString(arm, "selector")))) {
                continue;
            }
            if (optionalBool(arm, "initialState", false)) {
                // An initial arm is the absence of a writer, not a late one.
                continue;
            }
            JsonObject race = raceAt(manifest, fatalArms, arm);
            if (race != null) {
                return race;
            }
        }
        return null;
    }

    /** The race one selected writer arm evidences, or {@code null}. */
    private static JsonObject raceAt(JsonObject manifest,
                                     List<JsonObject> fatalArms,
                                     JsonObject selected) {
        long version = optionalLongInteger(selected, WRITER_VERSION, -1L);
        long readEvent = optionalLongInteger(selected, READ_EVENT, -1L);
        String read = optionalString(selected, "readIdentity");
        String location = optionalString(selected,
                SharedStateEvidence.SESSION_LOCATION_FIELD);
        if (version <= 0L || readEvent <= 0L || read.isEmpty()
                || location.isEmpty()) {
            return null;
        }
        // The model took the program's own last writer, not an earlier one it
        // was free to fall back to.
        for (JsonObject arm : fatalArms) {
            if (!read.equals(optionalString(arm, "readIdentity"))) {
                continue;
            }
            if (optionalLongInteger(arm, WRITER_VERSION, -1L) > version) {
                return null;
            }
        }
        JsonObject later = firstWriteAfter(manifest, location, readEvent);
        if (later == null) {
            return null;
        }
        long laterVersion = optionalLongInteger(later, WRITER_VERSION, -1L);
        JsonObject race = new JsonObject();
        race.addProperty("kind", KIND);
        race.addProperty("authority", AUTHORITY);
        race.addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD, location);
        race.addProperty("locationKey", optionalString(selected,
                "locationKey"));
        race.addProperty("readIdentity", read);
        race.addProperty(READ_EVENT, readEvent);
        race.addProperty("selector", optionalString(selected, "selector"));
        race.addProperty("selectedWriterVersionId", version);
        race.addProperty("laterWriterVersionId", laterVersion);
        race.addProperty("laterWriterReadIdentity",
                optionalString(later, "readIdentity"));
        race.addProperty("laterWriterCaseOwner",
                optionalString(later, SymbolicPropagationClosure
                        .WRITER_CASE_OWNER));
        race.addProperty("fatalSite", optionalString(manifest, "fatalSite"));
        race.addProperty("detail", "the fatal read at event " + readEvent
                + " of " + location + " takes its recorded last writer"
                + " (version " + version + ") while the same location is"
                + " written again at version " + laterVersion
                + ", so the value the read is compared against is installed"
                + " after it: a recorded-order rotation race");
        return race;
    }

    /**
     * The earliest write to this location the recording places after the
     * read, taken from every guarded read's arms.
     *
     * <p>A write later than one read is a candidate arm of some later read of
     * the same location, so the union of every read's arms is where the
     * recording states it. Only the earliest is reported: it is the write the
     * fatal read raced, and naming the rest adds nothing.</p>
     */
    private static JsonObject firstWriteAfter(JsonObject manifest,
                                              String location,
                                              long readEvent) {
        JsonObject earliest = null;
        long earliestVersion = Long.MAX_VALUE;
        for (JsonElement element
                : array(object(manifest, "guardedReadModel"), "reads")) {
            if (!element.isJsonObject()) {
                continue;
            }
            for (JsonElement candidate
                    : array(element.getAsJsonObject(), "arms")) {
                if (!candidate.isJsonObject()) {
                    continue;
                }
                JsonObject arm = candidate.getAsJsonObject();
                if (!location.equals(optionalString(arm,
                        SharedStateEvidence.SESSION_LOCATION_FIELD))) {
                    continue;
                }
                long version = optionalLongInteger(arm, WRITER_VERSION, -1L);
                if (version <= readEvent || version >= earliestVersion) {
                    continue;
                }
                earliestVersion = version;
                earliest = arm;
            }
        }
        return earliest;
    }
}
