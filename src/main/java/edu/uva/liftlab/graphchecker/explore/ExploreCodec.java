package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The JSON of the exploration contract: tasks, obligations, results.
 *
 * <p>The contract gives the row kinds a codec and leaves these to their
 * readers, so this is where the runtime's and the explorer's spelling of an
 * obligation is fixed.  Addresses go through {@link RowCodec}'s own
 * occurrence form, so a task names an occurrence exactly as every row does
 * and the two join on the rendered address.</p>
 *
 * <p>Reading a field of a row is NOT fixed here: the forgiving accessors are
 * {@code smt.JsonFields}', statically imported, because "what does this
 * member hold when the writer left it out" is one answer for every row kind
 * and this file used to hold a third copy of it.</p>
 */
public final class ExploreCodec {
    /**
     * The session id a gap raised BY this stage carries.
     *
     * <p>{@code GapRow.sessionId} is required, and a gap the exploration
     * itself raises belongs to no replay -- exactly as a composer-raised one
     * belongs to none and says "composition".  Every such row used to pass
     * "", which throws, so the first divergence a wave found killed the
     * wave instead of being reported by it.</p>
     */
    public static final String EXPLORATION = "exploration";

    private ExploreCodec() {
    }

    public static JsonObject writeTask(Task task) {
        JsonObject json = new JsonObject();
        json.addProperty("taskId", task.taskId());
        json.add("focused", RowCodec.writeOccurrence(task.focused()));
        JsonArray factor = new JsonArray();
        for (OccurrenceAddress member : task.factor()) {
            factor.add(RowCodec.writeOccurrence(member));
        }
        json.add("factor", factor);
        json.addProperty("seedSessionId", task.seedSessionId());
        return json;
    }

    public static JsonObject writeObligation(Obligation obligation) {
        JsonObject json = new JsonObject();
        json.addProperty("obligationId", obligation.obligationId());
        json.addProperty("taskId", obligation.taskId());
        json.addProperty("pathId", obligation.pathId());
        json.addProperty("siteId", obligation.siteId());
        json.addProperty("ordinal", obligation.ordinal());
        json.addProperty("flippedOutcome", obligation.flippedOutcome());
        json.add("rootAssignments", strings(obligation.rootAssignments()));
        json.add("answers", strings(obligation.answers()));
        JsonArray unproducible = new JsonArray();
        for (String endpoint : obligation.unproducible()) {
            unproducible.add(endpoint);
        }
        json.add("unproducible", unproducible);
        return json;
    }

    public static Obligation readObligation(JsonObject json) {
        return Obligation.of(optionalString(json, "obligationId"),
                optionalString(json, "taskId"),
                optionalString(json, "pathId"),
                optionalString(json, "siteId"),
                optionalInteger(json, "ordinal", 0),
                optionalBool(json, "flippedOutcome", false),
                map(object(json, "rootAssignments")),
                map(object(json, "answers")),
                list(array(json, "unproducible")));
    }


    /**
     * The WORLD one focus row states: what the replay it drove ran in.
     *
     * <p>The one reader of a focus row on this side -- {@link Corpus} indexes
     * it and {@code runtime.FocusedReplay} enforces it -- so the members are
     * spelled once here and once there, and never in a third place.  The
     * flips are the row's OWN flip first (addressed at its {@code
     * focusedOccurrenceId}, carrying its own obligation id) and then the
     * ones it inherited, in the order the row lists them: that is the order
     * a child of this session inherits them in.</p>
     */
    public static Corpus.World readWorld(JsonObject json) {
        List<Corpus.Flip> flips = new ArrayList<Corpus.Flip>();
        JsonObject own = object(json, "flip");
        String at = optionalString(json, "focusedOccurrenceId");
        if (own.has("siteId")) {
            flips.add(new Corpus.Flip(at, optionalString(own, "siteId"),
                    optionalInteger(own, "ordinal", 0),
                    optionalBool(own, "outcome", false),
                    optionalString(json, "obligationId")));
        }
        for (JsonElement element : array(json, "inheritedFlips")) {
            if (!element.isJsonObject()) continue;
            JsonObject flip = element.getAsJsonObject();
            flips.add(new Corpus.Flip(
                    optionalString(flip, "focusedOccurrenceId"),
                    optionalString(flip, "siteId"),
                    optionalInteger(flip, "ordinal", 0),
                    optionalBool(flip, "outcome", false),
                    optionalString(flip, "obligationId")));
        }
        return new Corpus.World(map(object(json, "rootAssignments")),
                map(object(json, "clockDeltas")),
                map(object(json, "answers")),
                map(object(json, "rootMints")), flips);
    }

    /** One inherited flip, as the focus row states it. */
    public static JsonObject writeFlip(Corpus.Flip flip) {
        JsonObject json = new JsonObject();
        json.addProperty("focusedOccurrenceId", flip.focusedOccurrenceId);
        json.addProperty("siteId", flip.siteId);
        json.addProperty("ordinal", flip.ordinal);
        json.addProperty("outcome", flip.outcome);
        json.addProperty("obligationId", flip.obligationId);
        return json;
    }

    /** One slot of the epoch's skeleton. */
    public static JsonObject writeSlot(SlotTable.Slot slot) {
        JsonObject json = new JsonObject();
        json.addProperty("schemaVersion", 1);
        json.addProperty("kind", "SLOT");
        json.addProperty("interactionId", slot.interactionId());
        json.addProperty("interactionKind", slot.kind.name());
        json.add("producer", RowCodec.writeEndpoint(slot.producer));
        json.add("consumer", RowCodec.writeEndpoint(slot.consumer));
        json.addProperty("openedBySession", slot.openedBySession);
        json.addProperty("openedAtWave", slot.openedAtWave);
        json.addProperty("world", slot.world);
        return json;
    }

    public static SlotTable.Slot readSlot(JsonObject json) {
        return new SlotTable.Slot(
                InteractionKind.valueOf(
                        optionalString(json, "interactionKind")),
                RowCodec.readEndpoint(object(json, "producer")),
                RowCodec.readEndpoint(object(json, "consumer")),
                optionalString(json, "openedBySession"),
                optionalInteger(json, "openedAtWave", 0),
                optionalString(json, "world"));
    }

    private static JsonObject strings(Map<String, String> values) {
        JsonObject json = new JsonObject();
        for (Map.Entry<String, String> entry : values.entrySet()) {
            json.addProperty(entry.getKey(), entry.getValue());
        }
        return json;
    }

    private static Map<String, String> map(JsonObject json) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        for (Map.Entry<String, JsonElement> entry : json.entrySet()) {
            values.put(entry.getKey(), entry.getValue().getAsString());
        }
        return values;
    }

    private static List<String> list(JsonArray array) {
        List<String> values = new ArrayList<String>();
        for (JsonElement element : array) values.add(element.getAsString());
        return values;
    }

}
