package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.Task;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** The JSON of the exploration contract: tasks, obligations, results. Addresses
 *  use {@link RowCodec}'s occurrence form so tasks and rows join on the
 *  rendered address; field accessors are {@code smt.JsonFields}'. */
public final class ExploreCodec {
    /** Session id of a gap this stage raises ({@code GapRow.sessionId} must be
     *  non-empty). */
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
        json.add("unproducible", list(obligation.unproducible()));
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
                JsonFields.strings(json, "unproducible"));
    }


    /**
     * THE FOCUS ROW ({@code focused_task.jsonl}) a replay runs: focus, factor,
     * the flip ({@code null} when {@code obligation} flips nothing), inherited
     * flips, mint values (a clock as a skew), answers, pairings (the replay
     * is held to them by its {@code expected_edges.jsonl}), each root's mint
     * occurrence, unproducible handoffs and the schedule cut ({@code cut}
     * null: none). Read back by {@link #readWorld}.  {@code declaredTarget}, the
     * case's one occurrence (null: none resolved), is where the replay stops
     * once it observes the fatal ({@code runtime.FocusedReplay}).
     */
    /** One JSON object file, as a wave's artifacts are written. */
    static JsonObject readObject(Path file) throws IOException {
        return JsonParser.parseString(new String(Files.readAllBytes(file),
                StandardCharsets.UTF_8)).getAsJsonObject();
    }

    static JsonObject writeFocusRow(OccurrenceAddress focused,
                                    OccurrenceAddress declaredTarget,
                                    String seedSessionId,
                                    List<OccurrenceAddress> factor,
                                    Obligation obligation,
                                    List<Corpus.Flip> inheritedFlips,
                                    Map<String, String> clockDeltas,
                                    Map<String, String> rootMints,
                                    Map<String, String> pairings,
                                    SchedulePrefix.Cut cut) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "FOCUSED_TASK");
        row.addProperty("taskId", obligation.taskId());
        // Render for OccurrenceAddress.parse, id for grep.
        row.addProperty("focused", focused.render());
        row.addProperty("focusedOccurrenceId", focused.id());
        if (declaredTarget != null) {
            row.addProperty("declaredTarget", declaredTarget.render());
        }
        row.addProperty("seedSessionId", seedSessionId);
        JsonArray members = new JsonArray();
        for (OccurrenceAddress member : factor) members.add(member.render());
        row.add("factor", members);
        row.addProperty("obligationId", obligation.obligationId());
        row.addProperty("pathId", obligation.pathId());
        JsonObject flip = null;
        if (obligation.flips()) {
            flip = new JsonObject();
            flip.addProperty("siteId", obligation.siteId());
            flip.addProperty("ordinal", obligation.ordinal());
            flip.addProperty("outcome", obligation.flippedOutcome());
        }
        row.add("flip", flip);
        // Held like the flip (a wrong arm un-admits); still ONE verdict row.
        JsonArray inherited = new JsonArray();
        for (Corpus.Flip carried : inheritedFlips) {
            inherited.add(writeFlip(carried));
        }
        row.add("inheritedFlips", inherited);
        row.add("rootAssignments", strings(obligation.rootAssignments()));
        // A clock's counterfactual is a SKEW off the replay's own reading.
        row.add("clockDeltas", strings(clockDeltas));
        row.add("answers", strings(obligation.answers()));
        row.add("pairings", strings(pairings));
        // Each root's mint occurrence is focused, or it reads the recording.
        row.add("rootMints", strings(rootMints));
        row.add("unproducible", list(obligation.unproducible()));
        if (cut != null) row.add("schedulePrefix", cut.toJson());
        return row;
    }

    /** The world one focus row states; mirrored by {@code
     *  runtime.FocusedReplay}. Flips: the row's own (at {@code
     *  focusedOccurrenceId}) first, then inherited ones in row order -- the
     *  order a child session inherits them in. */
    public static Corpus.World readWorld(JsonObject json) {
        List<Corpus.Flip> flips = new ArrayList<Corpus.Flip>();
        JsonObject own = object(json, "flip");
        if (own.has("siteId")) flips.add(readFlip(own, json));
        for (JsonElement element : array(json, "inheritedFlips")) {
            if (!element.isJsonObject()) continue;
            JsonObject flip = element.getAsJsonObject();
            flips.add(readFlip(flip, flip));
        }
        return new Corpus.World(map(object(json, "rootAssignments")),
                map(object(json, "clockDeltas")),
                map(object(json, "answers")),
                map(object(json, "rootMints")),
                map(object(json, "pairings")), flips);
    }

    /** One flip's decision; {@code owner} states whose and which obligation
     *  (the row itself for its own flip). */
    private static Corpus.Flip readFlip(JsonObject flip, JsonObject owner) {
        return new Corpus.Flip(optionalString(owner, "focusedOccurrenceId"),
                optionalString(flip, "siteId"),
                optionalInteger(flip, "ordinal", 0),
                optionalBool(flip, "outcome", false),
                optionalString(owner, "obligationId"));
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
        json.addProperty("openedAtRound", slot.openedAtRound);
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
                optionalInteger(json, "openedAtRound", 0),
                optionalString(json, "world"));
    }

    private static JsonObject strings(Map<String, String> values) {
        JsonObject json = new JsonObject();
        for (Map.Entry<String, String> entry : values.entrySet()) {
            json.addProperty(entry.getKey(), entry.getValue());
        }
        return json;
    }

    static JsonArray list(Collection<String> values) {
        JsonArray json = new JsonArray();
        for (String value : values) json.add(value);
        return json;
    }

    /** A string-valued object as a map. */
    static Map<String, String> map(JsonObject json) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        for (Map.Entry<String, JsonElement> entry : json.entrySet()) {
            values.put(entry.getKey(), entry.getValue().getAsString());
        }
        return values;
    }
}
