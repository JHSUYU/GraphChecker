package edu.uva.liftlab.graphchecker.d3.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.d3.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.d3.contract.Obligation;
import edu.uva.liftlab.graphchecker.d3.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.d3.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.d3.contract.RootDomain;
import edu.uva.liftlab.graphchecker.d3.contract.RootKind;
import edu.uva.liftlab.graphchecker.d3.contract.RowCodec;
import edu.uva.liftlab.graphchecker.d3.contract.Task;
import edu.uva.liftlab.graphchecker.d3.contract.Verdict;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The JSON of the exploration contract: tasks, obligations, results.
 *
 * <p>The contract gives the row kinds a codec and leaves these to their
 * readers, so this is where the runtime's and the explorer's spelling of an
 * obligation is fixed.  Addresses go through {@link RowCodec}'s own
 * occurrence form, so a task names an occurrence exactly as every row does
 * and the two join on the rendered address.</p>
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

    public static Task readTask(JsonObject json) {
        List<OccurrenceAddress> factor = new ArrayList<OccurrenceAddress>();
        for (JsonElement member : array(json, "factor")) {
            factor.add(RowCodec.readOccurrence(member.getAsJsonObject()));
        }
        return Task.of(string(json, "taskId"),
                RowCodec.readOccurrence(object(json, "focused")), factor,
                string(json, "seedSessionId"));
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
        return Obligation.of(string(json, "obligationId"),
                string(json, "taskId"), string(json, "pathId"),
                string(json, "siteId"), integer(json, "ordinal"),
                bool(json, "flippedOutcome"),
                map(object(json, "rootAssignments")),
                map(object(json, "answers")),
                list(array(json, "unproducible")));
    }

    public static JsonObject writeResult(ObligationResult result) {
        JsonObject json = new JsonObject();
        json.addProperty("obligationId", result.obligationId());
        json.addProperty("verdict", result.verdict().name());
        json.addProperty("sessionId", result.sessionId());
        json.addProperty("detail", result.detail());
        return json;
    }

    public static ObligationResult readResult(JsonObject json) {
        return ObligationResult.of(string(json, "obligationId"),
                Verdict.valueOf(string(json, "verdict")),
                string(json, "sessionId"), string(json, "detail"));
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
        return json;
    }

    public static SlotTable.Slot readSlot(JsonObject json) {
        return new SlotTable.Slot(
                InteractionKind.valueOf(string(json, "interactionKind")),
                RowCodec.readEndpoint(object(json, "producer")),
                RowCodec.readEndpoint(object(json, "consumer")),
                string(json, "openedBySession"),
                integer(json, "openedAtWave"));
    }

    /**
     * One row of the case's {@code root-domains.jsonl}.
     *
     * <p>TWO spellings, one reader, because one file has two readers: the
     * case writes {@code sourceId} with {@code declaredDomainMin/Max}, and
     * a manifest writes {@code rootId} with {@code min/max}.  The composer
     * already accepts both (ComposeMain); an explorer that accepted only
     * one threw on the very file the case declares.</p>
     */
    public static RootDomain readDomain(JsonObject json) {
        String kind = string(json, "kind");
        String rootId = has(json, "rootId") ? string(json, "rootId")
                : string(json, "sourceId");
        String min = has(json, "min") ? string(json, "min")
                : has(json, "declaredDomainMin")
                ? string(json, "declaredDomainMin") : null;
        String max = has(json, "max") ? string(json, "max")
                : has(json, "declaredDomainMax")
                ? string(json, "declaredDomainMax") : null;
        return RootDomain.of(rootId,
                kind.isEmpty() ? RootKind.INTEGRAL : RootKind.valueOf(kind),
                string(json, "recordedValue"), min, max);
    }

    public static JsonObject writeDomain(RootDomain domain) {
        JsonObject json = new JsonObject();
        json.addProperty("rootId", domain.rootId());
        json.addProperty("kind", domain.kind().name());
        json.addProperty("recordedValue", domain.recordedValue());
        if (domain.min() != null) json.addProperty("min", domain.min());
        if (domain.max() != null) json.addProperty("max", domain.max());
        return json;
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

    static boolean has(JsonObject json, String member) {
        JsonElement value = json.get(member);
        return value != null && !value.isJsonNull();
    }

    static String string(JsonObject json, String member) {
        return has(json, member) ? json.get(member).getAsString() : "";
    }

    static int integer(JsonObject json, String member) {
        return has(json, member) ? json.get(member).getAsInt() : 0;
    }

    static boolean bool(JsonObject json, String member) {
        return has(json, member) && json.get(member).getAsBoolean();
    }

    static JsonObject object(JsonObject json, String member) {
        JsonElement value = json.get(member);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    static JsonArray array(JsonObject json, String member) {
        JsonElement value = json.get(member);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }
}
