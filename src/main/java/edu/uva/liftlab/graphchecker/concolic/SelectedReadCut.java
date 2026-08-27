package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * The read-from arm a solved model selected, and the gate a replay carries.
 */
public final class SelectedReadCut {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "SELECTED_READ_CUT";
    public static final String PLAN_KIND = "SELECTED_READ_CUT_PLAN";
    public static final String AUTHORITY = "SELECTED_READ_CUT_V1";

    /** Task member one replay carries its selected cut in. */
    public static final String TASK_FIELD = "readCutPlan";

    /** What an installed gate is allowed to do. */
    public static final String OBSERVE_AND_CONFIRM = "OBSERVE_AND_CONFIRM";

    /** The model assigned no value to one of the read's selectors. */
    public static final String MODEL_OMITS_READ_SELECTOR =
            "GATE_MODEL_OMITS_READ_SELECTOR";
    /** Every arm of one read is false in the model. */
    public static final String MODEL_SELECTS_NO_ARM =
            "GATE_MODEL_SELECTS_NO_ARM";
    /** More than one arm of one read is true in the model. */
    public static final String MODEL_SELECTS_SEVERAL_ARMS =
            "GATE_MODEL_SELECTS_SEVERAL_ARMS";
    /** The selected arm has neither a compiled gate nor a named refusal. */
    public static final String SELECTED_ARM_HAS_NO_GATE =
            "GATE_SELECTED_ARM_HAS_NO_GATE";
    /** The selected cut is observed and confirmed, never scheduled. */
    public static final String ORDER_NOT_ENFORCED =
            "GATE_ORDER_NOT_ENFORCED";

    private final List<JsonObject> selections = new ArrayList<>();
    private final List<JsonObject> gates = new ArrayList<>();
    private final List<JsonObject> refusals = new ArrayList<>();

    private SelectedReadCut() {
    }

    /** The cut of a query that declared no read choice at all. */
    public static SelectedReadCut none() { return new SelectedReadCut(); }

    /**
     * Reads one solved model's read-from selectors.
     *
     * @param query  the {@code recordedReadCut} payload the query carried
     * @param values the solver's model, by declared name
     */
    public static SelectedReadCut of(JsonObject query,
                                     Map<String, String> values) {
        SelectedReadCut cut = new SelectedReadCut();
        if (!RecordedSessionModel.isQueryPayload(query)) return cut;
        for (JsonElement element : array(query, "readChoices")) {
            if (!element.isJsonObject()) continue;
            cut.selectRead(element.getAsJsonObject(),
                    array(query, "readCutGates"), values);
        }
        return cut;
    }

    private void selectRead(JsonObject read, JsonArray plans,
                            Map<String, String> values) {
        long readEventId = longInteger(read, "readEventId", 0L);
        JsonObject plan = planFor(plans, readEventId);
        JsonObject selected = null;
        for (JsonElement element : array(read, "candidates")) {
            JsonObject candidate = element.getAsJsonObject();
            String value = values == null ? null
                    : values.get(string(candidate, "selector"));
            if (!"true".equals(value) && !"false".equals(value)) {
                refuse(MODEL_OMITS_READ_SELECTOR, plan, read, candidate,
                        "the model assigns no Boolean to selector "
                                + string(candidate, "selector"));
                return;
            }
            if (!"true".equals(value)) continue;
            if (selected != null) {
                // The query asserts exactly one, so two is a model that does
                // not satisfy its own choice constraint.  Enforcing either arm
                // would be enforcing something the solver did not say.
                refuse(MODEL_SELECTS_SEVERAL_ARMS, plan, read, candidate,
                        "arms " + string(selected, "arm") + " and "
                                + string(candidate, "arm")
                                + " are both true for read " + readEventId);
                return;
            }
            selected = candidate;
        }
        if (selected == null) {
            refuse(MODEL_SELECTS_NO_ARM, plan, read, null,
                    "no arm of read " + readEventId + " is true in the model");
            return;
        }
        install(read, plan, selected);
    }

    private void install(JsonObject read, JsonObject plan,
                         JsonObject selected) {
        String arm = string(selected, "arm");
        JsonObject gate = gateFor(plan, arm);
        JsonObject selection = selection(read, selected);
        if (gate.size() == 0) {
            JsonObject refusal = refusalFor(plan, arm);
            selection.addProperty("installed", false);
            selections.add(selection);
            if (refusal.size() > 0) {
                // The compiler already named why this arm cannot be gated -
                // for example a cut the recorded order contradicts or an
                // unknown writer. That reason is the finding.
                JsonObject named = refusal.deepCopy();
                named.addProperty("selectedByModel", true);
                refusals.add(named);
                return;
            }
            refusals.add(SparseReadCutGate.refusal(SELECTED_ARM_HAS_NO_GATE,
                    subject(read, selected),
                    "the model selected arm " + arm + " of read "
                            + longInteger(read, "readEventId", 0L)
                            + ", which compiled to neither a gate nor a "
                            + "refusal"));
            return;
        }
        String unsafe = SparseReadCutGate.unsafeGateReason(gate);
        if (!unsafe.isEmpty()) {
            // The gate is re-checked against its own invariants here rather
            // than trusted merely because a plan produced it.
            selection.addProperty("installed", false);
            selections.add(selection);
            refusals.add(SparseReadCutGate.refusal(unsafe, gate,
                    "the selected gate does not satisfy the invariants it "
                            + "states"));
            return;
        }
        selection.addProperty("installed", true);
        selections.add(selection);
        gates.add(gate);
        // Installing observes and confirms; it does not schedule.  The order
        // the model chose therefore stays unenforced, and that is a coverage
        // fact of every replay this cut produces, not a footnote.
        refusals.add(SparseReadCutGate.refusal(ORDER_NOT_ENFORCED, gate,
                "the selected cut is observed and confirmed; no wait is "
                        + "installed, so the order is not enforced"));
    }

    private JsonObject selection(JsonObject read, JsonObject selected) {
        JsonObject selection = new JsonObject();
        selection.addProperty("readEventId",
                longInteger(read, "readEventId", 0L));
        selection.addProperty("locationKey", string(read, "locationKey"));
        selection.addProperty("selector", string(selected, "selector"));
        selection.addProperty("arm", string(selected, "arm"));
        selection.addProperty("fieldVersionId",
                longInteger(selected, "fieldVersionId", 0L));
        selection.addProperty("unknown", bool(selected, "unknown", false));
        return selection;
    }

    private void refuse(String reason, JsonObject plan, JsonObject read,
                        JsonObject candidate, String detail) {
        JsonObject subject = subject(read, candidate);
        subject.addProperty("readFromField",
                string(plan, "readFromField"));
        subject.addProperty("readerRegionId",
                string(plan, "readerRegionId"));
        refusals.add(SparseReadCutGate.refusal(reason, subject, detail));
    }

    private static JsonObject subject(JsonObject read, JsonObject candidate) {
        JsonObject subject = new JsonObject();
        subject.addProperty("readEventId",
                longInteger(read, "readEventId", 0L));
        subject.addProperty("locationKey", string(read, "locationKey"));
        subject.addProperty("selector", candidate == null ? ""
                : string(candidate, "arm"));
        return subject;
    }

    private static JsonObject planFor(JsonArray plans, long readEventId) {
        for (JsonElement element : plans) {
            if (!element.isJsonObject()) continue;
            JsonObject plan = element.getAsJsonObject();
            if (longInteger(plan, "readEventId", 0L) == readEventId) {
                return plan;
            }
        }
        return new JsonObject();
    }

    private static JsonObject gateFor(JsonObject plan, String arm) {
        return rowFor(array(plan, "gates"), arm);
    }

    private static JsonObject refusalFor(JsonObject plan, String arm) {
        return rowFor(array(plan, "refusals"), arm);
    }

    private static JsonObject rowFor(JsonArray rows, String arm) {
        for (JsonElement element : rows) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            if (string(row, "selector").equals(arm)) return row.deepCopy();
        }
        return new JsonObject();
    }

    /** Whether this query declared any read choice at all. */
    public boolean isEmpty() {
        return selections.isEmpty() && refusals.isEmpty();
    }

    /** Named gate refusals, in the coverage stream's own gap family. */
    public List<JsonObject> refusals() {
        return Collections.unmodifiableList(refusals);
    }

    /** The selection as one record member. */
    public JsonObject toJson() {
        JsonObject cut = new JsonObject();
        cut.addProperty("schemaVersion", SCHEMA_VERSION);
        cut.addProperty("kind", KIND);
        cut.addProperty("authority", AUTHORITY);
        cut.addProperty("selectedReads", selections.size());
        cut.addProperty("installedGates", gates.size());
        cut.add("selections", copy(selections));
        cut.add("gates", copy(gates));
        cut.add("refusals", copy(refusals));
        return cut;
    }

    /**
     * The plan one replay task carries: the gates to install, and the one
     * thing installing them means.
     */
    public JsonObject replayPlan() {
        if (gates.isEmpty()) return new JsonObject();
        JsonObject plan = new JsonObject();
        plan.addProperty("schemaVersion", SCHEMA_VERSION);
        plan.addProperty("kind", PLAN_KIND);
        plan.addProperty("authority", AUTHORITY);
        plan.addProperty("enforcement", OBSERVE_AND_CONFIRM);
        plan.add("gates", copy(gates));
        return plan;
    }

    /** Whether {@code plan} is a replay plan this class produced. */
    public static boolean isReplayPlan(JsonObject plan) {
        return plan != null
                && PLAN_KIND.equals(string(plan, "kind"))
                && AUTHORITY.equals(string(plan, "authority"))
                && OBSERVE_AND_CONFIRM.equals(string(plan, "enforcement"))
                && array(plan, "gates").size() > 0;
    }

    /** The replay plan one task carries, or the empty object. */
    public static JsonObject planOf(JsonObject task) {
        JsonObject plan = object(task, TASK_FIELD);
        return isReplayPlan(plan) ? plan : new JsonObject();
    }

    private static JsonArray copy(List<JsonObject> rows) {
        JsonArray array = new JsonArray();
        for (JsonObject row : rows) array.add(row.deepCopy());
        return array;
    }
}
