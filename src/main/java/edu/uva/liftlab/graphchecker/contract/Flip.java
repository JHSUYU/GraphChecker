package edu.uva.liftlab.graphchecker.contract;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.List;

public final class Flip {
    public static final String RERUN = "rerun";

    public final String focusedOccurrenceId;
    public final String siteId;
    public final int ordinal;
    public final boolean outcome;
    public final String obligationId;

    public Flip(String focusedOccurrenceId, String siteId, int ordinal,
                boolean outcome, String obligationId) {
        this.focusedOccurrenceId = focusedOccurrenceId == null ? ""
                : focusedOccurrenceId;
        this.siteId = siteId == null ? "" : siteId;
        this.ordinal = ordinal;
        this.outcome = outcome;
        this.obligationId = obligationId == null ? "" : obligationId;
    }

    public static List<Flip> world(JsonObject focus) {
        List<Flip> flips = new ArrayList<Flip>();
        JsonObject own = object(focus, "flip");
        if (own.has("siteId") && !optionalBool(focus, RERUN, false)) {
            flips.add(read(own, focus));
        }
        for (JsonElement element : array(focus, "inheritedFlips")) {
            if (!element.isJsonObject()) continue;
            JsonObject flip = element.getAsJsonObject();
            flips.add(read(flip, flip));
        }
        return flips;
    }

    private static Flip read(JsonObject flip, JsonObject owner) {
        return new Flip(optionalString(owner, "focusedOccurrenceId"),
                optionalString(flip, "siteId"),
                optionalInteger(flip, "ordinal", 0),
                optionalBool(flip, "outcome", false),
                optionalString(owner, "obligationId"));
    }

    public boolean pairing() {
        return Obligation.pairing(siteId);
    }

    public DecisionRow taken(List<DecisionRow> atOccurrence) {
        DecisionRow last = null;
        for (DecisionRow row : atOccurrence) {
            if (row.siteId().equals(siteId) && row.ordinal() == ordinal) {
                last = row;
            }
        }
        return last != null && last.outcome() == outcome ? last : null;
    }

    public String render() {
        return siteId + "#" + ordinal + " -> " + outcome
                + " at occurrence " + focusedOccurrenceId
                + " (obligation " + obligationId + ")";
    }
}
