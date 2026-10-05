package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The models CONFIRM decided against in this iteration (PIPELINE §10): each
 * claim the program ran and disagreed with, {@code
 * <iteration>/refuted_claims.jsonl} ({@code run_engine.sh campaign_refute}),
 * and each it gave no verdict on, {@code refused_models.jsonl}
 * ({@code campaign_refuse}), one row each off the claim's {@code
 * claim.json}: its {@code model} -- {@code findingKind}, {@code pathId} (the
 * selected path), {@code arms} (the arm selectors the model chose on it),
 * {@code assignment} (its valuation, root id to value) and {@code moved}
 * (the claim's moved roots, a clock by its cell's symbol at the model's
 * instant) -- where it was {@code claimed}, and the confirmation's {@code
 * reason}.  The composition excludes each ({@code Composer#refutations}):
 * that path, those arms and that valuation together are no model of it, so
 * the next claim is another model, or none.  A refused model is excluded
 * like a refuted one, but no run decided it: an UNSAT resting on it is no
 * verdict ({@code ComposeMain#campaignClaim}).
 */
final class Refutations {

    static final String FILE = "refuted_claims.jsonl";
    static final String REFUSED_FILE = "refused_models.jsonl";

    /** One model CONFIRM refuted, or gave no verdict on. */
    static final class Refuted {
        final String pathId;
        final List<String> arms;
        final Map<String, String> assignment;
        final Map<String, String> moved;
        final String reason;
        /** No verdict: CONFIRM did not run the model. */
        final boolean refused;

        private Refuted(String pathId, List<String> arms,
                        Map<String, String> assignment,
                        Map<String, String> moved, String reason,
                        boolean refused) {
            this.pathId = pathId;
            this.arms = Collections.unmodifiableList(arms);
            this.assignment = Collections.unmodifiableMap(assignment);
            this.moved = Collections.unmodifiableMap(moved);
            this.reason = reason;
            this.refused = refused;
        }
    }

    private Refutations() {
    }

    /** This iteration's refuted models, then its refused ones, each in the
     *  order the campaign decided them. */
    static List<Refuted> read(Path iteration) throws IOException {
        List<Refuted> models = new ArrayList<Refuted>();
        if (iteration == null) return models;
        for (String file : new String[]{FILE, REFUSED_FILE}) {
            boolean refused = REFUSED_FILE.equals(file);
            models.addAll(RowCodec.readAll(iteration.resolve(file),
                    row -> row(row, refused)));
        }
        return models;
    }

    private static Refuted row(JsonObject row, boolean refused) {
        JsonObject model = JsonFields.object(row, "model");
        if (model == null) model = new JsonObject();
        return new Refuted(JsonFields.optionalString(model, "pathId"),
                new ArrayList<String>(JsonFields.strings(model, "arms")),
                values(model, "assignment"), values(model, "moved"),
                JsonFields.optionalString(row, "reason"), refused);
    }

    /** One {@code {name: value}} field of a row, in its order. */
    private static Map<String, String> values(JsonObject row, String field) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        JsonObject stated = JsonFields.object(row, field);
        if (stated == null) return values;
        for (Map.Entry<String, JsonElement> value : stated.entrySet()) {
            values.put(value.getKey(), value.getValue().getAsString());
        }
        return values;
    }

    /**
     * {@code <kind>__<path ordinal>__<digest>}: a path's and an arm's
     * selector ({@code Composer#compose}, {@code ComposedFamilies}); the
     * digest names it in every composition, the ordinal only its path's
     * place in one.
     */
    private static final Pattern SELECTOR =
            Pattern.compile("^(.*?)__(\\d+)__(.+)$");

    /** One refuted arm's selector on the path composed at {@code ordinal},
     *  or "" when it is spelled no selector. */
    static String atPath(String selector, String ordinal) {
        Matcher arm = SELECTOR.matcher(selector == null ? "" : selector);
        return arm.matches()
                ? arm.group(1) + "__" + ordinal + "__" + arm.group(3) : "";
    }

    /** The path ordinal one selector names, or "". */
    static String ordinal(String selector) {
        Matcher named = SELECTOR.matcher(selector == null ? "" : selector);
        return named.matches() ? named.group(2) : "";
    }
}
