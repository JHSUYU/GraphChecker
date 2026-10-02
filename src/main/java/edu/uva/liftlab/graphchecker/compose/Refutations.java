package edu.uva.liftlab.graphchecker.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The models CONFIRM refuted in this iteration, {@code
 * <iteration>/refuted_claims.jsonl} (PIPELINE §10): one row per claim the
 * program did not agree with, appended by the campaign
 * ({@code run_engine.sh campaign_refute}) off the claim's {@code claim.json}
 * -- {@code pathId} (the selected path), {@code arms} (the arm selectors the
 * model chose on it), {@code assignment} (its valuation, root id to value)
 * and {@code reason} (the confirmation's).  The composition excludes each
 * ({@code Composer#refutations}): that path, those arms and that valuation
 * together are no model of it, so the next claim is another model, or none.
 */
final class Refutations {

    static final String FILE = "refuted_claims.jsonl";

    /** One refuted model. */
    static final class Refuted {
        final String pathId;
        final List<String> arms;
        final Map<String, String> assignment;
        final String reason;

        private Refuted(String pathId, List<String> arms,
                        Map<String, String> assignment, String reason) {
            this.pathId = pathId;
            this.arms = Collections.unmodifiableList(arms);
            this.assignment = Collections.unmodifiableMap(assignment);
            this.reason = reason;
        }
    }

    private Refutations() {
    }

    /** This iteration's refuted models, in the order they were refuted. */
    static List<Refuted> read(Path iteration) throws IOException {
        if (iteration == null
                || !Files.isRegularFile(iteration.resolve(FILE))) {
            return Collections.emptyList();
        }
        return RowCodec.readAll(iteration.resolve(FILE), Refutations::row);
    }

    private static Refuted row(JsonObject row) {
        Map<String, String> assignment = new LinkedHashMap<String, String>();
        JsonObject stated = JsonFields.object(row, "assignment");
        if (stated != null) {
            for (Map.Entry<String, JsonElement> root : stated.entrySet()) {
                assignment.put(root.getKey(), root.getValue().getAsString());
            }
        }
        return new Refuted(JsonFields.optionalString(row, "pathId"),
                new ArrayList<String>(JsonFields.strings(row, "arms")),
                assignment, JsonFields.optionalString(row, "reason"));
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
