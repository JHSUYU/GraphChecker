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

public final class Refutations {

    static final String FILE = "refuted_claims.jsonl";

    static final class Refuted {
        final String pathId;
        final List<String> arms;
        final Map<String, String> assignment;
        final Map<String, String> moved;
        final String reason;

        private Refuted(String pathId, List<String> arms,
                        Map<String, String> assignment,
                        Map<String, String> moved, String reason) {
            this.pathId = pathId;
            this.arms = Collections.unmodifiableList(arms);
            this.assignment = Collections.unmodifiableMap(assignment);
            this.moved = Collections.unmodifiableMap(moved);
            this.reason = reason;
        }
    }

    private Refutations() {
    }

    static List<Refuted> read(Path iteration) throws IOException {
        if (iteration == null) return new ArrayList<Refuted>();
        return RowCodec.readAll(iteration.resolve(FILE), Refutations::row);
    }

    private static Refuted row(JsonObject row) {
        JsonObject model = JsonFields.object(row, "model");
        if (model == null) model = new JsonObject();
        return new Refuted(JsonFields.optionalString(model, "pathId"),
                new ArrayList<String>(JsonFields.strings(model, "arms")),
                values(model, "assignment"), values(model, "moved"),
                JsonFields.optionalString(row, "reason"));
    }

    private static Map<String, String> values(JsonObject row, String field) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        JsonObject stated = JsonFields.object(row, field);
        if (stated == null) return values;
        for (Map.Entry<String, JsonElement> value : stated.entrySet()) {
            values.put(value.getKey(), value.getValue().getAsString());
        }
        return values;
    }

    private static final Pattern SELECTOR =
            Pattern.compile("^(.*?)__(\\d+)__(.+)$");

    static String atPath(String selector, String ordinal) {
        Matcher arm = SELECTOR.matcher(selector == null ? "" : selector);
        return arm.matches()
                ? arm.group(1) + "__" + ordinal + "__" + arm.group(3) : "";
    }

    public static String ordinal(String selector) {
        Matcher named = SELECTOR.matcher(selector == null ? "" : selector);
        return named.matches() ? named.group(2) : "";
    }
}
