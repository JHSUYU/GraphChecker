package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Names the bounded concrete path a branch contract describes.
 *
 * <p>Trace call ids deliberately do not participate: repeated activations
 * with the same relevant branch outcomes are interchangeable replay seeds,
 * while distinct outcome combinations remain parallel seeds.</p>
 *
 * <p>The key is a function of one branch contract and nothing else, and every
 * producer of a key derives it here.  A name computed from one branch list
 * and published beside a different one is not an identity: two contracts that
 * are in fact the same path then carry different names, and a valuation bound
 * to one of those names says nothing about the path it was solved for.</p>
 */
public final class BoundedPathSeed {
    public static final String PREFIX = "PATH.SEED.";

    private BoundedPathSeed() {
    }

    /** Path identity of the branch contract exactly as published. */
    public static String key(JsonArray branches) {
        List<String> decisions = new ArrayList<>();
        if (branches != null) {
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                String site = string(branch, "siteId");
                if (site.isEmpty()) continue;
                decisions.add(decision(site, branch));
            }
        }
        Collections.sort(decisions);
        String identity = decisions.isEmpty()
                ? "EMPTY_BOUNDED_PATH" : String.join("\n--\n", decisions);
        return PREFIX + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    private static String decision(String site, JsonObject branch) {
        List<JsonObject> occurrences = new ArrayList<>();
        for (JsonElement element : array(branch, "occurrences")) {
            if (element.isJsonObject()) {
                occurrences.add(element.getAsJsonObject());
            }
        }
        StringBuilder decision = new StringBuilder(site);
        if (occurrences.isEmpty()) {
            return decision.append("\nUNOBSERVED").toString();
        }
        Collections.sort(occurrences, Comparator.comparingInt(
                value -> integer(value, "occurrence", Integer.MAX_VALUE)));
        for (JsonObject occurrence : occurrences) {
            decision.append('\n')
                    .append(integer(occurrence, "occurrence", -1))
                    .append('=')
                    .append(outcome(occurrence));
        }
        return decision.toString();
    }

    private static String outcome(JsonObject occurrence) {
        JsonElement value = occurrence.get("outcome");
        if (value == null || value.isJsonNull()
                || !value.isJsonPrimitive()) {
            return "null";
        }
        return value.getAsJsonPrimitive().isBoolean()
                ? String.valueOf(value.getAsBoolean())
                : value.getAsString();
    }
}
