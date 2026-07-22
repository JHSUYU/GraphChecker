package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;

/** Immutable selector for the initial, unforced capture of a target branch. */
public final class BranchCaptureSelector {
    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "BINARY_BRANCH_CAPTURE_SELECTOR";
    private static final String ID_PREFIX = "BRANCH.CAPTURE.";

    private final String siteId;
    private final int occurrence;
    private final boolean desiredOutcome;
    private final String selectorId;

    private BranchCaptureSelector(String siteId, int occurrence,
                                  boolean desiredOutcome) {
        if (siteId == null || siteId.trim().isEmpty() || occurrence < 1) {
            throw new IllegalArgumentException(
                    "capture selector requires a site and occurrence");
        }
        this.siteId = siteId.trim();
        this.occurrence = occurrence;
        this.desiredOutcome = desiredOutcome;
        this.selectorId = ID_PREFIX + CanonicalJson.sha256(coreJson());
    }

    public static BranchCaptureSelector of(String siteId, int occurrence,
                                           boolean desiredOutcome) {
        return new BranchCaptureSelector(siteId, occurrence, desiredOutcome);
    }

    public static BranchCaptureSelector fromJson(JsonObject json) {
        requireExactKeys(json, "schemaVersion", "kind", "selectorId",
                "siteId", "occurrence", "desiredOutcome");
        if (integer(json, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(json, "kind"))) {
            throw new IllegalArgumentException(
                    "unsupported branch capture selector schema");
        }
        JsonElement outcome = json.get("desiredOutcome");
        if (outcome == null || !outcome.isJsonPrimitive()
                || !outcome.getAsJsonPrimitive().isBoolean()) {
            throw new IllegalArgumentException(
                    "capture selector desiredOutcome must be Boolean");
        }
        BranchCaptureSelector result = of(string(json, "siteId"),
                integer(json, "occurrence", -1), outcome.getAsBoolean());
        if (!result.selectorId.equals(string(json, "selectorId"))) {
            throw new IllegalArgumentException(
                    "branch capture content hash does not match selectorId");
        }
        return result;
    }

    public JsonObject toJson() {
        JsonObject result = coreJson();
        result.addProperty("selectorId", selectorId);
        return (JsonObject) CanonicalJson.copy(result);
    }

    public String siteId() {
        return siteId;
    }

    public int occurrence() {
        return occurrence;
    }

    public boolean desiredOutcome() {
        return desiredOutcome;
    }

    private JsonObject coreJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("siteId", siteId);
        result.addProperty("occurrence", occurrence);
        result.addProperty("desiredOutcome", desiredOutcome);
        return result;
    }

    private static void requireExactKeys(JsonObject object,
                                         String... allowed) {
        if (object == null) {
            throw new IllegalArgumentException(
                    "branch capture selector is required");
        }
        Set<String> expected = new LinkedHashSet<>(Arrays.asList(allowed));
        Set<String> actual = new LinkedHashSet<>();
        for (java.util.Map.Entry<String, JsonElement> entry
                : object.entrySet()) {
            actual.add(entry.getKey());
        }
        if (!actual.equals(expected)) {
            throw new IllegalArgumentException(
                    "branch capture selector keys must be " + expected
                            + " but were " + actual);
        }
    }

    private static int integer(JsonObject object, String name, int fallback) {
        JsonElement value = object == null ? null : object.get(name);
        try {
            return value == null || !value.isJsonPrimitive()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException malformed) {
            return fallback;
        }
    }

    private static String string(JsonObject object, String name) {
        JsonElement value = object == null ? null : object.get(name);
        return value == null || !value.isJsonPrimitive()
                ? "" : value.getAsString();
    }
}
