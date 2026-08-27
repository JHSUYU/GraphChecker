package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Canonical carrier for one output port whose bounded execution produced
 * several write versions at one static site.  The version ordinal is the
 * site-local bounded occurrence index inside one region activation, not a
 * cross-execution identity: which version a reader observes is settled by the
 * composed versioned channel, so every bounded version is exported and each
 * becomes one guarded relation case.
 */
public final class BoundedOutputVersions {
    public static final String KIND = "BOUNDED_OUTPUT_VERSION_SET";
    public static final String AUTHORITY =
            "SITE_LOCAL_BOUNDED_OUTPUT_VERSION_INDEX_V1";
    /** Guard condition type selecting exactly one exported version. */
    public static final String VERSION_SELECTION_TYPE =
            "OutputVersionSelection";

    private BoundedOutputVersions() {
    }

    public static JsonObject encodeVersionSet(
            String outputSiteId,
            NavigableMap<Integer, JsonElement> expressionsByOrdinal) {
        if (outputSiteId == null || outputSiteId.isEmpty()
                || expressionsByOrdinal == null
                || expressionsByOrdinal.size() < 2) {
            throw new IllegalArgumentException(
                    "a bounded version set requires one site and at least "
                            + "two versions");
        }
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        result.addProperty("outputSiteId", outputSiteId);
        JsonArray versions = new JsonArray();
        for (Map.Entry<Integer, JsonElement> entry
                : expressionsByOrdinal.entrySet()) {
            if (entry.getKey() < 1 || entry.getValue() == null
                    || entry.getValue().isJsonNull()) {
                throw new IllegalArgumentException(
                        "invalid bounded output version at ordinal "
                                + entry.getKey());
            }
            JsonObject version = new JsonObject();
            version.addProperty("versionOrdinal", entry.getKey());
            version.add("expression", entry.getValue().deepCopy());
            versions.add(version);
        }
        result.add("versions", versions);
        return result;
    }

    public static boolean isVersionSet(JsonElement value) {
        return value != null && value.isJsonObject()
                && KIND.equals(string(value.getAsJsonObject(), "kind"))
                && AUTHORITY.equals(string(value.getAsJsonObject(),
                "authority"));
    }

    public static NavigableMap<Integer, JsonElement> versions(
            JsonObject versionSet) {
        NavigableMap<Integer, JsonElement> result = new TreeMap<>();
        for (JsonElement element : array(versionSet, "versions")) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "malformed bounded output version entry");
            }
            JsonObject version = element.getAsJsonObject();
            int ordinal = integer(version, "versionOrdinal", -1);
            JsonElement expression = version.get("expression");
            if (ordinal < 1 || expression == null
                    || expression.isJsonNull()
                    || result.put(ordinal, expression) != null) {
                throw new IllegalArgumentException(
                        "malformed bounded output version at ordinal "
                                + ordinal);
            }
        }
        if (result.size() < 2) {
            throw new IllegalArgumentException(
                    "a bounded version set requires at least two versions");
        }
        return result;
    }

    public static String outputSiteId(JsonObject versionSet) {
        return string(versionSet, "outputSiteId");
    }

    /** One guard condition binding a relation case to one exported version;
     *  the bound is the largest exported ordinal of the site-local index. */
    public static JsonObject versionSelectionCondition(
            String outputPort, String outputSiteId, int versionOrdinal,
            int versionBound) {
        if (outputPort == null || outputPort.isEmpty()
                || versionOrdinal < 1 || versionBound < versionOrdinal) {
            throw new IllegalArgumentException(
                    "invalid output version selection");
        }
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", VERSION_SELECTION_TYPE);
        condition.addProperty("authority", AUTHORITY);
        condition.addProperty("outputPort", outputPort);
        condition.addProperty("outputSiteId",
                outputSiteId == null ? "" : outputSiteId);
        condition.addProperty("versionOrdinal", versionOrdinal);
        condition.addProperty("versionBound", versionBound);
        return condition;
    }

    public static boolean isVersionSelection(JsonObject expression) {
        return expression != null && VERSION_SELECTION_TYPE.equals(
                string(expression, "_type"));
    }
}
