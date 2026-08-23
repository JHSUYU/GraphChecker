package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Exact VM roots minted at an explicitly configured program source. */
public final class SymbolicSourceEvidence {
    public static final String TASK_FIELD = "symbolicSourceFields";
    public static final String DECLARATION_AUTHORITY =
            "CONFIGURED_EXACT_SOURCE_FIELD_V1";
    public static final String FIELD = "symbolicSourceEvidence";
    public static final String KIND = "CONFIGURED_SYMBOLIC_SOURCE_FIELD";
    public static final String AUTHORITY = "VM_EXACT_SOURCE_FIELD_V1";
    public static final int SCHEMA_VERSION = 1;

    private SymbolicSourceEvidence() {
    }

    /** Stable semantic VM label shared by seed and every source replay. */
    public static String engineLabel(String sourceOccurrenceId,
                                     String sourceId) {
        return "SRC." + CanonicalJson.sha256(
                required(sourceOccurrenceId, "sourceOccurrenceId") + "\n"
                        + required(sourceId, "sourceId"));
    }

    public static JsonObject event(String sourceId, String occurrenceId,
                                   String fieldSignature,
                                   JsonElement expression) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", KIND);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("sourceId", required(sourceId, "sourceId"));
        row.addProperty("sourceOccurrenceId", required(occurrenceId,
                "sourceOccurrenceId"));
        row.addProperty("fieldSignature", required(fieldSignature,
                "fieldSignature"));
        JsonObject symbolic = exactSymbol(expression);
        row.addProperty("rawSymbol", string(symbolic, "_exp"));
        row.addProperty("javaType", string(symbolic, "_java_type"));
        row.add("expression", symbolic.deepCopy());
        return row;
    }

    public static void writeTo(JsonObject owner, List<JsonObject> events) {
        if (owner == null || events == null || events.isEmpty()) return;
        JsonArray encoded = new JsonArray();
        for (JsonObject event : events) encoded.add(validate(event));
        owner.add(FIELD, encoded);
    }

    public static List<JsonObject> eventsOf(JsonObject owner) {
        if (owner == null) return Collections.emptyList();
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(owner, FIELD)) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        FIELD + " entries must be objects");
            }
            result.add(validate(element.getAsJsonObject()));
        }
        return result;
    }

    /** Canonical identity shared by every replay of the same source event. */
    public static String identity(JsonObject event) {
        JsonObject valid = validate(event);
        return string(valid, "sourceOccurrenceId") + "\n"
                + string(valid, "sourceId");
    }

    /**
     * Builds the one-to-one raw-symbol registry consumed by the Composer.
     * A collision is evidence corruption, never a reason to pick one row.
     */
    public static Map<String, String> rawSymbolIdentities(
            Iterable<JsonObject> owners) {
        Map<String, String> result = new LinkedHashMap<>();
        Map<String, String> symbolsByIdentity = new LinkedHashMap<>();
        if (owners == null) return result;
        for (JsonObject owner : owners) {
            for (JsonObject event : eventsOf(owner)) {
                String raw = string(event, "rawSymbol");
                String identity = identity(event);
                String priorIdentity = result.putIfAbsent(raw, identity);
                if (priorIdentity != null && !priorIdentity.equals(identity)) {
                    throw new IllegalArgumentException(
                            "one VM symbol names two configured sources: "
                                    + raw);
                }
                String priorRaw = symbolsByIdentity.putIfAbsent(identity,
                        raw);
                if (priorRaw != null && !priorRaw.equals(raw)) {
                    throw new IllegalArgumentException(
                            "one configured source names two VM symbols: "
                                    + identity);
                }
            }
        }
        return Collections.unmodifiableMap(result);
    }

    private static JsonObject validate(JsonObject event) {
        if (event == null
                || event.size() != 9
                || !event.has("schemaVersion")
                || !event.has("kind")
                || !event.has("authority")
                || !event.has("sourceId")
                || !event.has("sourceOccurrenceId")
                || !event.has("fieldSignature")
                || !event.has("rawSymbol")
                || !event.has("javaType")
                || !event.has("expression")) {
            throw new IllegalArgumentException(
                    FIELD + " has an incomplete schema");
        }
        int version = JsonFields.exactInteger(event, "schemaVersion", -1);
        if (version != SCHEMA_VERSION) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported schemaVersion");
        }
        if (!KIND.equals(string(event, "kind"))
                || !AUTHORITY.equals(string(event, "authority"))) {
            throw new IllegalArgumentException(
                    FIELD + " has unsupported authority");
        }
        required(string(event, "sourceId"), "sourceId");
        required(string(event, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        required(string(event, "fieldSignature"), "fieldSignature");
        JsonObject expression = exactSymbol(event.get("expression"));
        if (!string(event, "rawSymbol").equals(string(expression, "_exp"))
                || !string(event, "javaType").equals(
                string(expression, "_java_type"))) {
            throw new IllegalArgumentException(
                    FIELD + " symbol metadata differs from expression");
        }
        return event.deepCopy();
    }

    private static JsonObject exactSymbol(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) {
            throw new IllegalArgumentException(
                    FIELD + " expression must be an object");
        }
        JsonObject symbolic = expression.getAsJsonObject();
        String type = string(symbolic, "_type");
        String raw = string(symbolic, "_exp");
        String javaType = string(symbolic, "_java_type");
        if (!"SymbolExpression".equals(type)
                || raw.isEmpty() || javaType.isEmpty()
                || raw.startsWith("Y_") || raw.startsWith("N_")) {
            throw new IllegalArgumentException(
                    FIELD + " must carry one non-constant VM symbol");
        }
        if (SharedStateEvidence.containsVmSerializationTruncation(symbolic)) {
            throw new IllegalArgumentException(
                    FIELD + " contains a truncated VM expression");
        }
        return symbolic;
    }

    private static String required(String value, String label) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " is required");
        }
        return result;
    }
}
