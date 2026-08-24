package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Exact configured-source values selected for a different execution task.
 *
 * <p>A selector is not a symbolic root.  It identifies the one source
 * publication phase whose live value chooses an application object, such as
 * {@code allKeys.get(K)}.  Runtime admission resolves that identity to the
 * unique producer task in the current session plan; this remains valid when a
 * seed producer task is replaced by a path-replay task with a new task id.</p>
 */
public final class ConfiguredSourceSelectorContract {
    public static final String CONFIG_FIELD =
            "configuredSourceSelectorDeclarations";
    public static final String DECLARATION_KIND =
            "CONFIGURED_SOURCE_INT_SELECTOR_DECLARATION";
    public static final int DECLARATION_SCHEMA_VERSION = 2;
    public static final String DECLARATION_AUTHORITY =
            "CONFIGURED_EXACT_SOURCE_ID_INT_SELECTOR_TASK_DEMAND_V2";
    public static final String REQUIRED_BY_SOURCE_IDS_FIELD =
            "requiredBySourceIds";
    public static final String TASK_FIELD = "configuredSourceSelectors";
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "CONFIGURED_SOURCE_INT_SELECTOR";
    public static final String AUTHORITY =
            "SESSION_EXACT_SOURCE_PHASE_VALUE_REQUIRED_V2";
    public static final String VALUE_TYPE = "INT32";
    public static final String EVIDENCE_FIELD =
            "configuredSourceSelectorEvidence";
    public static final String EVIDENCE_KIND =
            "CONFIGURED_SOURCE_INT_SELECTOR_EVIDENCE";
    public static final String EVIDENCE_AUTHORITY =
            "ACTIVE_SESSION_EXACT_SOURCE_PHASE_VALUE_V2";

    private ConfiguredSourceSelectorContract() {
    }

    public static JsonObject intDeclaration(
            String sourceId, String fieldSignature,
            List<String> requiredBySourceIds) {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", DECLARATION_SCHEMA_VERSION);
        declaration.addProperty("kind", DECLARATION_KIND);
        declaration.addProperty("authority", DECLARATION_AUTHORITY);
        declaration.addProperty("sourceId", required(sourceId, "sourceId"));
        declaration.addProperty("fieldSignature", required(fieldSignature,
                "fieldSignature"));
        declaration.addProperty("valueType", VALUE_TYPE);
        JsonArray requiredBy = new JsonArray();
        if (requiredBySourceIds != null) {
            for (String requiredBySourceId : requiredBySourceIds) {
                requiredBy.add(required(requiredBySourceId,
                        REQUIRED_BY_SOURCE_IDS_FIELD + " entry"));
            }
        }
        declaration.add(REQUIRED_BY_SOURCE_IDS_FIELD, requiredBy);
        return validateDeclaration(declaration);
    }

    /**
     * Source roots whose task-local presence makes this selector necessary.
     * A declaration is configuration-time policy; it is deliberately versioned
     * independently from the exact selector installed into a replay task.
     */
    public static List<String> requiredBySourceIds(JsonObject declaration) {
        JsonObject admitted = validateDeclaration(declaration);
        List<String> result = new ArrayList<>();
        for (JsonElement element : admitted.getAsJsonArray(
                REQUIRED_BY_SOURCE_IDS_FIELD)) {
            result.add(element.getAsString());
        }
        return Collections.unmodifiableList(result);
    }

    public static List<JsonObject> declarationsOf(JsonObject region) {
        List<JsonObject> result = new ArrayList<>();
        Set<String> sourceIds = new LinkedHashSet<>();
        JsonElement encoded = region == null ? null : region.get(CONFIG_FIELD);
        if (encoded == null || encoded.isJsonNull()) {
            return Collections.emptyList();
        }
        if (!encoded.isJsonArray()) {
            throw new IllegalArgumentException(
                    CONFIG_FIELD + " must be an array");
        }
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        CONFIG_FIELD + " entries must be objects");
            }
            JsonObject declaration = validateDeclaration(
                    element.getAsJsonObject());
            String sourceId = string(declaration, "sourceId");
            if (!sourceIds.add(sourceId)) {
                throw new IllegalArgumentException(
                        "region selects one configured source twice: "
                                + sourceId);
            }
            result.add(declaration);
        }
        return Collections.unmodifiableList(result);
    }

    public static JsonObject exactInt(
            String consumePhaseId, String producerPhaseId,
            String sourceOccurrenceId, String sourceId,
            String fieldSignature) {
        JsonObject selector = new JsonObject();
        selector.addProperty("schemaVersion", SCHEMA_VERSION);
        selector.addProperty("kind", KIND);
        selector.addProperty("authority", AUTHORITY);
        selector.addProperty("consumePhaseId", requiredPhaseId(
                consumePhaseId, "consumePhaseId"));
        selector.addProperty("producerPhaseId", requiredPhaseId(
                producerPhaseId, "producerPhaseId"));
        selector.addProperty("sourceOccurrenceId", required(
                sourceOccurrenceId, "sourceOccurrenceId"));
        selector.addProperty("sourceId", required(sourceId, "sourceId"));
        selector.addProperty("fieldSignature", required(fieldSignature,
                "fieldSignature"));
        selector.addProperty("valueType", VALUE_TYPE);
        return validate(selector).json();
    }

    public static JsonObject evidence(Selector selector, String sourceTaskId,
                                      String rawSymbol, int selectedIntValue) {
        if (selector == null) {
            throw new IllegalArgumentException("selector is required");
        }
        JsonObject evidence = selector.json();
        evidence.addProperty("kind", EVIDENCE_KIND);
        evidence.addProperty("authority", EVIDENCE_AUTHORITY);
        evidence.addProperty("sourceTaskId", required(sourceTaskId,
                "sourceTaskId"));
        evidence.addProperty("rawSymbol", required(rawSymbol, "rawSymbol"));
        evidence.addProperty("selectedIntValue", selectedIntValue);
        return validateEvidence(evidence);
    }

    /** Stable prefix of the VM field symbol minted by the selected int hook. */
    public static String expectedRawSymbolPrefix(
            String producerPhaseId, String sourceId,
            String fieldSignature) {
        FieldPathSpec.DeclaredField field = FieldPathSpec.declaredField(
                required(fieldSignature, "fieldSignature"));
        if (field == null || !"int".equals(field.type())) {
            throw new IllegalArgumentException(
                    "configured selector requires an exact int field");
        }
        return "M_I_field_" + SymbolicSourceEvidence.engineLabelForPhase(
                requiredPhaseId(producerPhaseId, "producerPhaseId"),
                required(sourceId, "sourceId")) + "_";
    }

    public static List<JsonObject> evidenceOf(JsonObject owner) {
        List<JsonObject> result = new ArrayList<>();
        Set<String> consumePhaseIds = new LinkedHashSet<>();
        for (JsonElement element : array(owner, EVIDENCE_FIELD)) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        EVIDENCE_FIELD + " entries must be objects");
            }
            JsonObject evidence = validateEvidence(
                    element.getAsJsonObject());
            String consumePhaseId = string(evidence, "consumePhaseId");
            if (!consumePhaseIds.add(consumePhaseId)) {
                throw new IllegalArgumentException(
                        "one task recorded one consume phase twice: "
                                + consumePhaseId);
            }
            result.add(evidence);
        }
        return Collections.unmodifiableList(result);
    }

    public static List<Selector> decode(JsonObject task) {
        List<Selector> result = new ArrayList<>();
        Set<String> consumePhaseIds = new LinkedHashSet<>();
        JsonArray encoded;
        if (task == null || !task.has(TASK_FIELD)) {
            encoded = new JsonArray();
        } else if (!task.get(TASK_FIELD).isJsonArray()) {
            throw new IllegalArgumentException(TASK_FIELD
                    + " must be an array");
        } else {
            encoded = task.getAsJsonArray(TASK_FIELD);
        }
        for (JsonElement element : encoded) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        TASK_FIELD + " entries must be objects");
            }
            Selector selector = validate(element.getAsJsonObject());
            if (!consumePhaseIds.add(selector.consumePhaseId())) {
                throw new IllegalArgumentException(
                        "task selects one configured consume phase twice: "
                                + selector.consumePhaseId());
            }
            result.add(selector);
        }
        return Collections.unmodifiableList(result);
    }

    private static Selector validate(JsonObject row) {
        if (row == null || row.size() != 9
                || !row.has("schemaVersion") || !row.has("kind")
                || !row.has("authority") || !row.has("consumePhaseId")
                || !row.has("producerPhaseId")
                || !row.has("sourceOccurrenceId")
                || !row.has("sourceId")
                || !row.has("fieldSignature") || !row.has("valueType")
                ) {
            throw new IllegalArgumentException(
                    TASK_FIELD + " has an incomplete schema");
        }
        int schemaVersion;
        try {
            schemaVersion = exactInt(row.get("schemaVersion"));
        } catch (RuntimeException malformed) {
            throw new IllegalArgumentException(
                    TASK_FIELD + " has malformed integer fields", malformed);
        }
        String consumePhaseId = requiredPhaseId(
                string(row, "consumePhaseId"), "consumePhaseId");
        String producerPhaseId = requiredPhaseId(
                string(row, "producerPhaseId"), "producerPhaseId");
        String occurrence = required(string(row, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        String sourceId = required(string(row, "sourceId"), "sourceId");
        String field = required(string(row, "fieldSignature"),
                "fieldSignature");
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(field);
        if (schemaVersion != SCHEMA_VERSION
                || !KIND.equals(string(row, "kind"))
                || !AUTHORITY.equals(string(row, "authority"))
                || !VALUE_TYPE.equals(string(row, "valueType"))
                || consumePhaseId.equals(producerPhaseId)
                || declared == null || !"int".equals(declared.type())) {
            throw new IllegalArgumentException(
                    TASK_FIELD + " has unsupported selector authority");
        }
        return new Selector(row, consumePhaseId, producerPhaseId,
                occurrence, sourceId, field);
    }

    private static JsonObject validateEvidence(JsonObject row) {
        if (row == null || row.size() != 12
                || exactInt(row.get("schemaVersion")) != SCHEMA_VERSION
                || !EVIDENCE_KIND.equals(string(row, "kind"))
                || !EVIDENCE_AUTHORITY.equals(string(row, "authority"))
                || !VALUE_TYPE.equals(string(row, "valueType"))) {
            throw new IllegalArgumentException(
                    EVIDENCE_FIELD + " has unsupported selector authority");
        }
        String sourceTaskId = required(string(row, "sourceTaskId"),
                "sourceTaskId");
        String consumePhaseId = requiredPhaseId(
                string(row, "consumePhaseId"), "consumePhaseId");
        String producerPhaseId = requiredPhaseId(
                string(row, "producerPhaseId"), "producerPhaseId");
        String occurrence = required(string(row, "sourceOccurrenceId"),
                "sourceOccurrenceId");
        String sourceId = required(string(row, "sourceId"), "sourceId");
        String field = required(string(row, "fieldSignature"),
                "fieldSignature");
        String raw = required(string(row, "rawSymbol"), "rawSymbol");
        int selected = exactInt(row.get("selectedIntValue"));
        String expectedPrefix = expectedRawSymbolPrefix(
                producerPhaseId, sourceId, field);
        if (!raw.startsWith(expectedPrefix)
                || raw.length() == expectedPrefix.length()) {
            throw new IllegalArgumentException(
                    EVIDENCE_FIELD + " rawSymbol differs from exact source");
        }
        Selector selector = validate(exactInt(consumePhaseId,
                producerPhaseId, occurrence, sourceId, field));
        JsonObject result = selector.json();
        result.addProperty("kind", EVIDENCE_KIND);
        result.addProperty("authority", EVIDENCE_AUTHORITY);
        result.addProperty("sourceTaskId", sourceTaskId);
        result.addProperty("rawSymbol", raw);
        result.addProperty("selectedIntValue", selected);
        return result;
    }

    private static JsonObject validateDeclaration(JsonObject row) {
        if (row == null || row.size() != 7
                || exactInt(row.get("schemaVersion"))
                != DECLARATION_SCHEMA_VERSION
                || !DECLARATION_KIND.equals(string(row, "kind"))
                || !DECLARATION_AUTHORITY.equals(string(row, "authority"))
                || !VALUE_TYPE.equals(string(row, "valueType"))
                || !row.has(REQUIRED_BY_SOURCE_IDS_FIELD)
                || !row.get(REQUIRED_BY_SOURCE_IDS_FIELD).isJsonArray()) {
            throw new IllegalArgumentException(
                    CONFIG_FIELD + " has unsupported selector authority");
        }
        String sourceId = required(string(row, "sourceId"), "sourceId");
        String field = required(string(row, "fieldSignature"),
                "fieldSignature");
        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(field);
        if (declared == null || !"int".equals(declared.type())) {
            throw new IllegalArgumentException(
                    CONFIG_FIELD + " requires an exact int field");
        }
        JsonArray requiredBy = new JsonArray();
        Set<String> requiredBySourceIds = new LinkedHashSet<>();
        for (JsonElement element : row.getAsJsonArray(
                REQUIRED_BY_SOURCE_IDS_FIELD)) {
            if (!element.isJsonPrimitive()
                    || !element.getAsJsonPrimitive().isString()) {
                throw new IllegalArgumentException(CONFIG_FIELD + "."
                        + REQUIRED_BY_SOURCE_IDS_FIELD
                        + " entries must be strings");
            }
            String requiredBySourceId = required(element.getAsString(),
                    REQUIRED_BY_SOURCE_IDS_FIELD + " entry");
            if (!requiredBySourceIds.add(requiredBySourceId)) {
                throw new IllegalArgumentException(CONFIG_FIELD + "."
                        + REQUIRED_BY_SOURCE_IDS_FIELD
                        + " contains duplicate sourceId "
                        + requiredBySourceId);
            }
            requiredBy.add(requiredBySourceId);
        }
        if (requiredBy.size() == 0) {
            throw new IllegalArgumentException(CONFIG_FIELD + "."
                    + REQUIRED_BY_SOURCE_IDS_FIELD
                    + " must name at least one dependent source");
        }
        JsonObject result = row.deepCopy();
        result.addProperty("sourceId", sourceId);
        result.addProperty("fieldSignature", field);
        result.add(REQUIRED_BY_SOURCE_IDS_FIELD, requiredBy);
        return result;
    }

    private static String required(String value, String label) {
        String result = value == null ? "" : value.trim();
        if (result.isEmpty()) {
            throw new IllegalArgumentException(label + " is required");
        }
        return result;
    }

    private static String requiredPhaseId(String value, String label) {
        String result = required(value, label);
        if (!result.startsWith("SOURCE_PHASE.")) {
            throw new IllegalArgumentException(
                    label + " must name an exact source phase");
        }
        return result;
    }

    private static int exactInt(JsonElement value) {
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            throw new NumberFormatException("not an exact JSON integer");
        }
        return new BigDecimal(value.getAsString()).intValueExact();
    }

    public static final class Selector {
        private final JsonObject encoded;
        private final String consumePhaseId;
        private final String producerPhaseId;
        private final String sourceOccurrenceId;
        private final String sourceId;
        private final String fieldSignature;

        private Selector(JsonObject encoded, String consumePhaseId,
                         String producerPhaseId, String sourceOccurrenceId,
                         String sourceId, String fieldSignature) {
            this.encoded = encoded.deepCopy();
            this.consumePhaseId = consumePhaseId;
            this.producerPhaseId = producerPhaseId;
            this.sourceOccurrenceId = sourceOccurrenceId;
            this.sourceId = sourceId;
            this.fieldSignature = fieldSignature;
        }

        public JsonObject json() { return encoded.deepCopy(); }

        public String consumePhaseId() { return consumePhaseId; }

        public String producerPhaseId() { return producerPhaseId; }

        public String sourceOccurrenceId() { return sourceOccurrenceId; }

        public String sourceId() { return sourceId; }

        public String fieldSignature() { return fieldSignature; }

        public boolean matches(JsonObject evidence) {
            return evidence != null
                    && consumePhaseId.equals(string(evidence,
                    "consumePhaseId"))
                    && producerPhaseId.equals(string(evidence,
                    "producerPhaseId"))
                    && sourceOccurrenceId.equals(string(evidence,
                    "sourceOccurrenceId"))
                    && sourceId.equals(string(evidence, "sourceId"))
                    && fieldSignature.equals(string(evidence,
                    "fieldSignature"));
        }
    }
}
