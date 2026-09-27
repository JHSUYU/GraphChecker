package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Converts a VM-session expression-id DAG into portable Merkle anchors ({@link
 *  SharedExpressionTable}), preserving node sharing. Session ids are never
 *  persisted as identity, and ownership is never inferred from them. */
public final class VmExpressionTable {
    public static final String FIELD = "vmExpressionTable";
    public static final String KIND = "VM_EXPRESSION_TABLE";
    public static final String AUTHORITY = "VM_SESSION_EXPRESSION_ID_V1";
    public static final String REFERENCE_TYPE = "VmExpressionReference";
    public static final String DEFINITION_TYPE = "VmExpressionDefinition";

    private VmExpressionTable() {
    }

    /** Whether an artifact contains the VM's session-local DAG encoding. */
    public static boolean usesNativeDag(JsonElement artifact) {
        if (artifact == null || artifact.isJsonNull()
                || artifact.isJsonPrimitive()) return false;
        if (artifact.isJsonArray()) {
            for (JsonElement child : artifact.getAsJsonArray()) {
                if (usesNativeDag(child)) return true;
            }
            return false;
        }
        JsonObject object = artifact.getAsJsonObject();
        if (object.has(FIELD)
                || REFERENCE_TYPE.equals(optionalString(object, "_type"))) {
            return true;
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            if (usesNativeDag(field.getValue())) return true;
        }
        return false;
    }

    /** Decodes a region's VM envelopes, interning equal nodes. */
    public static final class Store {
        private final SharedExpressionTable.Codec codec =
                new SharedExpressionTable.Codec();
        private final RawResolver rawResolver = new RawResolver();

        public synchronized JsonObject importEnvelope(String serialized) {
            JsonElement parsed;
            try {
                parsed = JsonParser.parseString(serialized == null
                        ? "" : serialized);
            } catch (RuntimeException malformed) {
                throw new IllegalArgumentException(
                        "malformed VM expression artifact", malformed);
            }
            if (!parsed.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM expression artifact must be an object");
            }
            return importEnvelope(parsed.getAsJsonObject());
        }

        public synchronized JsonObject importEnvelope(JsonObject envelope) {
            JsonObject expanded;
            if (usesNativeDag(envelope)) {
                // Register portable tables beside the VM table first;
                // RawResolver alone walks the native table.
                collectPortableTables(envelope, codec,
                        Collections.newSetFromMap(
                                new IdentityHashMap<JsonElement, Boolean>()));
                expanded = rawResolver.importEnvelope(envelope, codec);
            } else {
                expanded = codec.expand(envelope);
            }
            return expanded;
        }

        public synchronized JsonElement importField(String serialized,
                                                     String field) {
            JsonObject envelope = importEnvelope(serialized);
            JsonElement value = envelope.get(field);
            return value == null || value.isJsonNull() ? null : value;
        }

        private static void collectPortableTables(
                JsonElement value, SharedExpressionTable.Codec codec,
                Set<JsonElement> seen) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive() || !seen.add(value)) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectPortableTables(child, codec, seen);
                }
                return;
            }
            JsonObject object = value.getAsJsonObject();
            JsonElement table = object.get(SharedExpressionTable.FIELD);
            if (table != null) {
                JsonObject tableOnly = new JsonObject();
                tableOnly.add(SharedExpressionTable.FIELD, table);
                codec.collectTables(tableOnly);
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                if (!FIELD.equals(field.getKey())
                        && !SharedExpressionTable.FIELD.equals(
                                field.getKey())) {
                    collectPortableTables(field.getValue(), codec, seen);
                }
            }
        }
    }

    private static final class RawResolver {
        private final Map<RawKey, JsonObject> definitions =
                new LinkedHashMap<>();
        private final Map<RawKey, JsonElement> expanded =
                new LinkedHashMap<>();
        /** Resolves one self-contained envelope, interning each new definition
         *  once. */
        private JsonObject importEnvelope(
                JsonObject artifact, SharedExpressionTable.Codec codec) {
            Set<RawKey> supplied = new LinkedHashSet<>();
            collectTables(artifact, supplied);
            validateDefinitions(artifact, supplied);
            JsonElement expandedArtifact = expandInterned(artifact, codec);
            if (!expandedArtifact.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM artifact root must be object");
            }
            return expandedArtifact.getAsJsonObject();
        }

        /** Envelopes are self-contained: validate this table's closure before
         *  any cache hit, so none borrows an earlier one's definitions. */
        private void validateDefinitions(JsonElement artifact,
                                         Set<RawKey> supplied) {
            SharedExpressionTable.Dag<RawKey> dag =
                    new SharedExpressionTable.Dag<>("VM expression",
                            key -> supplied.contains(key)
                                    ? definitions.get(key) : null,
                            RawResolver::references);
            for (RawKey key : supplied) dag.require(key);
            references(artifact, dag::require);
        }

        private static void references(JsonElement value,
                                       Consumer<RawKey> visit) {
            SharedExpressionTable.eachReference(value, FIELD,
                    object -> REFERENCE_TYPE.equals(
                            optionalString(object, "_type"))
                            ? rawKey(object, REFERENCE_TYPE) : null,
                    visit, Collections.newSetFromMap(
                            new IdentityHashMap<JsonElement, Boolean>()));
        }

        private void collectTables(JsonElement value, Set<RawKey> supplied) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectTables(child, supplied);
                }
                return;
            }
            JsonObject row = value.getAsJsonObject();
            JsonElement table = row.get(FIELD);
            if (table != null) importTable(table, supplied);
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    collectTables(field.getValue(), supplied);
                }
            }
        }

        private void importTable(JsonElement encoded, Set<RawKey> supplied) {
            if (encoded == null || !encoded.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM expression table must be an object");
            }
            JsonObject table = encoded.getAsJsonObject();
            long session = exactNonNegativeLong(table, "sessionId");
            JsonArray rows = array(table, "definitions");
            if (optionalInteger(table, "schemaVersion", -1) != 1
                    || !KIND.equals(optionalString(table, "kind"))
                    || !AUTHORITY.equals(optionalString(table, "authority"))
                    || optionalInteger(table, "definitionCount", -1) != rows.size()
                    || session == 0L && rows.size() != 0) {
                throw new IllegalArgumentException(
                        "unsupported VM expression table schema");
            }
            for (JsonElement element : rows) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM expression definition must be an object");
                }
                JsonObject row = element.getAsJsonObject();
                RawKey key = rawKey(row, DEFINITION_TYPE);
                if (supplied != null) supplied.add(key);
                JsonElement expression = row.get("expression");
                if (key.session != session || expression == null
                        || !expression.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM expression definition disagrees with table");
                }
                JsonObject definition = expression.getAsJsonObject();
                JsonObject prior = definitions.get(key);
                if (prior == null) {
                    // Retain no caller-owned mutable object.
                    JsonObject stable = definition.deepCopy();
                    prior = definitions.putIfAbsent(key, stable);
                }
                if (prior != null && !prior.equals(definition)) {
                    throw new IllegalArgumentException(
                            "conflicting VM expression definition: " + key);
                }
            }
        }

        private JsonElement expandInterned(
                JsonElement value,
                SharedExpressionTable.Codec codec) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            if (value.isJsonArray()) {
                JsonArray result = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    result.add(expandInterned(child, codec));
                }
                return result;
            }
            JsonObject source = value.getAsJsonObject();
            if (REFERENCE_TYPE.equals(optionalString(source, "_type"))) {
                RawKey key = rawKey(source, REFERENCE_TYPE);
                JsonElement held = expanded.get(key);
                if (held != null) return held;
                JsonObject definition = definitions.get(key);
                JsonElement local = expandInterned(definition, codec);
                if (!local.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM expression definition is not an object: "
                                    + key);
                }
                JsonElement interned = codec.internExpression(
                        local.getAsJsonObject());
                JsonElement raced = expanded.putIfAbsent(key, interned);
                return raced == null ? interned : raced;
            }
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> field : source.entrySet()) {
                if (FIELD.equals(field.getKey())) continue;
                JsonElement child = field.getValue();
                result.add(field.getKey(), "pathGuard".equals(field.getKey())
                        && (child == null || child.isJsonNull())
                        ? emptyConjunction()
                        : expandInterned(child, codec));
            }
            return result;
        }
    }

    private static RawKey rawKey(JsonObject row, String expectedType) {
        if (!expectedType.equals(optionalString(row, "_type"))) {
            throw new IllegalArgumentException(
                    "VM expression row has wrong type");
        }
        return new RawKey(exactPositiveLong(row, "sessionId"),
                exactPositiveLong(row, "expressionId"));
    }

    private static long exactPositiveLong(JsonObject row, String field) {
        long result = exactNonNegativeLong(row, field);
        if (result == 0L) {
            throw new IllegalArgumentException(field
                    + " must be a positive integer");
        }
        return result;
    }

    private static long exactNonNegativeLong(JsonObject row, String field) {
        JsonElement value = row == null ? null : row.get(field);
        if (value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isNumber()) {
            throw new IllegalArgumentException(field
                    + " must be a non-negative integer");
        }
        try {
            long result = value.getAsBigDecimal().longValueExact();
            if (result < 0L) throw new ArithmeticException("negative");
            return result;
        } catch (RuntimeException malformed) {
            throw new IllegalArgumentException(field
                    + " must be a non-negative integer", malformed);
        }
    }

    private static final class RawKey {
        private final long session;
        private final long expression;

        private RawKey(long session, long expression) {
            this.session = session;
            this.expression = expression;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof RawKey)) return false;
            RawKey key = (RawKey) other;
            return session == key.session && expression == key.expression;
        }

        @Override public int hashCode() {
            return 31 * Long.valueOf(session).hashCode()
                    + Long.valueOf(expression).hashCode();
        }

        @Override public String toString() {
            return session + ":" + expression;
        }
    }

    /** Explicit empty conjunction (unguarded write); an absent guard means
     *  "never captured". */
    static JsonObject emptyConjunction() {
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "EMPTY_CONJUNCTION");
        guard.addProperty("authority", "VM_UNGUARDED_WRITE_V1");
        return guard;
    }
}
