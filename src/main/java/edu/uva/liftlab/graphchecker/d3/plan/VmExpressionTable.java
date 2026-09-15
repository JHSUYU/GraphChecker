package edu.uva.liftlab.graphchecker.d3.plan;

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

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Converts one VM-session expression-id DAG into portable Merkle anchors.
 *
 * <p>The native VM can use {@code (sessionId, expressionId)} while a symbolic
 * session is alive.  Those ids are deliberately not persisted as semantic
 * identity: this adapter resolves them once, preserves node sharing, and lets
 * {@link SharedExpressionTable} assign content addresses.  Region/case/event
 * ownership remains in the surrounding evidence and is never inferred from
 * an expression id or anchor.</p>
 */
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

    /**
     * Decodes several VM envelopes for one region while interning equal
     * content-addressed nodes.  Runtime analysis receives the real expression
     * objects, so its existing symbolic-expression checks keep working.  The
     * completed result is compacted once at publication.
     */
    public static final class Store {
        private final SharedExpressionTable.Decoder decoder =
                new SharedExpressionTable.Decoder();
        /** Stable native ids are retained for the lifetime of this activation. */
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
                // A runtime row can contain already-portable propagated
                // values beside a fresh VM table.  Register those Merkle
                // definitions before the raw decoder interns new nodes. Do
                // not make the portable decoder walk the native definition
                // table too; RawResolver owns that table and will visit it
                // once below.
                collectPortableTables(envelope, decoder,
                        Collections.newSetFromMap(
                                new IdentityHashMap<JsonElement, Boolean>()));
                expanded = rawResolver.importEnvelope(envelope, decoder);
            } else {
                expanded = decoder.expand(envelope);
            }
            return expanded;
        }

        public synchronized JsonElement importField(String serialized,
                                                     String field) {
            JsonObject envelope = importEnvelope(serialized);
            JsonElement value = envelope.get(field);
            return value == null || value.isJsonNull() ? null : value;
        }

        /** Returns one portable artifact with every reachable node stored once. */
        public synchronized JsonObject compact(JsonObject artifact) {
            return decoder.compact(artifact);
        }

        private static void collectPortableTables(
                JsonElement value, SharedExpressionTable.Decoder decoder,
                Set<JsonElement> seen) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive() || !seen.add(value)) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectPortableTables(child, decoder, seen);
                }
                return;
            }
            JsonObject object = value.getAsJsonObject();
            JsonElement table = object.get(SharedExpressionTable.FIELD);
            if (table != null) {
                JsonObject tableOnly = new JsonObject();
                tableOnly.add(SharedExpressionTable.FIELD, table);
                decoder.collectTables(tableOnly);
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                if (!FIELD.equals(field.getKey())
                        && !SharedExpressionTable.FIELD.equals(
                                field.getKey())) {
                    collectPortableTables(field.getValue(), decoder, seen);
                }
            }
        }
    }

    private static final class RawResolver {
        private final Map<RawKey, JsonObject> definitions =
                new LinkedHashMap<>();
        private final Map<RawKey, JsonElement> expanded =
                new LinkedHashMap<>();
        /**
         * Resolves one self-contained VM envelope through the persistent raw-id
         * cache and interns each previously unseen definition exactly once.
         */
        private JsonObject importEnvelope(
                JsonObject artifact, SharedExpressionTable.Decoder decoder) {
            Set<RawKey> supplied = new LinkedHashSet<>();
            collectTables(artifact, supplied);
            validateDefinitions(artifact, supplied);
            JsonElement expandedArtifact = expandInterned(artifact, decoder);
            if (!expandedArtifact.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM artifact root must be object");
            }
            return expandedArtifact.getAsJsonObject();
        }

        /**
         * Cached expansions must not let a later, incomplete envelope borrow
         * definitions from an earlier envelope.  Native artifacts are
         * self-contained, so validate the current table closure before using
         * any raw-key cache hit.
         */
        private void validateDefinitions(JsonElement artifact,
                                         Set<RawKey> supplied) {
            Set<RawKey> visited = new LinkedHashSet<>();
            Set<RawKey> active = new LinkedHashSet<>();
            for (RawKey key : supplied) {
                validateDefinition(key, supplied, visited, active);
            }
            validateArtifactReferences(artifact, supplied, visited, active,
                    Collections.newSetFromMap(
                            new IdentityHashMap<JsonElement, Boolean>()));
        }

        private void validateDefinition(
                RawKey key, Set<RawKey> supplied, Set<RawKey> visited,
                Set<RawKey> active) {
            if (visited.contains(key)) return;
            if (!supplied.contains(key)) {
                throw new IllegalArgumentException(
                        "missing VM expression definition: " + key);
            }
            JsonObject definition = definitions.get(key);
            if (definition == null) {
                throw new IllegalArgumentException(
                        "missing VM expression definition: " + key);
            }
            if (!active.add(key)) {
                throw new IllegalArgumentException(
                        "cyclic VM expression definition: " + key);
            }
            validateArtifactReferences(definition, supplied, visited, active,
                    Collections.newSetFromMap(
                            new IdentityHashMap<JsonElement, Boolean>()));
            active.remove(key);
            visited.add(key);
        }

        private void validateArtifactReferences(
                JsonElement value, Set<RawKey> supplied,
                Set<RawKey> visited, Set<RawKey> active,
                Set<JsonElement> seen) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive() || !seen.add(value)) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    validateArtifactReferences(child, supplied, visited,
                            active, seen);
                }
                return;
            }
            JsonObject object = value.getAsJsonObject();
            if (REFERENCE_TYPE.equals(optionalString(object, "_type"))) {
                validateDefinition(rawKey(object, REFERENCE_TYPE), supplied,
                        visited, active);
                return;
            }
            for (Map.Entry<String, JsonElement> field : object.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    validateArtifactReferences(field.getValue(), supplied,
                            visited, active, seen);
                }
            }
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
                    // Store accepts JsonObject callers as well as parsed text;
                    // retain no mutable object owned by that caller.
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
                SharedExpressionTable.Decoder decoder) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            if (value.isJsonArray()) {
                JsonArray result = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    result.add(expandInterned(child, decoder));
                }
                return result;
            }
            JsonObject source = value.getAsJsonObject();
            if (REFERENCE_TYPE.equals(optionalString(source, "_type"))) {
                RawKey key = rawKey(source, REFERENCE_TYPE);
                JsonElement held = expanded.get(key);
                if (held != null) return held;
                JsonObject definition = definitions.get(key);
                JsonElement local = expandInterned(definition, decoder);
                if (!local.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM expression definition is not an object: "
                                    + key);
                }
                JsonElement interned = decoder.internExpression(
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
                        ? SharedStateEvidence.emptyConjunction()
                        : expandInterned(child, decoder));
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
}
