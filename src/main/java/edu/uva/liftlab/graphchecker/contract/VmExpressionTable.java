package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
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

    /** Whether an artifact contains the VM's session-local DAG encoding
     *  ({@link ExpressionWalk}: an inline expression it holds may be as
     *  deep as the VM's chain). */
    public static boolean usesNativeDag(JsonElement artifact) {
        for (ExpressionWalk walk = ExpressionWalk.of(artifact);
             walk.hasNext(); ) {
            JsonObject object = walk.next();
            if (object.has(FIELD) || REFERENCE_TYPE.equals(
                    optionalString(object, "_type"))) {
                return true;
            }
        }
        return false;
    }

    /** Decodes a region's VM envelopes, each VM node one object however
     *  many envelopes name it. */
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
            return usesNativeDag(envelope)
                    ? rawResolver.importEnvelope(envelope)
                    : codec.expand(envelope);
        }

        public synchronized JsonElement importField(String serialized,
                                                     String field) {
            JsonObject envelope = importEnvelope(serialized);
            JsonElement value = envelope.get(field);
            return value == null || value.isJsonNull() ? null : value;
        }
    }

    private static final class RawResolver
            extends SharedExpressionTable.Expansion<RawKey> {
        private final Map<RawKey, JsonObject> definitions =
                new LinkedHashMap<>();

        private RawResolver() {
            super("VM expression");
        }

        @Override
        RawKey reference(JsonObject object, boolean root) {
            return REFERENCE_TYPE.equals(optionalString(object, "_type"))
                    ? rawKey(object, REFERENCE_TYPE) : null;
        }

        @Override
        JsonObject definition(RawKey key) {
            return definitions.get(key);
        }

        @Override
        JsonElement member(String name, JsonElement value) {
            if (FIELD.equals(name)) return null;
            return "pathGuard".equals(name)
                    && (value == null || value.isJsonNull())
                    ? emptyConjunction() : value;
        }

        /** Resolves one self-contained envelope, each definition expanded
         *  once. */
        private JsonObject importEnvelope(JsonObject artifact) {
            Set<RawKey> supplied = new LinkedHashSet<>();
            collectTables(artifact, supplied);
            validateDefinitions(artifact, supplied);
            JsonElement expandedArtifact = expand(artifact);
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
