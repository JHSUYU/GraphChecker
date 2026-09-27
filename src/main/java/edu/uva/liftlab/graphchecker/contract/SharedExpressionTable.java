package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * Content-addressed storage for immutable symbolic-expression DAGs.
 *
 * <p>JSON has no references, so expanding shared VM nodes as trees restated the
 * whole upstream history at every use. At artifact boundaries a value is an
 * {@code EXPR.v1.<sha256>} reference and each node is defined once. Anchors are
 * Merkle identities (children hashed first). Deduplicates values only; never
 * infers causality or ownership.</p>
 */
public final class SharedExpressionTable {
    /** The table's artifact member name. */
    public static final String FIELD = "sharedExpressionTable";
    private static final int SCHEMA_VERSION = 1;
    private static final String KIND = "CONTENT_ADDRESSED_EXPRESSION_TABLE";
    private static final String AUTHORITY = "MERKLE_EXPRESSION_SHA256_V1";
    private static final String REFERENCE_TYPE = "SharedExpressionReference";
    private static final String ANCHOR = "expressionAnchor";
    private static final String PREFIX = "EXPR.v1.";
    private static final String HASH_DOMAIN =
            "GraphChecker/content-addressed-expression/v1\n";

    private SharedExpressionTable() {
    }

    /** Compacts a graph whose content-addressed definitions are trusted. */
    private static JsonObject compactDecodedArtifact(JsonObject artifact,
                                                     Builder builder) {
        JsonElement compact = builder.compact(artifact, true);
        if (!compact.isJsonObject()) {
            throw new IllegalArgumentException("artifact root must be object");
        }
        builder.validateReferences();
        JsonObject result = compact.getAsJsonObject();
        if (!builder.reachable.isEmpty()) {
            result.add(FIELD, builder.encode());
        }
        return result;
    }

    private static JsonObject expandArtifact(JsonObject artifact,
                                             Resolver resolver) {
        JsonElement expanded = resolver.expand(artifact,
                new HashSet<String>(), true);
        if (!expanded.isJsonObject()) {
            throw new IllegalArgumentException("artifact root must be object");
        }
        return expanded.getAsJsonObject();
    }

    /**
     * One store of anchors, each distinct node (by identity) hashed once:
     * decodes envelopes, compacts the graphs it holds, and content-addresses
     * an expression.  A walk that re-hashed shared nodes costs the tree, not
     * the DAG: a File.getParent chain (finalize-gs a8) was 389066 nodes of
     * 198 distinct, and its session table never finished writing.
     */
    public static final class Codec {
        private final Resolver resolver = new Resolver();

        public synchronized JsonObject expand(JsonObject artifact) {
            if (artifact == null) return new JsonObject();
            requirePortableArtifact(artifact);
            resolver.collectTables(artifact);
            return expandArtifact(artifact, resolver);
        }

        /** Interns one expression from an already validated VM DAG.
         *  Package-local: not a trust boundary like {@link #expand}; known
         *  children are reused. */
        synchronized JsonElement internExpression(JsonObject expression) {
            return resolver.internExpression(expression);
        }

        /** Loads portable definitions before a mixed native/portable decode. */
        synchronized void collectTables(JsonObject artifact) {
            if (artifact != null) resolver.collectTables(artifact);
        }

        /** One portable artifact: each expression a reference, each node
         *  defined once. */
        public synchronized JsonObject compact(JsonObject artifact) {
            if (artifact == null) return new JsonObject();
            return compactDecodedArtifact(artifact, builder());
        }

        /** The SHA-256 hex of one expression's Merkle anchor. */
        public synchronized String digest(JsonObject expression) {
            JsonElement compact = builder().compact(expression, false);
            String anchor = isReference(compact) ? anchor(compact)
                    : anchorFor(compact.getAsJsonObject());
            return anchor.substring(PREFIX.length());
        }

        private Builder builder() {
            return new Builder(resolver.definitions,
                    resolver.anchorsByExpanded);
        }
    }

    private static boolean isReference(JsonElement value) {
        if (!declaresReference(value)) return false;
        JsonObject reference = value.getAsJsonObject();
        return referenceMembers(reference, reference.has(FIELD));
    }

    private static String anchor(JsonElement reference) {
        return isReference(reference)
                ? optionalString(reference.getAsJsonObject(), ANCHOR) : "";
    }

    private static JsonObject reference(String anchor) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", REFERENCE_TYPE);
        result.addProperty(ANCHOR, anchor);
        return result;
    }

    private static boolean expression(JsonObject value) {
        String type = exactString(value, "_type");
        return !type.isEmpty() && !REFERENCE_TYPE.equals(type);
    }

    /** Artifact readers accept references, never inline expression trees. */
    private static void requirePortableArtifact(JsonElement value) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()) {
            return;
        }
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                requirePortableArtifact(child);
            }
            return;
        }
        JsonObject object = value.getAsJsonObject();
        if (expression(object)) {
            throw new IllegalArgumentException(
                    "inline symbolic expression at artifact boundary");
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            if (!FIELD.equals(field.getKey())) {
                requirePortableArtifact(field.getValue());
            }
        }
    }

    private static boolean declaresReference(JsonElement value) {
        return value != null && value.isJsonObject()
                && REFERENCE_TYPE.equals(exactString(
                value.getAsJsonObject(), "_type"));
    }

    private static void requireReference(JsonObject value,
                                         boolean allowArtifactTable) {
        if (!referenceMembers(value, allowArtifactTable)) {
            throw new IllegalArgumentException(
                    "shared expression reference has unsupported members");
        }
        requireAnchor(exactString(value, ANCHOR));
    }

    private static boolean referenceMembers(JsonObject value,
                                            boolean allowArtifactTable) {
        if (value == null || !REFERENCE_TYPE.equals(
                exactString(value, "_type"))
                || exactString(value, ANCHOR).isEmpty()) {
            return false;
        }
        int expected = allowArtifactTable && value.has(FIELD) ? 3 : 2;
        return value.size() == expected
                && (!value.has(FIELD) || allowArtifactTable);
    }

    private static String exactString(JsonObject value, String field) {
        JsonElement encoded = value == null ? null : value.get(field);
        return encoded != null && encoded.isJsonPrimitive()
                && encoded.getAsJsonPrimitive().isString()
                ? encoded.getAsString() : "";
    }

    private static String anchorFor(JsonObject definition) {
        return PREFIX + ArtifactIO.sha256(HASH_DOMAIN
                + CanonicalJson.render(definition));
    }

    /** Parses and hash-checks rows not already verified. */
    private static void readTable(JsonElement encoded,
                                  Map<String, JsonObject> verified,
                                  Map<String, JsonObject> incoming) {
        if (encoded == null || !encoded.isJsonObject()) {
            throw new IllegalArgumentException(
                    "shared expression table must be object");
        }
        JsonObject table = encoded.getAsJsonObject();
        JsonElement encodedDefinitions = table.get("definitions");
        if (optionalInteger(table, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(optionalString(table, "kind"))
                || !AUTHORITY.equals(optionalString(table, "authority"))
                || encodedDefinitions == null
                || !encodedDefinitions.isJsonArray()) {
            throw new IllegalArgumentException(
                    "unsupported shared expression table schema");
        }
        for (JsonElement element : encodedDefinitions.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "shared expression definition must be object");
            }
            JsonObject row = element.getAsJsonObject();
            if (row.size() != 2 || !row.has(ANCHOR)
                    || !row.has("expression")) {
                throw new IllegalArgumentException(
                        "shared expression definition has unsupported "
                                + "members");
            }
            String anchor = exactString(row, ANCHOR);
            JsonObject definition = object(row, "expression");
            requireAnchor(anchor);
            if (!expression(definition)) {
                throw new IllegalArgumentException(
                        "shared expression definition must contain a "
                                + "concrete expression");
            }
            if (!anchor.equals(anchorFor(definition))) {
                if (verified.containsKey(anchor)
                        || incoming.containsKey(anchor)) {
                    throw new IllegalArgumentException(
                            "conflicting shared expression definition: "
                                    + anchor);
                }
                throw new IllegalArgumentException(
                        "shared expression definition hash differs: " + anchor);
            }
            if (!verified.containsKey(anchor)) {
                incoming.putIfAbsent(anchor, definition);
            }
        }
    }

    /** Drops null members, except {@code pathGuard} (empty conjunction). */
    private static boolean portableMember(String name, JsonElement value) {
        return !FIELD.equals(name)
                && ("pathGuard".equals(name)
                || value != null && !value.isJsonNull());
    }

    private static void requireAnchor(String value) {
        if (value == null || !value.startsWith(PREFIX)
                || value.length() != PREFIX.length() + 64) {
            throw new IllegalArgumentException(
                    "malformed shared expression anchor: " + value);
        }
        for (int index = PREFIX.length(); index < value.length(); index++) {
            char digit = value.charAt(index);
            if (!((digit >= '0' && digit <= '9')
                    || (digit >= 'a' && digit <= 'f'))) {
                throw new IllegalArgumentException(
                        "malformed shared expression anchor: " + value);
            }
        }
    }

    /**
     * THE DAG CHECK of every expression table: each key a walk reaches is
     * defined ({@code definition} answers null otherwise) and none lies on a
     * cycle. {@code references} visits the keys one value names.
     */
    static final class Dag<K> {
        private final String noun;
        private final Function<K, JsonObject> definition;
        private final BiConsumer<JsonElement, Consumer<K>> references;
        final Set<K> visited = new LinkedHashSet<>();
        private final Set<K> active = new LinkedHashSet<>();

        Dag(String noun, Function<K, JsonObject> definition,
            BiConsumer<JsonElement, Consumer<K>> references) {
            this.noun = noun;
            this.definition = definition;
            this.references = references;
        }

        void require(K key) {
            if (visited.contains(key)) return;
            JsonObject defined = definition.apply(key);
            if (defined == null) {
                throw new IllegalArgumentException(
                        "missing " + noun + " definition: " + key);
            }
            if (!active.add(key)) {
                throw new IllegalArgumentException(
                        "cyclic " + noun + " definition: " + key);
            }
            references.accept(defined, this::require);
            active.remove(key);
            visited.add(key);
        }
    }

    /** Visits the key of every reference object {@code keyOf} recognizes
     *  (null: not a reference) in one value, each shared subtree once, never
     *  inside a {@code skipped} member. */
    static <K> void eachReference(JsonElement value, String skipped,
                                  Function<JsonObject, K> keyOf,
                                  Consumer<K> visit, Set<JsonElement> seen) {
        if (value == null || value.isJsonNull() || value.isJsonPrimitive()
                || !seen.add(value)) return;
        if (value.isJsonArray()) {
            for (JsonElement child : value.getAsJsonArray()) {
                eachReference(child, skipped, keyOf, visit, seen);
            }
            return;
        }
        JsonObject object = value.getAsJsonObject();
        K key = keyOf.apply(object);
        if (key != null) {
            visit.accept(key);
            return;
        }
        for (Map.Entry<String, JsonElement> field : object.entrySet()) {
            if (!field.getKey().equals(skipped)) {
                eachReference(field.getValue(), skipped, keyOf, visit, seen);
            }
        }
    }

    /** The check over portable anchors. */
    private static Dag<String> anchors(
            Function<String, JsonObject> definition) {
        return new Dag<>("shared expression", definition,
                (value, visit) -> eachReference(value, null, row -> {
                    if (!declaresReference(row)) return null;
                    requireReference(row, false);
                    return exactString(row, ANCHOR);
                }, visit, Collections.newSetFromMap(
                        new IdentityHashMap<JsonElement, Boolean>())));
    }

    /** One compaction over the codec's anchors, adding the ones it hashes. */
    private static final class Builder {
        private final Map<String, JsonObject> definitions;
        private final Map<JsonElement, String> compactedExpressions;
        private final Set<String> references = new LinkedHashSet<>();
        private Set<String> reachable = Collections.emptySet();

        private Builder(Map<String, JsonObject> definitions,
                        Map<JsonElement, String> anchors) {
            this.definitions = definitions;
            this.compactedExpressions = anchors;
        }

        private JsonElement compact(JsonElement value, boolean artifactRoot) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            if (value.isJsonArray()) {
                JsonArray result = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    result.add(compact(child, false));
                }
                return result;
            }
            JsonObject source = value.getAsJsonObject();
            if (declaresReference(source)) {
                requireReference(source, artifactRoot && source.has(FIELD));
                String anchor = exactString(source, ANCHOR);
                references.add(anchor);
                return reference(anchor);
            }
            if (expression(source)) {
                String held = compactedExpressions.get(source);
                if (held != null) {
                    references.add(held);
                    return reference(held);
                }
            }
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> field : source.entrySet()) {
                // pathGuard:null = observed empty conjunction; absent = not
                // captured.
                if (portableMember(field.getKey(), field.getValue())) {
                    result.add(field.getKey(), compact(field.getValue(),
                            false));
                }
            }
            if (!expression(source)) return result;
            String anchor = anchorFor(result);
            definitions.putIfAbsent(anchor, result);
            compactedExpressions.put(source, anchor);
            references.add(anchor);
            return reference(anchor);
        }

        private void validateReferences() {
            Dag<String> dag = anchors(anchor -> {
                requireAnchor(anchor);
                return definitions.get(anchor);
            });
            for (String anchor : references) dag.require(anchor);
            reachable = dag.visited;
        }

        private JsonObject encode() {
            JsonObject table = new JsonObject();
            table.addProperty("schemaVersion", SCHEMA_VERSION);
            table.addProperty("kind", KIND);
            table.addProperty("authority", AUTHORITY);
            List<String> anchors = new ArrayList<>(reachable);
            Collections.sort(anchors);
            JsonArray rows = new JsonArray();
            for (String anchor : anchors) {
                JsonObject row = new JsonObject();
                row.addProperty(ANCHOR, anchor);
                row.add("expression", definitions.get(anchor));
                rows.add(row);
            }
            table.add("definitions", rows);
            return table;
        }
    }

    private static final class Resolver {
        private final Map<String, JsonObject> definitions = new HashMap<>();
        private final Map<String, JsonElement> expanded = new HashMap<>();
        private final Map<JsonElement, String> anchorsByExpanded =
                new IdentityHashMap<>();
        private final Set<JsonElement> collected = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());

        private void collectTables(JsonElement value) {
            Map<String, JsonObject> incoming = new LinkedHashMap<>();
            Set<JsonElement> scanned = Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>());
            collectTables(value, incoming, scanned);
            validateIncoming(incoming);
            for (Map.Entry<String, JsonObject> entry : incoming.entrySet()) {
                // Copy: callers keep their artifact; verified definitions stay
                // immutable.
                definitions.put(entry.getKey(), entry.getValue().deepCopy());
            }
            collected.addAll(scanned);
        }

        private void collectTables(JsonElement value,
                                   Map<String, JsonObject> incoming,
                                   Set<JsonElement> scanned) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) return;
            if (collected.contains(value) || !scanned.add(value)) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectTables(child, incoming, scanned);
                }
                return;
            }
            JsonObject row = value.getAsJsonObject();
            JsonElement table = row.get(FIELD);
            if (table != null) readTable(table, definitions, incoming);
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    collectTables(field.getValue(), incoming, scanned);
                }
            }
        }

        /** A verified definition's closure was checked when it arrived, so
         *  it stands for no further dependency. */
        private void validateIncoming(Map<String, JsonObject> incoming) {
            Dag<String> dag = anchors(anchor -> definitions.containsKey(anchor)
                    ? new JsonObject() : incoming.get(anchor));
            for (String anchor : incoming.keySet()) dag.require(anchor);
        }

        private JsonElement internExpression(JsonObject expression) {
            if (expression == null || !SharedExpressionTable.expression(
                    expression)) {
                throw new IllegalArgumentException(
                        "VM definition must contain a concrete expression");
            }
            Set<JsonElement> active = Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>());
            JsonElement root = internCompact(expression,
                    new IdentityHashMap<JsonElement, JsonElement>(), active);
            if (!isReference(root)) {
                throw new IllegalStateException(
                        "interned expression did not produce a reference");
            }
            JsonElement result = expanded.get(anchor(root));
            if (result == null) {
                throw new IllegalStateException(
                        "interned expression has no expanded value");
            }
            return result;
        }

        private JsonElement internCompact(
                JsonElement value,
                IdentityHashMap<JsonElement, JsonElement> memo,
                Set<JsonElement> active) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            JsonElement memoized = memo.get(value);
            if (memoized != null) return memoized;
            if (!active.add(value)) {
                throw new IllegalArgumentException(
                        "cyclic expanded VM expression graph");
            }
            JsonElement result;
            if (value.isJsonArray()) {
                JsonArray copy = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    copy.add(internCompact(child, memo, active));
                }
                result = copy;
            } else {
                JsonObject source = value.getAsJsonObject();
                if (declaresReference(source)) {
                    requireReference(source, false);
                    String heldAnchor = exactString(source, ANCHOR);
                    if (!definitions.containsKey(heldAnchor)) {
                        throw new IllegalArgumentException(
                                "missing shared expression definition: "
                                        + heldAnchor);
                    }
                    result = reference(heldAnchor);
                } else {
                    String heldAnchor = anchorsByExpanded.get(source);
                    if (heldAnchor != null) {
                        result = reference(heldAnchor);
                    } else {
                        JsonObject compact = new JsonObject();
                        for (Map.Entry<String, JsonElement> field
                                : source.entrySet()) {
                            if (portableMember(field.getKey(),
                                    field.getValue())) {
                                compact.add(field.getKey(), internCompact(
                                        field.getValue(), memo, active));
                            }
                        }
                        if (!SharedExpressionTable.expression(source)) {
                            result = compact;
                        } else {
                            String computed = anchorFor(compact);
                            definitions.putIfAbsent(computed, compact);
                            anchorsByExpanded.put(source, computed);
                            expanded.putIfAbsent(computed, source);
                            result = reference(computed);
                        }
                    }
                }
            }
            active.remove(value);
            memo.put(value, result);
            return result;
        }

        private JsonElement expand(JsonElement value, Set<String> active,
                                   boolean artifactRoot) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            if (value.isJsonArray()) {
                JsonArray result = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    result.add(expand(child, active, false));
                }
                return result;
            }
            JsonObject source = value.getAsJsonObject();
            if (declaresReference(source)) {
                requireReference(source, artifactRoot && source.has(FIELD));
                String anchor = exactString(source, ANCHOR);
                JsonElement held = expanded.get(anchor);
                if (held != null) return held;
                JsonObject definition = definitions.get(anchor);
                if (definition == null) {
                    throw new IllegalArgumentException(
                            "missing shared expression definition: "
                                    + anchor);
                }
                if (!active.add(anchor)) {
                    throw new IllegalArgumentException(
                            "cyclic shared expression definition: "
                                    + anchor);
                }
                JsonElement result = expand(definition, active, false);
                active.remove(anchor);
                expanded.put(anchor, result);
                anchorsByExpanded.put(result, anchor);
                return result;
            }
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> field : source.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    result.add(field.getKey(), expand(field.getValue(),
                            active, false));
                }
            }
            return result;
        }
    }
}
