package edu.uva.liftlab.graphchecker.d3.plan;

import edu.uva.liftlab.graphchecker.d3.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.d3.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;

/**
 * Content-addressed storage for immutable symbolic-expression DAGs.
 *
 * <p>The VM propagates values as shared expression nodes, but JSON has no
 * object references.  Expanding every use as a tree made a downstream value
 * restate its complete upstream history at every handoff, summary field and
 * case dependency.  This codec restores the DAG at artifact boundaries: an
 * occurrence contains only an {@code EXPR.v1.<sha256>} reference and the
 * artifact carries each immutable node definition once.</p>
 *
 * <p>An anchor hashes one node whose expression children have already become
 * anchors.  It is therefore a Merkle identity: computing or comparing a
 * parent never serializes the full causal chain again.  Case ownership,
 * path-condition selectors and VM event ids remain in their existing evidence
 * records; this table deduplicates values and does not infer causality.</p>
 */
public final class SharedExpressionTable {
    public static final int SCHEMA_VERSION = 1;
    public static final String FIELD = "sharedExpressionTable";
    public static final String KIND = "CONTENT_ADDRESSED_EXPRESSION_TABLE";
    public static final String AUTHORITY = "MERKLE_EXPRESSION_SHA256_V1";
    public static final String REFERENCE_TYPE = "SharedExpressionReference";
    public static final String ANCHOR = "expressionAnchor";
    private static final String PREFIX = "EXPR.v1.";
    private static final String HASH_DOMAIN =
            "GraphChecker/content-addressed-expression/v1\n";

    private SharedExpressionTable() {
    }

    /** Compacts every VM expression nested in one portable artifact. */
    public static JsonObject compact(JsonObject artifact) {
        if (artifact == null) return new JsonObject();
        Builder builder = new Builder();
        return compactArtifact(artifact, builder);
    }

    private static JsonObject compactArtifact(JsonObject artifact,
                                              Builder builder) {
        builder.collectTables(artifact);
        // A table is one self-contained artifact.  Bad unreachable rows are
        // corruption too; pruning must not make compact() accept what
        // expand() rejects.
        builder.validateDefinitions();
        return compactDecodedArtifact(artifact, builder);
    }

    /**
     * Compacts a run of artifacts that carry one common expression table.
     *
     * <p>{@link #compact(JsonObject)} is one self-contained trust boundary: it
     * parses and re-hashes every definition it is handed. A wave's flip rows
     * are handed the <em>same</em> table object, so doing that per row re-read
     * and re-hashed one table once per row, which grows with the product of
     * the row count and the table size.</p>
     *
     * <p>This compactor keeps the definitions it has already verified, and the
     * anchors it has already computed, across the artifacts of one such run.
     * Each artifact still publishes only the rows reachable from itself, so
     * each one carries exactly the table {@link #compact(JsonObject)} gave it.
     * Use it only where the artifacts genuinely share their table: definitions
     * verified for an earlier member of the run stay available to a later one,
     * which is what makes the reuse sound and what a mixed batch would not
     * support.</p>
     */
    public static final class Compactor {
        private final Builder builder = new Builder();

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

    /** Replaces expression DAGs by their Merkle roots without serializing them. */
    private static JsonObject compactRoot(JsonObject artifact,
                                          Builder builder) {
        JsonElement compact = builder.compact(artifact, true);
        if (!compact.isJsonObject()) {
            throw new IllegalArgumentException("artifact root must be object");
        }
        builder.requireReferencesDefined();
        return compact.getAsJsonObject();
    }

    /**
     * Expands several portable artifacts through one resolver.
     *
     * <p>Inputs are already content-addressed. The resolver interns equal
     * definitions across artifact rows, so one expression node has one
     * in-memory representation even when several summaries use it. Internal
     * consumers still receive the tree-shaped VM IR.</p>
     */
    public static List<JsonObject> expandAll(
            Collection<JsonObject> artifacts) {
        return new Decoder().expandAll(artifacts);
    }

    private static JsonObject expandArtifact(JsonObject artifact,
                                             Resolver resolver) {
        JsonElement expanded = resolver.expand(artifact,
                new HashSet<String>());
        if (!expanded.isJsonObject()) {
            throw new IllegalArgumentException("artifact root must be object");
        }
        return expanded.getAsJsonObject();
    }

    /** Reuses node identities while hashing a related set of expressions. */
    public static final class Anchors {
        private final Builder builder = new Builder();

        public String contentAnchor(JsonElement expression) {
            if (declaresReference(expression)) {
                requireReference(expression.getAsJsonObject(), false);
                String value = anchor(expression);
                return value;
            }
            if (expression == null || !expression.isJsonObject()
                    || !expression(expression.getAsJsonObject())) {
                throw new IllegalArgumentException(
                        "content anchor requires one expression object");
            }
            JsonElement root = builder.compact(expression, false);
            if (!isReference(root)) {
                throw new IllegalStateException(
                        "expression root did not compact to a reference");
            }
            String result = anchor(root);
            builder.validateReference(result);
            return result;
        }
    }

    /** Incremental decoder which interns anchors across several envelopes. */
    public static final class Decoder {
        private final Resolver resolver = new Resolver();

        public synchronized JsonObject expand(JsonObject artifact) {
            if (artifact == null) return new JsonObject();
            requirePortableArtifact(artifact);
            resolver.collectTables(artifact);
            return expandArtifact(artifact, resolver);
        }

        /** Expands a related batch while retaining one anchor resolver. */
        public synchronized List<JsonObject> expandAll(
                Collection<JsonObject> artifacts) {
            List<JsonObject> portable = new ArrayList<>();
            if (artifacts != null) {
                for (JsonObject artifact : artifacts) {
                    if (artifact != null) {
                        requirePortableArtifact(artifact);
                        portable.add(artifact);
                    }
                }
            }
            for (JsonObject artifact : portable) {
                resolver.collectTables(artifact);
            }
            List<JsonObject> result = new ArrayList<>(portable.size());
            for (JsonObject artifact : portable) {
                result.add(expandArtifact(artifact, resolver));
            }
            return Collections.unmodifiableList(result);
        }

        /**
         * Interns one expression assembled from a validated VM-session DAG.
         *
         * <p>This is deliberately package-local: unlike {@link #expand}, it is
         * not an artifact trust boundary.  The VM adapter has already checked
         * every session/id reference and this method computes the Merkle anchor
         * itself.  Existing child identities and equal content are reused, so
         * a raw expression id is hashed only when it is first imported.</p>
         */
        synchronized JsonElement internExpression(JsonObject expression) {
            return resolver.internExpression(expression);
        }

        /** Loads portable definitions before a mixed native/portable decode. */
        synchronized void collectTables(JsonObject artifact) {
            if (artifact != null) resolver.collectTables(artifact);
        }

        /**
         * Compacts an object graph previously returned by this decoder.
         *
         * <p>The decoder remembers the anchor for every expanded expression
         * identity. Reusing that map avoids hashing the same VM expression a
         * second time when a runtime result is published. New wrapper nodes
         * added after decoding are still content-addressed normally.</p>
         */
        public synchronized JsonObject compact(JsonObject artifact) {
            if (artifact == null) return new JsonObject();
            return compactDecodedArtifact(artifact,
                    new Builder(resolver.definitions,
                            resolver.anchorsByExpanded));
        }

    }

    public static boolean isReference(JsonElement value) {
        if (!declaresReference(value)) return false;
        JsonObject reference = value.getAsJsonObject();
        return referenceMembers(reference, reference.has(FIELD));
    }

    public static String anchor(JsonElement reference) {
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

    /** Artifact readers accept references, never old inline expression trees. */
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

    /** Parses and hash-checks only rows not already verified by a decoder. */
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

    /** Matches the default Gson wire while retaining semantic null guards. */
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

    private static final class Builder {
        private final Map<String, JsonObject> definitions =
                new LinkedHashMap<>();
        private final Map<JsonElement, String> compactedExpressions =
                new IdentityHashMap<>();
        /** One compact operation may receive an already expanded shared DAG. */
        private final Set<JsonElement> collected = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        /** References reachable from the compacted artifact root. */
        private final Set<String> references = new LinkedHashSet<>();
        /** Anchors already checked by an incremental identity client. */
        private final Set<String> validatedReferences = new HashSet<>();
        /**
         * Definitions already walked for shape and acyclicity.  A definition
         * is immutable and named by its own content, so one pass over it
         * settles it for every artifact this builder goes on to compact.
         */
        private final Set<String> validatedDefinitions = new LinkedHashSet<>();
        private Set<String> reachable = Collections.emptySet();

        private Builder() {
        }

        /** Direct view of definitions already verified by one Decoder. */
        private Builder(Map<String, JsonObject> verifiedDefinitions,
                        Map<JsonElement, String> verifiedAnchors) {
            definitions.putAll(verifiedDefinitions);
            compactedExpressions.putAll(verifiedAnchors);
        }

        private void collectTables(JsonElement value) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) return;
            if (!collected.add(value)) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectTables(child);
                }
                return;
            }
            JsonObject row = value.getAsJsonObject();
            JsonElement encoded = row.get(FIELD);
            if (encoded != null) importTable(encoded);
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    collectTables(field.getValue());
                }
            }
        }

        private void importTable(JsonElement encoded) {
            Map<String, JsonObject> incoming = new LinkedHashMap<>();
            readTable(encoded, definitions, incoming);
            definitions.putAll(incoming);
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
                // pathGuard:null means an observed empty conjunction, while
                // an absent pathGuard means the guard was not captured.
                if (portableMember(field.getKey(), field.getValue())) {
                    result.add(field.getKey(), compact(field.getValue(),
                            false));
                }
            }
            if (!expression(source)) return result;
            String anchor = anchorFor(result);
            put(anchor, result);
            compactedExpressions.put(source, anchor);
            references.add(anchor);
            return reference(anchor);
        }

        private void put(String anchor, JsonObject definition) {
            definitions.putIfAbsent(anchor, definition);
        }

        private void requireReferencesDefined() {
            for (String anchor : references) {
                requireAnchor(anchor);
                if (!definitions.containsKey(anchor)) {
                    throw new IllegalArgumentException(
                            "missing shared expression definition: " + anchor);
                }
            }
        }

        private void validateReferences() {
            Set<String> visited = new LinkedHashSet<>();
            Set<String> active = new LinkedHashSet<>();
            for (String anchor : references) {
                validateReachable(anchor, visited, active);
            }
            reachable = visited;
        }

        private void validateReference(String anchor) {
            validateReachable(anchor, validatedReferences,
                    new LinkedHashSet<String>());
        }

        private void validateDefinitions() {
            Set<String> active = new LinkedHashSet<>();
            for (String anchor : definitions.keySet()) {
                validateReachable(anchor, validatedDefinitions, active);
            }
        }

        /**
         * Starts one artifact's reachability.  Definitions and anchors carry
         * over; what this artifact publishes must not.
         */
        private void beginArtifact() {
            references.clear();
            reachable = Collections.emptySet();
        }

        private void validateReachable(String anchor, Set<String> visited,
                                       Set<String> active) {
            requireAnchor(anchor);
            if (visited.contains(anchor)) return;
            JsonObject definition = definitions.get(anchor);
            if (definition == null) {
                throw new IllegalArgumentException(
                        "missing shared expression definition: " + anchor);
            }
            if (!active.add(anchor)) {
                throw new IllegalArgumentException(
                        "cyclic shared expression definition: " + anchor);
            }
            for (String dependency : referencesIn(definition)) {
                validateReachable(dependency, visited, active);
            }
            active.remove(anchor);
            visited.add(anchor);
        }

        private static Set<String> referencesIn(JsonElement value) {
            Set<String> result = new LinkedHashSet<>();
            collectReferences(value, result);
            return result;
        }

        private static void collectReferences(JsonElement value,
                                              Set<String> result) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectReferences(child, result);
                }
                return;
            }
            JsonObject row = value.getAsJsonObject();
            if (declaresReference(row)) {
                requireReference(row, false);
                String anchor = exactString(row, ANCHOR);
                result.add(anchor);
                return;
            }
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                collectReferences(field.getValue(), result);
            }
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
        /** Decoder instances retain this across envelopes they intern. */
        private final Set<JsonElement> collected = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());

        private void collectTables(JsonElement value) {
            Map<String, JsonObject> incoming = new LinkedHashMap<>();
            Set<JsonElement> scanned = Collections.newSetFromMap(
                    new IdentityHashMap<JsonElement, Boolean>());
            collectTables(value, incoming, scanned);
            validateIncoming(incoming);
            for (Map.Entry<String, JsonObject> entry : incoming.entrySet()) {
                // Public callers retain their artifact object. Keep verified
                // definitions immutable across later decoder calls.
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

        /** Validates only new rows; old definitions already passed this check. */
        private void validateIncoming(Map<String, JsonObject> incoming) {
            Set<String> visited = new LinkedHashSet<>();
            Set<String> active = new LinkedHashSet<>();
            for (String anchor : incoming.keySet()) {
                validateIncoming(anchor, incoming, visited, active);
            }
        }

        private void validateIncoming(String anchor,
                                      Map<String, JsonObject> incoming,
                                      Set<String> visited,
                                      Set<String> active) {
            if (definitions.containsKey(anchor) || visited.contains(anchor)) {
                return;
            }
            JsonObject definition = incoming.get(anchor);
            if (definition == null) {
                throw new IllegalArgumentException(
                        "missing shared expression definition: " + anchor);
            }
            if (!active.add(anchor)) {
                throw new IllegalArgumentException(
                        "cyclic shared expression definition: " + anchor);
            }
            for (String dependency : Builder.referencesIn(definition)) {
                validateIncoming(dependency, incoming, visited, active);
            }
            active.remove(anchor);
            visited.add(anchor);
        }

        /** Computes and interns only expression identities not seen before. */
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

        private JsonElement expand(JsonElement value, Set<String> active) {
            return expand(value, active, true);
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
