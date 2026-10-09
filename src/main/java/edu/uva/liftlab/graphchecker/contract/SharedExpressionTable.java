package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.textString;

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

    /**
     * One store of verified anchors: decodes envelopes, each definition
     * expanded once however many envelopes name it.
     */
    public static final class Codec {
        private final Resolver resolver = new Resolver();

        public synchronized JsonObject expand(JsonObject artifact) {
            if (artifact == null) return new JsonObject();
            requirePortableArtifact(artifact);
            resolver.collectTables(artifact);
            JsonElement expanded = resolver.expand(artifact);
            if (!expanded.isJsonObject()) {
                throw new IllegalArgumentException(
                        "artifact root must be object");
            }
            return expanded.getAsJsonObject();
        }
    }

    private static boolean expression(JsonObject value) {
        String type = textString(value, "_type");
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
                && REFERENCE_TYPE.equals(textString(
                value.getAsJsonObject(), "_type"));
    }

    private static void requireReference(JsonObject value,
                                         boolean allowArtifactTable) {
        if (!referenceMembers(value, allowArtifactTable)) {
            throw new IllegalArgumentException(
                    "shared expression reference has unsupported members");
        }
        requireAnchor(textString(value, ANCHOR));
    }

    private static boolean referenceMembers(JsonObject value,
                                            boolean allowArtifactTable) {
        if (value == null || !REFERENCE_TYPE.equals(
                textString(value, "_type"))
                || textString(value, ANCHOR).isEmpty()) {
            return false;
        }
        int expected = allowArtifactTable && value.has(FIELD) ? 3 : 2;
        return value.size() == expected
                && (!value.has(FIELD) || allowArtifactTable);
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
            String anchor = textString(row, ANCHOR);
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
     * cycle. {@code references} visits the keys one value names.  Depth
     * first on a stack: a definition chain is as deep as the VM's
     * expression chain.
     */
    static final class Dag<K> {
        private final String noun;
        private final Function<K, JsonObject> definition;
        private final BiConsumer<JsonElement, Consumer<K>> references;
        private final Set<K> visited = new HashSet<>();

        Dag(String noun, Function<K, JsonObject> definition,
            BiConsumer<JsonElement, Consumer<K>> references) {
            this.noun = noun;
            this.definition = definition;
            this.references = references;
        }

        void require(K key) {
            if (visited.contains(key)) return;
            Set<K> active = new HashSet<>();
            Deque<K> path = new ArrayDeque<>();
            Deque<Iterator<K>> named = new ArrayDeque<>();
            enter(key, active, path, named);
            while (!named.isEmpty()) {
                if (named.peek().hasNext()) {
                    K next = named.peek().next();
                    if (!visited.contains(next)) {
                        enter(next, active, path, named);
                    }
                    continue;
                }
                named.pop();
                K done = path.pop();
                active.remove(done);
                visited.add(done);
            }
        }

        private void enter(K key, Set<K> active, Deque<K> path,
                           Deque<Iterator<K>> named) {
            JsonObject defined = definition.apply(key);
            if (defined == null) {
                throw new IllegalArgumentException(
                        "missing " + noun + " definition: " + key);
            }
            if (!active.add(key)) {
                throw new IllegalArgumentException(
                        "cyclic " + noun + " definition: " + key);
            }
            List<K> keys = new ArrayList<>();
            references.accept(defined, keys::add);
            path.push(key);
            named.push(keys.iterator());
        }
    }

    /**
     * THE EXPANSION of every expression table: a copy of one value in which
     * each reference is its definition's expansion, each definition expanded
     * once, so the copy shares what the table shares.  On a stack: a
     * reference chain is as deep as the VM's expression chain, and the
     * recursion along it needed the publication thread's 512 MB stack.
     */
    abstract static class Expansion<K> {
        private final String noun;
        /** Concurrent: {@link #expanded(Object)} is asked unlocked. */
        private final Map<K, JsonElement> expanded =
                new ConcurrentHashMap<>();

        Expansion(String noun) {
            this.noun = noun;
        }

        /** Whether {@code key}'s definition has been expanded, which then
         *  answers for it; safe without the expanding thread's lock. */
        final boolean expanded(K key) {
            return expanded.containsKey(key);
        }

        /** The key {@code object} references, or null for a plain object;
         *  {@code root}: it is the artifact itself. */
        abstract K reference(JsonObject object, boolean root);

        /** The definition one key names, or null. */
        abstract JsonObject definition(K key);

        /** What the copy of a plain object holds for one member, still to
         *  expand; null drops the member. */
        abstract JsonElement member(String name, JsonElement value);

        final JsonElement expand(JsonElement root) {
            Deque<Copy<K>> copies = new ArrayDeque<>();
            Set<K> active = new HashSet<>();
            JsonElement done = enter(root, true, copies, active);
            while (!copies.isEmpty()) {
                Copy<K> copy = copies.peek();
                if (done != null) copy.add(done);
                JsonElement next = copy.next(this);
                if (next != null) {
                    done = enter(next, false, copies, active);
                    continue;
                }
                copies.pop();
                done = copy.result;
                if (copy.key != null) {
                    active.remove(copy.key);
                    expanded.put(copy.key, done);
                }
            }
            return done;
        }

        /** A value's copy when it is whole already, else null with the copy
         *  it needs pushed. */
        private JsonElement enter(JsonElement value, boolean root,
                                  Deque<Copy<K>> copies, Set<K> active) {
            if (value == null || value.isJsonNull()) return JsonNull.INSTANCE;
            if (value.isJsonPrimitive()) return value.deepCopy();
            K key = value.isJsonObject()
                    ? reference(value.getAsJsonObject(), root) : null;
            if (key == null) {
                copies.push(new Copy<K>(value));
                return null;
            }
            JsonElement held = expanded.get(key);
            if (held != null) return held;
            JsonObject definition = definition(key);
            if (definition == null) {
                throw new IllegalArgumentException(
                        "missing " + noun + " definition: " + key);
            }
            if (!active.add(key)) {
                throw new IllegalArgumentException(
                        "cyclic " + noun + " definition: " + key);
            }
            copies.push(new Copy<K>(key, definition));
            return null;
        }
    }

    /** One copy in progress: a plain object or array, or one key's value. */
    private static final class Copy<K> {
        /** The key whose definition this copy expands, or null. */
        private final K key;
        private final Iterator<JsonElement> items;
        private final Iterator<Map.Entry<String, JsonElement>> members;
        private JsonElement result;
        /** The member the next value fills. */
        private String name;

        private Copy(JsonElement plain) {
            this.key = null;
            if (plain.isJsonArray()) {
                items = plain.getAsJsonArray().iterator();
                members = null;
                result = new JsonArray();
            } else {
                items = null;
                members = plain.getAsJsonObject().entrySet().iterator();
                result = new JsonObject();
            }
        }

        private Copy(K key, JsonObject definition) {
            this.key = key;
            items = Collections.<JsonElement>singletonList(definition)
                    .iterator();
            members = null;
        }

        /** The next value to expand into this copy, or null when whole. */
        private JsonElement next(Expansion<K> expansion) {
            if (items != null) return items.hasNext() ? items.next() : null;
            while (members.hasNext()) {
                Map.Entry<String, JsonElement> member = members.next();
                JsonElement value = expansion.member(member.getKey(),
                        member.getValue());
                if (value != null) {
                    name = member.getKey();
                    return value;
                }
            }
            return null;
        }

        private void add(JsonElement value) {
            if (key != null) {
                result = value;
            } else if (members == null) {
                result.getAsJsonArray().add(value);
            } else {
                result.getAsJsonObject().add(name, value);
            }
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
                    return textString(row, ANCHOR);
                }, visit, Collections.newSetFromMap(
                        new IdentityHashMap<JsonElement, Boolean>())));
    }

    private static final class Resolver extends Expansion<String> {
        private final Map<String, JsonObject> definitions = new HashMap<>();
        private final Set<JsonElement> collected = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());

        private Resolver() {
            super("shared expression");
        }

        @Override
        String reference(JsonObject object, boolean root) {
            if (!declaresReference(object)) return null;
            requireReference(object, root && object.has(FIELD));
            return textString(object, ANCHOR);
        }

        @Override
        JsonObject definition(String anchor) {
            return definitions.get(anchor);
        }

        @Override
        JsonElement member(String name, JsonElement value) {
            return FIELD.equals(name) ? null : value;
        }

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
    }
}
