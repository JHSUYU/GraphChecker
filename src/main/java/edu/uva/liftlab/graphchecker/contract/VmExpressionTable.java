package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;

import java.io.IOException;
import java.io.StringReader;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

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

        /**
         * One page of a paged VM read-out -- a JSON object holding one array
         * of records ({@code records}, each self-contained but for the
         * nodes it references) beside the page's one expression table --
         * read as a stream: never parsed whole, never copied whole.  The
         * table comes last on the page, so the page is read twice.  First
         * every member but the records: the table is imported and checked
         * closed, the records are counted, and the rest is the header;
         * {@code admit} is asked of the header with the count stated as
         * {@link #RECORD_COUNT}.  Admitted, each record is then parsed,
         * expanded against the table and handed to {@code each} in page
         * order, one at a time; a definition is let go once expanded (the
         * expansion answers for its key from then on), and the rest when
         * the page ends.  A page with no table is a plain envelope read the
         * same way.
         *
         * @return the header, with the count
         */
        public synchronized JsonObject importRecords(
                String page, String records, Predicate<JsonObject> admit,
                Consumer<JsonElement> each) {
            return rawResolver.importRecords(page, records, admit, each);
        }
    }

    /** The member {@link Store#importRecords} states the record count in. */
    public static final String RECORD_COUNT = "__records";

    /**
     * One JVM's VM nodes, each expanded once and kept (Expansion).  What it
     * keeps grows with every node the run makes, so it keeps no more: a
     * node's definition only while its envelope imports (an envelope states
     * the closure of every node it names), then its hash, and one instance
     * of each member name and string value -- VM nodes repeat their sites'
     * class, method, descriptor and code-position strings.  Kept whole, the
     * definitions beside their expansions and every string a copy, they held
     * the 4 GB heap of a Solr seed replay full for its last ten minutes
     * (solr-adhoc SplitShardCmd-658: 265 thousand nodes, 2.1 GB of strings,
     * 1.1 GB of definition and expansion trees; jmap -histo).
     */
    private static final class RawResolver
            extends SharedExpressionTable.Expansion<RawKey> {
        /** The importing envelope's definitions. */
        private final Map<RawKey, JsonObject> definitions = new HashMap<>();
        /** Per node ever defined, its definition's {@link #fingerprint}: an
         *  envelope that defines it again defines it alike (to 32 bits). */
        private final Map<RawKey, Integer> defined = new HashMap<>();
        private final Map<String, String> names = new HashMap<>();
        private final Map<String, JsonPrimitive> strings = new HashMap<>();

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
            // Asked once per node, when it is first expanded: the copy its
            // expansion keeps, in this store's names and strings.  A page
            // read record by record lets it go then, since the expansion
            // answers for the key from now on.
            JsonObject stated = streaming ? definitions.remove(key)
                    : definitions.get(key);
            return stated == null ? null : canonical(stated).getAsJsonObject();
        }

        /** Whether a page is being read record by record. */
        private boolean streaming;

        private JsonObject importRecords(String page, String records,
                                         Predicate<JsonObject> admit,
                                         Consumer<JsonElement> each) {
            Set<RawKey> supplied = new LinkedHashSet<>();
            JsonObject header = new JsonObject();
            try {
                int count = 0;
                JsonReader reader = reader(page);
                while (reader.hasNext()) {
                    String name = reader.nextName();
                    if (FIELD.equals(name)) {
                        importTable(JsonParser.parseReader(reader), supplied);
                    } else if (records.equals(name)
                            && reader.peek() == JsonToken.BEGIN_ARRAY) {
                        reader.beginArray();
                        for (; reader.hasNext(); count++) reader.skipValue();
                        reader.endArray();
                    } else {
                        header.add(name, JsonParser.parseReader(reader));
                    }
                }
                header.addProperty(RECORD_COUNT, count);
                SharedExpressionTable.Dag<RawKey> dag =
                        new SharedExpressionTable.Dag<>("VM expression",
                                key -> supplied.contains(key)
                                        ? definitions.get(key) : null,
                                RawResolver::references);
                for (RawKey key : supplied) dag.require(key);
                if (!admit.test(header)) return header;
                streaming = true;
                reader = reader(page);
                while (reader.hasNext()) {
                    if (!records.equals(reader.nextName())
                            || reader.peek() != JsonToken.BEGIN_ARRAY) {
                        reader.skipValue();
                        continue;
                    }
                    reader.beginArray();
                    while (reader.hasNext()) {
                        JsonElement record = JsonParser.parseReader(reader);
                        // Self-contained but for the page's table.
                        references(record, key -> {
                            if (!supplied.contains(key)) {
                                throw new IllegalArgumentException(
                                        "missing VM expression definition: "
                                                + key);
                            }
                        });
                        each.accept(expand(record));
                    }
                    reader.endArray();
                }
                return header;
            } catch (IOException malformed) {
                throw new IllegalArgumentException(
                        "malformed VM read-out page", malformed);
            } finally {
                streaming = false;
                definitions.clear();
            }
        }

        /** A reader at the first member of a page that is a JSON object. */
        private static JsonReader reader(String page) throws IOException {
            JsonReader reader = new JsonReader(new StringReader(
                    page == null ? "" : page));
            if (reader.peek() != JsonToken.BEGIN_OBJECT) {
                throw new IllegalArgumentException(
                        "VM read-out page must be an object");
            }
            reader.beginObject();
            return reader;
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
            try {
                collectTables(artifact, supplied);
                validateDefinitions(artifact, supplied);
                JsonElement expandedArtifact = expand(artifact);
                if (!expandedArtifact.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM artifact root must be object");
                }
                return expandedArtifact.getAsJsonObject();
            } finally {
                definitions.clear();
            }
        }

        /** A copy of a definition with this store's one instance of each
         *  member name and string value (definitions are shallow: a child
         *  node is a reference). */
        private JsonElement canonical(JsonElement value) {
            if (value.isJsonObject()) {
                JsonObject copy = new JsonObject();
                for (Map.Entry<String, JsonElement> member
                        : value.getAsJsonObject().entrySet()) {
                    copy.add(names.computeIfAbsent(member.getKey(),
                            name -> name), canonical(member.getValue()));
                }
                return copy;
            }
            if (value.isJsonArray()) {
                JsonArray copy = new JsonArray();
                for (JsonElement item : value.getAsJsonArray()) {
                    copy.add(canonical(item));
                }
                return copy;
            }
            if (value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()) {
                return strings.computeIfAbsent(value.getAsString(),
                        text -> value.getAsJsonPrimitive());
            }
            // Numbers are mostly ids, each its own; JsonNull is one.
            return value.deepCopy();
        }

        /**
         * A definition's hash, alike for definitions alike as JSON: members
         * in any order, every primitive by its kind and text.  Gson's own
         * hashes a number it parsed by parsing it as a double, which the
         * concolic VM paid on every definition of every page (solr-18406
         * seed replay, jstack: its publication thread in
         * FloatingDecimal under JsonObject#hashCode).
         */
        private static int fingerprint(JsonElement value) {
            if (value.isJsonObject()) {
                int hash = 0;
                for (Map.Entry<String, JsonElement> member
                        : value.getAsJsonObject().entrySet()) {
                    hash += member.getKey().hashCode()
                            ^ fingerprint(member.getValue());
                }
                return hash;
            }
            if (value.isJsonArray()) {
                int hash = 1;
                for (JsonElement item : value.getAsJsonArray()) {
                    hash = 31 * hash + fingerprint(item);
                }
                return hash;
            }
            if (value.isJsonNull()) return 0;
            JsonPrimitive primitive = value.getAsJsonPrimitive();
            return 31 * (primitive.isString() ? 1 : primitive.isNumber() ? 2
                    : 3) + primitive.getAsString().hashCode();
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
                Integer hash = fingerprint(definition);
                Integer before = defined.putIfAbsent(key, hash);
                JsonObject here = definitions.putIfAbsent(key, definition);
                if (before != null && !before.equals(hash)
                        || here != null && !here.equals(definition)) {
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
