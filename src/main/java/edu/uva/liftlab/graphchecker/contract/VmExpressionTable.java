package edu.uva.liftlab.graphchecker.contract;

import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.VmRows;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;

import java.io.IOException;
import java.io.StringReader;
import java.lang.ref.SoftReference;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Consumer;
import java.util.function.Function;
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

    /**
     * Decodes a region's VM envelopes, each VM node one object however many
     * envelopes name it.  Shared by the threads that decode into it (a
     * region's owner, its branch windows; the decoding thread, its
     * read-out pages), it is locked only while a node is expanded or an
     * envelope's table is imported, never while text is parsed or a decoded
     * record is consumed: held across a whole read-out page, its decoding
     * and its filing, it stalled the owner's every branch window behind the
     * publication thread (A2's SB19 seed replay: the Overseer BLOCKED in
     * {@code PathConditionWindow} while the publication thread filed a page).
     */
    public static final class Store {
        private final SharedExpressionTable.Codec codec =
                new SharedExpressionTable.Codec();
        private final RawResolver rawResolver;

        /**
         * @param plumbing whether code of a class (the VM's spelling, {@code
         *                 a/b/C$D}) is the engine's own plumbing, never
         *                 program state (RULES): a read such code made is
         *                 imported as the value of the version it observed
         */
        public Store(Predicate<String> plumbing) {
            rawResolver = new RawResolver(plumbing);
        }

        public JsonObject importEnvelope(String serialized) {
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

        public JsonObject importEnvelope(JsonObject envelope) {
            return usesNativeDag(envelope)
                    ? rawResolver.importEnvelope(envelope)
                    : codec.expand(envelope);
        }

        public JsonElement importField(String serialized, String field) {
            JsonObject envelope = importEnvelope(serialized);
            JsonElement value = envelope.get(field);
            return value == null || value.isJsonNull() ? null : value;
        }

        /**
         * One VM envelope of records -- a JSON object holding one array of
         * records ({@code records}, each self-contained but for the nodes it
         * references) beside the envelope's one expression table, as a
         * read-out page and a branch's path-condition window are -- never
         * parsed whole, never copied whole.  Its top level is read off the
         * text once: the members but the records parsed as the header, each
         * record's extent found by its brackets, up to the table, the last
         * member.  The table's rows are read off the text, a row of a node
         * this store has expanded already skipped by its id, unscanned (its
         * expansion answers for it: a window repeats the closure of its
         * condition, a page the closure its locations share), the rest
         * parsed, checked closed and kept; {@code admit} is asked of the
         * header with the record count stated as {@link #RECORD_COUNT}.
         * Admitted, each record is then parsed, expanded against the table
         * and handed to {@code each} in order, one at a time, outside the
         * store's lock; a definition is let go once expanded, and the rest
         * when the envelope ends.  An envelope with no table is a plain one
         * read the same way.
         *
         * @return the header, with the count
         */
        public JsonObject importRecords(String page, String records,
                                        Predicate<JsonObject> admit,
                                        Consumer<JsonElement> each) {
            return rawResolver.<JsonElement>importRecords(page, records,
                    admit, null, record -> record, each);
        }

        /**
         * {@link #importRecords}, each record decoded by {@code decode} and
         * its decoding handed to {@code each} -- once per text: a record
         * whose text this store has decoded before (a location a read-out
         * states again unchanged) is neither parsed, expanded nor decoded
         * again, and {@code each} takes the decoding it had.  So
         * {@code decode} must be a function of the record's text and this
         * store alone.  A page every record of which is held reads no
         * table: it no longer checks that table's well-formedness (schema,
         * count, closing), its rows' shape, nor registers and closure-checks
         * the rows not yet expanded -- there are none: every row it would
         * define is a node the records' first decoding expanded (a page's
         * table is the closure of what its records name).  Nor is a held
         * record checked for a node the page's table lacks ("missing VM
         * expression definition"): its first decoding was, against its own
         * page's table.
         */
        public <T> JsonObject importRepeatedRecords(
                String page, String records, Predicate<JsonObject> admit,
                Class<T> decoding, Function<JsonElement, T> decode,
                Consumer<? super T> each) {
            return rawResolver.importRecords(page, records, admit,
                    repeats(decoding), decode, each);
        }

        /**
         * The records read-out pages decoded, one memo per decoding type
         * ({@link Repeats}): a memo holds the decodings of its own type
         * only.  This store's own: a session's decodings name its nodes.
         */
        private final Map<Class<?>, Repeats<?>> repeated = new HashMap<>();

        private <T> Repeats<T> repeats(Class<T> decoding) {
            synchronized (repeated) {
                Repeats<?> held = repeated.get(decoding);
                if (held == null) {
                    held = new Repeats<T>();
                    repeated.put(decoding, held);
                }
                // Keyed by its decoding type: it holds that type only.
                @SuppressWarnings("unchecked")
                Repeats<T> typed = (Repeats<T>) held;
                return typed;
            }
        }

        /**
         * What the held records cost: how many are held, the chars of their
         * text, and how many the collector cleared (each one decoded again
         * if it is read out again).
         */
        public String repeatedSummary() {
            long[] total = new long[3];
            synchronized (repeated) {
                for (Repeats<?> held : repeated.values()) {
                    long[] tally = held.tally();
                    for (int index = 0; index < total.length; index++) {
                        total[index] += tally[index];
                    }
                }
            }
            return String.format(java.util.Locale.ROOT, "%d record(s) held,"
                            + " %.1f M chars of their text, %d cleared by the"
                            + " collector", total[0], total[1] / 1e6,
                    total[2]);
        }
    }

    /** One decoded record's exact text and its decoding. */
    private static final class Held<T> {
        private final String text;
        private final T decoding;

        private Held(String text, T decoding) {
            this.text = text;
            this.decoding = decoding;
        }
    }

    /**
     * A store's held records of one decoding type, by their text up to its
     * first {@code '}'} (a location envelope's location: one entry per
     * location, the latest): the exact text and its decoding.  Held softly:
     * a collection under memory pressure drops an entry, and the next
     * read-out of that record decodes it again.
     */
    private static final class Repeats<T> {
        private final Map<String, SoftReference<Held<T>>> held =
                new HashMap<>();
        /** Entries a lookup found cleared, and let go. */
        private long cleared;

        /** The lookup key of the record at {@code start}: its text up to
         *  its first '}', or null. */
        private static String key(String page, int start) {
            int end = page.indexOf('}', start);
            return end < 0 ? null : page.substring(start, end + 1);
        }

        /** The held record the page holds at {@code start} exactly, or
         *  null: a JSON object ends where its text does, so a page whose
         *  text from {@code start} begins with a held record's whole text
         *  holds that record there. */
        private Held<T> at(String page, int start) {
            String key = key(page, start);
            if (key == null) return null;
            Held<T> record;
            synchronized (held) {
                SoftReference<Held<T>> reference = held.get(key);
                record = reference == null ? null : reference.get();
                if (reference != null && record == null) {
                    cleared++;
                    held.remove(key);
                }
            }
            return record != null && page.regionMatches(start, record.text,
                    0, record.text.length()) ? record : null;
        }

        /** Holds one decoded record, the latest of its key. */
        private void hold(String text, T decoded) {
            String key = key(text, 0);
            if (key == null) return;
            synchronized (held) {
                held.put(key, new SoftReference<Held<T>>(
                        new Held<T>(text, decoded)));
            }
        }

        /** {records held, chars of their text, entries cleared}. */
        private long[] tally() {
            long[] tally = {0L, 0L, 0L};
            synchronized (held) {
                tally[2] = cleared;
                for (SoftReference<Held<T>> reference : held.values()) {
                    Held<T> record = reference.get();
                    if (record == null) {
                        tally[2]++;
                    } else {
                        tally[0]++;
                        tally[1] += record.text.length();
                    }
                }
            }
            return tally;
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
        /** The definitions the expansion holding the lock reads: its
         *  envelope's, set for it and cleared after it. */
        private Map<RawKey, JsonObject> definitions = Collections.emptyMap();
        /** Per node ever defined, its definition's {@link #fingerprint}: an
         *  envelope that defines it again, unless the node was expanded
         *  already, defines it alike (to 32 bits).  Concurrent: a stream's
         *  table is checked against it unlocked. */
        private final Map<RawKey, Integer> defined = new ConcurrentHashMap<>();
        private final Map<String, String> names = new HashMap<>();
        private final Map<String, JsonPrimitive> strings = new HashMap<>();
        private final Predicate<String> plumbing;

        private RawResolver(Predicate<String> plumbing) {
            super("VM expression");
            this.plumbing = plumbing;
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
            return stated == null ? null
                    : canonical(observedValue(stated)).getAsJsonObject();
        }

        /**
         * A read the engine's own plumbing made -- a wire carrier's read-back,
         * a generated message's or builder's field -- stands for the value
         * of the version it observed (its {@code observedVersion}'s
         * expression, else the value it read): no row states such a read,
         * and its location is no program state (RULES).  Any other node
         * stands for itself.
         */
        private JsonObject observedValue(JsonObject stated) {
            if (!VmRows.GUARDED_READ_TYPE.equals(
                    optionalString(stated, "_type"))) {
                return stated;
            }
            JsonElement site = stated.get("site");
            if (site == null || !site.isJsonObject() || !plumbing.test(
                    optionalString(site.getAsJsonObject(), "className"))) {
                return stated;
            }
            JsonElement observed = stated.get("observedVersion");
            JsonElement value = observed != null && observed.isJsonObject()
                    ? observed.getAsJsonObject().get("expression") : null;
            if (value == null || !value.isJsonObject()) {
                value = stated.get("concreteValue");
            }
            return value != null && value.isJsonObject()
                    ? value.getAsJsonObject() : stated;
        }

        /** Whether a page is being read record by record. */
        private boolean streaming;

        /**
         * One envelope of records ({@link Store#importRecords}), its top
         * level read off the text once: the header's members parsed, each
         * record's extent found -- a record {@code repeats} holds by its
         * whole text, any other by scanning it -- up to the table, the last
         * member.  The table is read when a record is to be decoded (or
         * there is none), then the header with its count is admitted, then
         * the records are handed on in page order: a held one's decoding,
         * any other parsed, expanded, decoded and held.
         */
        private <T> JsonObject importRecords(String page, String records,
                                             Predicate<JsonObject> admit,
                                             Repeats<T> repeats,
                                             Function<JsonElement, T> decode,
                                             Consumer<? super T> each) {
            Map<RawKey, JsonObject> table = new HashMap<>();
            Set<RawKey> supplied = new HashSet<>();
            JsonObject header = new JsonObject();
            // Each record's extent, and what repeats holds of it (or null).
            List<int[]> extents = new ArrayList<>();
            List<Held<T>> held = new ArrayList<>();
            boolean decodes = false;
            int tabled = -1;
            int at = TopLevel.open(page);
            while (TopLevel.peek(page, at) != '}') {
                String name = TopLevel.name(page, at);
                int value = TopLevel.value(page, at);
                if (FIELD.equals(name)) {
                    // The envelope's last member, read off the text.
                    tabled = at;
                    break;
                }
                if (!records.equals(name)
                        || TopLevel.peek(page, value) != '[') {
                    int end = TopLevel.end(page, value);
                    header.add(name, parse(page, value, end));
                    at = TopLevel.next(page, end, '}');
                    continue;
                }
                at = TopLevel.space(page, value + 1);
                while (TopLevel.peek(page, at) != ']') {
                    Held<T> record = repeats == null ? null
                            : repeats.at(page, at);
                    int end = record != null ? at + record.text.length()
                            : TopLevel.end(page, at);
                    extents.add(new int[] {at, end});
                    held.add(record);
                    decodes |= record == null;
                    at = TopLevel.next(page, end, ']');
                }
                at = TopLevel.next(page, at + 1, '}');
            }
            if (tabled >= 0 && (decodes || extents.isEmpty())) {
                // From the separator before the table's member.
                readTable(page, Math.max(0, tabled - 1), supplied, table);
            }
            header.addProperty(RECORD_COUNT, extents.size());
            SharedExpressionTable.Dag<RawKey> dag =
                    new SharedExpressionTable.Dag<>("VM expression",
                            key -> table.containsKey(key) ? table.get(key)
                                    : supplied.contains(key)
                                            && expanded(key) ? CLOSED : null,
                            RawResolver::references);
            // A node expanded already is closed: only the rows the table
            // defines have a closure to check.
            for (RawKey key : table.keySet()) dag.require(key);
            if (!admit.test(header)) return header;
            for (int index = 0; index < extents.size(); index++) {
                Held<T> record = held.get(index);
                if (record != null) {
                    each.accept(record.decoding);
                    continue;
                }
                int[] extent = extents.get(index);
                String text = page.substring(extent[0], extent[1]);
                JsonElement parsed = JsonParser.parseString(text);
                // Self-contained but for the envelope's table.
                references(parsed, key -> {
                    if (!supplied.contains(key)) {
                        throw new IllegalArgumentException(
                                "missing VM expression definition: " + key);
                    }
                });
                T decoded = decode.apply(expandAgainst(table, parsed));
                if (repeats != null) repeats.hold(text, decoded);
                each.accept(decoded);
            }
            return header;
        }

        /** The JSON value at {@code [start, end)} of {@code page}. */
        private static JsonElement parse(String page, int start, int end) {
            return JsonParser.parseString(page.substring(start, end));
        }

        /**
         * An envelope's top level read off its text: where each member,
         * value and record starts and ends, nothing parsed.  A value's end
         * is found by its brackets outside strings; a string by its first
         * unescaped quote.  Anything else than JSON is refused.
         */
        private static final class TopLevel {
            private TopLevel() {
            }

            /** The first member of the object {@code page} is, or its
             *  closing brace. */
            static int open(String page) {
                int at = space(page == null ? "" : page, 0);
                if (page == null || at >= page.length()
                        || page.charAt(at) != '{') {
                    throw new IllegalArgumentException(
                            "VM read-out page must be an object");
                }
                return space(page, at + 1);
            }

            /** The character at {@code at}, refused past the end. */
            static char peek(String page, int at) {
                if (at >= page.length()) throw malformed();
                return page.charAt(at);
            }

            /** The first non-blank at or after {@code at}. */
            static int space(String page, int at) {
                while (at < page.length()
                        && Character.isWhitespace(page.charAt(at))) {
                    at++;
                }
                return at;
            }

            /** The name of the member at {@code at}. */
            static String name(String page, int at) {
                if (peek(page, at) != '"') throw malformed();
                int end = quote(page, at);
                String spelled = page.substring(at + 1, end);
                return spelled.indexOf('\\') < 0 ? spelled
                        : parse(page, at, end + 1).getAsString();
            }

            /** Where the value of the member at {@code at} starts. */
            static int value(String page, int at) {
                int colon = space(page, quote(page, at) + 1);
                if (peek(page, colon) != ':') throw malformed();
                return space(page, colon + 1);
            }

            /** Past the value starting at {@code at}. */
            static int end(String page, int at) {
                char first = peek(page, at);
                if (first == '"') return quote(page, at) + 1;
                if (first != '{' && first != '[') {
                    int end = at;
                    while (end < page.length()
                            && ",}] \t\r\n".indexOf(page.charAt(end)) < 0) {
                        end++;
                    }
                    if (end == at) throw malformed();
                    return end;
                }
                int depth = 0;
                for (int index = at; index < page.length(); index++) {
                    char c = page.charAt(index);
                    if (c == '"') {
                        index = quote(page, index);
                    } else if (c == '{' || c == '[') {
                        depth++;
                    } else if ((c == '}' || c == ']') && --depth == 0) {
                        return index + 1;
                    }
                }
                throw malformed();
            }

            /** After a value ending at {@code end}: the next one's start,
             *  or the {@code closer} of its object or array. */
            static int next(String page, int end, char closer) {
                int at = space(page, end);
                char c = peek(page, at);
                if (c == closer) return at;
                if (c != ',') throw malformed();
                return space(page, at + 1);
            }

            /** The quote closing the string opened at {@code open}. */
            private static int quote(String page, int open) {
                for (int at = page.indexOf('"', open + 1); at >= 0;
                     at = page.indexOf('"', at + 1)) {
                    int escapes = 0;
                    while (page.charAt(at - 1 - escapes) == '\\') escapes++;
                    if (escapes % 2 == 0) return at;
                }
                throw malformed();
            }

            private static IllegalArgumentException malformed() {
                return new IllegalArgumentException(
                        "malformed VM read-out page");
            }
        }

        /** One record expanded against its envelope's table, under the
         *  lock; each definition it reads is let go. */
        private synchronized JsonElement expandAgainst(
                Map<RawKey, JsonObject> table, JsonElement record) {
            definitions = table;
            streaming = true;
            try {
                return expand(record);
            } finally {
                streaming = false;
                definitions = Collections.emptyMap();
            }
        }

        /** What a node already expanded stands for in a closure check: a
         *  node with nothing left to check. */
        private static final JsonObject CLOSED = new JsonObject();

        /** How the VM spells the start of the table, the last member of an
         *  envelope, and of its rows (CONTRACT-SPEC §2.3): compact, a row's
         *  members in this order.  A definition is one shallow object (a
         *  child is a reference) whose strings are escaped, so neither can
         *  occur inside one. */
        private static final String TABLE_KEY = ",\"" + FIELD + "\":{";
        private static final String ROWS_KEY = ",\"definitions\":[";
        private static final String ROW = "{\"_type\":\"" + DEFINITION_TYPE
                + "\",\"sessionId\":";
        private static final String ROW_ID = ",\"expressionId\":";
        private static final String ROW_EXPRESSION = ",\"expression\":";
        /** Closes the rows, the table and the envelope. */
        private static final String TABLE_END = "]}}";

        /**
         * The envelope's expression table, read off its text: each row's
         * key into {@code supplied}, and into {@code table} the definition
         * of every node this store has not expanded yet, checked against
         * what an earlier envelope defined it as.  A row of a node the
         * store has expanded is skipped by its id, unparsed: a row ends
         * where the next one starts, so its definition is never scanned as
         * JSON (a branch window repeats the closure of its condition, a page
         * the closure its locations share: hdfs-adhoc-03's read-out pages
         * were 20 MB of rows the store held, 18 s each to scan).  Fail
         * closed: a row whose id does not read as the VM spells it is
         * parsed whole, and the table must close the envelope, state its
         * schema, its own session on every row, and its row count.  It is
         * looked for from {@code from}, where the envelope's members end.
         */
        private void readTable(String page, int from, Set<RawKey> supplied,
                               Map<RawKey, JsonObject> table) {
            try {
                readTableRows(page, from, supplied, table);
            } catch (IOException malformed) {
                throw new IllegalArgumentException(
                        "malformed VM read-out page", malformed);
            }
        }

        private void readTableRows(String page, int from,
                                   Set<RawKey> supplied,
                                   Map<RawKey, JsonObject> table)
                throws IOException {
            int start = page.indexOf(TABLE_KEY, from);
            int rows = start < 0 ? -1 : page.indexOf(ROWS_KEY, start);
            int end = page.length() - TABLE_END.length();
            if (rows < 0 || !page.startsWith(TABLE_END, end)) {
                throw new IllegalArgumentException(
                        "VM expression table must close its envelope");
            }
            JsonObject stated = JsonParser.parseString(page.substring(
                    start + TABLE_KEY.length() - 1, rows) + "}")
                    .getAsJsonObject();
            List<RawKey> keys = new ArrayList<>();
            for (int row = rows + ROWS_KEY.length(); row < end; ) {
                if (!keys.isEmpty() && page.charAt(row++) != ',') {
                    throw new IllegalArgumentException(
                            "VM expression rows must be separated");
                }
                int next = page.indexOf("," + ROW, row);
                int stop = next < 0 || next > end ? end : next;
                RawKey held = heldRow(page, row);
                keys.add(held != null ? held : readDefinition(
                        page.substring(row, stop), table));
                row = stop;
            }
            long session = exactNonNegativeLong(stated, "sessionId");
            if (optionalInteger(stated, "schemaVersion", -1) != 1
                    || !KIND.equals(optionalString(stated, "kind"))
                    || !AUTHORITY.equals(optionalString(stated, "authority"))
                    || session == 0L && !keys.isEmpty()) {
                throw new IllegalArgumentException(
                        "unsupported VM expression table schema");
            }
            if (optionalInteger(stated, "definitionCount", -1)
                    != keys.size()) {
                throw new IllegalArgumentException("the VM expression table"
                        + " states another count than the rows it holds");
            }
            for (RawKey key : keys) {
                if (key.session != session) {
                    throw new IllegalArgumentException(
                            "VM expression definition disagrees with table");
                }
                supplied.add(key);
            }
        }

        /** The key of the row at {@code row} when its ids read as the VM
         *  spells them and this store has expanded that node; else null. */
        private RawKey heldRow(String page, int row) {
            if (!page.startsWith(ROW, row)) return null;
            int at = row + ROW.length();
            int sessionEnd = digits(page, at);
            if (sessionEnd < 0 || !page.startsWith(ROW_ID, sessionEnd)) {
                return null;
            }
            int idEnd = digits(page, sessionEnd + ROW_ID.length());
            if (idEnd < 0 || !page.startsWith(ROW_EXPRESSION, idEnd)) {
                return null;
            }
            RawKey key = new RawKey(
                    Long.parseLong(page.substring(at, sessionEnd)),
                    Long.parseLong(page.substring(
                            sessionEnd + ROW_ID.length(), idEnd)));
            return key.session > 0L && key.expression > 0L && expanded(key)
                    ? key : null;
        }

        /** The end of the run of 1-18 decimal digits at {@code at}, or -1. */
        private static int digits(String text, int at) {
            int end = at;
            while (end < text.length() && end - at < 19
                    && Character.isDigit(text.charAt(end))) {
                end++;
            }
            return end == at || end - at > 18 ? -1 : end;
        }

        /** One row's text parsed whole: it must be exactly one row. */
        private RawKey readDefinition(String row,
                                      Map<RawKey, JsonObject> table)
                throws IOException {
            JsonReader reader = new JsonReader(new StringReader(row));
            RawKey key = readDefinition(reader, table);
            boolean one;
            try {
                one = reader.peek() == JsonToken.END_DOCUMENT;
            } catch (IOException more) {
                one = false;
            }
            if (!one) {
                throw new IllegalArgumentException(
                        "a VM expression row holds more than one row");
            }
            return key;
        }

        /** One table row: its key, its definition kept in {@code table}
         *  unless the node is expanded already.  Its members are read as
         *  tokens: a row of an expanded node builds nothing. */
        private RawKey readDefinition(JsonReader reader,
                                      Map<RawKey, JsonObject> table)
                throws IOException {
            if (reader.peek() != JsonToken.BEGIN_OBJECT) {
                throw new IllegalArgumentException(
                        "VM expression definition must be an object");
            }
            String type = null;
            long session = -1L;
            long id = -1L;
            JsonElement expression = null;
            boolean known = false;
            reader.beginObject();
            while (reader.hasNext()) {
                String name = reader.nextName();
                if ("_type".equals(name)
                        && reader.peek() == JsonToken.STRING) {
                    type = reader.nextString();
                } else if ("sessionId".equals(name)
                        && reader.peek() == JsonToken.NUMBER) {
                    session = reader.nextLong();
                } else if ("expressionId".equals(name)
                        && reader.peek() == JsonToken.NUMBER) {
                    id = reader.nextLong();
                } else if (!"expression".equals(name)) {
                    reader.skipValue();
                } else if (DEFINITION_TYPE.equals(type) && session > 0L
                        && id > 0L && expanded(new RawKey(session, id))) {
                    reader.skipValue();
                    known = true;
                } else {
                    expression = JsonParser.parseReader(reader);
                }
            }
            reader.endObject();
            if (!DEFINITION_TYPE.equals(type)) {
                throw new IllegalArgumentException(
                        "VM expression row has wrong type");
            }
            if (session <= 0L || id <= 0L) {
                throw new IllegalArgumentException(
                        "VM expression row needs a positive session and id");
            }
            RawKey key = new RawKey(session, id);
            if (known) return key;
            if (expression == null || !expression.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM expression definition disagrees with table");
            }
            JsonObject definition = expression.getAsJsonObject();
            Integer hash = fingerprint(definition);
            Integer before = defined.putIfAbsent(key, hash);
            JsonObject here = table.putIfAbsent(key, definition);
            if (before != null && !before.equals(hash)
                    || here != null && !here.equals(definition)) {
                throw new IllegalArgumentException(
                        "conflicting VM expression definition: " + key);
            }
            return key;
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
        private synchronized JsonObject importEnvelope(JsonObject artifact) {
            Set<RawKey> supplied = new LinkedHashSet<>();
            definitions = new HashMap<>();
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
                definitions = Collections.emptyMap();
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
