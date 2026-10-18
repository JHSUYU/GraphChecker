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
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executor;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntConsumer;
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
    /** A table holding the closure of what its envelope names. */
    public static final String AUTHORITY = "VM_SESSION_EXPRESSION_ID_V1";
    /**
     * A read-out page's table: the definitions its closure needs that no
     * earlier table of the session's read-out channel stated, and its
     * {@code sequence} there (VM {@code VmExpressionChannel}).
     */
    public static final String READ_OUT_AUTHORITY =
            "VM_READ_OUT_EXPRESSION_DELTA_V1";
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
     * Decodes a session's VM envelopes, each VM node one object however many
     * envelopes name it.  Shared by the threads that decode into it (a
     * region's owner, its branch windows; the read-out's decoding threads,
     * its pages), with no lock: a walk keeps its state to itself and of two
     * walks expanding one node the first wins ({@link
     * SharedExpressionTable.Expansion}).  Locked while a whole read-out page
     * was filed, it stalled the owner's every branch window behind the
     * publication thread (A2's SB19 seed replay: the Overseer BLOCKED in
     * {@code PathConditionWindow}); locked while a node expanded, it kept a
     * page's records from decoding in parallel.
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
         * One self-contained VM envelope of records -- a JSON object holding
         * one array of records ({@code records}, each self-contained but for
         * the nodes it references) beside the envelope's one expression
         * table, the closure of what its records name, as a branch's
         * path-condition window is -- never parsed whole, never copied
         * whole.  Its top level is read off the text once: the members but
         * the records parsed as the header, each record's extent found by
         * its brackets, up to the table, the last member.  The table's rows
         * are read off the text, a row of a node this store has expanded
         * already skipped by its id, unscanned (its expansion answers for
         * it: a window repeats the closure of its condition), the rest
         * parsed, checked closed and kept; {@code admit} is asked of the
         * header with the record count stated as {@link #RECORD_COUNT}.
         * Admitted, each record is then parsed, expanded against the table
         * and handed to {@code each} in order, one at a time; a definition is
         * let go once expanded, and the rest when the envelope ends.  An
         * envelope with no table is a plain one read the same way.
         *
         * @return the header, with the count
         */
        public JsonObject importRecords(String page, String records,
                                        Predicate<JsonObject> admit,
                                        Consumer<JsonElement> each) {
            return rawResolver.importRecords(page, records, admit, each);
        }

        /**
         * One page of a session's read-out ({@code SHARED_TRACKED_LOCATIONS},
         * read the way {@link #importRecords} reads an envelope) whose table
         * is its read-out channel's next ({@link #READ_OUT_AUTHORITY}): the
         * definitions no earlier page stated, numbered {@code sequence}.  The
         * table is imported first, whatever happens to the records -- a page
         * {@code admit} refuses, a page whose records stop half-way -- since
         * a later page's records may name a node only this table defines; so
         * every page must come here, in the order the VM numbered the
         * tables (an older table after a newer one is refused).  A node the
         * channel defined stays in the store until a record expands it.
         *
         * <p>Admitted, each record is decoded by {@code decode} and its
         * decoding handed to {@code each}, in page order, once per text: a
         * record whose text this store has decoded before (a location a
         * read-out states again unchanged) is neither parsed, expanded nor
         * decoded again, and {@code each} takes the decoding it had.  So
         * {@code decode} must be a function of the record's text and this
         * store alone.  The other records are decoded at once, on the
         * calling thread and up to {@code helping} parts on {@code helpers};
         * once every part has returned, the decodings go to {@code each} in
         * page order, up to the first record that failed, whose failure is
         * then thrown -- as one thread decoding them in order would.</p>
         *
         * @return the header, with the count
         */
        public <T> JsonObject importReadOutPage(
                String page, String records, Predicate<JsonObject> admit,
                Class<T> decoding, Function<JsonElement, T> decode,
                Consumer<? super T> each, Executor helpers, int helping) {
            return rawResolver.importReadOutPage(page, records, admit,
                    repeats(decoding), decode, each, helpers, helping);
        }

        /**
         * Whether a node this store expanded, or a read-out record it read,
         * may hold the VM serializer's truncation marker ({@code
         * TruncatedExpression}): a definition holding one, or a record whose
         * text names it, was imported this session.  Until then no
         * expansion holds one, and a record needs no scan for it.
         */
        public boolean truncationMarked() {
            return rawResolver.marked;
        }

        public void readOutLost(String what) {
            rawResolver.lost(what);
        }

        public String readOutLosses() {
            return rawResolver.losses();
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
     * One session's VM nodes, each expanded once and kept (Expansion).  What
     * it keeps grows with every node the run makes, so it keeps no more: a
     * node's definition only until it is expanded -- a self-contained
     * envelope's while it imports (it states the closure of every node it
     * names), one the read-out channel sent until a record names it -- then
     * its hash, and one instance of each member name and string value -- VM
     * nodes repeat their sites' class, method, descriptor and code-position
     * strings.  Kept whole, the definitions beside their expansions and every
     * string a copy, they held the 4 GB heap of a Solr seed replay full for
     * its last ten minutes (solr-adhoc SplitShardCmd-658: 265 thousand nodes,
     * 2.1 GB of strings, 1.1 GB of definition and expansion trees; jmap
     * -histo).
     */
    private static final class RawResolver
            extends SharedExpressionTable.Expansion<RawKey> {
        /** The definitions the read-out channel sent that no record has
         *  expanded yet ({@link #readChannelTable}). */
        private final Map<RawKey, JsonObject> pending =
                new ConcurrentHashMap<>();
        /** Per node ever defined, its definition's {@link #fingerprint}: an
         *  envelope that defines it again, unless the node was expanded
         *  already, defines it alike (to 32 bits). */
        private final Map<RawKey, Integer> defined = new ConcurrentHashMap<>();
        private final Map<String, String> names = new ConcurrentHashMap<>();
        private final Map<String, JsonPrimitive> strings =
                new ConcurrentHashMap<>();
        private final Predicate<String> plumbing;
        /** {@link Store#truncationMarked}. */
        private volatile boolean marked;
        /** The read-out channel's session and the sequence of the last
         *  table imported from it; guarded by this. */
        private long readOutSession;
        private long readOutSequence;
        private final List<String> lost = new ArrayList<>();

        private RawResolver(Predicate<String> plumbing) {
            super("VM expression");
            this.plumbing = plumbing;
        }

        @Override
        RawKey reference(JsonObject object, boolean root) {
            return REFERENCE_TYPE.equals(optionalString(object, "_type"))
                    ? rawKey(object, REFERENCE_TYPE) : null;
        }

        /** The copy of a stated definition its expansion keeps, in this
         *  store's names and strings; null for none. */
        private JsonObject definition(JsonObject stated) {
            return stated == null ? null
                    : canonical(observedValue(stated)).getAsJsonObject();
        }

        /** A definition the read-out channel sent is let go once expanded:
         *  the expansion answers for its key from now on. */
        @Override
        void expandedNow(RawKey key) {
            pending.remove(key);
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

        /**
         * One self-contained envelope of records ({@link Store#importRecords}),
         * its top level read off the text once ({@link #topLevel}).  The
         * table is read, then the header with its count is admitted, then
         * the records are parsed, expanded and handed on in page order.
         */
        private JsonObject importRecords(String page, String records,
                                         Predicate<JsonObject> admit,
                                         Consumer<JsonElement> each) {
            Map<RawKey, JsonObject> table = new HashMap<>();
            Set<RawKey> supplied = new HashSet<>();
            JsonObject header = new JsonObject();
            List<int[]> extents = new ArrayList<>();
            int tabled = topLevel(page, records, header, extents, null, null);
            if (tabled >= 0) {
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
            for (int[] extent : extents) {
                JsonElement parsed = parse(page, extent[0], extent[1]);
                // Self-contained but for the envelope's table.
                references(parsed, key -> {
                    if (!supplied.contains(key)) {
                        throw new IllegalArgumentException(
                                "missing VM expression definition: " + key);
                    }
                });
                // A definition is let go once expanded: the expansion
                // answers for its key from now on.
                each.accept(expand(parsed,
                        key -> definition(table.remove(key))));
            }
            return header;
        }

        /**
         * One read-out page ({@link Store#importReadOutPage}): its top level
         * read off the text once, a record {@code repeats} holds found by its
         * whole text; the channel's table imported, whatever comes next; the
         * header admitted; then the records not held decoded at once by
         * {@link #inParallel} and every record's decoding handed on in page
         * order.
         */
        private <T> JsonObject importReadOutPage(
                String page, String records, Predicate<JsonObject> admit,
                Repeats<T> repeats, Function<JsonElement, T> decode,
                Consumer<? super T> each, Executor helpers, int helping) {
            int table = page.lastIndexOf(TABLE_KEY);
            if (table < 0) {
                lost("a page with no expression table");
                throw new IllegalArgumentException(
                        "a VM read-out page states no expression table");
            }
            readChannelTable(page, table, helpers, helping);
            JsonObject header = new JsonObject();
            List<int[]> extents = new ArrayList<>();
            List<Held<T>> held = new ArrayList<>();
            if (topLevel(page, records, header, extents, held, repeats) < 0) {
                throw new IllegalArgumentException(
                        "malformed VM read-out page");
            }
            header.addProperty(RECORD_COUNT, extents.size());
            if (!admit.test(header)) return header;
            int fresh = 0;
            for (Held<T> record : held) {
                if (record == null) fresh++;
            }
            int[] decoded = new int[fresh];
            for (int index = 0, next = 0; index < held.size(); index++) {
                if (held.get(index) == null) decoded[next++] = index;
            }
            Object[] results = new Object[extents.size()];
            Throwable[] failures = new Throwable[extents.size()];
            inParallel(decoded, index -> {
                int[] extent = extents.get(index);
                String text = page.substring(extent[0], extent[1]);
                // A marker in a record's own text (one in a definition is
                // found as the definition is copied, #canonical).
                if (!marked && text.contains(TRUNCATED_TYPE)) marked = true;
                T value = decode.apply(expand(JsonParser.parseString(text),
                        key -> definition(pending.get(key))));
                if (repeats != null) repeats.hold(text, value);
                results[index] = value;
            }, failures, helpers, helping);
            for (int index = 0; index < extents.size(); index++) {
                Held<T> record = held.get(index);
                if (record != null) {
                    each.accept(record.decoding);
                    continue;
                }
                if (failures[index] != null) throw rethrown(failures[index]);
                // Decoded above, by decode: a T.
                @SuppressWarnings("unchecked")
                T value = (T) results[index];
                each.accept(value);
            }
            return header;
        }

        /**
         * Runs {@code task} on each of {@code indices} at once: on the
         * calling thread and in up to {@code helping} parts on
         * {@code helpers}, each part taking the next index until none is
         * left or a part failed (each index's failure kept in
         * {@code failures}); returns once every part has returned, so every
         * index below a failed one was run or failed too.
         */
        private static void inParallel(int[] indices, IntConsumer task,
                                       Throwable[] failures, Executor helpers,
                                       int helping) {
            AtomicInteger next = new AtomicInteger();
            AtomicBoolean failed = new AtomicBoolean();
            Runnable part = () -> {
                for (int at; !failed.get()
                        && (at = next.getAndIncrement()) < indices.length; ) {
                    try {
                        task.accept(indices[at]);
                    } catch (Throwable failure) {
                        failures[indices[at]] = failure;
                        failed.set(true);
                    }
                }
            };
            int parts = helpers == null ? 0
                    : Math.max(0, Math.min(helping, indices.length - 1));
            CountDownLatch returned = new CountDownLatch(parts);
            for (int index = 0; index < parts; index++) {
                try {
                    helpers.execute(() -> {
                        try {
                            part.run();
                        } finally {
                            returned.countDown();
                        }
                    });
                } catch (RejectedExecutionException refused) {
                    returned.countDown();
                }
            }
            part.run();
            boolean interrupted = false;
            while (true) {
                try {
                    returned.await();
                    break;
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
            }
            if (interrupted) Thread.currentThread().interrupt();
        }

        /** A part's failure, thrown on the thread that hands the page on. */
        private static RuntimeException rethrown(Throwable failure) {
            if (failure instanceof RuntimeException) {
                return (RuntimeException) failure;
            }
            if (failure instanceof Error) throw (Error) failure;
            return new IllegalStateException(failure);
        }

        /**
         * An envelope's top level read off its text: each member before the
         * table but {@code records} parsed into {@code header}, each record's
         * extent into {@code extents} -- a record {@code repeats} holds by
         * its whole text (and what it holds into {@code held}), any other by
         * scanning it -- up to the table, the last member.
         *
         * @return where the table's member starts, or -1 when there is none
         */
        private static <T> int topLevel(String page, String records,
                                        JsonObject header,
                                        List<int[]> extents,
                                        List<Held<T>> held,
                                        Repeats<T> repeats) {
            int at = TopLevel.open(page);
            while (TopLevel.peek(page, at) != '}') {
                String name = TopLevel.name(page, at);
                int value = TopLevel.value(page, at);
                if (FIELD.equals(name)) return at;
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
                    if (held != null) held.add(record);
                    at = TopLevel.next(page, end, ']');
                }
                at = TopLevel.next(page, at + 1, '}');
            }
            return -1;
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
        /** The node type the VM serializer puts where it bounded a
         *  rendering (SerializationScope::append_truncation, a path
         *  condition's PathCondition::write_truncation_marker). */
        private static final String TRUNCATED_TYPE = "TruncatedExpression";

        /**
         * A self-contained envelope's expression table ({@link #AUTHORITY}),
         * read off its text ({@link #readRows}): each row's key into
         * {@code supplied}, and into {@code table} the definition of every
         * node this store has not expanded yet.
         */
        private void readTable(String page, int from, Set<RawKey> supplied,
                               Map<RawKey, JsonObject> table) {
            JsonObject stated = readRows(page, from, AUTHORITY, supplied,
                    table, null, 0, null);
            if (stated == null) {
                throw new IllegalArgumentException(
                        "unsupported VM expression table schema");
            }
        }

        /**
         * A read-out page's table ({@link #READ_OUT_AUTHORITY}): the
         * channel's next, numbered after the last one imported -- an older
         * one, or one of another session, is refused -- its rows held until
         * a record expands them.  Every row that reads is held, whatever
         * else of the table fails, and a node a row names is looked for only
         * when a record expands it.  A table never imported -- a gap in the
         * numbering, a table that failed, a page lost on its way ({@link
         * Store#readOutLost}) -- is remembered ({@link #losses}): a record
         * naming a node only it defined fails where it expands.
         */
        private synchronized void readChannelTable(String page, int from,
                                                   Executor helpers,
                                                   int helping) {
            long sequence = -1L;
            try {
                JsonObject stated = tableHeader(page, from);
                if (!channelTable(stated)) {
                    throw new IllegalArgumentException("a VM read-out page"
                            + " whose table is no table of the read-out"
                            + " channel (" + READ_OUT_AUTHORITY + "): an"
                            + " image whose read-out restates every"
                            + " definition?");
                }
                long session = exactNonNegativeLong(stated, "sessionId");
                long numbered = exactNonNegativeLong(stated, "sequence");
                if (readOutSession != 0L && session != readOutSession
                        || numbered <= readOutSequence) {
                    throw new IllegalStateException("VM read-out table "
                            + numbered + " of session " + session
                            + " after table " + readOutSequence
                            + " of session " + readOutSession);
                }
                sequence = numbered;
                if (sequence > readOutSequence + 1L) {
                    lost("table(s) " + (readOutSequence + 1L)
                            + (sequence > readOutSequence + 2L
                            ? "-" + (sequence - 1L) : "")
                            + " never reached the decoder");
                }
                readOutSession = session;
                readOutSequence = sequence;
            } catch (IllegalStateException older) {
                throw new IllegalArgumentException(older.getMessage());
            } catch (RuntimeException | Error unread) {
                lost("a table: " + unread);
                throw unread;
            }
            Map<RawKey, JsonObject> table = new HashMap<>();
            List<Throwable> failed = new ArrayList<>();
            try {
                readRows(page, from, READ_OUT_AUTHORITY, new HashSet<RawKey>(),
                        table, helpers, helping, failed);
            } catch (RuntimeException | Error unread) {
                failed.add(unread);
            }
            for (Map.Entry<RawKey, JsonObject> row : table.entrySet()) {
                if (!expanded(row.getKey())) {
                    pending.putIfAbsent(row.getKey(), row.getValue());
                }
            }
            if (!failed.isEmpty()) {
                lost("table " + sequence + ": " + failed.get(0));
                throw rethrown(failed.get(0));
            }
        }

        private synchronized void lost(String what) {
            lost.add(what);
        }

        private synchronized String losses() {
            int shown = Math.min(lost.size(), 4);
            return lost.isEmpty() ? "" : String.join("; ",
                    lost.subList(0, shown)) + (lost.size() > shown
                    ? "; and " + (lost.size() - shown) + " more" : "");
        }

        private static boolean channelTable(JsonObject stated) {
            return optionalInteger(stated, "schemaVersion", -1) == 1
                    && KIND.equals(optionalString(stated, "kind"))
                    && READ_OUT_AUTHORITY.equals(optionalString(stated,
                    "authority"));
        }

        private static JsonObject tableHeader(String page, int from) {
            int start = page.indexOf(TABLE_KEY, from);
            int rows = start < 0 ? -1 : page.indexOf(ROWS_KEY, start);
            if (rows < 0 || !page.startsWith(TABLE_END,
                    page.length() - TABLE_END.length())) {
                throw new IllegalArgumentException(
                        "VM expression table must close its envelope");
            }
            return JsonParser.parseString(page.substring(
                    start + TABLE_KEY.length() - 1, rows) + "}")
                    .getAsJsonObject();
        }

        /**
         * One expression table read off its envelope's text: each row's key
         * into {@code supplied}, and into {@code table} the definition of
         * every node this store has not expanded yet, checked against what
         * an earlier envelope defined it as.  A row of a node the store has
         * expanded is skipped by its id, unparsed: a row ends where the next
         * one starts, so its definition is never scanned as JSON
         * (hdfs-adhoc-03's read-out pages were 20 MB of rows the store held,
         * 18 s each to scan).  Fail closed: a row whose id does not read as
         * the VM spells it is parsed whole, and the table must close the
         * envelope, state its schema, its own session on every row, and its
         * row count.  It is looked for from {@code from}, where the
         * envelope's members end.  The rows are parsed at once, on the
         * calling thread and up to {@code helping} parts on {@code helpers}
         * ({@link #inParallel}), then checked and kept in table order.  With
         * {@code failed}, a row that fails is skipped and its failure, as
         * the table's own, goes there: every row that reads is kept.
         *
         * @return the table's members but its rows, or null when it states
         *         another schema, kind or authority than {@code authority}
         */
        private JsonObject readRows(String page, int from, String authority,
                                    Set<RawKey> supplied,
                                    Map<RawKey, JsonObject> table,
                                    Executor helpers, int helping,
                                    List<Throwable> failed) {
            JsonObject stated = tableHeader(page, from);
            int rows = page.indexOf(ROWS_KEY, page.indexOf(TABLE_KEY, from));
            int end = page.length() - TABLE_END.length();
            if (optionalInteger(stated, "schemaVersion", -1) != 1
                    || !KIND.equals(optionalString(stated, "kind"))
                    || !authority.equals(optionalString(stated,
                    "authority"))) {
                return null;
            }
            List<int[]> spans = new ArrayList<>();
            for (int row = rows + ROWS_KEY.length(); row < end; ) {
                if (!spans.isEmpty() && page.charAt(row++) != ',') {
                    throw new IllegalArgumentException(
                            "VM expression rows must be separated");
                }
                int next = page.indexOf("," + ROW, row);
                int stop = next < 0 || next > end ? end : next;
                spans.add(new int[] {row, stop});
                row = stop;
            }
            int count = spans.size();
            RawKey[] keys = new RawKey[count];
            JsonObject[] definitions = new JsonObject[count];
            int[] hashes = new int[count];
            Throwable[] failures = new Throwable[count];
            int[] every = new int[count];
            for (int index = 0; index < count; index++) every[index] = index;
            inParallel(every, index -> {
                try {
                    int[] span = spans.get(index);
                    RawKey held = heldRow(page, span[0]);
                    if (held != null) {
                        keys[index] = held;
                        return;
                    }
                    JsonObject[] definition = new JsonObject[1];
                    try {
                        keys[index] = readDefinition(
                                page.substring(span[0], span[1]), definition);
                    } catch (IOException malformed) {
                        throw new IllegalArgumentException(
                                "malformed VM read-out page", malformed);
                    }
                    if (definition[0] != null) {
                        definitions[index] = definition[0];
                        hashes[index] = fingerprint(definition[0]);
                    }
                } catch (RuntimeException | Error unread) {
                    if (failed == null) throw unread;
                    failures[index] = unread;
                }
            }, failures, helpers, helping);
            long session = exactNonNegativeLong(stated, "sessionId");
            List<Throwable> faults = new ArrayList<>();
            for (int index = 0; index < count; index++) {
                if (failures[index] != null) {
                    if (failed == null) throw rethrown(failures[index]);
                    faults.add(failures[index]);
                } else if (keys[index].session != session) {
                    faults.add(new IllegalArgumentException(
                            "VM expression definition disagrees with table"));
                } else if (definitions[index] != null
                        && !remember(keys[index], definitions[index],
                        hashes[index], table) && failed == null) {
                    throw new IllegalArgumentException(
                            "conflicting VM expression definition: "
                                    + keys[index]);
                }
                if (failures[index] == null) supplied.add(keys[index]);
            }
            if (session == 0L && count > 0) {
                faults.add(new IllegalArgumentException(
                        "unsupported VM expression table schema"));
            }
            if (optionalInteger(stated, "definitionCount", -1) != count) {
                faults.add(new IllegalArgumentException("the VM expression"
                        + " table states another count than the rows it"
                        + " holds"));
            }
            if (!faults.isEmpty()) {
                if (failed == null) throw rethrown(faults.get(0));
                failed.addAll(faults);
            }
            return stated;
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
        private RawKey readDefinition(String row, JsonObject[] definition)
                throws IOException {
            JsonReader reader = new JsonReader(new StringReader(row));
            RawKey key = readDefinition(reader, definition);
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

        /** One table row: its key, and its definition into
         *  {@code definition[0]} unless the node is expanded already.  Its
         *  members are read as tokens: a row of an expanded node builds
         *  nothing. */
        private RawKey readDefinition(JsonReader reader,
                                      JsonObject[] definition)
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
            definition[0] = expression.getAsJsonObject();
            return key;
        }

        /** One stated definition, of {@link #fingerprint} {@code hash},
         *  into {@code table}; false when this store or the table defined
         *  the node otherwise before. */
        private boolean remember(RawKey key, JsonObject definition, int hash,
                                 Map<RawKey, JsonObject> table) {
            Integer before = defined.putIfAbsent(key, hash);
            JsonObject here = table.putIfAbsent(key, definition);
            return !(before != null && before != hash
                    || here != null && !here.equals(definition));
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
            Map<RawKey, JsonObject> definitions = new HashMap<>();
            collectTables(artifact, supplied, definitions);
            validateDefinitions(artifact, supplied, definitions);
            JsonElement expandedArtifact = expand(artifact,
                    key -> definition(definitions.get(key)));
            if (!expandedArtifact.isJsonObject()) {
                throw new IllegalArgumentException(
                        "VM artifact root must be object");
            }
            return expandedArtifact.getAsJsonObject();
        }

        /**
         * A copy of a definition with this store's one instance of each
         * member name and string value (definitions are shallow: a child
         * node is a reference).  A definition holding the VM serializer's
         * truncation marker marks the store ({@link Store#truncationMarked}):
         * every record naming the node may hold it from now on.
         */
        private JsonElement canonical(JsonElement value) {
            if (value.isJsonObject()) {
                JsonObject copy = new JsonObject();
                for (Map.Entry<String, JsonElement> member
                        : value.getAsJsonObject().entrySet()) {
                    JsonElement item = member.getValue();
                    if ("_type".equals(member.getKey())
                            && item.isJsonPrimitive()
                            && TRUNCATED_TYPE.equals(item.getAsString())) {
                        marked = true;
                    }
                    copy.add(names.computeIfAbsent(member.getKey(),
                            name -> name), canonical(item));
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
        private static void validateDefinitions(
                JsonElement artifact, Set<RawKey> supplied,
                Map<RawKey, JsonObject> definitions) {
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

        private void collectTables(JsonElement value, Set<RawKey> supplied,
                                   Map<RawKey, JsonObject> definitions) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) return;
            if (value.isJsonArray()) {
                for (JsonElement child : value.getAsJsonArray()) {
                    collectTables(child, supplied, definitions);
                }
                return;
            }
            JsonObject row = value.getAsJsonObject();
            JsonElement table = row.get(FIELD);
            if (table != null) importTable(table, supplied, definitions);
            for (Map.Entry<String, JsonElement> field : row.entrySet()) {
                if (!FIELD.equals(field.getKey())) {
                    collectTables(field.getValue(), supplied, definitions);
                }
            }
        }

        private void importTable(JsonElement encoded, Set<RawKey> supplied,
                                 Map<RawKey, JsonObject> definitions) {
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
                supplied.add(key);
                JsonElement expression = row.get("expression");
                if (key.session != session || expression == null
                        || !expression.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "VM expression definition disagrees with table");
                }
                JsonObject definition = expression.getAsJsonObject();
                if (!remember(key, definition, fingerprint(definition),
                        definitions)) {
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
