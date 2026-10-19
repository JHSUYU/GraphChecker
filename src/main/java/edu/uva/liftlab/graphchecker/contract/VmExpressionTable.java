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

public final class VmExpressionTable {
    public static final String FIELD = "vmExpressionTable";
    public static final String KIND = "VM_EXPRESSION_TABLE";
    public static final String AUTHORITY = "VM_SESSION_EXPRESSION_ID_V1";
    public static final String READ_OUT_AUTHORITY =
            "VM_READ_OUT_EXPRESSION_DELTA_V1";
    public static final String REFERENCE_TYPE = "VmExpressionReference";
    public static final String DEFINITION_TYPE = "VmExpressionDefinition";

    private VmExpressionTable() {
    }

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

    public static final class Store {
        private final SharedExpressionTable.Codec codec =
                new SharedExpressionTable.Codec();
        private final RawResolver rawResolver;

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

        public JsonObject importRecords(String page, String records,
                                        Predicate<JsonObject> admit,
                                        Consumer<JsonElement> each) {
            return rawResolver.importRecords(page, records, admit, each);
        }

        public <T> JsonObject importReadOutPage(
                String page, String records, Predicate<JsonObject> admit,
                Class<T> decoding, Function<JsonElement, T> decode,
                Consumer<? super T> each, Executor helpers, int helping) {
            return rawResolver.importReadOutPage(page, records, admit,
                    repeats(decoding), decode, each, helpers, helping);
        }

        public boolean truncationMarked() {
            return rawResolver.marked;
        }

        public void readOutLost(String what) {
            rawResolver.lost(what);
        }

        public String readOutLosses() {
            return rawResolver.losses();
        }

        private final Map<Class<?>, Repeats<?>> repeated = new HashMap<>();

        private <T> Repeats<T> repeats(Class<T> decoding) {
            synchronized (repeated) {
                Repeats<?> held = repeated.get(decoding);
                if (held == null) {
                    held = new Repeats<T>();
                    repeated.put(decoding, held);
                }
                @SuppressWarnings("unchecked")
                Repeats<T> typed = (Repeats<T>) held;
                return typed;
            }
        }

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

    private static final class Held<T> {
        private final String text;
        private final T decoding;

        private Held(String text, T decoding) {
            this.text = text;
            this.decoding = decoding;
        }
    }

    private static final class Repeats<T> {
        private final Map<String, SoftReference<Held<T>>> held =
                new HashMap<>();
        private long cleared;

        private static String key(String page, int start) {
            int end = page.indexOf('}', start);
            return end < 0 ? null : page.substring(start, end + 1);
        }

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

        private void hold(String text, T decoded) {
            String key = key(text, 0);
            if (key == null) return;
            synchronized (held) {
                held.put(key, new SoftReference<Held<T>>(
                        new Held<T>(text, decoded)));
            }
        }

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

    public static final String RECORD_COUNT = "__records";

    private static final class RawResolver
            extends SharedExpressionTable.Expansion<RawKey> {
        private final Map<RawKey, JsonObject> pending =
                new ConcurrentHashMap<>();
        private final Map<RawKey, Integer> defined = new ConcurrentHashMap<>();
        private final Map<String, String> names = new ConcurrentHashMap<>();
        private final Map<String, JsonPrimitive> strings =
                new ConcurrentHashMap<>();
        private final Predicate<String> plumbing;
        private volatile boolean marked;
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

        private JsonObject definition(JsonObject stated) {
            return stated == null ? null
                    : canonical(observedValue(stated)).getAsJsonObject();
        }

        @Override
        void expandedNow(RawKey key) {
            pending.remove(key);
        }

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

        private JsonObject importRecords(String page, String records,
                                         Predicate<JsonObject> admit,
                                         Consumer<JsonElement> each) {
            Map<RawKey, JsonObject> table = new HashMap<>();
            Set<RawKey> supplied = new HashSet<>();
            JsonObject header = new JsonObject();
            List<int[]> extents = new ArrayList<>();
            int tabled = topLevel(page, records, header, extents, null, null);
            if (tabled >= 0) {
                readTable(page, Math.max(0, tabled - 1), supplied, table);
            }
            header.addProperty(RECORD_COUNT, extents.size());
            SharedExpressionTable.Dag<RawKey> dag =
                    new SharedExpressionTable.Dag<>("VM expression",
                            key -> table.containsKey(key) ? table.get(key)
                                    : supplied.contains(key)
                                            && expanded(key) ? CLOSED : null,
                            RawResolver::references);
            for (RawKey key : table.keySet()) dag.require(key);
            if (!admit.test(header)) return header;
            for (int[] extent : extents) {
                JsonElement parsed = parse(page, extent[0], extent[1]);
                references(parsed, key -> {
                    if (!supplied.contains(key)) {
                        throw new IllegalArgumentException(
                                "missing VM expression definition: " + key);
                    }
                });
                each.accept(expand(parsed,
                        key -> definition(table.remove(key))));
            }
            return header;
        }

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
                @SuppressWarnings("unchecked")
                T value = (T) results[index];
                each.accept(value);
            }
            return header;
        }

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

        private static RuntimeException rethrown(Throwable failure) {
            if (failure instanceof RuntimeException) {
                return (RuntimeException) failure;
            }
            if (failure instanceof Error) throw (Error) failure;
            return new IllegalStateException(failure);
        }

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

        private static JsonElement parse(String page, int start, int end) {
            return JsonParser.parseString(page.substring(start, end));
        }

        private static final class TopLevel {
            private TopLevel() {
            }

            static int open(String page) {
                int at = space(page == null ? "" : page, 0);
                if (page == null || at >= page.length()
                        || page.charAt(at) != '{') {
                    throw new IllegalArgumentException(
                            "VM read-out page must be an object");
                }
                return space(page, at + 1);
            }

            static char peek(String page, int at) {
                if (at >= page.length()) throw malformed();
                return page.charAt(at);
            }

            static int space(String page, int at) {
                while (at < page.length()
                        && Character.isWhitespace(page.charAt(at))) {
                    at++;
                }
                return at;
            }

            static String name(String page, int at) {
                if (peek(page, at) != '"') throw malformed();
                int end = quote(page, at);
                String spelled = page.substring(at + 1, end);
                return spelled.indexOf('\\') < 0 ? spelled
                        : parse(page, at, end + 1).getAsString();
            }

            static int value(String page, int at) {
                int colon = space(page, quote(page, at) + 1);
                if (peek(page, colon) != ':') throw malformed();
                return space(page, colon + 1);
            }

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

            static int next(String page, int end, char closer) {
                int at = space(page, end);
                char c = peek(page, at);
                if (c == closer) return at;
                if (c != ',') throw malformed();
                return space(page, at + 1);
            }

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

        private static final JsonObject CLOSED = new JsonObject();

        private static final String TABLE_KEY = ",\"" + FIELD + "\":{";
        private static final String ROWS_KEY = ",\"definitions\":[";
        private static final String ROW = "{\"_type\":\"" + DEFINITION_TYPE
                + "\",\"sessionId\":";
        private static final String ROW_ID = ",\"expressionId\":";
        private static final String ROW_EXPRESSION = ",\"expression\":";
        private static final String TABLE_END = "]}}";
        private static final String TRUNCATED_TYPE = "TruncatedExpression";

        private void readTable(String page, int from, Set<RawKey> supplied,
                               Map<RawKey, JsonObject> table) {
            JsonObject stated = readRows(page, from, AUTHORITY, supplied,
                    table, null, 0, null);
            if (stated == null) {
                throw new IllegalArgumentException(
                        "unsupported VM expression table schema");
            }
        }

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

        private static int digits(String text, int at) {
            int end = at;
            while (end < text.length() && end - at < 19
                    && Character.isDigit(text.charAt(end))) {
                end++;
            }
            return end == at || end - at > 18 ? -1 : end;
        }

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
            return value.deepCopy();
        }

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

    static JsonObject emptyConjunction() {
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "EMPTY_CONJUNCTION");
        guard.addProperty("authority", "VM_UNGUARDED_WRITE_V1");
        return guard;
    }
}
