package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonParser;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;
import com.google.gson.stream.JsonWriter;

import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.StringReader;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * EMIT's gap ledger (PIPELINE §11): every gap this campaign raised, in one
 * document, {@code final/gaps.json}, each row classed by the row itself.
 *
 * <pre>
 *   --iteration &lt;dir&gt;     every gaps.jsonl.gz (a session's, a round's) and
 *                          gaps.jsonl (a worker's) under it, and its own
 *                          campaign_gaps.jsonl
 *   --composition &lt;file&gt;  the composition manifest: its refusals, its gaps
 *                          and its claim's gaps
 *   --static &lt;file&gt;       the static catalog's communication_gaps.jsonl.gz
 *   --plan &lt;file&gt;         the runtime region plan, whose first row (the
 *                          catalog's) states the planning gaps
 *   --provenance &lt;json&gt;   the campaign's provenance
 *   --out &lt;file&gt;          the ledger, final/gaps.json
 *   --read &lt;file&gt;         what EMIT itself reads of it ({@link #readByEmit}):
 *                          the same document with every BLOCKING row and the
 *                          counts, of the DIAGNOSTIC rows those EMIT selects,
 *                          and the ledger's own bytes and sha256 as written
 *                          ({@code published})
 * </pre>
 *
 * <p>A GapRow states its own kind and class (CONTRACT-SPEC §2.5): the stage
 * that raised it knows what it could not do, and no later stage is in a
 * position to overrule that.  So this is a partition, not a classification:
 * a row that states no class is BLOCKING.  This main and the {@code accepted}
 * conjunction it feeds ({@code run_engine.sh campaign_emit}) are the ONE
 * reader of a gap's class in the campaign; classReason says which of the two
 * rules answered.</p>
 *
 * <p>The ledger holds one row per distinct (stage, source, code, subject,
 * detail), the first raised kept, in {@link Row#compare}'s order; the BLOCKING rows as {@code gaps}, the DIAGNOSTIC
 * as {@code telemetryGaps}, their counts, and the BLOCKING rows by stage and
 * by code.  That jq read each gap file in a jq of its own and slurped the
 * rows whole (SGF8-adhoc-07: 1047 files, 3.2 M rows, 5.6 GB of text: 520 s
 * and a 10 GB jq), and each later reader of EMIT parsed the 3.8 GB document
 * again (~50 s each, five of them); here the files are read side by side,
 * once, their texts held as the UTF-8 bytes they are, and EMIT reads
 * {@code --read}.</p>
 */
public final class GapLedgerMain {
    private static final Gson GSON = new GsonBuilder().serializeNulls()
            .disableHtmlEscaping().create();
    /** A worker's own gap rows (ObligationSolverMain), plain. */
    static final String WORKER_GAPS = "gaps.jsonl";
    /** A session's and a round's gap rows (SessionDir, ExploreMain). */
    static final String GAPS = SessionDir.GAPS;
    /** The campaign's own gap rows, appended by whoever raises them. */
    static final String CAMPAIGN_GAPS = "campaign_gaps.jsonl";

    /** A session's rows: {@code *}{@code /sessions/*}{@code /gaps.jsonl.gz},
     *  a withdrawn exposing session's under {@code before-*}{@code
     *  /sessions/} included. */
    private static final Pattern REPLAY_FILE =
            Pattern.compile(".*/sessions/.*/gaps\\.jsonl\\.gz", Pattern.DOTALL);
    /** A worker's or a round's: anything under {@code obligations-*}{@code
     *  /}, a session withdrawn to {@code timed-out-sessions/} or {@code
     *  refused-sessions/} included. */
    private static final Pattern EXPLORE_FILE = Pattern.compile(
            ".*/obligations-.*/gaps\\.jsonl(\\.gz)?", Pattern.DOTALL);
    /** The rows {@code campaign_emit} counts for {@code undeclaredHookCount}. */
    private static final Text HOOK_UNDECLARED = Text.of("HOOK_UNDECLARED");

    private static final String STATED = "the row states its own class";
    private static final String UNSTATED =
            "no stated class: blocking by default";
    private static final String REFUSAL =
            "a composition refusal withholds its own claim";

    /** The fields a gap file's row is read for, by these indices. */
    private static final List<String> ROW_FIELDS = Arrays.asList(
            "stage", "sessionId", "kind", "subject", "detail", "cls");
    private static final int STAGE = 0;
    private static final int SESSION = 1;
    private static final int KIND = 2;
    private static final int SUBJECT = 3;
    private static final int DETAIL = 4;
    private static final int CLS = 5;

    private GapLedgerMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        long started = System.nanoTime();
        String provenance = options.value("provenance", null);
        if (provenance == null) {
            throw new IllegalArgumentException("Missing --provenance");
        }
        JsonElement stated = JsonParser.parseString(provenance);
        // A head step, one JVM on its host after the case's last replay.
        Parallel.width(Parallel.HOST_CORES);
        Ledger ledger = read(required(options, "iteration"),
                required(options, "composition"),
                required(options, "static"), required(options, "plan"));
        long read = System.nanoTime();
        Written whole = ledger.write(required(options, "out"), stated,
                true, null);
        long wrote = System.nanoTime();
        Path view = options.path("read");
        if (view != null) ledger.write(view, stated, false, whole);
        System.err.printf("[gaps] %d file(s), %d row(s), %d distinct: %d"
                        + " BLOCKING, %d DIAGNOSTIC; read in %d ms, %d"
                        + " bytes written in %d ms%n",
                ledger.files, ledger.raised, ledger.rows.size(),
                ledger.blocking.size(), ledger.diagnostic.size(),
                (read - started) / 1_000_000L, whole.bytes,
                (wrote - read) / 1_000_000L);
    }

    private static Path required(LongOptions options, String name) {
        Path path = options.path(name);
        if (path == null) {
            throw new IllegalArgumentException("Missing --" + name);
        }
        return path;
    }

    /** Every gap of the campaign, read once: the gap files under {@code
     *  iteration} side by side, then the composer's and the plan's. */
    static Ledger read(Path iteration, Path composition, Path statics,
                       Path plan) throws IOException {
        Strings strings = new Strings();
        List<Path> files = gapFiles(iteration);
        for (Path file : files) stageOf(file);
        List<List<Row>> raised = new ArrayList<List<Row>>(Parallel.map(files,
                file -> stageRows(file, stageOf(file), strings),
                Parallel.directoriesAtOnce()));
        Path campaign = iteration.resolve(CAMPAIGN_GAPS);
        if (Files.isRegularFile(campaign) && Files.size(campaign) > 0) {
            raised.add(stageRows(campaign, "IMPORT", strings));
        }
        raised.add(composeRows(composition, strings));
        List<Row> declared = new ArrayList<Row>();
        for (JsonElement row : jsonl(statics)) {
            declared.add(declaredRow(row, strings));
        }
        for (JsonElement row : planGaps(plan)) {
            declared.add(declaredRow(row, strings));
        }
        raised.add(declared);
        return new Ledger(files.size(), raised);
    }

    /**
     * The gap files under {@code iteration}, in the order of their paths'
     * bytes ({@code find -type f | LC_ALL=C sort}).
     */
    static List<Path> gapFiles(Path iteration) throws IOException {
        try (Stream<Path> walk = Files.walk(iteration)) {
            List<Path> files = walk.filter(path -> {
                String name = path.getFileName().toString();
                return (name.equals(GAPS) || name.equals(WORKER_GAPS))
                        && Files.isRegularFile(path,
                        LinkOption.NOFOLLOW_LINKS);
            }).collect(Collectors.toList());
            files.sort(Comparator.comparing(Path::toString));
            return files;
        }
    }

    /** The stage a gap file's rows were raised at, by where it lies. */
    static String stageOf(Path file) throws IOException {
        String path = file.toString();
        if (REPLAY_FILE.matcher(path).matches()) return "REPLAY";
        if (EXPLORE_FILE.matcher(path).matches()) return "EXPLORE";
        throw new IOException("a gaps file at a path no stage of this"
                + " campaign writes: " + path);
    }

    /** A gap file's rows: each at the stage it states, else {@code
     *  stage}; its source the session that raised it, else RUNTIME. */
    static List<Row> stageRows(Path file, String stage, Strings strings)
            throws IOException {
        List<Row> rows = new ArrayList<Row>();
        Object fileStage = strings.of(stage);
        Object runtime = strings.of("RUNTIME");
        Object admission = strings.of("ADMISSION_GAP");
        Object empty = strings.of("");
        Object[] fields = new Object[ROW_FIELDS.size()];
        try (BufferedReader reader = text(file)) {
            String line;
            int number = 0;
            while ((line = reader.readLine()) != null) {
                number++;
                if (line.trim().isEmpty()) continue;
                read(line, file, number, fields, strings);
                Object session = fields[SESSION];
                rows.add(new Row(
                        fields[STAGE] == null ? fileStage : fields[STAGE],
                        session == null || empty.equals(session) ? runtime
                                : session,
                        fields[KIND] == null ? admission : fields[KIND],
                        fields[SUBJECT] == null ? empty : fields[SUBJECT],
                        fields[DETAIL] == null ? empty : fields[DETAIL],
                        Strings.DIAGNOSTIC.equals(fields[CLS]), STATED));
            }
        }
        return rows;
    }

    /**
     * {@link #ROW_FIELDS} of one row, each {@code .field // null}: null
     * where absent, null or false, a {@link Text} for a string, else its
     * element.  Every other field is skipped unread; a null row is all
     * absent, as jq takes it.
     */
    private static void read(String line, Path file, int number,
                             Object[] fields, Strings strings)
            throws IOException {
        Arrays.fill(fields, null);
        try {
            JsonReader reader = new JsonReader(new StringReader(line));
            reader.setLenient(true);
            JsonToken token = reader.peek();
            if (token == JsonToken.NULL) {
                reader.nextNull();
            } else if (token != JsonToken.BEGIN_OBJECT) {
                throw new IllegalArgumentException("not an object");
            } else {
                reader.beginObject();
                while (reader.hasNext()) {
                    int at = ROW_FIELDS.indexOf(reader.nextName());
                    if (at < 0) {
                        reader.skipValue();
                    } else if (reader.peek() == JsonToken.STRING) {
                        fields[at] = strings.text(reader.nextString());
                    } else {
                        JsonElement value = Jq.or(
                                JsonParser.parseReader(reader), null);
                        fields[at] = value == null ? null
                                : strings.value(value);
                    }
                }
                reader.endObject();
            }
            if (reader.peek() != JsonToken.END_DOCUMENT) {
                throw new IllegalArgumentException("more than one value");
            }
        } catch (IOException | RuntimeException malformed) {
            throw new IOException("malformed gap row " + file + ":" + number
                    + ": " + malformed.getMessage(), malformed);
        }
    }

    /**
     * The composer's rows: its refusals, each BLOCKING by construction, and
     * its own gap rows and its claim's, each as it states its class (none
     * stated: BLOCKING, which is what an unregistered code means).
     */
    static List<Row> composeRows(Path composition, Strings strings)
            throws IOException {
        JsonElement composed;
        try (JsonReader reader = new JsonReader(new InputStreamReader(
                ArtifactIO.input(composition), StandardCharsets.UTF_8))) {
            composed = JsonParser.parseReader(reader);
        }
        List<Row> rows = new ArrayList<Row>();
        Object stage = strings.of("COMPOSE");
        Object source = strings.of("ComposeMain");
        for (JsonElement refusal : Jq.array(Jq.or(
                Jq.field(composed, "finalStatusRefusals"), null))) {
            rows.add(new Row(stage, source,
                    strings.or(Jq.field(refusal, "kind"), "COMPOSITION_GAP"),
                    strings.or(Jq.field(refusal, "subject"), ""),
                    strings.or(Jq.field(refusal, "detail"), ""),
                    false, REFUSAL));
        }
        List<JsonElement> gaps = new ArrayList<JsonElement>(Jq.array(
                Jq.or(Jq.field(composed, "gaps"), null)));
        gaps.addAll(Jq.array(Jq.or(Jq.field(Jq.field(composed, "claim"),
                "gaps"), null)));
        for (JsonElement gap : gaps) {
            JsonElement kind = Jq.or(Jq.field(gap, "kind"),
                    Jq.field(gap, "reason"));
            rows.add(statedRow(stage, source, strings.or(kind, ""), gap,
                    strings.or(Jq.field(gap, "subject"), ""), strings));
        }
        return rows;
    }

    /** A static catalog's or the runtime plan's row, at PLAN. */
    static Row declaredRow(JsonElement row, Strings strings) {
        JsonElement subject = Jq.or(Jq.field(row, "subject"),
                Jq.field(row, "siteId"));
        return statedRow(strings.of("PLAN"),
                strings.or(Jq.field(row, "source"), "CATALOG"),
                strings.or(Jq.field(row, "kind"), ""), row,
                strings.or(subject, ""), strings);
    }

    /** A row whose class is the one it states, BLOCKING when none. */
    private static Row statedRow(Object stage, Object source, Object code,
                                 JsonElement row, Object subject,
                                 Strings strings) {
        JsonElement cls = Jq.or(Jq.field(row, "cls"), null);
        return new Row(stage, source, code, subject,
                strings.or(Jq.field(row, "detail"), ""),
                Jq.isString(cls, GapClass.DIAGNOSTIC.name()),
                cls == null || Jq.isString(cls, "") ? UNSTATED : STATED);
    }

    /** The planning gaps the runtime plan's first row, its catalog's,
     *  carries ({@code head -n 1 | jq '.gaps // []'}). */
    static List<JsonElement> planGaps(Path plan) throws IOException {
        String first;
        try (BufferedReader reader = text(plan)) {
            first = reader.readLine();
        }
        if (first == null || first.trim().isEmpty()) {
            return Collections.emptyList();
        }
        return Jq.array(Jq.or(Jq.field(parse(first, plan, 1), "gaps"), null));
    }

    /** Every JSON value of a JSONL file, a line each, blank lines skipped. */
    static List<JsonElement> jsonl(Path file) throws IOException {
        List<JsonElement> rows = new ArrayList<JsonElement>();
        try (BufferedReader reader = text(file)) {
            String line;
            int number = 0;
            while ((line = reader.readLine()) != null) {
                number++;
                if (line.trim().isEmpty()) continue;
                rows.add(parse(line, file, number));
            }
        }
        return rows;
    }

    private static BufferedReader text(Path file) throws IOException {
        return new BufferedReader(new InputStreamReader(
                ArtifactIO.input(file), StandardCharsets.UTF_8), 1 << 16);
    }

    private static JsonElement parse(String line, Path file, int number)
            throws IOException {
        try {
            return JsonParser.parseString(line);
        } catch (RuntimeException malformed) {
            throw new IOException("malformed gap row " + file + ":" + number,
                    malformed);
        }
    }

    /**
     * One gap row as published: the five fields that name it, its class
     * and why.  Two rows that name the same five are one, the first raised
     * kept.  A field is a {@link Text}, or the JSON element of a value that
     * is no string.
     */
    static final class Row {
        final Object stage;
        final Object source;
        final Object code;
        final Object subject;
        final Object detail;
        final boolean diagnostic;
        final String classReason;
        private final int hash;

        Row(Object stage, Object source, Object code, Object subject,
            Object detail, boolean diagnostic, String classReason) {
            this.stage = stage;
            this.source = source;
            this.code = code;
            this.subject = subject;
            this.detail = detail;
            this.diagnostic = diagnostic;
            this.classReason = classReason;
            int h = String.valueOf(stage).hashCode();
            h = 31 * h + String.valueOf(source).hashCode();
            h = 31 * h + String.valueOf(code).hashCode();
            h = 31 * h + String.valueOf(subject).hashCode();
            this.hash = 31 * h + String.valueOf(detail).hashCode();
        }

        /** The order of {@code [stage, source, code, subject, detail]}: a
         *  text before any other value, texts by their UTF-8 bytes, other
         *  values by their JSON text. */
        static int compare(Row one, Row other) {
            int order = order(one.stage, other.stage);
            if (order == 0) order = order(one.source, other.source);
            if (order == 0) order = order(one.code, other.code);
            if (order == 0) order = order(one.subject, other.subject);
            return order != 0 ? order : order(one.detail, other.detail);
        }

        private static int order(Object one, Object other) {
            boolean text = one instanceof Text;
            if (text != other instanceof Text) return text ? -1 : 1;
            if (text) return ((Text) one).compareTo((Text) other);
            return String.valueOf(one).compareTo(String.valueOf(other));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Row && hash == ((Row) other).hash
                    && compare(this, (Row) other) == 0;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** A document's size and digest, as it was written. */
    static final class Written {
        final long bytes;
        final String sha256;

        Written(long bytes, String sha256) {
            this.bytes = bytes;
            this.sha256 = sha256;
        }
    }

    /** The rows, distinct and in {@link Row#compare}'s order, split by
     *  class. */
    static final class Ledger {
        final int files;
        final long raised;
        final List<Row> rows;
        final List<Row> blocking = new ArrayList<Row>();
        final List<Row> diagnostic = new ArrayList<Row>();

        Ledger(int files, List<List<Row>> raised) {
            this.files = files;
            Set<Row> first = new HashSet<Row>();
            long count = 0;
            for (List<Row> part : raised) {
                count += part.size();
                first.addAll(part);
            }
            this.raised = count;
            Row[] sorted = first.toArray(new Row[0]);
            Arrays.parallelSort(sorted, Row::compare);
            this.rows = Arrays.asList(sorted);
            for (Row row : rows) {
                (row.diagnostic ? diagnostic : blocking).add(row);
            }
        }

        /**
         * The document, at {@code out} in one atomic write: the published
         * one in jq's pretty text, or (given what was {@code published})
         * what EMIT reads of it, compact: of the DIAGNOSTIC rows only those
         * {@link #readByEmit} names, and the published one's bytes and
         * sha256.
         */
        Written write(Path out, JsonElement provenance, boolean pretty,
                      Written published) throws IOException {
            List<Row> telemetry = diagnostic;
            if (published != null) {
                telemetry = new ArrayList<Row>();
                for (Row row : diagnostic) {
                    if (readByEmit(row)) telemetry.add(row);
                }
            }
            List<Row> selected = telemetry;
            Written[] written = {null};
            ArtifactIO.atomicWrite(out, file -> {
                Counted counted = new Counted(file);
                Writer text = new OutputStreamWriter(new BufferedOutputStream(
                        counted, 1 << 20), StandardCharsets.UTF_8);
                JsonWriter print = new JsonWriter(text);
                if (pretty) print.setIndent("  ");
                print.beginObject();
                print.name("schemaVersion").value(2);
                print.name("kind").value("CAMPAIGN_COVERAGE_GAPS");
                print.name("provenance");
                GSON.toJson(provenance, print);
                print.name("gaps");
                rows(print, blocking);
                print.name("telemetryGaps");
                rows(print, selected);
                print.name("gapCount").value(blocking.size());
                print.name("telemetryCount").value(diagnostic.size());
                print.name("byStage");
                counts(print, blocking, row -> row.stage);
                print.name("byCode");
                counts(print, blocking, row -> row.code);
                if (published != null) {
                    print.name("published").beginObject();
                    print.name("bytes").value(published.bytes);
                    print.name("sha256").value(published.sha256);
                    print.endObject();
                }
                print.endObject();
                text.write('\n');
                text.flush();
                written[0] = counted.written();
            });
            return written[0];
        }

        private static void rows(JsonWriter print, List<Row> rows)
                throws IOException {
            print.beginArray();
            for (Row row : rows) {
                print.beginObject();
                value(print.name("stage"), row.stage);
                value(print.name("source"), row.source);
                value(print.name("code"), row.code);
                value(print.name("subject"), row.subject);
                value(print.name("detail"), row.detail);
                print.name("class").value(row.diagnostic
                        ? GapClass.DIAGNOSTIC.name()
                        : GapClass.BLOCKING.name());
                print.name("classReason").value(row.classReason);
                print.endObject();
            }
            print.endArray();
        }

        private static void value(JsonWriter print, Object value)
                throws IOException {
            if (value instanceof Text) {
                print.value(value.toString());
            } else {
                GSON.toJson((JsonElement) value, print);
            }
        }

        /** A count per value of {@code key}, in {@link Text}'s order. */
        private static void counts(JsonWriter print, List<Row> rows,
                                   Function<Row, Object> key)
                throws IOException {
            Map<Text, Integer> counts = new TreeMap<Text, Integer>();
            for (Row row : rows) {
                Object name = key.apply(row);
                if (!(name instanceof Text)) {
                    throw new IllegalStateException("Cannot use "
                            + name + " as object key");
                }
                counts.merge((Text) name, 1, Integer::sum);
            }
            print.beginObject();
            for (Map.Entry<Text, Integer> count : counts.entrySet()) {
                print.name(count.getKey().toString()).value(count.getValue());
            }
            print.endObject();
        }
    }

    /**
     * Whether EMIT reads this DIAGNOSTIC row of the ledger: a hook no task
     * declared ({@code undeclaredHookCount}); a row whose subject names a
     * bound, {@code <name>=<count>} at the end of a line, or is no string
     * (one {@code campaign_bounds}' {@code test(" " + $bound + "=[0-9]+$")}
     * selects, or fails EMIT on, as it did over the whole ledger).  Every
     * BLOCKING row is read.  A reader of the DIAGNOSTIC rows added to EMIT
     * selects here too.
     */
    static boolean readByEmit(Row row) {
        if (HOOK_UNDECLARED.equals(row.code)) return true;
        if (!(row.subject instanceof Text)) return true;
        byte[] text = ((Text) row.subject).utf8;
        for (int end = 0; end <= text.length; end++) {
            if (end < text.length && text[end] != '\n') continue;
            int at = end - 1;
            while (at >= 0 && text[at] >= '0' && text[at] <= '9') at--;
            if (at == end - 1 || at < 0 || text[at] != '=') continue;
            int name = at - 1;
            while (name >= 0 && text[name] != ' ') name--;
            if (name >= 0 && name < at - 1) return true;
        }
        return false;
    }

    /**
     * One instance of each text the rows carry: the same subject and detail
     * recur in every session that raised them.
     */
    static final class Strings {
        static final Text DIAGNOSTIC = Text.of(GapClass.DIAGNOSTIC.name());
        private final Map<Text, Text> held =
                new ConcurrentHashMap<Text, Text>();

        Text of(String text) {
            Text one = Text.of(text);
            Text before = held.putIfAbsent(one, one);
            return before == null ? one : before;
        }

        Text text(String value) {
            return of(value);
        }

        /** A value as a row holds it: a {@link Text} for a string. */
        Object value(JsonElement element) {
            if (element.isJsonPrimitive()
                    && element.getAsJsonPrimitive().isString()) {
                return text(element.getAsString());
            }
            return element;
        }

        /** {@code element // fallback}. */
        Object or(JsonElement element, String fallback) {
            JsonElement stated = Jq.or(element, null);
            return stated == null ? of(fallback) : value(stated);
        }
    }

    /** A string as jq holds it: its UTF-8 bytes, ordered as bytes. */
    static final class Text implements Comparable<Text> {
        final byte[] utf8;
        private final int hash;

        private Text(byte[] utf8) {
            this.utf8 = utf8;
            this.hash = Arrays.hashCode(utf8);
        }

        static Text of(String text) {
            return new Text(text.getBytes(StandardCharsets.UTF_8));
        }

        @Override
        public int compareTo(Text other) {
            byte[] a = utf8;
            byte[] b = other.utf8;
            int length = Math.min(a.length, b.length);
            for (int at = 0; at < length; at++) {
                if (a[at] != b[at]) return (a[at] & 0xff) - (b[at] & 0xff);
            }
            return a.length - b.length;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Text && hash == ((Text) other).hash
                    && Arrays.equals(utf8, ((Text) other).utf8);
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public String toString() {
            return new String(utf8, StandardCharsets.UTF_8);
        }
    }

    /**
     * The bytes on their way to the file, counted, digested and written on
     * threads of their own, so the printing, the digest and the write run
     * side by side: SHA-256 takes this JVM 7.7 s a GB, about the write's own
     * time over NFS (109 MB/s from a lift; SGF8-adhoc-07's 3.8 GB: 29 and
     * 35 s), and EMIT's run manifest names the ledger by its digest.
     */
    private static final class Counted extends OutputStream {
        private static final byte[] END = new byte[0];
        private final MessageDigest digest = ArtifactIO.sha256Digest();
        private final BlockingQueue<byte[]> toDigest =
                new ArrayBlockingQueue<byte[]>(64);
        private final BlockingQueue<byte[]> toWrite =
                new ArrayBlockingQueue<byte[]>(64);
        private final Thread digesting;
        private final Thread writing;
        private volatile IOException failed;
        private long bytes;

        Counted(OutputStream file) {
            digesting = start("gaps-digest", toDigest, digest::update);
            writing = start("gaps-write", toWrite, chunk -> {
                if (failed != null) return;
                try {
                    file.write(chunk);
                } catch (IOException refused) {
                    failed = refused;
                }
            });
        }

        private static Thread start(String name, BlockingQueue<byte[]> chunks,
                                    Consumer<byte[]> take) {
            Thread thread = new Thread(() -> {
                try {
                    for (byte[] chunk = chunks.take(); chunk != END;
                         chunk = chunks.take()) {
                        take.accept(chunk);
                    }
                } catch (InterruptedException stopped) {
                    Thread.currentThread().interrupt();
                }
            }, name);
            thread.setDaemon(true);
            thread.start();
            return thread;
        }

        @Override
        public void write(int b) throws IOException {
            write(new byte[] {(byte) b}, 0, 1);
        }

        @Override
        public void write(byte[] b, int offset, int length)
                throws IOException {
            if (failed != null) throw failed;
            byte[] chunk = Arrays.copyOfRange(b, offset, offset + length);
            hand(toDigest, chunk);
            hand(toWrite, chunk);
            bytes += length;
        }

        /** What was written, once every byte is digested and written. */
        Written written() throws IOException {
            hand(toDigest, END);
            hand(toWrite, END);
            try {
                digesting.join();
                writing.join();
            } catch (InterruptedException stopped) {
                Thread.currentThread().interrupt();
                throw new IOException("interrupted", stopped);
            }
            if (failed != null) throw failed;
            return new Written(bytes, ArtifactIO.hex(digest.digest()));
        }

        private static void hand(BlockingQueue<byte[]> chunks, byte[] chunk)
                throws IOException {
            try {
                chunks.put(chunk);
            } catch (InterruptedException stopped) {
                Thread.currentThread().interrupt();
                throw new IOException("interrupted", stopped);
            }
        }
    }

    /** The ledger's reads of its inputs, as jq's {@code //} and {@code
     *  .name} read them. */
    static final class Jq {
        private Jq() {
        }

        /** {@code a // b}: {@code a} unless absent, null or false. */
        static JsonElement or(JsonElement a, JsonElement b) {
            if (a == null || a.isJsonNull()) return b;
            if (a.isJsonPrimitive() && a.getAsJsonPrimitive().isBoolean()
                    && !a.getAsBoolean()) {
                return b;
            }
            return a;
        }

        /** {@code .name}: absent on null, a failure on any non-object. */
        static JsonElement field(JsonElement value, String name) {
            if (value == null || value.isJsonNull()) return null;
            if (!value.isJsonObject()) {
                throw new IllegalArgumentException("Cannot index "
                        + value + " with \"" + name + "\"");
            }
            return value.getAsJsonObject().get(name);
        }

        /** {@code value // []} as an array; a failure on any other. */
        static List<JsonElement> array(JsonElement value) {
            if (value == null) return Collections.emptyList();
            if (!value.isJsonArray()) {
                throw new IllegalArgumentException("not an array: " + value);
            }
            List<JsonElement> items = new ArrayList<JsonElement>();
            for (JsonElement item : value.getAsJsonArray()) items.add(item);
            return items;
        }

        static boolean isString(JsonElement value, String text) {
            return value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()
                    && text.equals(value.getAsString());
        }
    }
}
