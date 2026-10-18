package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;

import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.StringReader;
import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
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
 * <p>The ledger is the document the shell's jq built before it (2026-10-18),
 * byte for byte, in jq 1.6's order and text ({@link Jq}): one row per
 * distinct (stage, source, code, subject, detail), the first raised kept, in
 * jq's order of those five; the BLOCKING rows as {@code gaps}, the DIAGNOSTIC
 * as {@code telemetryGaps}, their counts, and the BLOCKING rows by stage and
 * by code.  That jq read each gap file in a jq of its own and slurped the
 * rows whole (SGF8-adhoc-07: 1047 files, 3.2 M rows, 5.6 GB of text: 520 s
 * and a 10 GB jq), and each later reader of EMIT parsed the 3.8 GB document
 * again (~50 s each, five of them); here the files are read side by side,
 * once, their texts held as the UTF-8 bytes they are, and EMIT reads
 * {@code --read}.</p>
 */
public final class GapLedgerMain {
    /** A session's, a round's and a worker's gap rows (SessionDir,
     *  ExploreMain, ObligationSolverMain). */
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
                return name.equals(GAPS)
                        && Files.isRegularFile(path,
                        LinkOption.NOFOLLOW_LINKS);
            }).collect(Collectors.toList());
            files.sort(Comparator.comparing(Path::toString, Jq::compareText));
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
            int h = Jq.hash(stage);
            h = 31 * h + Jq.hash(source);
            h = 31 * h + Jq.hash(code);
            h = 31 * h + Jq.hash(subject);
            this.hash = 31 * h + Jq.hash(detail);
        }

        /** jq's order of {@code [.stage, .source, .code, .subject,
         *  .detail]}. */
        static int compare(Row one, Row other) {
            int order = Jq.compare(one.stage, other.stage);
            if (order == 0) order = Jq.compare(one.source, other.source);
            if (order == 0) order = Jq.compare(one.code, other.code);
            if (order == 0) order = Jq.compare(one.subject, other.subject);
            return order != 0 ? order : Jq.compare(one.detail, other.detail);
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

    /**
     * The rows, distinct and in jq's order ({@code unique_by}), split by
     * class.
     */
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
                Jq.Printer print = new Jq.Printer(new BufferedOutputStream(
                        counted, 1 << 20), pretty);
                print.open('{');
                print.key("schemaVersion", 1);
                print.number(2);
                print.key("kind", 1);
                print.string("CAMPAIGN_COVERAGE_GAPS");
                print.key("provenance", 1);
                print.value(provenance, 1);
                print.key("gaps", 1);
                rows(print, blocking);
                print.key("telemetryGaps", 1);
                rows(print, selected);
                print.key("gapCount", 1);
                print.number(blocking.size());
                print.key("telemetryCount", 1);
                print.number(diagnostic.size());
                print.key("byStage", 1);
                counts(print, blocking, row -> row.stage);
                print.key("byCode", 1);
                counts(print, blocking, row -> row.code);
                if (published != null) {
                    print.key("published", 1);
                    print.open('{');
                    print.key("bytes", 2);
                    print.number(published.bytes);
                    print.key("sha256", 2);
                    print.string(published.sha256);
                    print.close('}', 1);
                }
                print.close('}', 0);
                print.raw("\n");
                print.flush();
                written[0] = counted.written();
            });
            return written[0];
        }

        private static void rows(Jq.Printer print, List<Row> rows)
                throws IOException {
            if (rows.isEmpty()) {
                print.raw("[]");
                return;
            }
            print.open('[');
            for (Row row : rows) {
                print.item(2);
                print.open('{');
                print.key("stage", 3);
                print.value(row.stage, 3);
                print.key("source", 3);
                print.value(row.source, 3);
                print.key("code", 3);
                print.value(row.code, 3);
                print.key("subject", 3);
                print.value(row.subject, 3);
                print.key("detail", 3);
                print.value(row.detail, 3);
                print.key("class", 3);
                print.string(row.diagnostic ? GapClass.DIAGNOSTIC.name()
                        : GapClass.BLOCKING.name());
                print.key("classReason", 3);
                print.string(row.classReason);
                print.close('}', 2);
            }
            print.close(']', 1);
        }

        /** {@code group_by(f) | map({key: .[0] | f, value: length}) |
         *  from_entries}: a count per value, in jq's order of the values. */
        private static void counts(Jq.Printer print, List<Row> rows,
                                   Function<Row, Object> key)
                throws IOException {
            List<Object> keys = new ArrayList<Object>(rows.size());
            for (Row row : rows) keys.add(key.apply(row));
            keys.sort(Jq::compare);
            Map<Text, Integer> counts = new LinkedHashMap<Text, Integer>();
            for (int at = 0; at < keys.size(); ) {
                int end = at + 1;
                while (end < keys.size()
                        && Jq.compare(keys.get(at), keys.get(end)) == 0) {
                    end++;
                }
                Object name = keys.get(at);
                if (!(name instanceof Text)) {
                    throw new IllegalStateException("Cannot use "
                            + name + " as object key");
                }
                counts.put((Text) name, end - at);
                at = end;
            }
            if (counts.isEmpty()) {
                print.raw("{}");
                return;
            }
            print.open('{');
            for (Map.Entry<Text, Integer> count : counts.entrySet()) {
                print.item(2);
                print.string(count.getKey());
                print.raw(print.pretty ? ": " : ":");
                print.number(count.getValue());
            }
            print.close('}', 1);
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

        /** A string jq read: one with a lone surrogate jq refuses. */
        Text text(String value) {
            return of(Jq.text(value));
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
        private final MessageDigest digest = sha256();
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
            return new Written(bytes, hex(digest.digest()));
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

    private static MessageDigest sha256() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException absent) {
            throw new IllegalStateException(absent);
        }
    }

    private static String hex(byte[] hash) {
        StringBuilder text = new StringBuilder(hash.length * 2);
        for (byte b : hash) text.append(String.format("%02x", b & 0xff));
        return text.toString();
    }

    /**
     * jq 1.6's values, as the jq program this replaces read and printed
     * them: its {@code //}, its order of values (null &lt; false &lt; true &lt;
     * numbers &lt; strings by their UTF-8 bytes &lt; arrays &lt; objects), and
     * its text (two-space indent, numbers by the shortest digits that read
     * back, at most 17).
     */
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

        /** A string as jq reads it: one with a lone surrogate it refuses
         *  ("Invalid \\uXXXX\\uXXXX surrogate pair escape"). */
        static String text(String value) {
            for (int at = 0; at < value.length(); at++) {
                char c = value.charAt(at);
                if (!Character.isSurrogate(c)) continue;
                if (Character.isHighSurrogate(c) && at + 1 < value.length()
                        && Character.isLowSurrogate(value.charAt(at + 1))) {
                    at++;
                    continue;
                }
                throw new IllegalArgumentException("Invalid \\uXXXX\\uXXXX"
                        + " surrogate pair escape in " + value);
            }
            return value;
        }

        static int hash(Object value) {
            return value instanceof Text ? value.hashCode() : kind(value);
        }

        private static int kind(Object value) {
            if (value instanceof Text || value instanceof String) return 5;
            JsonElement element = (JsonElement) value;
            if (element.isJsonNull()) return 1;
            if (element.isJsonArray()) return 6;
            if (element.isJsonObject()) return 7;
            JsonPrimitive primitive = element.getAsJsonPrimitive();
            if (primitive.isBoolean()) return primitive.getAsBoolean() ? 3 : 2;
            if (primitive.isNumber()) return 4;
            return 5;
        }

        /** jq's order of two values: a row's (a {@link Text}, or an
         *  element), or an item of an array or object (a {@link String},
         *  or an element). */
        static int compare(Object one, Object other) {
            if (one instanceof Text && other instanceof Text) {
                return ((Text) one).compareTo((Text) other);
            }
            int kinds = kind(one) - kind(other);
            if (kinds != 0) return kinds;
            switch (kind(one)) {
                case 4: {
                    double a = ((JsonElement) one).getAsDouble();
                    double b = ((JsonElement) other).getAsDouble();
                    return a < b ? -1 : a == b ? 0 : 1;
                }
                case 5:
                    return compareText(string(one), string(other));
                case 6: {
                    JsonArray a = ((JsonElement) one).getAsJsonArray();
                    JsonArray b = ((JsonElement) other).getAsJsonArray();
                    for (int at = 0; ; at++) {
                        if (at >= a.size() || at >= b.size()) {
                            return (at >= b.size() ? 1 : 0)
                                    - (at >= a.size() ? 1 : 0);
                        }
                        int order = compare(item(a.get(at)), item(b.get(at)));
                        if (order != 0) return order;
                    }
                }
                case 7: {
                    JsonObject a = ((JsonElement) one).getAsJsonObject();
                    JsonObject b = ((JsonElement) other).getAsJsonObject();
                    List<String> keysA = keys(a);
                    List<String> keysB = keys(b);
                    for (int at = 0; ; at++) {
                        if (at >= keysA.size() || at >= keysB.size()) {
                            int order = (at >= keysB.size() ? 1 : 0)
                                    - (at >= keysA.size() ? 1 : 0);
                            if (order != 0) return order;
                            break;
                        }
                        int order = compareText(keysA.get(at), keysB.get(at));
                        if (order != 0) return order;
                    }
                    for (String key : keysA) {
                        int order = compare(item(a.get(key)),
                                item(b.get(key)));
                        if (order != 0) return order;
                    }
                    return 0;
                }
                default:
                    return 0;
            }
        }

        private static Object item(JsonElement element) {
            return element.isJsonPrimitive()
                    && element.getAsJsonPrimitive().isString()
                    ? text(element.getAsString()) : element;
        }

        private static String string(Object value) {
            if (value instanceof Text) return value.toString();
            return value instanceof String ? (String) value
                    : ((JsonElement) value).getAsString();
        }

        private static List<String> keys(JsonObject object) {
            TreeSet<String> sorted = new TreeSet<String>(Jq::compareText);
            sorted.addAll(object.keySet());
            return new ArrayList<String>(sorted);
        }

        /** Two strings by their UTF-8 bytes, which is their code points'
         *  order (a UTF-16 comparison puts U+E000..U+FFFF after the
         *  supplementary characters). */
        static int compareText(String one, String other) {
            int length = Math.min(one.length(), other.length());
            for (int at = 0; at < length; at++) {
                char a = one.charAt(at);
                char b = other.charAt(at);
                if (a == b) continue;
                if (a >= 0xD800 && b >= 0xD800) {
                    a = codePointOrder(a);
                    b = codePointOrder(b);
                }
                return a - b;
            }
            return one.length() - other.length();
        }

        private static char codePointOrder(char c) {
            return (char) (c >= 0xE000 ? c - 0x800 : c + 0x2000);
        }

        /** jq 1.6's text of a number ({@code jvp_dtoa_fmt}). */
        static String number(double value) {
            if (Double.isNaN(value)) return "null";
            if (value > Double.MAX_VALUE) value = Double.MAX_VALUE;
            if (value < -Double.MAX_VALUE) value = -Double.MAX_VALUE;
            StringBuilder text = new StringBuilder();
            if (value < 0 || (value == 0 && 1 / value < 0)) text.append('-');
            double magnitude = Math.abs(value);
            if (magnitude == 0) return text.append('0').toString();
            String digits;
            int point;
            if (magnitude < 9007199254740992.0
                    && magnitude == Math.rint(magnitude)) {
                digits = Long.toString((long) magnitude);
                point = digits.length();
            } else {
                BigDecimal exact = new BigDecimal(magnitude);
                BigDecimal shortest = exact;
                for (int precision = 1; precision <= 17; precision++) {
                    BigDecimal rounded = exact.round(new MathContext(
                            precision, RoundingMode.HALF_EVEN));
                    if (rounded.doubleValue() == magnitude) {
                        shortest = rounded;
                        break;
                    }
                }
                digits = shortest.unscaledValue().toString();
                point = digits.length() - shortest.scale();
            }
            int end = digits.length();
            while (end > 1 && digits.charAt(end - 1) == '0') end--;
            digits = digits.substring(0, end);
            if (point <= -4 || point > digits.length() + 15) {
                text.append(digits.charAt(0));
                if (digits.length() > 1) {
                    text.append('.').append(digits, 1, digits.length());
                }
                int exponent = point - 1;
                text.append('e').append(exponent < 0 ? '-' : '+');
                exponent = Math.abs(exponent);
                if (exponent < 10) text.append('0');
                text.append(exponent);
            } else if (point <= 0) {
                text.append("0.");
                for (int zero = point; zero < 0; zero++) text.append('0');
                text.append(digits);
            } else if (point >= digits.length()) {
                text.append(digits);
                for (int zero = digits.length(); zero < point; zero++) {
                    text.append('0');
                }
            } else {
                text.append(digits, 0, point).append('.')
                        .append(digits, point, digits.length());
            }
            return text.toString();
        }

        /** jq's text of values, pretty (indent 2) or compact ({@code -c}),
         *  as UTF-8 bytes, written as it goes. */
        static final class Printer {
            private static final byte[][] INDENT = new byte[16][];
            private static final byte[][] ESCAPE = new byte[128][];
            private static final byte[] COLON = ascii(":");
            private static final byte[] COLON_SPACE = ascii(": ");
            private final OutputStream out;
            final boolean pretty;
            /** Whether the container being written has had an item. */
            private boolean[] started = new boolean[16];
            private int depth;

            static {
                for (int level = 0; level < INDENT.length; level++) {
                    INDENT[level] = new byte[1 + 2 * level];
                    Arrays.fill(INDENT[level], (byte) ' ');
                    INDENT[level][0] = '\n';
                }
                for (int c = 0; c < 0x20; c++) {
                    ESCAPE[c] = ascii(String.format("\\u%04x", c));
                }
                ESCAPE['\b'] = ascii("\\b");
                ESCAPE['\t'] = ascii("\\t");
                ESCAPE['\n'] = ascii("\\n");
                ESCAPE['\f'] = ascii("\\f");
                ESCAPE['\r'] = ascii("\\r");
                ESCAPE['"'] = ascii("\\\"");
                ESCAPE['\\'] = ascii("\\\\");
                ESCAPE[0x7f] = ascii("\\u007f");
            }

            private static byte[] ascii(String text) {
                return text.getBytes(StandardCharsets.US_ASCII);
            }

            Printer(OutputStream out, boolean pretty) {
                this.out = out;
                this.pretty = pretty;
            }

            void flush() throws IOException {
                out.flush();
            }

            void raw(String text) throws IOException {
                out.write(ascii(text));
            }

            void open(char bracket) throws IOException {
                out.write(bracket);
                depth++;
                if (depth >= started.length) {
                    started = Arrays.copyOf(started, started.length * 2);
                }
                started[depth] = false;
            }

            /** Before an item of an array or object at indent {@code
             *  level}. */
            void item(int level) throws IOException {
                if (started[depth]) out.write(',');
                started[depth] = true;
                newline(level);
            }

            /** A key of an object, its items at indent {@code level}. */
            void key(String name, int level) throws IOException {
                item(level);
                string(name);
                out.write(pretty ? COLON_SPACE : COLON);
            }

            void close(char bracket, int level) throws IOException {
                depth--;
                newline(level);
                out.write(bracket);
            }

            private void newline(int level) throws IOException {
                if (!pretty) return;
                if (level < INDENT.length) {
                    out.write(INDENT[level]);
                    return;
                }
                out.write('\n');
                for (int at = 0; at < level; at++) raw("  ");
            }

            void number(double value) throws IOException {
                raw(Jq.number(value));
            }

            /** Any value, its items (if any) at indent {@code level} + 1. */
            void value(Object value, int level) throws IOException {
                if (value instanceof Text) {
                    string((Text) value);
                    return;
                }
                JsonElement element = (JsonElement) value;
                if (element.isJsonNull()) {
                    raw("null");
                } else if (element.isJsonPrimitive()) {
                    JsonPrimitive primitive = element.getAsJsonPrimitive();
                    if (primitive.isBoolean()) {
                        raw(primitive.getAsBoolean() ? "true" : "false");
                    } else if (primitive.isNumber()) {
                        number(primitive.getAsDouble());
                    } else {
                        string(text(primitive.getAsString()));
                    }
                } else if (element.isJsonArray()) {
                    JsonArray items = element.getAsJsonArray();
                    if (items.size() == 0) {
                        raw("[]");
                        return;
                    }
                    open('[');
                    for (JsonElement item : items) {
                        item(level + 1);
                        value(item, level + 1);
                    }
                    close(']', level);
                } else {
                    JsonObject fields = element.getAsJsonObject();
                    if (fields.size() == 0) {
                        raw("{}");
                        return;
                    }
                    open('{');
                    for (Map.Entry<String, JsonElement> field
                            : fields.entrySet()) {
                        key(text(field.getKey()), level + 1);
                        value(field.getValue(), level + 1);
                    }
                    close('}', level);
                }
            }

            void string(String text) throws IOException {
                string(text.getBytes(StandardCharsets.UTF_8));
            }

            void string(Text text) throws IOException {
                string(text.utf8);
            }

            /** jq's string text: {@code "} and {@code \} escaped, the
             *  control characters and DEL as {@code \b \t \n \f \r} or
             *  {@code \}{@code u00xx}, every other byte as it is. */
            private void string(byte[] text) throws IOException {
                out.write('"');
                int from = 0;
                for (int at = 0; at < text.length; at++) {
                    byte b = text[at];
                    if (b < 0 || ESCAPE[b] == null) continue;
                    out.write(text, from, at - from);
                    out.write(ESCAPE[b]);
                    from = at + 1;
                }
                out.write(text, from, text.length - from);
                out.write('"');
            }
        }
    }
}
