package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonSyntaxException;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.StringReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * CONTRACT-SPEC §2.2: the one codec for the row kinds, one method pair per kind.
 * JSONL, one kind per file.  A nullable field is omitted when null; every
 * other field is always written, so absence never means false or zero.
 * Occurrences are written as parts, not as their render.
 */
public final class RowCodec {
    private static final Gson GSON = new Gson();

    private static final String SESSION_ID = "sessionId";
    private static final String OCCURRENCE = "occurrence";
    private static final String ENDPOINT = "endpoint";
    private static final String LOCATION = "location";
    private static final String NODE = "node";
    private static final String REGION_ID = "regionId";
    private static final String CONTEXT = "context";
    private static final String INDEX = "index";
    private static final String SITE_INDEX = "siteIndex";
    private static final String FORM = "form";
    private static final String ROLE = "role";
    /** The api a root context's window index was counted under. */
    private static final String ROOT_API = "api";
    private static final String CALL_SITE = "callSite";
    private static final String ITERATION = "iteration";
    private static final String SEQ = "seq";
    private static final String JAVA_TYPE = "javaType";

    private RowCodec() {
    }

    // ---- shared parts -------------------------------------------------

    /** An address as its four parts; the render is for people, not rows. */
    public static JsonObject writeOccurrence(OccurrenceAddress occurrence) {
        JsonObject json = new JsonObject();
        json.addProperty(NODE, occurrence.node().render());
        json.addProperty(REGION_ID, occurrence.regionId());
        json.add(CONTEXT, writeContext(occurrence.context()));
        json.add(INDEX, writeIndex(occurrence.index()));
        return json;
    }

    public static OccurrenceAddress readOccurrence(JsonObject json) {
        return readOccurrence(json, new RowPool());
    }

    /** An occurrence, held once per pool: a session's rows name a few
     *  hundred occurrences on tens of thousands of rows. */
    private static OccurrenceAddress readOccurrence(JsonObject json,
                                                    RowPool pool) {
        return pool.shared(OccurrenceAddress.of(
                NodeId.parse(string(json, NODE)), string(json, REGION_ID),
                readContext(object(json, CONTEXT)),
                readIndex(array(json, INDEX), pool)));
    }

    /** A causal context as {@code {form, ...}}: one shape per form. */
    private static JsonObject writeContext(CausalContext context) {
        JsonObject json = new JsonObject();
        json.addProperty(FORM, context.form().name());
        switch (context.form()) {
            case ANCHOR:
                CausalContext.Anchor anchor = (CausalContext.Anchor) context;
                json.addProperty("producerEndpointId",
                        anchor.producerEndpointId());
                json.addProperty("rpcSite", anchor.rpcSite());
                break;
            case ROOT:
                CausalContext.Root root = (CausalContext.Root) context;
                json.addProperty(ROLE, root.role().name());
                // Omitted when undeclared (a daemon tick).
                if (!root.api().isEmpty()) {
                    json.addProperty(ROOT_API, root.api());
                }
                json.addProperty("windowIndex", root.windowIndex());
                break;
            default:
                json.addProperty(ROLE,
                        ((CausalContext.Lost) context).role().name());
                break;
        }
        return json;
    }

    private static CausalContext readContext(JsonObject json) {
        CausalContext.Form form =
                CausalContext.Form.valueOf(string(json, FORM));
        switch (form) {
            case ANCHOR:
                return CausalContext.of(string(json, "producerEndpointId"),
                        string(json, "rpcSite"));
            case ROOT:
                return CausalContext.of(Role.of(string(json, ROLE)),
                        optionalString(json, ROOT_API),
                        integer(json, "windowIndex"));
            default:
                return CausalContext.of(Role.of(string(json, ROLE)));
        }
    }

    /** An execution index as its frames, outermost first. */
    private static JsonArray writeIndex(ExecutionIndex index) {
        JsonArray frames = new JsonArray();
        for (Frame frame : index.frames()) {
            JsonObject json = new JsonObject();
            json.addProperty(CALL_SITE, frame.callSite());
            json.addProperty(ITERATION, frame.iteration());
            frames.add(json);
        }
        return frames;
    }

    /** An index and each of its frames, held once per pool. */
    private static ExecutionIndex readIndex(JsonArray frames, RowPool pool) {
        List<Frame> read = new ArrayList<>();
        for (JsonElement frame : frames) {
            JsonObject json = frame.getAsJsonObject();
            read.add(pool.shared(Frame.of(string(json, CALL_SITE),
                    integer(json, ITERATION))));
        }
        return pool.shared(ExecutionIndex.of(read));
    }

    public static JsonObject writeEndpoint(Endpoint endpoint) {
        JsonObject json = new JsonObject();
        json.add(OCCURRENCE, writeOccurrence(endpoint.occurrence()));
        json.addProperty("site", endpoint.site());
        json.add(SITE_INDEX, writeIndex(endpoint.siteIndex()));
        json.addProperty("attempt", endpoint.attempt());
        return json;
    }

    public static Endpoint readEndpoint(JsonObject json) {
        return readEndpoint(json, new RowPool());
    }

    private static Endpoint readEndpoint(JsonObject json, RowPool pool) {
        return Endpoint.of(readOccurrence(object(json, OCCURRENCE), pool),
                string(json, "site"), readIndex(array(json, SITE_INDEX), pool),
                integer(json, "attempt"));
    }

    private static JsonObject writeLocation(LocationId location) {
        JsonObject json = new JsonObject();
        json.addProperty("kind", location.kind().name());
        json.addProperty("owner", location.owner());
        json.addProperty("slot", location.slot());
        return json;
    }

    private static LocationId readLocation(JsonObject json) {
        return LocationId.of(
                LocationKind.valueOf(string(json, "kind")),
                string(json, "owner"), string(json, "slot"));
    }

    // ---- one pair per row kind ----------------------------------------

    public static JsonObject writeActivation(ActivationRow row) {
        JsonObject json = row(row.sessionId());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("taskId", row.taskId());
        json.addProperty("focused", row.focused());
        json.addProperty("instrumented", row.instrumented());
        json.addProperty("threadKey", row.threadKey());
        if (row.anchorProducer() != null) {
            json.add(ANCHOR_PRODUCER, writeEndpoint(row.anchorProducer()));
        }
        return json;
    }

    public static ActivationRow readActivation(JsonObject json) {
        return readActivation(json, new RowPool());
    }

    /** One row, its parts taken from the pool of the read it is part of;
     *  so for each kind below. */
    static ActivationRow readActivation(JsonObject json, RowPool pool) {
        JsonObject producer = optionalObject(json, ANCHOR_PRODUCER);
        return ActivationRow.of(string(json, SESSION_ID),
                readOccurrence(object(json, OCCURRENCE), pool),
                string(json, "taskId"), bool(json, "focused"),
                bool(json, "instrumented"), string(json, "threadKey"),
                producer == null ? null : readEndpoint(producer, pool));
    }

    private static final String ANCHOR_PRODUCER = "anchorProducer";

    public static JsonObject writeDecision(DecisionRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("siteId", row.siteId());
        json.addProperty("ordinal", row.ordinal());
        json.addProperty("outcome", row.outcome());
        json.addProperty("term", row.term());
        JsonObject clocks = new JsonObject();
        for (Map.Entry<String, Long> reading : row.clockReadings().entrySet()) {
            clocks.addProperty(reading.getKey(), reading.getValue());
        }
        json.add("clockReadings", clocks);
        return json;
    }

    public static DecisionRow readDecision(JsonObject json) {
        return readDecision(json, new RowPool());
    }

    static DecisionRow readDecision(JsonObject json, RowPool pool) {
        Map<String, Long> clocks = new LinkedHashMap<>();
        JsonObject readings = object(json, "clockReadings");
        for (Map.Entry<String, JsonElement> reading : readings.entrySet()) {
            clocks.put(reading.getKey(), reading.getValue().getAsLong());
        }
        return DecisionRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE), pool),
                string(json, "siteId"), integer(json, "ordinal"),
                bool(json, "outcome"), string(json, "term"), clocks);
    }

    public static JsonObject writeExport(ExportRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(ENDPOINT, writeEndpoint(row.endpoint()));
        json.addProperty("expressionRef", row.expressionRef());
        json.addProperty(JAVA_TYPE, row.javaType());
        json.addProperty("handle", row.handle());
        json.addProperty("recordedValue", row.recordedValue());
        return json;
    }

    public static ExportRow readExport(JsonObject json) {
        return readExport(json, new RowPool());
    }

    static ExportRow readExport(JsonObject json, RowPool pool) {
        return ExportRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT), pool),
                string(json, "expressionRef"), string(json, JAVA_TYPE),
                number(json, "handle"), string(json, "recordedValue"));
    }

    public static JsonObject writeAttach(AttachRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(ENDPOINT, writeEndpoint(row.endpoint()));
        json.addProperty("symbol", row.symbol());
        json.addProperty(JAVA_TYPE, row.javaType());
        json.addProperty("arrival", row.arrival());
        json.addProperty("answered", row.answered());
        if (row.answeredValue() != null) {
            json.addProperty("answeredValue", row.answeredValue());
        }
        if (row.producer() != null) {
            json.add("producer", writeEndpoint(row.producer()));
        }
        json.addProperty("correlationId", row.correlationId());
        // Absent = unstated, distinct from either answer.
        if (row.pairedBy() != null) {
            json.addProperty("pairedBy", row.pairedBy());
        }
        return json;
    }

    public static AttachRow readAttach(JsonObject json) {
        return readAttach(json, new RowPool());
    }

    static AttachRow readAttach(JsonObject json, RowPool pool) {
        JsonObject producer = optionalObject(json, "producer");
        return AttachRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT), pool),
                string(json, "symbol"), string(json, JAVA_TYPE),
                string(json, "arrival"), bool(json, "answered"),
                optionalString(json, "answeredValue"),
                producer == null ? null : readEndpoint(producer, pool),
                string(json, "correlationId"),
                optionalString(json, "pairedBy"));
    }

    public static JsonObject writeWrite(WriteRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(ENDPOINT, writeEndpoint(row.endpoint()));
        json.add(LOCATION, writeLocation(row.location()));
        json.addProperty("version", row.version());
        json.addProperty("expressionRef", row.expressionRef());
        json.addProperty(JAVA_TYPE, row.javaType());
        if (row.referentState() != null) {
            JsonObject referent = new JsonObject();
            referent.add(LOCATION, writeLocation(
                    row.referentState().location()));
            referent.addProperty("version", row.referentState().version());
            json.add(REFERENT_STATE, referent);
        }
        if (row.referentStateRefused() != null) {
            json.addProperty(REFERENT_STATE_REFUSED,
                    row.referentStateRefused());
        }
        if (row.initial()) json.addProperty(INITIAL, true);
        return json;
    }

    public static WriteRow readWrite(JsonObject json) {
        return readWrite(json, new RowPool());
    }

    static WriteRow readWrite(JsonObject json, RowPool pool) {
        Endpoint endpoint = readEndpoint(object(json, ENDPOINT), pool);
        LocationId location = readLocation(object(json, LOCATION));
        if (json.has(INITIAL) && json.get(INITIAL).getAsBoolean()) {
            return WriteRow.initial(string(json, SESSION_ID),
                    number(json, SEQ), endpoint, location,
                    number(json, "version"), string(json, "expressionRef"),
                    string(json, JAVA_TYPE));
        }
        JsonObject referent = optionalObject(json, REFERENT_STATE);
        return WriteRow.of(string(json, SESSION_ID), number(json, SEQ),
                endpoint, location, number(json, "version"),
                string(json, "expressionRef"), string(json, JAVA_TYPE),
                referent == null ? null : WriteRow.Referent.of(
                        readLocation(object(referent, LOCATION)),
                        number(referent, "version")),
                optionalString(json, REFERENT_STATE_REFUSED));
    }

    private static final String INITIAL = "initial";
    private static final String REFERENT_STATE = "referentState";
    private static final String REFERENT_STATE_REFUSED =
            "referentStateRefused";

    public static JsonObject writeRead(ReadRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(ENDPOINT, writeEndpoint(row.endpoint()));
        json.add(LOCATION, writeLocation(row.location()));
        json.addProperty("observedVersion", row.observedVersion());
        json.addProperty("symbol", row.symbol());
        json.addProperty(JAVA_TYPE, row.javaType());
        if (row.mintVersion() != ReadRow.UNKNOWN_VERSION) {
            json.addProperty("mintVersion", row.mintVersion());
        }
        if (row.concreteValue() != null) {
            json.addProperty("concreteValue", row.concreteValue());
        }
        // Stated only when true, so every other read spells as it did.
        if (row.unnamedWriter()) {
            json.addProperty("unnamedWriter", true);
        }
        return json;
    }

    public static ReadRow readRead(JsonObject json) {
        return readRead(json, new RowPool());
    }

    static ReadRow readRead(JsonObject json, RowPool pool) {
        return ReadRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT), pool),
                readLocation(object(json, LOCATION)),
                number(json, "observedVersion"), string(json, "symbol"),
                string(json, JAVA_TYPE),
                optionalString(json, "concreteValue"),
                json.has("mintVersion") ? number(json, "mintVersion")
                        : ReadRow.UNKNOWN_VERSION,
                json.has("unnamedWriter")
                        && json.get("unnamedWriter").getAsBoolean());
    }

    public static JsonObject writeRootMint(RootMintRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("rootId", row.rootId());
        json.addProperty("symbol", row.symbol());
        json.addProperty("kind", row.kind().name());
        json.addProperty("category", row.category().name());
        json.addProperty("recordedValue", row.recordedValue());
        if (row.domainMin() != null) {
            json.addProperty("domainMin", row.domainMin());
        }
        if (row.domainMax() != null) {
            json.addProperty("domainMax", row.domainMax());
        }
        json.addProperty("declared", row.declared());
        if (row.clock() != null) {
            json.addProperty("clockNanos", row.clock().nanos());
            if (!row.clock().source().isEmpty()) {
                json.addProperty(RootMintRow.CLOCK_SOURCE,
                        row.clock().source());
            }
        }
        if (row.clockSkew() != 0L) {
            json.addProperty(RootMintRow.CLOCK_SKEW, row.clockSkew());
        }
        return json;
    }

    public static RootMintRow readRootMint(JsonObject json) {
        return readRootMint(json, new RowPool());
    }

    static RootMintRow readRootMint(JsonObject json, RowPool pool) {
        return RootMintRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE), pool),
                string(json, "rootId"), string(json, "symbol"),
                RootKind.valueOf(string(json, "kind")),
                RootCategory.valueOf(string(json, "category")),
                string(json, "recordedValue"),
                optionalString(json, "domainMin"),
                optionalString(json, "domainMax"), bool(json, "declared"),
                json.has("clockNanos") ? Clock.of(number(json, "clockNanos"),
                        optionalString(json, RootMintRow.CLOCK_SOURCE))
                        : null,
                json.has(RootMintRow.CLOCK_SKEW)
                        ? number(json, RootMintRow.CLOCK_SKEW) : 0L);
    }

    public static JsonObject writeTarget(TargetRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("anchorSiteId", row.anchorSiteId());
        json.addProperty("phiTerm", row.phiTerm());
        json.addProperty("observedFatal", row.observedFatal());
        json.addProperty("reachedAnchor", row.reachedAnchor());
        TargetRow.OpenArm open = row.openArm();
        if (open != null) {
            JsonObject arm = new JsonObject();
            arm.addProperty("siteId", open.siteId());
            arm.addProperty("ordinal", open.ordinal());
            arm.addProperty("outcome", open.outcome());
            if (!open.askedSiteId().isEmpty()) {
                arm.addProperty("askedSiteId", open.askedSiteId());
                arm.addProperty("askedOrdinal", open.askedOrdinal());
            }
            json.add(OPEN_ARM, arm);
        }
        return json;
    }

    public static TargetRow readTarget(JsonObject json) {
        return readTarget(json, new RowPool());
    }

    static TargetRow readTarget(JsonObject json, RowPool pool) {
        TargetRow.OpenArm open = null;
        if (json.has(OPEN_ARM)) {
            JsonObject arm = object(json, OPEN_ARM);
            open = TargetRow.OpenArm.of(string(arm, "siteId"),
                    (int) number(arm, "ordinal"), bool(arm, "outcome"),
                    optionalString(arm, "askedSiteId"),
                    arm.has("askedOrdinal")
                            ? (int) number(arm, "askedOrdinal") : 0);
        }
        return TargetRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE), pool),
                string(json, "anchorSiteId"), string(json, "phiTerm"),
                bool(json, "observedFatal"), bool(json, "reachedAnchor"),
                open);
    }

    /** A target row's open decider arm (TargetRow.OpenArm). */
    private static final String OPEN_ARM = "openArm";

    public static JsonObject writeGap(GapRow row) {
        JsonObject json = row(row.sessionId());
        json.addProperty("kind", row.kind().name());
        json.addProperty("cls", row.cls().name());
        json.addProperty("subject", row.subject());
        json.addProperty("detail", row.detail());
        return json;
    }

    public static GapRow readGap(JsonObject json) {
        return GapRow.of(string(json, SESSION_ID),
                GapKind.valueOf(string(json, "kind")),
                GapClass.valueOf(string(json, "cls")), string(json, "subject"),
                string(json, "detail"));
    }

    /** What one obligation settled; every writer and reader uses this pair. */
    public static JsonObject writeObligationResult(ObligationResult row) {
        JsonObject json = row(row.sessionId());
        json.addProperty("schemaVersion", 1);
        json.addProperty("kind", "OBLIGATION_RESULT");
        json.addProperty("obligationId", row.obligationId());
        json.addProperty("verdict", row.verdict().name());
        json.addProperty("detail", row.detail());
        return json;
    }

    public static ObligationResult readObligationResult(JsonObject json) {
        return ObligationResult.of(string(json, "obligationId"),
                Verdict.valueOf(string(json, "verdict")),
                string(json, SESSION_ID), string(json, "detail"));
    }

    /** One scheduling event; no session id (prefixes cross sessions). */
    public static JsonObject writeScheduleEvent(ScheduleEvent event) {
        JsonObject json = new JsonObject();
        json.addProperty(SEQ, event.seq());
        json.addProperty("kind", event.kind().name());
        json.addProperty(CONTEXT, event.context());
        json.addProperty("site", event.site());
        json.addProperty("k", event.k());
        if (!event.occurrence().isEmpty()) {
            json.addProperty(OCCURRENCE, event.occurrence());
        }
        if (!event.endpoint().isEmpty()) {
            json.addProperty(ENDPOINT, event.endpoint());
        }
        return json;
    }

    /**
     * A schedule mark: where occurrence {@code id} opened, or
     * {@link ScheduleEvent#WITNESS}; not an event, so readers of events skip
     * it ({@code SessionReader#readSchedule}).
     */
    public static JsonObject writeScheduleMark(String id, long at) {
        JsonObject json = new JsonObject();
        json.addProperty("mark", id);
        json.addProperty("at", at);
        return json;
    }

    /**
     * The mark of the invocation of a parameterized test the run is, as its
     * arguments render ({@link ScheduleEvent#INVOCATION}): {@code of}.
     */
    public static JsonObject writeScheduleInvocation(String stated) {
        JsonObject json = writeScheduleMark(ScheduleEvent.INVOCATION, 0L);
        json.addProperty("of", stated);
        return json;
    }

    /** The mark of {@code who} completing startup {@code step} ({@link
     *  ScheduleEvent#STARTUP}). */
    public static JsonObject writeScheduleStartup(String step, String who) {
        JsonObject json = writeScheduleMark(ScheduleEvent.STARTUP, 0L);
        json.addProperty("step", step);
        json.addProperty("who", who);
        return json;
    }

    public static ScheduleEvent readScheduleEvent(JsonObject json) {
        return ScheduleEvent.of(number(json, SEQ),
                ScheduleEvent.Kind.valueOf(string(json, "kind")),
                json.has(CONTEXT) ? string(json, CONTEXT) : "",
                string(json, "site"), integer(json, "k"),
                optionalString(json, OCCURRENCE),
                optionalString(json, ENDPOINT));
    }

    // ---- files ---------------------------------------------------------

    /** Writes one kind's file: one object per line, nothing else in it. */
    public static <T> void writeAll(Path file, List<T> rows,
                                    Function<T, JsonObject> writer)
            throws IOException {
        List<JsonObject> objects = new ArrayList<>(rows.size());
        for (T row : rows) {
            objects.add(writer.apply(row));
        }
        writeJsonl(file, objects);
    }

    /** Reads one kind's file; a file that is not there is no rows. */
    public static <T> List<T> readAll(Path file,
                                      Function<JsonObject, T> reader)
            throws IOException {
        return readAll(file, new RowPool(), reader);
    }

    /**
     * The same read, its strings from {@code pool}, each line read into its
     * row as it is parsed: a file's parsed lines are never all held.
     */
    static <T> List<T> readAll(Path file, RowPool pool,
                               Function<JsonObject, T> reader)
            throws IOException {
        List<T> rows = new ArrayList<>();
        eachLine(file, line -> rows.add(reader.apply(fromLine(line, pool))));
        return rows;
    }

    public static void writeJsonl(Path file, List<JsonObject> rows)
            throws IOException {
        Files.createDirectories(file.toAbsolutePath().getParent());
        try (BufferedWriter out = Files.newBufferedWriter(file,
                StandardCharsets.UTF_8)) {
            for (JsonObject row : rows) {
                out.write(toLine(row));
                out.write("\n");
            }
        }
    }

    /** Every line of a JSONL file, their strings shared ({@link RowPool}). */
    public static List<JsonObject> readJsonl(Path file) throws IOException {
        RowPool pool = new RowPool();
        List<JsonObject> rows = new ArrayList<>();
        eachLine(file, line -> rows.add(fromLine(line, pool)));
        return rows;
    }

    /**
     * Hands each non-blank line of a JSONL file to {@code each} in order,
     * until it returns false; a file that is not there has no lines.
     */
    static void eachLine(Path file, Predicate<String> each)
            throws IOException {
        if (file == null || !Files.isRegularFile(file)) return;
        try (BufferedReader in = Files.newBufferedReader(file,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = in.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                if (!each.test(line)) return;
            }
        }
    }

    /** A whole table as one session's expression log. */
    public static void writeExpressions(Path file, ExpressionTable table)
            throws IOException {
        SessionExpressionLog.Writer log = new SessionExpressionLog.Writer();
        List<JsonObject> lines = new ArrayList<>();
        lines.add(SessionExpressionLog.header());
        for (Map.Entry<String, JsonObject> entry
                : table.expressions().entrySet()) {
            lines.addAll(log.lines(entry.getKey(), entry.getValue()));
        }
        writeJsonl(file, lines);
    }

    /** The session's expressions; a missing file is refused, never empty. */
    public static ExpressionTable readExpressions(Path file)
            throws IOException {
        return SessionExpressionLog.read(file, new RowPool());
    }

    /** The role this session states, as one JSON object. */
    public static void writeManifest(Path file, SessionManifest manifest)
            throws IOException {
        writeObject(file, manifest.toJson());
    }

    /** The role this session states; none is refused, never defaulted. */
    public static SessionManifest readManifest(Path file) throws IOException {
        if (file == null || !Files.isRegularFile(file)) {
            throw new IllegalArgumentException(
                    "the session states no role: no " + SessionDir.MANIFEST);
        }
        return SessionManifest.fromJson(readObject(file));
    }

    /**
     * One JSON object, whole or not at all: written with java.io (a channel
     * write on a thread the program interrupts closes with
     * ClosedByInterruptException after truncating -- the runtime writes from
     * workload threads, and hdfs-17899-bug1 v82 kept two sessions whose
     * expressions.json was empty) to a sibling renamed over the file, so a
     * killed replay leaves the last whole table.
     */
    private static void writeObject(Path file, JsonObject json)
            throws IOException {
        Path parent = file.toAbsolutePath().getParent();
        Files.createDirectories(parent);
        Path partial = parent.resolve(file.getFileName() + ".partial");
        try (OutputStream out = new FileOutputStream(partial.toFile())) {
            out.write(GSON.toJson(json).getBytes(StandardCharsets.UTF_8));
        }
        Files.move(partial, file, StandardCopyOption.REPLACE_EXISTING,
                StandardCopyOption.ATOMIC_MOVE);
    }

    private static JsonObject readObject(Path file) throws IOException {
        return parse(new JsonReader(new StringReader(new String(
                Files.readAllBytes(file), StandardCharsets.UTF_8))),
                file.toString());
    }

    /** One row as one line: compact, and never containing a newline. */
    public static String toLine(JsonObject row) {
        return GSON.toJson(row);
    }

    public static JsonObject fromLine(String line) {
        return parse(new JsonReader(new StringReader(line)), "row");
    }

    /** One line, each of its strings taken from {@code pool}. */
    static JsonObject fromLine(String line, RowPool pool) {
        return parse(pool.reader(line), "row");
    }

    // ---- reading fields -------------------------------------------------

    private static JsonObject row(String sessionId) {
        JsonObject json = new JsonObject();
        json.addProperty(SESSION_ID, sessionId);
        return json;
    }

    private static JsonObject row(String sessionId, long seq) {
        JsonObject json = row(sessionId);
        json.addProperty(SEQ, seq);
        return json;
    }

    /** One JSON object read as {@link JsonParser#parseString} reads one:
     *  leniently, and nothing after it. */
    private static JsonObject parse(JsonReader reader, String what) {
        JsonElement parsed;
        try {
            parsed = JsonParser.parseReader(reader);
            if (!parsed.isJsonNull()
                    && reader.peek() != JsonToken.END_DOCUMENT) {
                throw new JsonSyntaxException(
                        "Did not consume the entire document.");
            }
        } catch (IOException | RuntimeException malformed) {
            throw new IllegalArgumentException(
                    "malformed JSON in " + what, malformed);
        }
        if (!parsed.isJsonObject()) {
            throw new IllegalArgumentException(
                    "expected one JSON object in " + what);
        }
        return parsed.getAsJsonObject();
    }

    private static JsonElement member(JsonObject json, String name) {
        JsonElement value = optional(json, name);
        if (value == null) {
            throw new IllegalArgumentException("row states no " + name);
        }
        return value;
    }

    private static String string(JsonObject json, String name) {
        return member(json, name).getAsString();
    }

    private static String optionalString(JsonObject json, String name) {
        JsonElement value = optional(json, name);
        return value == null ? null : value.getAsString();
    }

    private static boolean bool(JsonObject json, String name) {
        return member(json, name).getAsBoolean();
    }

    private static int integer(JsonObject json, String name) {
        return member(json, name).getAsInt();
    }

    private static long number(JsonObject json, String name) {
        return member(json, name).getAsLong();
    }

    private static JsonObject object(JsonObject json, String name) {
        return member(json, name).getAsJsonObject();
    }

    private static JsonArray array(JsonObject json, String name) {
        return member(json, name).getAsJsonArray();
    }

    private static JsonObject optionalObject(JsonObject json, String name) {
        JsonElement value = optional(json, name);
        return value == null ? null : value.getAsJsonObject();
    }

    /** The member, or null when absent or JSON null. */
    private static JsonElement optional(JsonObject json, String name) {
        JsonElement value = json == null ? null : json.get(name);
        return value == null || value.isJsonNull() ? null : value;
    }
}
