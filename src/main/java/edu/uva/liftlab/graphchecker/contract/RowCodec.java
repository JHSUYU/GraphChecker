package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * CONTRACT-SPEC 2: the one codec for the row kinds, one method pair per kind.
 *
 * <p>Rows are JSONL -- one object per line, one kind per file -- so a reader
 * never has to parse another kind's file and a producer can append while a
 * reader streams.  A field the spec marks nullable is omitted when it is null
 * and reads back as null; every other field is always written, because a row
 * that silently drops a false or a zero is a row whose absence means two
 * things.</p>
 *
 * <p>Contract v1.1 added {@code seq} (the session-monotonic event sequence
 * number) to the six event rows and {@code javaType} (the JVM descriptor) to
 * the four value-carrying ones; v1.2 added {@code seq} to the root mints.
 * Both are always written.</p>
 *
 * <p>v2.0 writes an occurrence structurally -- node, region, causal context,
 * execution index -- rather than as one rendered string.  The render exists and
 * round-trips, but a row that carries the parts needs no parser to be read by
 * anything else, and the degraded case is the context's own {@code LOST} form
 * rather than a flag beside it.</p>
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
        return OccurrenceAddress.of(NodeId.parse(string(json, NODE)),
                string(json, REGION_ID), readContext(object(json, CONTEXT)),
                readIndex(array(json, INDEX)));
    }

    /** A causal context as {@code {form, ...}}: one shape per form. */
    public static JsonObject writeContext(CausalContext context) {
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
                // The api the window index was counted under, and only when
                // there is one: a root nothing declared an api for (a daemon
                // tick) states no api, which is also how a row written
                // before the api was carried reads back unchanged.
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

    public static CausalContext readContext(JsonObject json) {
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
    public static JsonArray writeIndex(ExecutionIndex index) {
        JsonArray frames = new JsonArray();
        for (Frame frame : index.frames()) {
            JsonObject json = new JsonObject();
            json.addProperty(CALL_SITE, frame.callSite());
            json.addProperty(ITERATION, frame.iteration());
            frames.add(json);
        }
        return frames;
    }

    public static ExecutionIndex readIndex(JsonArray frames) {
        List<Frame> read = new ArrayList<>();
        for (JsonElement frame : frames) {
            JsonObject json = frame.getAsJsonObject();
            read.add(Frame.of(string(json, CALL_SITE),
                    integer(json, ITERATION)));
        }
        return ExecutionIndex.of(read);
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
        return Endpoint.of(readOccurrence(object(json, OCCURRENCE)),
                string(json, "site"), readIndex(array(json, SITE_INDEX)),
                integer(json, "attempt"));
    }

    public static JsonObject writeLocation(LocationId location) {
        JsonObject json = new JsonObject();
        json.addProperty("kind", location.kind().name());
        json.addProperty("owner", location.owner());
        json.addProperty("slot", location.slot());
        return json;
    }

    public static LocationId readLocation(JsonObject json) {
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
        return json;
    }

    public static ActivationRow readActivation(JsonObject json) {
        return ActivationRow.of(string(json, SESSION_ID),
                readOccurrence(object(json, OCCURRENCE)),
                string(json, "taskId"), bool(json, "focused"),
                bool(json, "instrumented"), string(json, "threadKey"));
    }

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
        Map<String, Long> clocks = new LinkedHashMap<>();
        JsonObject readings = object(json, "clockReadings");
        for (Map.Entry<String, JsonElement> reading : readings.entrySet()) {
            clocks.put(reading.getKey(), reading.getValue().getAsLong());
        }
        return DecisionRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE)),
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
        return ExportRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT)),
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
        return json;
    }

    public static AttachRow readAttach(JsonObject json) {
        JsonObject producer = optionalObject(json, "producer");
        return AttachRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT)), string(json, "symbol"),
                string(json, JAVA_TYPE), string(json, "arrival"),
                bool(json, "answered"),
                optionalString(json, "answeredValue"),
                producer == null ? null : readEndpoint(producer),
                string(json, "correlationId"));
    }

    public static JsonObject writeWrite(WriteRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(ENDPOINT, writeEndpoint(row.endpoint()));
        json.add(LOCATION, writeLocation(row.location()));
        json.addProperty("version", row.version());
        json.addProperty("expressionRef", row.expressionRef());
        json.addProperty(JAVA_TYPE, row.javaType());
        return json;
    }

    public static WriteRow readWrite(JsonObject json) {
        return WriteRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT)),
                readLocation(object(json, LOCATION)), number(json, "version"),
                string(json, "expressionRef"), string(json, JAVA_TYPE));
    }

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
        return json;
    }

    public static ReadRow readRead(JsonObject json) {
        return ReadRow.of(string(json, SESSION_ID), number(json, SEQ),
                readEndpoint(object(json, ENDPOINT)),
                readLocation(object(json, LOCATION)),
                number(json, "observedVersion"), string(json, "symbol"),
                string(json, JAVA_TYPE),
                optionalString(json, "concreteValue"),
                json.has("mintVersion") ? number(json, "mintVersion")
                        : ReadRow.UNKNOWN_VERSION);
    }

    public static JsonObject writeRootMint(RootMintRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("rootId", row.rootId());
        json.addProperty("symbol", row.symbol());
        json.addProperty("kind", row.kind().name());
        json.addProperty("recordedValue", row.recordedValue());
        if (row.domainMin() != null) {
            json.addProperty("domainMin", row.domainMin());
        }
        if (row.domainMax() != null) {
            json.addProperty("domainMax", row.domainMax());
        }
        json.addProperty("declared", row.declared());
        return json;
    }

    public static RootMintRow readRootMint(JsonObject json) {
        return RootMintRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE)),
                string(json, "rootId"), string(json, "symbol"),
                RootKind.valueOf(string(json, "kind")),
                string(json, "recordedValue"),
                optionalString(json, "domainMin"),
                optionalString(json, "domainMax"), bool(json, "declared"));
    }

    public static JsonObject writeTarget(TargetRow row) {
        JsonObject json = row(row.sessionId(), row.seq());
        json.add(OCCURRENCE, writeOccurrence(row.occurrence()));
        json.addProperty("anchorSiteId", row.anchorSiteId());
        json.addProperty("phiTerm", row.phiTerm());
        json.addProperty("observedFatal", row.observedFatal());
        json.addProperty("reachedAnchor", row.reachedAnchor());
        return json;
    }

    public static TargetRow readTarget(JsonObject json) {
        return TargetRow.of(string(json, SESSION_ID), number(json, SEQ),
                readOccurrence(object(json, OCCURRENCE)),
                string(json, "anchorSiteId"), string(json, "phiTerm"),
                bool(json, "observedFatal"), bool(json, "reachedAnchor"));
    }

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

    /**
     * What one obligation SETTLED, as the one row shape for it.
     *
     * <p>One pair, because the row had three hand-written spellings -- the
     * session's ({@code runtime.SessionPublisher}), the worker's ({@code
     * runtime.RowRuntime}) and the reader's ({@code
     * explore.ExploreCodec}) -- and a row written twice by hand is a row
     * whose two writers can disagree about a field.</p>
     */
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
        List<JsonObject> objects = readJsonl(file);
        List<T> rows = new ArrayList<>(objects.size());
        for (JsonObject object : objects) {
            rows.add(reader.apply(object));
        }
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

    public static List<JsonObject> readJsonl(Path file) throws IOException {
        List<JsonObject> rows = new ArrayList<>();
        if (file == null || !Files.isRegularFile(file)) return rows;
        try (BufferedReader in = Files.newBufferedReader(file,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = in.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                rows.add(fromLine(line));
            }
        }
        return rows;
    }

    /** The session's shared expressions, written as one JSON object. */
    public static void writeExpressions(Path file, ExpressionTable table)
            throws IOException {
        Files.createDirectories(file.toAbsolutePath().getParent());
        Files.write(file, GSON.toJson(table.toJson())
                .getBytes(StandardCharsets.UTF_8));
    }

    /** The session's shared expressions; a missing file is the empty table. */
    public static ExpressionTable readExpressions(Path file)
            throws IOException {
        if (file == null || !Files.isRegularFile(file)) {
            return ExpressionTable.empty();
        }
        String text = new String(Files.readAllBytes(file),
                StandardCharsets.UTF_8);
        return ExpressionTable.fromJson(parse(text, file.toString()));
    }

    /** The role this session states, as one JSON object. */
    public static void writeManifest(Path file, SessionManifest manifest)
            throws IOException {
        Files.createDirectories(file.toAbsolutePath().getParent());
        Files.write(file, GSON.toJson(manifest.toJson())
                .getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The role this session states; a session that states none is refused.
     *
     * <p>Never a default.  Which session is the recording is the one fact a
     * whole claim turns on, so an absent or unreadable manifest is a session
     * IMPORT names {@code SESSION_INCOMPLETE} rather than a session read as
     * the seed.</p>
     */
    public static SessionManifest readManifest(Path file) throws IOException {
        if (file == null || !Files.isRegularFile(file)) {
            throw new IllegalArgumentException(
                    "the session states no role: no " + SessionDir.MANIFEST);
        }
        String text = new String(Files.readAllBytes(file),
                StandardCharsets.UTF_8);
        return SessionManifest.fromJson(parse(text, file.toString()));
    }

    /** One row as one line: compact, and never containing a newline. */
    public static String toLine(JsonObject row) {
        return GSON.toJson(row);
    }

    public static JsonObject fromLine(String line) {
        return parse(line, "row");
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

    private static JsonObject parse(String text, String what) {
        JsonElement parsed;
        try {
            parsed = JsonParser.parseString(text);
        } catch (RuntimeException malformed) {
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
        JsonElement value = json == null ? null : json.get(name);
        if (value == null || value.isJsonNull()) {
            throw new IllegalArgumentException("row states no " + name);
        }
        return value;
    }

    private static String string(JsonObject json, String name) {
        return member(json, name).getAsString();
    }

    private static String optionalString(JsonObject json, String name) {
        JsonElement value = json == null ? null : json.get(name);
        return value == null || value.isJsonNull() ? null
                : value.getAsString();
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
        JsonElement value = json == null ? null : json.get(name);
        return value == null || value.isJsonNull() ? null
                : value.getAsJsonObject();
    }
}
