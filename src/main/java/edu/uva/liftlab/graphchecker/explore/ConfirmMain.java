package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.strings;

/**
 * CONFIRM: one focused replay that asks the program whether it agrees with
 * a SAT claim's model.
 *
 * <pre>
 *   --iteration &lt;dir&gt;   the iteration whose sessions the claim composed
 *   --claim &lt;file&gt;      final/claim.json
 *   --manifest &lt;file&gt;   final/candidate_composition_manifest.json
 *   --output &lt;dir&gt;      the worker directory the replay is run from
 *
 *   once the replay has published, the decision ({@link #decide}), printed
 *   as final/confirm.json:
 *   --claim &lt;file&gt; --output &lt;dir&gt; --sessions &lt;dir&gt;
 * </pre>
 *
 * <p>THE RULE (PIPELINE §10). SAT says the model satisfies our formula;
 * CONFIRM says the program agrees: re-run the world the selected path's own
 * session ran (its planted roots, clock skews, answers) overlaid with the
 * model's moved roots ({@link #plantModel}), with no flip forced, and require
 * (a) every edge the model chose is taken and (b) the fatal at the anchor.
 * The schedule is written UNHELD ({@link SchedulePrefix#write} with {@code
 * held} false): every event is the rest, only a WAKE still waits for what it
 * followed; the model's order is held by the {@code ORDER} rows of
 * {@code expected_edges.jsonl} ({@code runtime.Confirmation}). The model's
 * instants are the published witness, not what the run is held to (solvers
 * sit on boundaries). Written, in shapes the replay already reads:</p>
 * <ul>
 *   <li>{@code focused_task.jsonl}: a focus row with {@code flip: null} on
 *       the anchor, the selected session's obligation world, no inherited
 *       flips;</li>
 *   <li>{@code schedule_prefix.jsonl} (empty) / {@code
 *       schedule_suffix.jsonl} (the whole schedule);</li>
 *   <li>{@code expected_edges.jsonl}: {@code WIRE} per consumer of each
 *       selected message arm, {@code STATE} per read of the anchor's join
 *       closure (the writer the model chose, else the observed one), {@code
 *       ORDER} per held join (the writer's activation before the reader's;
 *       every other writer of the location before the writer or after the
 *       reader), {@code MARKER} per planted marker, {@code ANCHOR}.</li>
 * </ul>
 *
 * <p>The path and arms come from the claim's valuation ({@code selectedPathId},
 * {@code selectedSessionId}, {@code selectedArms}); nothing is re-solved. An
 * unrunnable confirmation is refused by name (exit 1), which the driver reads
 * as "unconfirmed, because ...".</p>
 *
 * <p>The decision ({@code --sessions}): confirmed iff the replay was ADMITTED,
 * its session published a readable gaps file with no {@code
 * CONFIRM_MISMATCH}, and a target row at the claim's own anchor occurrence id
 * reached it and observed the fatal.</p>
 */
public final class ConfirmMain {
    /** The one obligation id a confirmation carries. */
    static final String OBLIGATION_ID = "CONFIRM";
    /** Written instead of a replay when the selected session already realized
     *  the claim ({@link #realizedBy}). */
    static final String REALIZED = "realized.json";

    private ConfirmMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path iteration = options.path("iteration");
        Path claim = options.path("claim");
        Path manifest = options.path("manifest");
        Path out = options.path("output");
        Path sessions = options.path("sessions");
        if (sessions != null && claim != null && out != null) {
            System.out.println(ExploreMain.pretty(
                    decide(claim, out, sessions)));
            return;
        }
        if (iteration == null || claim == null || manifest == null
                || out == null) {
            throw new IllegalArgumentException("--iteration, --claim, "
                    + "--manifest and --output are required");
        }
        JsonObject summary;
        try {
            summary = write(iteration, claim, manifest, out);
        } catch (Refused refused) {
            System.err.println("CONFIRM refused: " + refused.getMessage());
            JsonObject row = new JsonObject();
            row.addProperty("kind", "CONFIRM_REFUSED");
            row.addProperty("reason", refused.getMessage());
            System.out.println(ExploreMain.pretty(row));
            System.exit(1);
            return;
        }
        System.out.println(ExploreMain.pretty(summary));
    }

    /** A confirmation nothing can run, named. */
    static final class Refused extends RuntimeException {
        Refused(String reason) {
            super(reason);
        }
    }

    /** Writes the worker's three inputs; returns what was written. */
    static JsonObject write(Path iteration, Path claimFile,
                            Path manifestFile, Path out) throws IOException {
        Files.createDirectories(out);
        JsonObject claim = ExploreCodec.readObject(claimFile);
        JsonObject manifest = ExploreCodec.readObject(manifestFile);
        JsonObject decided = claim.getAsJsonObject("claim");
        int ordinal = decided.get("valuationOrdinal").getAsInt();
        JsonObject valuation = valuation(claim, ordinal);
        String pathId = optionalString(valuation, "selectedPathId");
        String sessionId = optionalString(valuation, "selectedSessionId");
        if (pathId.isEmpty() || sessionId.isEmpty()) {
            throw new Refused("valuation " + ordinal
                    + " selected no path, so there is nothing to confirm");
        }
        OccurrenceAddress anchor =
                OccurrenceAddress.parse(optionalString(claim, "anchor"));
        if (anchor == null) {
            throw new Refused("the claim states no parseable anchor");
        }
        String seedSessionId = optionalString(claim, "seedSessionId");
        // Only the selected path's arms (others are free in the model),
        // joined by the path ordinal in the composer's selector names.
        String ordinalOfPath = "";
        for (JsonElement element : array(manifest, "paths")) {
            JsonObject path = element.getAsJsonObject();
            if (pathId.equals(optionalString(path, "pathId"))) {
                ordinalOfPath = ordinalOf(optionalString(path, "selector"));
            }
        }
        if (ordinalOfPath.isEmpty()) {
            throw new Refused("the manifest states no selector for the "
                    + "selected path " + pathId);
        }
        List<JsonObject> arms = new ArrayList<JsonObject>();
        for (JsonElement element : array(valuation, "selectedArms")) {
            JsonObject arm = element.getAsJsonObject();
            if (ordinalOfPath.equals(
                    ordinalOf(optionalString(arm, "selector")))) {
                arms.add(arm);
            }
        }
        SessionReader session = SessionReader.read(iteration, sessionId);
        TargetRow target = null;
        for (TargetRow row : session.targets()) {
            if (row.occurrence().id().equals(anchor.id())
                    && row.reachedAnchor()) {
                target = row;
            }
        }
        if (target == null) {
            throw new Refused("the selected session " + sessionId
                    + " states no target row at the anchor " + anchor.id());
        }
        // A session that already took every chosen edge at the model's root
        // values and observed the fatal IS the confirmation; re-running it only
        // tests a race twice. A model mixing sessions' deliveries needs the
        // replay below.
        String realized = realizedBy(decided, sessionId, arms, session,
                target);
        if (!realized.isEmpty()) {
            RowCodec.writeJsonl(out.resolve(REALIZED),
                    Collections.singletonList(
                            confirmation(true, realized, sessionId)));
            JsonObject summary = summary(anchor, pathId, sessionId, ordinal);
            summary.addProperty("realizedBy", sessionId);
            return summary;
        }

        // The selected path's world, values only, nothing forced.
        JsonObject world = obligationWorld(iteration, sessionId);
        Map<String, String> assignments =
                ExploreCodec.map(object(world, "rootAssignments"));
        Map<String, String> clockDeltas =
                ExploreCodec.map(object(world, "clockDeltas"));
        Map<String, String> mints =
                ExploreCodec.map(object(world, "rootMints"));
        Map<String, String> answers =
                ExploreCodec.map(object(world, "answers"));
        plantModel(decided, session,
                SessionReader.read(iteration, seedSessionId), assignments,
                clockDeltas, mints);
        List<JsonObject> markers = markerEdges(manifest, assignments);
        Map<String, SessionReader> armSessions =
                new LinkedHashMap<String, SessionReader>();
        armSessions.put(sessionId, session);
        for (JsonObject arm : arms) {
            String armSession = optionalString(arm, "sessionId");
            if (armSession.isEmpty() || armSessions.containsKey(armSession)) {
                continue;
            }
            armSessions.put(armSession, SessionReader.read(iteration,
                    armSession));
        }

        // The schedule half: the recorded order is not held (only a WAKE
        // still waits for what it followed); the model's order is held by
        // the ORDER rows below.
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration, sessionId,
                Collections.singletonList(anchor.id()), false, out);
        if (cut == null) {
            throw new Refused("the selected session " + sessionId
                    + " states no schedule to hold the confirmation to");
        }

        // The edges the model chose.
        List<JsonObject> edges = new ArrayList<JsonObject>();
        edges.addAll(wireEdges(arms, armSessions));
        edges.addAll(stateEdges(session, anchor, target.seq(), arms));
        edges.addAll(markers);
        JsonObject anchorRow = new JsonObject();
        anchorRow.addProperty("kind", "ANCHOR");
        anchorRow.addProperty("occurrence", anchor.id());
        anchorRow.addProperty("seq", target.seq());
        edges.add(anchorRow);
        RowCodec.writeJsonl(out.resolve(Confirmation.FILE), edges);

        // An obligation that flips nothing: the values drive every decision.
        JsonObject focus = ExploreCodec.writeFocusRow(anchor, anchor,
                seedSessionId,
                Collections.<OccurrenceAddress>emptyList(),
                Obligation.confirming(OBLIGATION_ID, OBLIGATION_ID, pathId,
                        assignments, answers, Collections.<String>emptyList()),
                Collections.<Corpus.Flip>emptyList(), clockDeltas, mints, cut);
        // {@code flip: null} is the statement: serialize nulls.
        Files.write(out.resolve(ObligationDir.FOCUSED_TASK),
                (new GsonBuilder().serializeNulls().create().toJson(focus)
                        + "\n").getBytes(StandardCharsets.UTF_8));

        JsonObject summary = summary(anchor, pathId, sessionId, ordinal);
        summary.addProperty("rootAssignments", assignments.size());
        summary.addProperty("clockDeltas", clockDeltas.size());
        summary.addProperty("expectedEdges", edges.size());
        summary.add("schedulePrefix", cut.toJson());
        return summary;
    }

    /**
     * The MODEL's world over the session's: a root the model moved off the
     * value this session ran -- a clock DECIDE left free at the recorded
     * valuation, which no replay moved -- is planted as an exploration
     * plants it (ObligationFactory): a clock as the skew off this session's
     * reading, any other root as the value, at the occurrence the recording
     * mints it.  Otherwise the replay runs the session again, not the claim.
     */
    static void plantModel(JsonObject decided, SessionReader session,
                           SessionReader recording,
                           Map<String, String> assignments,
                           Map<String, String> clockDeltas,
                           Map<String, String> mints) {
        JsonObject moved = object(decided, "movedRoots");
        for (RootMintRow row : session.roots()) {
            JsonElement value = moved.has(row.symbol())
                    ? moved.get(row.symbol()) : moved.get(row.rootId());
            if (value == null || value.isJsonNull()) continue;
            String model = value.getAsString().trim();
            if (row.kind() == RootKind.CLOCK) {
                String skew = ObligationFactory.skew(model,
                        row.recordedValue());
                if (skew.isEmpty()) continue;
                clockDeltas.put(row.rootId(), skew);
            } else {
                assignments.put(row.rootId(), model);
            }
            for (RootMintRow mint : recording.roots()) {
                if (mint.rootId().equals(row.rootId())) {
                    mints.put(row.rootId(), mint.occurrence().render());
                    break;
                }
            }
        }
    }

    /**
     * The decision, off the session the confirmation replay published: the
     * rule's conditions in order, the first one failing named.  The replay
     * was ADMITTED (roots planted); (a) its session published its gaps and
     * none is a CONFIRM_MISMATCH -- a session that published no readable
     * gaps answers nothing; (b) a target row AT THE CLAIM'S ANCHOR reached it
     * and observed the fatal.  A fatal at another occurrence of the target
     * site is another question (11741 v93's confirming session had two fatal
     * target rows), and an occurrence is named by its id, which only this
     * address computes.
     */
    static JsonObject decide(Path claimFile, Path worker, Path sessions)
            throws IOException {
        List<JsonObject> results =
                RowCodec.readJsonl(worker.resolve(ObligationDir.RESULT));
        JsonObject result = results.isEmpty() ? new JsonObject()
                : results.get(0);
        String verdict = optionalString(result, "verdict");
        String sessionId = optionalString(result, "sessionId");
        if (!"ADMITTED".equals(verdict)) {
            return confirmation(false, "the confirmation replay was "
                    + (verdict.isEmpty() ? "not run" : verdict) + ": "
                    + optionalString(result, "detail"), sessionId);
        }
        Path session = sessions.resolve(sessionId);
        if (sessionId.isEmpty() || !Files.isDirectory(session)) {
            return confirmation(false, "the confirmation replay names session "
                    + sessionId + ", which " + sessions + " does not hold",
                    sessionId);
        }
        List<JsonObject> gaps;
        List<TargetRow> targets;
        try {
            gaps = published(session.resolve(SessionDir.GAPS));
            targets = new ArrayList<TargetRow>();
            for (JsonObject row
                    : published(session.resolve(SessionDir.TARGETS))) {
                targets.add(RowCodec.readTarget(row));
            }
        } catch (IOException | RuntimeException unread) {
            return confirmation(false, "the run's session could not be read,"
                    + " so it answers nothing: " + unread.getMessage(),
                    sessionId);
        }
        for (JsonObject gap : gaps) {
            if ("CONFIRM_MISMATCH".equals(optionalString(gap, "kind"))) {
                return confirmation(false, "the run took an edge the model"
                        + " did not choose: " + optionalString(gap, "detail"),
                        sessionId);
            }
        }
        OccurrenceAddress anchor;
        try {
            anchor = OccurrenceAddress.parse(optionalString(
                    ExploreCodec.readObject(claimFile), "anchor"));
        } catch (RuntimeException unparsed) {
            return confirmation(false, "the claim states no parseable anchor: "
                    + unparsed.getMessage(), sessionId);
        }
        int elsewhere = 0;
        for (TargetRow target : targets) {
            if (!target.reachedAnchor() || !target.observedFatal()) continue;
            if (target.occurrence().id().equals(anchor.id())) {
                return confirmation(true, "every edge the model chose was"
                        + " taken, and the claim's anchor observed the fatal",
                        sessionId);
            }
            elsewhere++;
        }
        return confirmation(false, "the run published no target row at the"
                + " claim's anchor " + anchor.id() + " that reached it and"
                + " observed the fatal" + (elsewhere == 0 ? ""
                : " (" + elsewhere + " row(s) at other occurrences did)"),
                sessionId);
    }

    /** A session file's rows; one the replay did not publish is refused (its
     *  publisher creates every file at open, so absent is "not published"). */
    private static List<JsonObject> published(Path file) throws IOException {
        if (!Files.isReadable(file)) {
            throw new IOException("it published no readable " + file);
        }
        return RowCodec.readJsonl(file);
    }

    /** The one shape of final/confirm.json. */
    private static JsonObject confirmation(boolean confirmed, String reason,
                                           String sessionId) {
        JsonObject confirmation = new JsonObject();
        confirmation.addProperty("schemaVersion", 1);
        confirmation.addProperty("kind", "CONFIRMATION");
        confirmation.addProperty("confirmed", confirmed);
        confirmation.addProperty("reason", reason);
        confirmation.addProperty("sessionId", sessionId);
        return confirmation;
    }

    /** What either kind of confirmation task states first. */
    private static JsonObject summary(OccurrenceAddress anchor, String pathId,
                                      String sessionId, int ordinal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("kind", "CONFIRM_TASK");
        summary.addProperty("anchor", anchor.id());
        summary.addProperty("selectedPathId", pathId);
        summary.addProperty("selectedSessionId", sessionId);
        summary.addProperty("valuationOrdinal", ordinal);
        return summary;
    }

    /** Why the selected session is itself the confirming run, or "": all chosen
     *  arms are its own deliveries, it observed the fatal, and it minted every
     *  moved root (by root id or symbol) at the model's value. */
    static String realizedBy(JsonObject decided, String sessionId,
                             List<JsonObject> arms, SessionReader session,
                             TargetRow target) {
        if (!target.observedFatal()) return "";
        for (JsonObject arm : arms) {
            if (!sessionId.equals(optionalString(arm, "sessionId"))) return "";
        }
        Map<String, String> ran = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            ran.put(row.rootId(), row.recordedValue());
            ran.put(row.symbol(), row.recordedValue());
        }
        JsonObject moved = object(decided, "movedRoots");
        for (Map.Entry<String, JsonElement> root : moved.entrySet()) {
            String value = ran.get(root.getKey());
            if (value == null || !value.trim().equalsIgnoreCase(
                    root.getValue().getAsString().trim())) {
                return "";
            }
        }
        return "the selected session " + sessionId + " is itself the run: "
                + "it took every edge the model chose (" + arms.size()
                + " arm(s), all its own deliveries), ran "
                + (moved.size() == 0 ? "no moved root"
                : "every moved root at the model's value")
                + ", and observed the fatal at the anchor";
    }

    /** The focus row of the obligation whose replay is {@code sessionId}; empty
     *  for the recording. */
    static JsonObject obligationWorld(Path iteration, String sessionId)
            throws IOException {
        for (ObligationDir worker : ObligationDir.workersIn(iteration)) {
            if (!sessionId.equals(worker.sessionId())) continue;
            List<JsonObject> rows = RowCodec.readJsonl(
                    worker.dir().resolve(ObligationDir.FOCUSED_TASK));
            if (!rows.isEmpty()) return rows.get(0);
        }
        return new JsonObject();
    }

    /** One MARKER edge per planted marker root the manifest names. */
    private static List<JsonObject> markerEdges(
            JsonObject manifest, Map<String, String> assignments) {
        List<JsonObject> markers = new ArrayList<JsonObject>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            String rootId = optionalString(root, "rootId");
            if (!"MARKER".equals(optionalString(root, "kind"))
                    || !assignments.containsKey(rootId)) {
                continue;
            }
            JsonObject marker = new JsonObject();
            marker.addProperty("kind", "MARKER");
            marker.addProperty("root", rootId);
            marker.addProperty("value",
                    Boolean.parseBoolean(assignments.get(rootId)));
            markers.add(marker);
        }
        return markers;
    }

    /** One WIRE edge per consumer of each selected message arm, paired as that
     *  arm's session recorded. */
    private static List<JsonObject> wireEdges(
            List<JsonObject> arms, Map<String, SessionReader> armSessions) {
        List<JsonObject> edges = new ArrayList<JsonObject>();
        for (JsonObject arm : arms) {
            String selector = optionalString(arm, "selector");
            if (!selector.startsWith("message_arm__")) continue;
            SessionReader producerSession =
                    armSessions.get(optionalString(arm, "sessionId"));
            if (producerSession == null) continue;
            for (JsonElement consumer : array(arm, "attachEndpointIds")) {
                String consumerId = consumer.getAsString();
                AttachRow paired = null;
                for (AttachRow row : producerSession.attaches()) {
                    if (row.endpoint().id().equals(consumerId)) paired = row;
                }
                if (paired == null || paired.producer() == null) {
                    throw new Refused("selected arm " + selector
                            + " names consumer " + consumerId + ", which "
                            + "session " + optionalString(arm, "sessionId")
                            + " states no paired attach for");
                }
                JsonObject edge = new JsonObject();
                edge.addProperty("kind", "WIRE");
                edge.addProperty("consumer", consumerId);
                edge.addProperty("producer", paired.producer().id());
                edge.addProperty("selector", selector);
                edges.add(edge);
            }
        }
        return edges;
    }

    /** STATE edges where the MODEL CHOSE the writer: reads in the anchor's join
     *  closure (the Composer's P3 rule) whose selected {@code writer_arm__}
     *  names their writer. */
    private static List<JsonObject> stateEdges(SessionReader session,
                                               OccurrenceAddress anchor,
                                               long cutoff,
                                               List<JsonObject> arms) {
        Map<String, WriteRow> writes = new LinkedHashMap<String, WriteRow>();
        Map<String, List<WriteRow>> byLocation =
                new LinkedHashMap<String, List<WriteRow>>();
        Map<String, Endpoint> writers = new LinkedHashMap<String, Endpoint>();
        for (WriteRow write : session.writes()) {
            writes.put(version(write.location(), write.version()), write);
            writers.put(write.endpoint().id(), write.endpoint());
            byLocation.computeIfAbsent(location(write.location()),
                    key -> new ArrayList<WriteRow>()).add(write);
        }
        Map<String, List<ReadRow>> readsOn =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : session.reads()) {
            readsOn.computeIfAbsent(read.endpoint().occurrence().id(),
                    key -> new ArrayList<ReadRow>()).add(read);
        }
        // Closure: occurrence id -> the seq its prefix reaches.
        Map<String, Long> reached = new LinkedHashMap<String, Long>();
        reached.put(anchor.id(), cutoff);
        List<String> pending = new ArrayList<String>();
        pending.add(anchor.id());
        List<WriteRow> versions = new ArrayList<WriteRow>();
        Set<String> handled = new LinkedHashSet<String>();
        Map<String, WriteRow> joined = new LinkedHashMap<String, WriteRow>();
        Map<String, ReadRow> readers = new LinkedHashMap<String, ReadRow>();
        while (!pending.isEmpty() || !versions.isEmpty()) {
            while (!pending.isEmpty()) {
                String at = pending.remove(0);
                long cut = reached.get(at);
                List<ReadRow> on = readsOn.get(at);
                if (on == null) continue;
                for (ReadRow read : on) {
                    // The anchor's too, unlike Composer#closure, which joins
                    // all its reads as its inputs: a run that takes the fatal
                    // arm throws there, and no edge after it can be taken
                    // (adhoc token-pw-expired: the key map is read after the
                    // expiry check).
                    if (read.seq() >= cut) continue;
                    if (read.observedVersion() < 0L) continue;
                    WriteRow write = writes.get(version(read.location(),
                            read.observedVersion()));
                    // A version no row wrote (a store outside every region)
                    // joins nothing; the model may still choose its writer.
                    readers.put(read.endpoint().id(), read);
                    if (write == null) continue;
                    joined.put(read.endpoint().id(), write);
                    reach(write, anchor, reached, pending, versions, handled);
                }
            }
            if (versions.isEmpty()) continue;
            WriteRow write = versions.remove(0);
            for (WriteRow under : byLocation.get(location(write.location()))) {
                if (under.version() >= write.version()) continue;
                reach(under, anchor, reached, pending, versions, handled);
            }
        }
        // The model's writer choices: a writer_arm__ fills STATE interactions
        // ({@code smt.Arms#stateArms}), each one writer endpoint to one read.
        // Not its groupId: that names the writer OCCURRENCE, which is no
        // endpoint this map is keyed by (no real choice was ever held).
        Map<String, String> chosen = new LinkedHashMap<String, String>();
        for (JsonObject arm : arms) {
            if (!optionalString(arm, "selector").startsWith("writer_arm__")) {
                continue;
            }
            Set<String> fills = new LinkedHashSet<String>(
                    strings(arm, "interactionIds"));
            for (ReadRow read : readers.values()) {
                for (WriteRow write : byLocation.getOrDefault(location(
                        read.location()), Collections.<WriteRow>emptyList())) {
                    if (fills.contains(Interaction.of(InteractionKind.STATE,
                            write.endpoint(), read.endpoint()).id())) {
                        chosen.put(read.endpoint().id(),
                                write.endpoint().id());
                    }
                }
            }
        }
        // Every join of the closure, pinned or chosen: the run is held to no
        // recorded order, so a pinned join is the model's as much as a choice.
        // A read no row answers is held only where the model chose a writer
        // for it; otherwise its outside store is the run's own.
        List<JsonObject> edges = new ArrayList<JsonObject>();
        Set<String> orders = new LinkedHashSet<String>();
        for (Map.Entry<String, ReadRow> reader : readers.entrySet()) {
            ReadRow read = reader.getValue();
            WriteRow recorded = joined.get(reader.getKey());
            Endpoint writer = chosen.containsKey(reader.getKey())
                    ? writers.get(chosen.get(reader.getKey()))
                    : recorded == null ? null : recorded.endpoint();
            WriteRow held = writer == null ? null : recorded != null
                    ? recorded : lastBy(byLocation.get(location(
                    read.location())), writer);
            if (held == null) continue;
            JsonObject edge = new JsonObject();
            edge.addProperty("kind", "STATE");
            edge.addProperty("reader", reader.getKey());
            // A mint read lands on whichever racing occurrence reads the cell
            // first, so it is held by the writer (runtime/Confirmation), not
            // the reader.
            boolean mint = read.mintVersion() != ReadRow.UNKNOWN_VERSION;
            edge.addProperty("mint", mint);
            edge.addProperty("writer", writer.id());
            edge.addProperty("version", held.version());
            edge.addProperty("location", location(held.location()));
            edges.add(edge);
            if (mint) continue;
            order(orders, writer, read.endpoint());
            // No other writer of the location between the two: one recorded
            // before the write goes before it, any other after the read.
            for (WriteRow other : byLocation.get(location(held.location()))) {
                if (other.endpoint().equals(writer)) continue;
                if (other.seq() < held.seq()) {
                    order(orders, other.endpoint(), writer);
                } else {
                    order(orders, read.endpoint(), other.endpoint());
                }
            }
        }
        for (String order : orders) {
            String[] ends = order.split("\n", 2);
            JsonObject row = new JsonObject();
            row.addProperty("kind", "ORDER");
            row.addProperty("before", ends[0]);
            row.addProperty("after", ends[1]);
            edges.add(row);
        }
        return edges;
    }

    /** The last write {@code writer} made of a location, of its writes. */
    private static WriteRow lastBy(List<WriteRow> writes, Endpoint writer) {
        WriteRow last = null;
        for (WriteRow write : writes) {
            if (write.endpoint().equals(writer)
                    && (last == null || write.seq() > last.seq())) {
                last = write;
            }
        }
        return last;
    }

    /** {@code first}'s activation exits before {@code then}'s enters, unless
     *  one occurrence holds both: it runs on one thread, whose program order
     *  already orders them (and a nested activation cannot exit before the
     *  one around it enters). */
    private static void order(Set<String> orders, Endpoint first,
                              Endpoint then) {
        if (first.occurrence().id().equals(then.occurrence().id())) return;
        orders.add(first.activation() + "\n" + then.activation());
    }

    /** One write the path rests on: reach its writer, sweep older versions. */
    private static void reach(WriteRow write, OccurrenceAddress anchor,
                              Map<String, Long> reached, List<String> pending,
                              List<WriteRow> versions, Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        // Never the anchor: its cutoff is the target observation.
        if (anchor.id().equals(writer)) return;
        if (handled.add(version(write.location(), write.version()))) {
            versions.add(write);
        }
        Long held = reached.get(writer);
        if (held != null && held.longValue() >= write.seq()) return;
        reached.put(writer, write.seq());
        pending.add(writer);
    }

    private static String location(LocationId location) {
        return location.kind().name() + "/" + location.owner() + "#"
                + location.slot();
    }

    /** One version of one location. */
    private static String version(LocationId location, long version) {
        return location(location) + "@" + version;
    }

    /** The path ordinal a composer selector carries: {@code kind__N__hash}. */
    static String ordinalOf(String selector) {
        String[] parts = selector.split("__", -1);
        return parts.length == 3 ? parts[1] : "";
    }

    /** The valuation row the claim rests on. */
    private static JsonObject valuation(JsonObject claim, int ordinal) {
        for (JsonElement element : array(claim, "valuations")) {
            JsonObject row = element.getAsJsonObject();
            if (row.get("ordinal").getAsInt() == ordinal) return row;
        }
        throw new Refused("the claim rests on valuation " + ordinal
                + ", which it does not state");
    }

}
