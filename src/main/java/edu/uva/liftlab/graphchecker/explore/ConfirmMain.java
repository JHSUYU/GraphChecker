package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
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

/**
 * CONFIRM: one focused replay that asks the program whether it agrees with
 * a SAT claim's model.
 *
 * <pre>
 *   --iteration &lt;dir&gt;   the iteration whose sessions the claim composed
 *   --claim &lt;file&gt;      final/claim.json
 *   --manifest &lt;file&gt;   final/candidate_composition_manifest.json
 *   --output &lt;dir&gt;      the worker directory the replay is run from
 * </pre>
 *
 * <p>THE RULE (DESIGN4 §5). SAT says the model satisfies our formula; CONFIRM
 * says the program agrees: re-run the world the selected path's own session ran
 * (its planted roots, clock skews, answers) with no flip forced, hold that
 * session's schedule (prefix to the anchor, timeouts after), and require (a)
 * every edge the model chose is taken and (b) the fatal at the anchor. The
 * model's instants are the published witness, not what the run is held to
 * (solvers sit on boundaries). Written, in shapes the replay already reads:</p>
 * <ul>
 *   <li>{@code focused_task.jsonl}: a focus row with {@code flip: null} on
 *       the anchor, the selected session's obligation world, no inherited
 *       flips;</li>
 *   <li>{@code schedule_prefix.jsonl} / {@code schedule_suffix.jsonl};</li>
 *   <li>{@code expected_edges.jsonl}: {@code WIRE} per selected message
 *       arm, {@code STATE} per model-chosen writer, {@code MARKER} per planted
 *       marker, {@code ANCHOR}.</li>
 * </ul>
 *
 * <p>The path and arms come from the claim's valuation ({@code selectedPathId},
 * {@code selectedSessionId}, {@code selectedArms}); nothing is re-solved. An
 * unrunnable confirmation is refused by name (exit 1), which the driver reads
 * as "unconfirmed, because ...".</p>
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
        Map<String, String> options = ExploreMain.options(argv);
        Path iteration = ExploreMain.path(options, "iteration");
        Path claim = ExploreMain.path(options, "claim");
        Path manifest = ExploreMain.path(options, "manifest");
        Path out = ExploreMain.path(options, "output");
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
        JsonObject claim = json(claimFile);
        JsonObject manifest = json(manifestFile);
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
            JsonObject confirmation = new JsonObject();
            confirmation.addProperty("schemaVersion", 1);
            confirmation.addProperty("kind", "CONFIRMATION");
            confirmation.addProperty("confirmed", true);
            confirmation.addProperty("reason", realized);
            confirmation.addProperty("sessionId", sessionId);
            RowCodec.writeJsonl(out.resolve(REALIZED),
                    Collections.singletonList(confirmation));
            JsonObject summary = new JsonObject();
            summary.addProperty("kind", "CONFIRM_TASK");
            summary.addProperty("anchor", anchor.id());
            summary.addProperty("selectedPathId", pathId);
            summary.addProperty("selectedSessionId", sessionId);
            summary.addProperty("valuationOrdinal", ordinal);
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

        // The schedule half (SchedulePrefix).
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration, sessionId,
                Collections.singletonList(anchor.id()), out);
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
        RowCodec.writeJsonl(
                out.resolve(edu.uva.liftlab.graphchecker.runtime
                        .Confirmation.FILE), edges);

        // An obligation that flips nothing: the values drive every decision.
        JsonObject focus = ExploreCodec.writeFocusRow(anchor, seedSessionId,
                Collections.<OccurrenceAddress>emptyList(),
                Obligation.confirming(OBLIGATION_ID, OBLIGATION_ID, pathId,
                        assignments, answers, Collections.<String>emptyList()),
                Collections.<Corpus.Flip>emptyList(), clockDeltas, mints, cut);
        // {@code flip: null} is the statement: serialize nulls.
        Files.write(out.resolve(ObligationDir.FOCUSED_TASK),
                (new GsonBuilder().serializeNulls().create().toJson(focus)
                        + "\n").getBytes(StandardCharsets.UTF_8));

        JsonObject summary = new JsonObject();
        summary.addProperty("kind", "CONFIRM_TASK");
        summary.addProperty("anchor", anchor.id());
        summary.addProperty("selectedPathId", pathId);
        summary.addProperty("selectedSessionId", sessionId);
        summary.addProperty("valuationOrdinal", ordinal);
        summary.addProperty("rootAssignments", assignments.size());
        summary.addProperty("clockDeltas", clockDeltas.size());
        summary.addProperty("expectedEdges", edges.size());
        summary.add("schedulePrefix", cut.toJson());
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
        for (WriteRow write : session.writes()) {
            String location = location(write.location().kind().name(),
                    write.location().owner(), write.location().slot());
            writes.put(location + "@" + write.version(), write);
            List<WriteRow> under = byLocation.get(location);
            if (under == null) {
                under = new ArrayList<WriteRow>();
                byLocation.put(location, under);
            }
            under.add(write);
        }
        Map<String, List<ReadRow>> readsOn =
                new LinkedHashMap<String, List<ReadRow>>();
        for (ReadRow read : session.reads()) {
            String at = read.endpoint().occurrence().id();
            List<ReadRow> on = readsOn.get(at);
            if (on == null) {
                on = new ArrayList<ReadRow>();
                readsOn.put(at, on);
            }
            on.add(read);
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
                boolean whole = anchor.id().equals(at);
                long cut = reached.get(at);
                List<ReadRow> on = readsOn.get(at);
                if (on == null) continue;
                for (ReadRow read : on) {
                    if (!whole && read.seq() >= cut) continue;
                    if (read.observedVersion() < 0L) continue;
                    WriteRow write = writes.get(location(
                            read.location().kind().name(),
                            read.location().owner(),
                            read.location().slot()) + "@"
                            + read.observedVersion());
                    if (write == null) continue;
                    joined.put(read.endpoint().id(), write);
                    readers.put(read.endpoint().id(), read);
                    reach(write, anchor, reached, pending, versions, handled);
                }
            }
            if (versions.isEmpty()) continue;
            WriteRow write = versions.remove(0);
            String location = location(write.location().kind().name(),
                    write.location().owner(), write.location().slot());
            for (WriteRow under : byLocation.get(location)) {
                if (under.version() >= write.version()) continue;
                reach(under, anchor, reached, pending, versions, handled);
            }
        }
        // The model's writer choices: a writer_arm__ names its writer (groupId)
        // and the STATE interaction ids it fills ({@code smt.Arms#stateArms}).
        Map<String, Endpoint> writers = new LinkedHashMap<String, Endpoint>();
        for (WriteRow write : session.writes()) {
            writers.put(write.endpoint().id(), write.endpoint());
        }
        Map<String, String> chosen = new LinkedHashMap<String, String>();
        for (JsonObject arm : arms) {
            if (!optionalString(arm, "selector").startsWith("writer_arm__")) {
                continue;
            }
            Endpoint writer = writers.get(optionalString(arm, "groupId"));
            if (writer == null) continue;
            Set<String> fills = new LinkedHashSet<String>();
            for (JsonElement id : array(arm, "interactionIds")) {
                fills.add(id.getAsString());
            }
            for (ReadRow read : readers.values()) {
                if (fills.contains(Interaction.of(InteractionKind.STATE,
                        writer, read.endpoint()).id())) {
                    chosen.put(read.endpoint().id(), writer.id());
                }
            }
        }
        List<JsonObject> edges = new ArrayList<JsonObject>();
        for (Map.Entry<String, WriteRow> join : joined.entrySet()) {
            // Only model choices: single-writer joins are pinned by the
            // formula, and rule (b) checks they still lead to the fatal.
            if (!chosen.containsKey(join.getKey())) continue;
            JsonObject edge = new JsonObject();
            edge.addProperty("kind", "STATE");
            edge.addProperty("reader", join.getKey());
            // A mint read lands on whichever racing occurrence reads the cell
            // first, so it is held by the writer (runtime/Confirmation), not
            // the reader.
            edge.addProperty("mint", readers.get(join.getKey())
                    .mintVersion() != ReadRow.UNKNOWN_VERSION);
            String writer = chosen.get(join.getKey());
            edge.addProperty("writer", writer);
            edge.addProperty("version", join.getValue().version());
            edge.addProperty("location", location(
                    join.getValue().location().kind().name(),
                    join.getValue().location().owner(),
                    join.getValue().location().slot()));
            edges.add(edge);
        }
        return edges;
    }

    /** One write the path rests on: reach its writer, sweep older versions. */
    private static void reach(WriteRow write, OccurrenceAddress anchor,
                              Map<String, Long> reached, List<String> pending,
                              List<WriteRow> versions, Set<String> handled) {
        String writer = write.endpoint().occurrence().id();
        // Never the anchor: its cutoff is the target observation.
        if (anchor.id().equals(writer)) return;
        if (handled.add(location(write.location().kind().name(),
                write.location().owner(), write.location().slot()) + "@"
                + write.version())) {
            versions.add(write);
        }
        Long held = reached.get(writer);
        if (held != null && held.longValue() >= write.seq()) return;
        reached.put(writer, write.seq());
        pending.add(writer);
    }

    private static String location(String kind, String owner, String slot) {
        return kind + "/" + owner + "#" + slot;
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

    private static JsonObject json(Path file) throws IOException {
        return JsonParser.parseString(new String(Files.readAllBytes(file),
                StandardCharsets.UTF_8)).getAsJsonObject();
    }
}
