package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import java.io.IOException;
import java.math.BigInteger;
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
 * <p>THE RULE (DESIGN4 §5).  SAT says the model satisfies our formula;
 * CONFIRM says the program agrees: plant the model's root values, hold the
 * selected path's session schedule -- strict prefix to the anchor, timeouts
 * after, exactly what an obligation replay does -- force no flip, run once,
 * and require (a) no SCHEDULE_DIVERGED before the anchor, (b) every edge
 * the model chose is the edge the run took, (c) the fatal observed at the
 * anchor.  This writes what that replay is handed, in the shapes the replay
 * already reads:</p>
 * <ul>
 *   <li>{@code focused_task.jsonl}: an obligation focus row whose {@code
 *       flip} is {@code null}, focused on the anchor, with {@code
 *       rootAssignments} = the model's value of every declared non-clock
 *       root (the valuation's moved value, else its assignment, else the
 *       recorded value the domain pins it to), {@code clockDeltas} = the
 *       model's instant of every moved clock cell minus the reading of the
 *       session that minted it, {@code rootMints} from the recording, no
 *       inherited flips -- flips are not forced, the values decide;</li>
 *   <li>{@code schedule_prefix.jsonl} / {@code schedule_suffix.jsonl}: the
 *       selected session's schedule cut at the anchor;</li>
 *   <li>{@code expected_edges.jsonl}: the edges the model chose -- {@code
 *       WIRE} (consumer endpoint, producer endpoint) per selected message
 *       arm, {@code STATE} (reader endpoint, writer endpoint, version) per
 *       state join of the selected path (the session's own join, or the
 *       writer a selected {@code writer_arm__} names), {@code MARKER}
 *       (root, polarity), {@code ANCHOR} (occurrence, seq).</li>
 * </ul>
 *
 * <p>WHICH PATH AND WHICH ARMS.  {@code claim.json} states the valuation
 * the claim rests on ({@code claim.valuationOrdinal}); that valuation's row
 * names {@code selectedPathId}, {@code selectedSessionId} and {@code
 * selectedArms} -- the arm selectors the sat model set true, which the
 * composer already reads off the model.  Nothing is re-solved.</p>
 *
 * <p>A confirmation nothing can run is refused by name (exit 1, the reason
 * on stderr and in the summary): a moved clock cell no session of the
 * witness minted, a root the recording mints nowhere, a selected session
 * without a target row at the anchor.  The driver reads a refusal as
 * "unconfirmed, because ...".</p>
 */
public final class ConfirmMain {
    /** The one obligation id a confirmation carries. */
    static final String OBLIGATION_ID = "CONFIRM";

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
        String pathId = text(valuation, "selectedPathId");
        String sessionId = text(valuation, "selectedSessionId");
        if (pathId.isEmpty() || sessionId.isEmpty()) {
            throw new Refused("valuation " + ordinal
                    + " selected no path, so there is nothing to confirm");
        }
        OccurrenceAddress anchor =
                OccurrenceAddress.parse(text(claim, "anchor"));
        if (anchor == null) {
            throw new Refused("the claim states no parseable anchor");
        }
        String seedSessionId = text(claim, "seedSessionId");
        // WHICH ARMS ARE THE SELECTED PATH'S.  A family's exactly-one holds
        // under its path's selector, so the arm booleans of every OTHER
        // path are free in the model and z3 may set any of them: the v15
        // hdfs-17899 model sets message_arm__16 beside the selected path
        // 35's own.  The composer names each arm by its path's ordinal
        // (path_selector__N__ / message_arm__N__ / writer_arm__N__), and
        // that ordinal is the join.
        String ordinalOfPath = "";
        for (JsonElement element : array(manifest, "paths")) {
            JsonObject path = element.getAsJsonObject();
            if (pathId.equals(text(path, "pathId"))) {
                ordinalOfPath = ordinalOf(text(path, "selector"));
            }
        }
        if (ordinalOfPath.isEmpty()) {
            throw new Refused("the manifest states no selector for the "
                    + "selected path " + pathId);
        }
        List<JsonObject> arms = new ArrayList<JsonObject>();
        for (JsonElement element : array(valuation, "selectedArms")) {
            JsonObject arm = element.getAsJsonObject();
            if (ordinalOfPath.equals(ordinalOf(text(arm, "selector")))) {
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

        // The model's values.  The valuation's moved roots win, then its
        // assignment, then the recorded value the domain pins an unvaried
        // root to -- ClaimPolicy's own overlay, read the same way.
        Map<String, String> model = new LinkedHashMap<String, String>();
        model.putAll(strings(valuation, "assignment"));
        model.putAll(strings(valuation, "moved"));
        Map<String, String> assignments =
                new LinkedHashMap<String, String>();
        List<JsonObject> markers = new ArrayList<JsonObject>();
        Map<String, String> kinds = new LinkedHashMap<String, String>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            String rootId = text(root, "rootId");
            String kind = text(root, "kind");
            kinds.put(rootId, kind);
            if ("CLOCK".equals(kind)) continue;
            String value = model.containsKey(rootId) ? model.get(rootId)
                    : text(root, "recordedValue");
            if (value.isEmpty()) continue;
            assignments.put(rootId, value);
            if ("MARKER".equals(kind)) {
                JsonObject marker = new JsonObject();
                marker.addProperty("kind", "MARKER");
                marker.addProperty("root", rootId);
                marker.addProperty("value", Boolean.parseBoolean(value));
                markers.add(marker);
            }
        }

        // A clock's counterfactual is a SKEW: the model's instant for the
        // cell minus the reading of the session that minted it, which is
        // the selected session or an arm's.  The claim names the cell by
        // its symbol; the mint row is what joins symbol to root.
        Map<String, RootMintRow> bySymbol =
                new LinkedHashMap<String, RootMintRow>();
        for (RootMintRow row : session.roots()) {
            bySymbol.put(row.symbol(), row);
        }
        Map<String, SessionReader> armSessions =
                new LinkedHashMap<String, SessionReader>();
        armSessions.put(sessionId, session);
        for (JsonObject arm : arms) {
            String armSession = text(arm, "sessionId");
            if (armSession.isEmpty() || armSessions.containsKey(armSession)) {
                continue;
            }
            SessionReader reader = SessionReader.read(iteration, armSession);
            armSessions.put(armSession, reader);
            for (RootMintRow row : reader.roots()) {
                if (!bySymbol.containsKey(row.symbol())) {
                    bySymbol.put(row.symbol(), row);
                }
            }
        }
        Map<String, String> clockDeltas = new LinkedHashMap<String, String>();
        for (Map.Entry<String, String> moved
                : strings(decided, "movedRoots").entrySet()) {
            RootMintRow cell = bySymbol.get(moved.getKey());
            if (cell == null) {
                if (kinds.containsKey(moved.getKey())) continue;
                throw new Refused("the claim moves cell " + moved.getKey()
                        + ", which no session of the witness minted");
            }
            if (!"CLOCK".equals(cell.kind().name())) continue;
            String reading = cell.recordedValue() == null ? ""
                    : cell.recordedValue().trim();
            BigInteger instant;
            BigInteger skew;
            try {
                instant = new BigInteger(moved.getValue().trim());
                skew = instant.subtract(new BigInteger(reading));
            } catch (NumberFormatException notAnInstant) {
                throw new Refused("clock cell " + cell.rootId()
                        + " is moved to " + moved.getValue() + " against a"
                        + " reading of \"" + reading + "\", so no skew can"
                        + " be stated");
            }
            // FAIL CLOSED, as ObligationFactory does: a CLOCK cell is a
            // millisecond count in a Java long, so both the skew the row
            // carries and the instant the mint plants have to be one.
            if (!JavaPrimitiveSmtSemantics.fitsJavaLong(skew)
                    || !JavaPrimitiveSmtSemantics.fitsJavaLong(instant)) {
                throw new Refused("clock cell " + cell.rootId()
                        + " is owed instant " + instant + ", a skew of "
                        + skew + " on the " + reading + " its session read,"
                        + " and a clock is a Java long: no replay could"
                        + " apply it");
            }
            clockDeltas.put(cell.rootId(), skew.toString());
        }

        // Where each root is minted, by the RECORDING -- the same rule an
        // obligation's focus row follows (ObligationFactory): a value is
        // planted at its mint and nowhere else.
        Map<String, String> mints = new LinkedHashMap<String, String>();
        SessionReader seed = SessionReader.read(iteration, seedSessionId);
        Set<String> planted = new LinkedHashSet<String>(assignments.keySet());
        planted.addAll(clockDeltas.keySet());
        for (String rootId : planted) {
            RootMintRow mint = null;
            for (RootMintRow row : seed.roots()) {
                if (row.rootId().equals(rootId)) mint = row;
            }
            if (mint == null) {
                throw new Refused("the model assigns root " + rootId
                        + ", which the recording " + seedSessionId
                        + " mints nowhere, so no occurrence can plant it");
            }
            mints.put(rootId, mint.occurrence().render());
        }

        // The schedule half: the selected session's order, cut at the
        // anchor -- held event by event before it, in its timeouts after.
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

        JsonObject focus = focusRow(anchor, seedSessionId, pathId,
                assignments, clockDeltas, mints, cut);
        // {@code flip: null} IS the row's statement, so the null is written
        // -- the codec's Gson drops nulls, and a row with no flip member is
        // no obligation at all to the replay.
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

    /** The focus row: an obligation that flips nothing. */
    private static JsonObject focusRow(OccurrenceAddress anchor,
                                       String seedSessionId, String pathId,
                                       Map<String, String> assignments,
                                       Map<String, String> clockDeltas,
                                       Map<String, String> mints,
                                       SchedulePrefix.Cut cut) {
        JsonObject task = new JsonObject();
        task.addProperty("schemaVersion", 1);
        task.addProperty("kind", "FOCUSED_TASK");
        task.addProperty("taskId", OBLIGATION_ID);
        task.addProperty("focused", anchor.render());
        task.addProperty("focusedOccurrenceId", anchor.id());
        task.addProperty("seedSessionId", seedSessionId);
        task.add("factor", new JsonArray());
        task.addProperty("obligationId", OBLIGATION_ID);
        task.addProperty("pathId", pathId);
        // NO FLIP: the values drive every decision, and the replay reads
        // {@code flip: null} as "nothing is owed at any decision".
        task.add("flip", null);
        task.add("inheritedFlips", new JsonArray());
        task.add("rootAssignments", object(assignments));
        task.add("clockDeltas", object(clockDeltas));
        task.add("answers", new JsonObject());
        task.add("rootMints", object(mints));
        task.add("unproducible", new JsonArray());
        task.add("schedulePrefix", cut.toJson());
        return task;
    }

    /**
     * One WIRE edge per consumer of every selected message arm: the
     * producer is the export that arm's own session paired the consumer
     * with, which its attach row states.
     */
    private static List<JsonObject> wireEdges(
            List<JsonObject> arms, Map<String, SessionReader> armSessions) {
        List<JsonObject> edges = new ArrayList<JsonObject>();
        for (JsonObject arm : arms) {
            if (!text(arm, "selector").startsWith("message_arm__")) continue;
            SessionReader producerSession =
                    armSessions.get(text(arm, "sessionId"));
            if (producerSession == null) continue;
            for (JsonElement consumer : array(arm, "attachEndpointIds")) {
                String consumerId = consumer.getAsString();
                AttachRow paired = null;
                for (AttachRow row : producerSession.attaches()) {
                    if (row.endpoint().id().equals(consumerId)) paired = row;
                }
                if (paired == null || paired.producer() == null) {
                    throw new Refused("selected arm " + text(arm, "selector")
                            + " names consumer " + consumerId + ", which "
                            + "session " + text(arm, "sessionId")
                            + " states no paired attach for");
                }
                JsonObject edge = new JsonObject();
                edge.addProperty("kind", "WIRE");
                edge.addProperty("consumer", consumerId);
                edge.addProperty("producer", paired.producer().id());
                edge.addProperty("selector", text(arm, "selector"));
                edges.add(edge);
            }
        }
        return edges;
    }

    /**
     * One STATE edge per state join of the selected path: the reads of the
     * occurrences the anchor's joins reach (Composer's P3 closure, the same
     * rule over the same rows), each joined to the write of the same
     * session whose version it observed -- unless a selected {@code
     * writer_arm__} names another writer for that reader, in which case
     * the model's choice is the edge.
     */
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
        // The closure: occurrence id -> the seq its prefix reaches up to.
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
        // The model's own writer choices, where a location had
        // alternatives: a selected {@code writer_arm__} names its writer
        // ({@code groupId}) and the STATE interactions it fills, each the
        // id of (writer endpoint, reader endpoint) -- the same id the arm
        // was keyed by ({@code smt.Arms#stateArms}), recomputed here over
        // this session's writers and the joined readers.
        Map<String, Endpoint> writers = new LinkedHashMap<String, Endpoint>();
        for (WriteRow write : session.writes()) {
            writers.put(write.endpoint().id(), write.endpoint());
        }
        Map<String, String> chosen = new LinkedHashMap<String, String>();
        for (JsonObject arm : arms) {
            if (!text(arm, "selector").startsWith("writer_arm__")) continue;
            Endpoint writer = writers.get(text(arm, "groupId"));
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
            JsonObject edge = new JsonObject();
            edge.addProperty("kind", "STATE");
            edge.addProperty("reader", join.getKey());
            String writer = chosen.containsKey(join.getKey())
                    ? chosen.get(join.getKey())
                    : join.getValue().endpoint().id();
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

    /** One write the path rests on: its writer reached, its state swept. */
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

    private static JsonArray array(JsonObject json, String member) {
        return json.has(member) && json.get(member).isJsonArray()
                ? json.getAsJsonArray(member) : new JsonArray();
    }

    private static String text(JsonObject json, String member) {
        return json.has(member) && !json.get(member).isJsonNull()
                ? json.get(member).getAsString() : "";
    }

    private static Map<String, String> strings(JsonObject json,
                                               String member) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        if (!json.has(member) || !json.get(member).isJsonObject()) {
            return values;
        }
        for (Map.Entry<String, JsonElement> entry
                : json.getAsJsonObject(member).entrySet()) {
            values.put(entry.getKey(), entry.getValue().getAsString());
        }
        return values;
    }

    private static JsonObject object(Map<String, String> values) {
        JsonObject json = new JsonObject();
        for (Map.Entry<String, String> entry : values.entrySet()) {
            json.addProperty(entry.getKey(), entry.getValue());
        }
        return json;
    }
}
