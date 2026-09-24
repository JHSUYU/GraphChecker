package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
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
import edu.uva.liftlab.graphchecker.contract.ReadsFrom;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.Task;
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
 * CONFIRM says the program agrees: re-run the world the selected path's own
 * session ran -- the root values, clock skews and answers its obligation
 * planted, proven in an execution -- with no flip forced, holding every
 * read the model rests on to the version the model chose, run once, and
 * require (a) every edge the model chose is the edge the run took and (b)
 * the fatal observed at the anchor.  The model's own instants are the
 * published witness, not what the run is held to: a solver sits on the
 * boundary of its constraints and a run's timeline moves by more than
 * that.  This writes what that replay is handed, in the shapes the replay
 * already reads:</p>
 * <ul>
 *   <li>{@code focused_task.jsonl}: a focus row whose {@code flip} is
 *       {@code null}, focused on the anchor, with {@code rootAssignments},
 *       {@code clockDeltas}, {@code answers} and {@code rootMints} copied
 *       from the focus row of the obligation whose replay is the selected
 *       session, no inherited flips -- flips are not forced, the values
 *       decide -- and the {@code versions} of the selected path's state
 *       joins: the writer a selected {@code writer_arm__} names, and the
 *       recorded writer of a join across threads
 *       ({@link ObligationFactory#held}).  The recording's own session
 *       planted nothing, and nothing is planted for it;</li>
 *   <li>{@code expected_edges.jsonl}: the edges the model chose that the
 *       versions do not state -- {@code WIRE} (consumer endpoint, producer
 *       endpoint) per selected message arm, {@code STATE} with {@code mint}
 *       per placeholder the model joined to a writer, {@code MARKER} (root,
 *       polarity) per marker that world planted, {@code ANCHOR}
 *       (occurrence, seq).</li>
 * </ul>
 *
 * <p>WHICH PATH AND WHICH ARMS.  {@code claim.json} states the valuation
 * the claim rests on ({@code claim.valuationOrdinal}); that valuation's row
 * names {@code selectedPathId}, {@code selectedSessionId} and {@code
 * selectedArms} -- the arm selectors the sat model set true, which the
 * composer already reads off the model.  Nothing is re-solved.</p>
 *
 * <p>A confirmation nothing can run is refused by name (exit 1, the reason
 * on stderr and in the summary): a selected session without a target row
 * at the anchor, a selected arm no session attested.  The driver reads a refusal as
 * "unconfirmed, because ...".</p>
 */
public final class ConfirmMain {
    /** The one obligation id a confirmation carries. */
    static final String OBLIGATION_ID = "CONFIRM";
    /**
     * The confirmation, when the selected session already realized the
     * claim ({@link #realizedBy}): the driver publishes it and runs no
     * replay.
     */
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
        Corpus corpus = Corpus.read(iteration, null);
        SessionReader session = corpus.session(sessionId);
        if (session == null) {
            throw new Refused("the corpus holds no session " + sessionId);
        }
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
        // AN EXECUTION THAT ALREADY REALIZED THE CLAIM IS THE CONFIRMATION.
        // What CONFIRM asks is whether one run of the program takes every
        // edge the model chose, with the moved roots at the model's values,
        // and observes the fatal at the anchor.  When every arm the model
        // chose is a delivery the selected session itself recorded, and
        // that session ran each moved root at the model's value and
        // observed the fatal, that session is the run: re-running its
        // world tests only whether its races go the same way twice
        // (hdfs-17899 bug2, rounds v36 and v38).  A model
        // that combines deliveries of different sessions has no such run,
        // and the replay below is the one that makes it.
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

        // THE WORLD THE SELECTED PATH RAN IN, values only.  Its own session
        // planted these roots and clocks and observed the fatal with its
        // flips forced; the confirmation re-runs that world with nothing
        // forced, so the values alone must drive every decision.  The
        // model's re-solved instants are the published witness, not what a
        // run is held to: a solver sits on the boundary of its constraints,
        // and a run's own timeline moves by more than that.
        Corpus.World world = corpus.world(sessionId);
        Map<String, String> assignments = world.rootAssignments;
        List<JsonObject> markers = new ArrayList<JsonObject>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            String rootId = text(root, "rootId");
            if (!"MARKER".equals(text(root, "kind"))
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
            String armSession = text(arm, "sessionId");
            if (armSession.isEmpty() || armSessions.containsKey(armSession)) {
                continue;
            }
            SessionReader delivering = corpus.session(armSession);
            if (delivering != null) armSessions.put(armSession, delivering);
        }

        // The edges the model chose: the versions the replay holds its
        // reads to, and the rest it checks.
        StateJoins joins = stateJoins(corpus, session, anchor, target.seq(),
                arms);
        List<JsonObject> edges = new ArrayList<JsonObject>();
        edges.addAll(wireEdges(arms, armSessions));
        edges.addAll(joins.mints);
        edges.addAll(markers);
        JsonObject anchorRow = new JsonObject();
        anchorRow.addProperty("kind", "ANCHOR");
        anchorRow.addProperty("occurrence", anchor.id());
        anchorRow.addProperty("seq", target.seq());
        edges.add(anchorRow);
        RowCodec.writeJsonl(
                out.resolve(edu.uva.liftlab.graphchecker.runtime
                        .Confirmation.FILE), edges);

        // NO FLIP: the values drive every decision, and the replay reads
        // {@code flip: null} as "nothing is owed at any decision".
        ExploreCodec.writeFocusFile(out.resolve(ObligationDir.FOCUSED_TASK),
                ExploreCodec.writeFocusRow(Task.of(OBLIGATION_ID, anchor,
                                Collections.<OccurrenceAddress>emptyList(),
                                seedSessionId),
                        Obligation.confirming(OBLIGATION_ID, OBLIGATION_ID,
                                pathId, assignments, world.answers,
                                Collections.<String>emptyList()),
                        world.clockDeltas, world.rootMints,
                        Collections.<Corpus.Flip>emptyList(), joins.versions));

        JsonObject summary = new JsonObject();
        summary.addProperty("kind", "CONFIRM_TASK");
        summary.addProperty("anchor", anchor.id());
        summary.addProperty("selectedPathId", pathId);
        summary.addProperty("selectedSessionId", sessionId);
        summary.addProperty("valuationOrdinal", ordinal);
        summary.addProperty("rootAssignments", assignments.size());
        summary.addProperty("clockDeltas", world.clockDeltas.size());
        summary.addProperty("versions", joins.versions.size());
        summary.addProperty("expectedEdges", edges.size());
        return summary;
    }

    /**
     * Why the selected session is itself the run that confirms the claim,
     * or {@code ""} when a replay has to make one.
     *
     * <p>Every arm the model chose for the selected path is one of that
     * session's own deliveries, the session's target row at the anchor
     * observed the fatal, and every root the claim moved is one that
     * session minted at the model's value -- named by root id or by the
     * symbol the formula carries, as {@code movedRoots} names it.</p>
     */
    static String realizedBy(JsonObject decided, String sessionId,
                             List<JsonObject> arms, SessionReader session,
                             TargetRow target) {
        if (!target.observedFatal()) return "";
        for (JsonObject arm : arms) {
            if (!sessionId.equals(text(arm, "sessionId"))) return "";
        }
        Map<String, String> ran = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            ran.put(row.rootId(), row.recordedValue());
            ran.put(row.symbol(), row.recordedValue());
        }
        JsonObject moved = decided.has("movedRoots")
                && decided.get("movedRoots").isJsonObject()
                ? decided.getAsJsonObject("movedRoots") : new JsonObject();
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

    /** The selected path's state joins, as CONFIRM hands them on. */
    static final class StateJoins {
        /** The versions the replay holds its reads to. */
        final List<ReadsFrom> versions = new ArrayList<ReadsFrom>();
        /**
         * One {@code STATE} edge per placeholder the model joined to a
         * writer: a placeholder stands on no bytecode, so it is checked by
         * its writer ({@code runtime.Confirmation}) and never held.
         */
        final List<JsonObject> mints = new ArrayList<JsonObject>();
    }

    /**
     * THE STATE JOINS OF THE SELECTED PATH: the reads of the occurrences the
     * anchor's joins reach (Composer's P3 closure, the same rule over the
     * same rows), each with the writer the model joined it to -- the one a
     * selected {@code writer_arm__} names, else the version the session
     * observed.  A join is held where the model chose among writers or the
     * writer ran on another thread ({@link ObligationFactory#held}): which
     * iteration's write a read observes on its own thread -- 17960's
     * snapshot builders, serialized in the order a set yields them -- is
     * program order's, and rule (b), the fatal at the anchor, is what checks
     * that such joins still lead there.
     */
    private static StateJoins stateJoins(Corpus corpus,
                                         SessionReader session,
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
        StateJoins joins = new StateJoins();
        for (Map.Entry<String, WriteRow> join : joined.entrySet()) {
            ReadRow reader = readers.get(join.getKey());
            String chosenWriter = chosen.get(join.getKey());
            if (reader.mintVersion() != ReadRow.UNKNOWN_VERSION) {
                if (chosenWriter == null) continue;
                // A PLACEHOLDER read is the mint of a declared cell, and the
                // mint lands on whichever occurrence of the region reads the
                // cell first: two occurrences racing for one cell -- 17960's
                // two FSImageSaver threads, saveFSImageInAllDirs@0 and @1 --
                // mint it at @0 in one run and at @1 in the next, while the
                // version the placeholder stands for is the same.  So the
                // edge is a join of the CELL to the model's writer, checked
                // by the writer (runtime/Confirmation).
                JsonObject edge = new JsonObject();
                edge.addProperty("kind", "STATE");
                edge.addProperty("reader", join.getKey());
                edge.addProperty("mint", true);
                edge.addProperty("writer", chosenWriter);
                edge.addProperty("version", join.getValue().version());
                edge.addProperty("location", location(
                        join.getValue().location().kind().name(),
                        join.getValue().location().owner(),
                        join.getValue().location().slot()));
                joins.mints.add(edge);
                continue;
            }
            Endpoint writer = chosenWriter == null
                    ? join.getValue().endpoint() : writers.get(chosenWriter);
            if (ObligationFactory.held(corpus, reader, writer,
                    chosenWriter == null ? 1 : 2)) {
                joins.versions.add(ReadsFrom.of(reader.endpoint(), writer));
            }
        }
        return joins;
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

}
