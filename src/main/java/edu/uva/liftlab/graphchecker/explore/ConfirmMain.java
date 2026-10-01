package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
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
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

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
 *   or, with --iteration and --claim, a native reproduction's plant
 *   ({@link #plant}):
 *   --plant &lt;file&gt;      the markers the confirmation's world plants
 *
 *   once the replay has published, the decision ({@link #decide}), printed
 *   as final/confirm.json:
 *   --claim &lt;file&gt; --output &lt;dir&gt; --sessions &lt;dir&gt;
 * </pre>
 *
 * <p>THE RULE (PIPELINE §10). SAT says the model satisfies our formula;
 * CONFIRM says the program agrees: re-run the world the selected path's own
 * session ran (its planted roots and answers) overlaid with the model's
 * moved roots, its clocks the model's jumps alone ({@link Moved}), with no
 * flip forced, and require
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
 *       closure at a location the selected path's fatal rests on (the
 *       manifest's {@code restsOn}; the write the model chose, else the
 *       observed one: a
 *       {@code writer_arm__}'s write for a read of its location, and for a
 *       query through a re-pointable reference the state of the delivered
 *       object its nested selector chose, the arm's {@code
 *       referentStates}), {@code ORDER} per held join (the writer's
 *       activation before the reader's; every other writer of the location
 *       the held write is of before the writer or after the reader), {@code
 *       MARKER} per planted marker, {@code ANCHOR}.</li>
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
        Path plant = options.path("plant");
        if (sessions != null && claim != null && out != null) {
            System.out.println(ExploreMain.pretty(
                    decide(claim, out, sessions)));
            return;
        }
        if (iteration == null || claim == null
                || (plant == null && (manifest == null || out == null))) {
            throw new IllegalArgumentException("--iteration, --claim, and "
                    + "--plant or --manifest and --output are required");
        }
        JsonObject summary;
        try {
            summary = plant != null ? writePlant(iteration, claim, plant)
                    : write(iteration, claim, manifest, out);
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
        Set<String> restsOn = new LinkedHashSet<String>();
        boolean stated = false;
        for (JsonElement element : array(manifest, "paths")) {
            JsonObject path = element.getAsJsonObject();
            if (pathId.equals(optionalString(path, "pathId"))) {
                ordinalOfPath = ordinalOf(optionalString(path, "selector"));
                stated = path.has("restsOn");
                restsOn.addAll(strings(path, "restsOn"));
            }
        }
        if (ordinalOfPath.isEmpty() || !stated) {
            throw new Refused("the manifest states no selector or no "
                    + "restsOn for the selected path " + pathId);
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
        // The writes the model chose for the anchor's join closure.
        StateClosure closure = new StateClosure(session, anchor, target.seq());
        Map<String, WriteRow> chosen = closure.chosen(arms);
        // A choice at a location the fatal does not rest on is the solver's
        // free pick among the formula's alternatives, not the witness.
        chosen.keySet().removeIf(reader -> !restsOn.contains(
                SmtLowering.locationKey(closure.readers.get(reader)
                        .location())));
        // A session that already took every chosen edge at the model's root
        // values and observed the fatal IS the confirmation; re-running it only
        // tests a race twice. A model mixing sessions' deliveries, or choosing
        // a write its reads did not see, needs the replay below.
        JsonObject world = obligationWorld(iteration, sessionId);
        Moved moved = Moved.of(decided, session,
                SessionReader.read(iteration, seedSessionId), manifest);
        String realized = realizedBy(moved, world, sessionId, arms, session,
                target, closure.ran(chosen));
        if (!realized.isEmpty()) {
            RowCodec.writeJsonl(out.resolve(REALIZED),
                    Collections.singletonList(
                            confirmation(true, realized, sessionId)));
            JsonObject summary = summary(anchor, pathId, sessionId, ordinal);
            summary.addProperty("realizedBy", sessionId);
            return summary;
        }

        // The selected path's world, values only, nothing forced, under the
        // model's.
        Map<String, String> assignments =
                ExploreCodec.map(object(world, "rootAssignments"));
        Map<String, String> clockDeltas =
                ExploreCodec.map(object(world, "clockDeltas"));
        Map<String, String> mints =
                ExploreCodec.map(object(world, "rootMints"));
        Map<String, String> answers =
                ExploreCodec.map(object(world, "answers"));
        moved.plant(assignments, clockDeltas, mints);
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
        edges.addAll(stateEdges(closure, chosen, restsOn));
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

    /** What a confirmation plants: root values, clock skews, the occurrence
     *  each root is minted at, and the answers at attach endpoints. */
    static final class World {
        final Map<String, String> assignments;
        final Map<String, String> clockDeltas;
        final Map<String, String> mints;
        final Map<String, String> answers;

        World(JsonObject focus) {
            assignments = ExploreCodec.map(object(focus, "rootAssignments"));
            clockDeltas = ExploreCodec.map(object(focus, "clockDeltas"));
            mints = ExploreCodec.map(object(focus, "rootMints"));
            answers = ExploreCodec.map(object(focus, "answers"));
        }
    }

    /** The world the claim is confirmed in: the selected session's own
     *  obligation world under the model's moved roots ({@link Moved}). */
    static World world(Path iteration, JsonObject decided,
                       JsonObject manifest, SessionReader session,
                       String seedSessionId) throws IOException {
        World world = new World(obligationWorld(iteration,
                session.sessionId()));
        Moved.of(decided, session,
                SessionReader.read(iteration, seedSessionId), manifest)
                .plant(world.assignments, world.clockDeltas, world.mints);
        return world;
    }

    /**
     * A native reproduction's plant (ADHOC-INFRA WP5.D; {@code
     * runtime.RecordingPlant}): the confirmation's world ({@link #world}), one
     * row per root at the site its plan input action calls and the id of the
     * occurrence it is minted at.  The recording weave plants only fault
     * markers: a world that also moves a clock, answers an attach or assigns
     * any other root is refused by name.  Whatever CONFIRM decided, and
     * whether or not it replayed.
     */
    static JsonObject writePlant(Path iteration, Path claimFile, Path out)
            throws IOException {
        JsonObject claim = ExploreCodec.readObject(claimFile);
        JsonObject decided = claim.getAsJsonObject("claim");
        String sessionId = optionalString(valuation(claim,
                decided.get("valuationOrdinal").getAsInt()),
                "selectedSessionId");
        if (sessionId.isEmpty()) {
            throw new Refused("the claim's valuation selected no session");
        }
        SessionReader session = SessionReader.read(iteration, sessionId);
        // COMPOSE publishes its manifest beside the claim (final/).
        Path manifestFile = claimFile.resolveSibling(
                "candidate_composition_manifest.json");
        if (!Files.isRegularFile(manifestFile)) {
            throw new Refused("the claim has no composition manifest beside it: "
                    + manifestFile);
        }
        World world = world(iteration, decided,
                ExploreCodec.readObject(manifestFile), session,
                optionalString(claim, "seedSessionId"));
        if (!world.clockDeltas.isEmpty() || !world.answers.isEmpty()) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: a native run plants "
                    + "fault markers only, and this world skews clocks "
                    + world.clockDeltas.keySet() + " and answers attaches "
                    + world.answers.keySet());
        }
        Map<String, RootKind> kinds = new LinkedHashMap<String, RootKind>();
        for (RootMintRow row : session.roots()) {
            kinds.put(row.rootId(), row.kind());
        }
        Map<String, Set<String>> sites = inputSites(
                iteration.resolve("execution_task_plan.jsonl"));
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<String, String> assigned
                : world.assignments.entrySet()) {
            String rootId = assigned.getKey();
            Set<String> site = sites.getOrDefault(rootId,
                    Collections.<String>emptySet());
            String mint = world.mints.getOrDefault(rootId, "");
            if (kinds.get(rootId) != RootKind.MARKER || site.size() != 1
                    || mint.isEmpty()) {
                throw new Refused("NATIVE_PLANT_UNSUPPORTED: root " + rootId
                        + " is " + kinds.get(rootId) + ", called at " + site
                        + ", minted at '" + mint + "'; a native run plants "
                        + "a fault marker of one call site at the occurrence "
                        + "it is minted at");
            }
            JsonObject row = new JsonObject();
            row.addProperty(RecordingPlant.KIND, RecordingPlant.MARKER);
            row.addProperty(RecordingPlant.OCCURRENCE,
                    OccurrenceAddress.parse(mint).id());
            row.addProperty(RecordingPlant.SITE, site.iterator().next());
            row.addProperty(RecordingPlant.VALUE,
                    Boolean.parseBoolean(assigned.getValue().trim()));
            rows.add(row);
        }
        if (rows.isEmpty()) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: the world plants no "
                    + "root, so a native run would repeat the recording");
        }
        RowCodec.writeJsonl(out, rows);
        JsonObject summary = new JsonObject();
        summary.addProperty("sessionId", sessionId);
        summary.addProperty("markers", rows.size());
        return summary;
    }

    /** Each input port of the plan: the call sites its input actions name. */
    private static Map<String, Set<String>> inputSites(Path plan)
            throws IOException {
        Map<String, Set<String>> sites =
                new LinkedHashMap<String, Set<String>>();
        for (JsonObject task : ArtifactIO.readJsonl(plan)) {
            for (JsonElement element : ExecutionTask.decode(task)
                    .inputActions().all()) {
                JsonObject action = element.getAsJsonObject();
                String port = optionalString(action, "portId");
                String site = optionalString(action, "siteId");
                if (port.isEmpty() || site.isEmpty()) continue;
                sites.computeIfAbsent(port,
                        key -> new LinkedHashSet<String>()).add(site);
            }
        }
        return sites;
    }

    /**
     * The MODEL's world, to be planted over the session's (an exploration
     * plants it so, ObligationFactory): every root the claim moved, by root
     * id, at the occurrence the recording mints it -- a clock as a skew, any
     * other root as its value.  Otherwise the replay runs the session again,
     * not the claim.
     *
     * <p>THE CLOCKS ARE THE MODEL'S ALONE.  On every clock cell the
     * composition anchors (the manifest's {@code roots}) the model's clock
     * is its jumps -- the claim's moved cells -- and every other cell runs
     * on from the jump before it; a skew the session planted there would be
     * a jump the model does not make, carried on by the replay's node clock
     * ({@code runtime.NodeClocks}).  A jump's skew is off the reading the
     * composition anchored its cell to: the model's instants are on that
     * timeline, the recording's; the selected session is a later replay
     * whose host read its own (SOLR-18406 a37f2: 1168 s later).</p>
     *
     * <p>A moved root no row of the session or the recording names, one the
     * recording mints nowhere (no occurrence of a replay can be focused to
     * plant it), or a moved clock the composition anchors nowhere is a
     * refusal, named when the model is planted.</p>
     */
    static final class Moved {
        /** Non-clock root id -> the model's value. */
        final Map<String, String> values = new LinkedHashMap<String, String>();
        /** Clock root id -> the model's skew off its anchored reading. */
        final Map<String, String> skews = new LinkedHashMap<String, String>();
        /** Root id -> the occurrence the recording mints it at. */
        final Map<String, String> mints = new LinkedHashMap<String, String>();
        /** Every clock root id the composition anchors. */
        final Set<String> anchored = new LinkedHashSet<String>();
        /** Why a moved root cannot be planted, or "". */
        String refusal = "";

        static Moved of(JsonObject decided, SessionReader session,
                        SessionReader recording, JsonObject manifest) {
            Moved moved = new Moved();
            Map<String, String> readings = new LinkedHashMap<String, String>();
            for (JsonElement element : array(manifest, "roots")) {
                JsonObject root = element.getAsJsonObject();
                if ("CLOCK".equals(optionalString(root, "kind"))) {
                    readings.put(optionalString(root, "rootId"),
                            optionalString(root, "recordedValue"));
                }
            }
            moved.anchored.addAll(readings.keySet());
            // By root id and by cell symbol; the recording's row first.
            Map<String, RootMintRow> named =
                    new LinkedHashMap<String, RootMintRow>();
            Map<String, RootMintRow> minted =
                    new LinkedHashMap<String, RootMintRow>();
            for (SessionReader rows : Arrays.asList(recording, session)) {
                for (RootMintRow row : rows.roots()) {
                    named.putIfAbsent(row.rootId(), row);
                    named.putIfAbsent(row.symbol(), row);
                    if (rows == recording) minted.putIfAbsent(row.rootId(), row);
                }
            }
            for (Map.Entry<String, JsonElement> entry
                    : object(decided, "movedRoots").entrySet()) {
                RootMintRow row = named.get(entry.getKey());
                RootMintRow mint = row == null ? null
                        : minted.get(row.rootId());
                if (mint == null) {
                    moved.refuse("the claim moves " + entry.getKey()
                            + ", which the recording mints nowhere, so no "
                            + "occurrence of a replay can be focused to "
                            + "plant it");
                    continue;
                }
                String model = entry.getValue().getAsString().trim();
                if (row.kind() == RootKind.CLOCK) {
                    String skew = ObligationFactory.skew(model,
                            readings.get(row.rootId()));
                    if (skew.isEmpty()) {
                        moved.refuse("the model moves clock cell "
                                + entry.getKey() + " to " + model + " and "
                                + "the composition anchors no reading of "
                                + "it, so no skew states that instant");
                        continue;
                    }
                    moved.skews.put(row.rootId(), skew);
                } else {
                    moved.values.put(row.rootId(), model);
                }
                moved.mints.put(row.rootId(), mint.occurrence().render());
            }
            return moved;
        }

        private void refuse(String why) {
            if (refusal.isEmpty()) refusal = why;
        }

        /** The model planted over the session's world, or refused. */
        void plant(Map<String, String> assignments,
                   Map<String, String> clockDeltas,
                   Map<String, String> mints) {
            if (!refusal.isEmpty()) throw new Refused(refusal);
            clockDeltas.keySet().removeAll(anchored);
            clockDeltas.putAll(skews);
            assignments.putAll(values);
            mints.putAll(this.mints);
        }

        /** Whether this world's clocks are the model's: on every anchored
         *  cell, the same skews planted (a skew compares as a number). */
        boolean clocksOf(Map<String, String> clockDeltas) {
            Map<String, BigInteger> planted = new LinkedHashMap<String,
                    BigInteger>();
            for (Map.Entry<String, String> delta : clockDeltas.entrySet()) {
                if (!anchored.contains(delta.getKey())) continue;
                BigInteger skew = number(delta.getValue());
                if (skew == null) return false;
                planted.put(delta.getKey(), skew);
            }
            Map<String, BigInteger> model = new LinkedHashMap<String,
                    BigInteger>();
            for (Map.Entry<String, String> skew : skews.entrySet()) {
                model.put(skew.getKey(), number(skew.getValue()));
            }
            return planted.equals(model);
        }

        private static BigInteger number(String text) {
            try {
                return new BigInteger(text.trim());
            } catch (NumberFormatException notANumber) {
                return null;
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
     *  arms are its own deliveries and its reads saw every write the model
     *  chose ({@code sawChosen}, {@link StateClosure#ran}: another writer, or
     *  another state of a delivered object, is a run a replay has to make),
     *  it observed the fatal, and it ran the model's world: every moved
     *  root at the model's value (its mint row), and its clocks the model's
     *  jumps and nothing else ({@link Moved#clocksOf}: skews, each off its
     *  own run's host, so the two timelines compare; an instant of the
     *  replay is not one of the recording's). */
    static String realizedBy(Moved moved, JsonObject world, String sessionId,
                             List<JsonObject> arms, SessionReader session,
                             TargetRow target, boolean sawChosen) {
        if (!target.observedFatal() || !sawChosen
                || !moved.refusal.isEmpty()) {
            return "";
        }
        for (JsonObject arm : arms) {
            if (!sessionId.equals(optionalString(arm, "sessionId"))) return "";
        }
        Map<String, String> ran = new LinkedHashMap<String, String>();
        for (RootMintRow row : session.roots()) {
            ran.put(row.rootId(), row.recordedValue());
        }
        for (Map.Entry<String, String> value : moved.values.entrySet()) {
            String at = ran.get(value.getKey());
            if (at == null
                    || !at.trim().equalsIgnoreCase(value.getValue())) {
                return "";
            }
        }
        if (!moved.clocksOf(ExploreCodec.map(object(world, "clockDeltas")))) {
            return "";
        }
        int count = moved.values.size() + moved.skews.size();
        return "the selected session " + sessionId + " is itself the run: "
                + "it took every edge the model chose (" + arms.size()
                + " arm(s), all its own deliveries), ran "
                + (count == 0 ? "no moved root"
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

    /**
     * A store's message key, {@code <transport> <path>@<version>}
     * (CONTRACT-SPEC §2.2): every run that reads that version spells it
     * alike.  An exchange's correlation id is its own run's, so a replay's
     * never equals the model's arm's, and only its consumer and producer
     * are compared.
     */
    private static final Pattern STORE_KEY =
            Pattern.compile("\\S+ \\S.*@[0-9]+");

    /** One WIRE edge per consumer of each selected message arm, paired as that
     *  arm's session recorded; a codec hole's with its message's store
     *  version and the text the model's valuation of it decodes to
     *  ({@code holeTexts}, COMPOSE's). */
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
                if (paired.hole() != null) {
                    // A codec's hole (WIRE-CODEC §6.5): the version of the
                    // store its message was, and what it must decode to.
                    if (STORE_KEY.matcher(paired.correlationId()).matches()) {
                        edge.addProperty("messageKey",
                                paired.correlationId());
                    }
                    JsonObject texts = object(arm, "holeTexts");
                    if (texts.has(consumerId)) {
                        edge.add("value", texts.get(consumerId));
                    }
                }
                edges.add(edge);
            }
        }
        return edges;
    }

    /**
     * The anchor's join closure in the selected session (the Composer's P3
     * rule): every read of each reached occurrence before its cutoff, the
     * anchor's before its target, with the write it joined; every write of
     * the session, by location and by version.
     */
    private static final class StateClosure {
        private final Map<String, WriteRow> writes =
                new LinkedHashMap<String, WriteRow>();
        private final Map<String, List<WriteRow>> byLocation =
                new LinkedHashMap<String, List<WriteRow>>();
        /** Reader endpoint id -> its read, in closure order. */
        private final Map<String, ReadRow> readers =
                new LinkedHashMap<String, ReadRow>();
        /** Reader endpoint id -> the write its version was, when one. */
        private final Map<String, WriteRow> joined =
                new LinkedHashMap<String, WriteRow>();
        /** The reads of a reached occurrence at or past its cutoff. */
        private final Set<String> past = new LinkedHashSet<String>();

        private StateClosure(SessionReader session, OccurrenceAddress anchor,
                             long cutoff) {
            for (WriteRow write : session.writes()) {
                writes.put(version(write.location(), write.version()), write);
                byLocation.computeIfAbsent(SmtLowering.locationKey(
                        write.location()),
                        key -> new ArrayList<WriteRow>()).add(write);
            }
            Map<String, List<ReadRow>> readsOn =
                    new LinkedHashMap<String, List<ReadRow>>();
            for (ReadRow read : session.reads()) {
                readsOn.computeIfAbsent(read.endpoint().occurrence().id(),
                        key -> new ArrayList<ReadRow>()).add(read);
            }
            // Occurrence id -> the seq its prefix reaches.
            Map<String, Long> reached = new LinkedHashMap<String, Long>();
            reached.put(anchor.id(), cutoff);
            List<String> pending = new ArrayList<String>();
            pending.add(anchor.id());
            List<WriteRow> versions = new ArrayList<WriteRow>();
            Set<String> handled = new LinkedHashSet<String>();
            while (!pending.isEmpty() || !versions.isEmpty()) {
                while (!pending.isEmpty()) {
                    String at = pending.remove(0);
                    long cut = reached.get(at);
                    List<ReadRow> on = readsOn.get(at);
                    if (on == null) continue;
                    for (ReadRow read : on) {
                        // The anchor's too, unlike Composer#closure, which
                        // joins all its reads as its inputs: a run that takes
                        // the fatal arm throws there, and no edge after it
                        // can be taken (adhoc token-pw-expired: the key map
                        // is read after the expiry check).
                        if (read.seq() >= cut) {
                            past.add(read.endpoint().id());
                            continue;
                        }
                        if (read.observedVersion() < 0L) continue;
                        WriteRow write = writes.get(version(read.location(),
                                read.observedVersion()));
                        // A version no row wrote (a store outside every
                        // region) joins nothing; the model may still choose
                        // its writer.
                        readers.put(read.endpoint().id(), read);
                        if (write == null) continue;
                        joined.put(read.endpoint().id(), write);
                        reach(write, anchor, reached, pending, versions,
                                handled);
                    }
                }
                if (versions.isEmpty()) continue;
                WriteRow write = versions.remove(0);
                for (WriteRow under : byLocation.get(SmtLowering.locationKey(
                        write.location()))) {
                    if (under.version() >= write.version()) continue;
                    reach(under, anchor, reached, pending, versions,
                            handled);
                }
            }
        }

        /**
         * The write the MODEL chose for each read it chose one for, by the
         * selected state arms: a {@code writer_arm__} fills STATE
         * interactions ({@code smt.Arms#stateArms}), each one write to one
         * read -- not its groupId, which names the writer OCCURRENCE -- and
         * its {@code referentStates} hold each read a query through a
         * re-pointable reference answered to the write of the state of the
         * delivered object the model's nested selector chose
         * ({@code compose.SmtLowering#stateChoices}).  A state no read of
         * this closure can be held to is refused by name.
         */
        private Map<String, WriteRow> chosen(List<JsonObject> arms) {
            Map<String, WriteRow> chosen = new LinkedHashMap<String, WriteRow>();
            for (JsonObject arm : arms) {
                String selector = optionalString(arm, "selector");
                if (!selector.startsWith("writer_arm__")) continue;
                Set<String> fills = new LinkedHashSet<String>(
                        strings(arm, "interactionIds"));
                for (ReadRow read : readers.values()) {
                    // The arm's write, as smt.Arms#stateArms chose it among
                    // one endpoint's writes of the location: the one the
                    // read observed, else the last.
                    WriteRow held = null;
                    for (WriteRow write : byLocation.getOrDefault(
                            SmtLowering.locationKey(read.location()),
                            Collections.<WriteRow>emptyList())) {
                        if (!fills.contains(Interaction.of(
                                InteractionKind.STATE, write.endpoint(),
                                read.endpoint()).id())
                                || held != null && held.version()
                                == read.observedVersion()) {
                            continue;
                        }
                        if (held == null || write.version()
                                == read.observedVersion()
                                || write.seq() > held.seq()) {
                            held = write;
                        }
                    }
                    if (held != null) chosen.put(read.endpoint().id(), held);
                }
                for (JsonElement element : array(arm, "referentStates")) {
                    JsonObject state = element.getAsJsonObject();
                    String reader = optionalString(state, "reader");
                    String seen = optionalString(state, "location") + "@"
                            + optionalString(state, "version");
                    WriteRow write = writes.get(seen);
                    String subject = "selected arm " + selector
                            + " answers a query through a re-pointable "
                            + "reference from state " + seen + " ("
                            + optionalString(state, "selector") + ")";
                    if (reader.isEmpty()) {
                        throw new Refused(subject + ", asked outside every "
                                + "read of a container, so no read of the "
                                + "run can be held to it");
                    }
                    if (!readers.containsKey(reader)) {
                        // Past its cutoff, no edge the fatal rests on.
                        if (past.contains(reader)) continue;
                        throw new Refused(subject + " at read " + reader
                                + ", which is no read of the anchor's join "
                                + "closure");
                    }
                    if (write == null || !write.endpoint().id().equals(
                            optionalString(state, "writer"))) {
                        throw new Refused(subject + ", which the selected "
                                + "session states no write of by "
                                + optionalString(state, "writer"));
                    }
                    chosen.put(reader, write);
                }
            }
            return chosen;
        }

        /** Whether the run's own reads saw every write the model chose. */
        private boolean ran(Map<String, WriteRow> chosen) {
            for (Map.Entry<String, WriteRow> each : chosen.entrySet()) {
                if (!each.getValue().equals(joined.get(each.getKey()))) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * STATE and ORDER edges over the join closure at the locations the
     * fatal rests on ({@code restsOn}): every such join, the write the model
     * chose or else the one the run read -- the run is held to no recorded
     * order, so a pinned join is the model's as much as a choice.  A read
     * elsewhere holds no value the witness needs; under a moved root the run
     * may make it at another endpoint or not at all (r7 hdfs-17960: the
     * fsimage's name maps, re-serialized after the flip).  A read no row
     * answers is held only where the model chose a writer for it; otherwise
     * its outside store is the run's own.
     */
    private static List<JsonObject> stateEdges(StateClosure closure,
                                               Map<String, WriteRow> chosen,
                                               Set<String> restsOn) {
        List<JsonObject> edges = new ArrayList<JsonObject>();
        Set<String> orders = new LinkedHashSet<String>();
        for (Map.Entry<String, ReadRow> reader : closure.readers.entrySet()) {
            ReadRow read = reader.getValue();
            if (!restsOn.contains(SmtLowering.locationKey(read.location()))) {
                continue;
            }
            WriteRow held = chosen.containsKey(reader.getKey())
                    ? chosen.get(reader.getKey())
                    : closure.joined.get(reader.getKey());
            if (held == null) continue;
            Endpoint writer = held.endpoint();
            String location = SmtLowering.locationKey(held.location());
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
            edge.addProperty("location", location);
            edges.add(edge);
            if (mint) continue;
            order(orders, writer, read.endpoint());
            // No other writer of the location it reads between the two: one
            // recorded before the write goes before it, any other after the
            // read.
            for (WriteRow other : closure.byLocation.get(location)) {
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

    /** One version of one location. */
    private static String version(LocationId location, long version) {
        return SmtLowering.locationKey(location) + "@" + version;
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
