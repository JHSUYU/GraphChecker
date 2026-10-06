package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.compose.ComposeMain;
import edu.uva.liftlab.graphchecker.compose.RestsOn;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
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
 *   or, with --iteration, --claim and --manifest, a native
 *   reproduction's plant ({@link #writePlant}):
 *   --plant &lt;file&gt;      what the confirmation's world plants and holds,
 *                        and the target's fatal arms at the claim's anchor
 *   --static-scope-map &lt;file&gt;   the campaign's, whose TARGET_SITE guards
 *                        state those arms
 *
 *   once the replay has published, the decision ({@link #decide}), printed
 *   as final/confirm.json:
 *   --claim &lt;file&gt; --output &lt;dir&gt; --sessions &lt;dir&gt;
 * </pre>
 *
 * <p>THE RULE (PIPELINE §10). SAT says the model satisfies our formula;
 * CONFIRM says the program agrees: re-run the world the selected path's own
 * session ran (its planted roots, answers and pairings, the pairings held by
 * the rows its replay was held to, {@link #holding}) overlaid with the model's
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
 *       activation exits before the last activation the reader entered
 *       before its read, {@code StateClosure#holdBefore}; every other writer
 *       of the location the held write is of before the writer or after the
 *       reader), {@code
 *       MARKER} per planted marker, {@code ANCHOR}.</li>
 * </ul>
 *
 * <p>The path and arms come from the claim's valuation ({@code selectedPathId},
 * {@code selectedSessionId}, {@code selectedArms}); nothing is re-solved.  The
 * selected path's closure runs to where it decided, the manifest's {@code
 * cutoff}: its target row, or -- a witness whose path left the way to the
 * throw at a symbolic guard, which never reached the anchor -- that guard;
 * such a witness is planted and judged as any other, by the fatal at the
 * declared occurrence, and no target row of its own run is asked for.  An
 * unrunnable confirmation is refused by name (exit 1, "CONFIRM refused:"):
 * a defect of the rows (RUN_DEFECT), never a refutation, since no replay
 * ran the model -- except a claim that is the run as recorded, which no
 * replay could make a counterfactual, refuted by name ("CONFIRM refutes:",
 * {@link Refused#refutes}).</p>
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
        Path scopeMap = options.path("static-scope-map");
        if (sessions != null && claim != null && out != null) {
            System.out.println(ExploreMain.pretty(
                    decide(claim, out, sessions)));
            return;
        }
        if (iteration == null || claim == null || manifest == null
                || (plant == null && out == null)
                || (plant != null && scopeMap == null)) {
            throw new IllegalArgumentException("--iteration, --claim, "
                    + "--manifest, and --output or --plant with "
                    + "--static-scope-map are required");
        }
        JsonObject summary;
        try {
            summary = plant != null
                    ? writePlant(iteration, claim, manifest, scopeMap, plant)
                    : write(iteration, claim, manifest, out);
        } catch (Refused refused) {
            // The driver reads which: "refutes" excludes the model, "refused"
            // is a defect of the run (run_engine.sh campaign_confirm_claim).
            System.err.println("CONFIRM " + (refused.refutes ? "refutes"
                    : "refused") + ": " + refused.getMessage());
            JsonObject row = new JsonObject();
            row.addProperty("kind", "CONFIRM_REFUSED");
            row.addProperty("refutes", refused.refutes);
            row.addProperty("reason", refused.getMessage());
            System.out.println(ExploreMain.pretty(row));
            System.exit(1);
            return;
        }
        System.out.println(ExploreMain.pretty(summary));
    }

    /**
     * A confirmation nothing can run, named.  A DEFECT of the rows or the
     * claim -- a selector, a cutoff, a schedule, a pairing, a moved root
     * they do not state -- refutes nothing: no replay ran the model, so the
     * claim is RUN_DEFECT.  Only a claim that is the run as recorded is
     * refuted without a replay ({@link #refutes}): no run of it is a
     * counterfactual, so the campaign excludes it and decides again.
     */
    static final class Refused extends RuntimeException {
        /** Whether the claim itself is refuted, not the run defective. */
        final boolean refutes;

        Refused(String reason) {
            this(reason, false);
        }

        private Refused(String reason, boolean refutes) {
            super(reason);
            this.refutes = refutes;
        }

        /** The claim is no counterfactual: excluded, never a defect. */
        static Refused noCounterfactual(String reason) {
            return new Refused(reason, true);
        }
    }

    /** Writes the worker's three inputs; returns what was written. */
    static JsonObject write(Path iteration, Path claimFile,
                            Path manifestFile, Path out) throws IOException {
        Files.createDirectories(out);
        Witness witness = Witness.of(iteration,
                ExploreCodec.readObject(claimFile),
                ExploreCodec.readObject(manifestFile));
        // The run as recorded is no counterfactual (owner 2026-10-04: a
        // claim moving no root is never a finding), whatever a replay of it
        // observes: refused by name, so the campaign excludes it.
        if (witness.sessionId.equals(witness.seedSessionId)
                && object(witness.decided, "movedRoots").size() == 0
                && ownDeliveries(witness.sessionId, witness.arms)
                && witness.sawChosen) {
            throw Refused.noCounterfactual("the claim moves nothing: its "
                    + "witness is the run as recorded -- the seed's own "
                    + "path, every root and clock as recorded, every arm its "
                    + "own delivery -- so no run of it is a counterfactual");
        }
        // A session that already took every chosen edge at the model's root
        // values and observed the fatal IS the confirmation; re-running it
        // only tests a race twice. A model mixing sessions' deliveries, or
        // choosing a write its reads did not see, needs the replay below.
        String realized = realizedBy(witness.moved, witness.world,
                witness.sessionId, witness.arms, witness.session,
                witness.anchor, witness.sawChosen);
        if (!realized.isEmpty()) {
            RowCodec.writeJsonl(out.resolve(REALIZED),
                    Collections.singletonList(
                            confirmation(true, false, realized,
                                    witness.sessionId)));
            JsonObject summary = witness.summary();
            summary.addProperty("realizedBy", witness.sessionId);
            return summary;
        }

        // The selected path's world, values only, nothing forced, under the
        // model's.
        World world = witness.planted();

        // The schedule half: the recorded order is not held (only a WAKE
        // still waits for what it followed); the model's order is held by
        // the ORDER rows of the edges.
        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                witness.sessionId,
                Collections.singletonList(witness.anchor.id()), false, out);
        if (cut == null) {
            throw new Refused("the selected session " + witness.sessionId
                    + " states no schedule to hold the confirmation to");
        }
        List<JsonObject> edges = witness.edges(iteration, world);
        RowCodec.writeJsonl(out.resolve(Confirmation.FILE), edges);

        // An obligation that flips nothing: the values drive every decision.
        JsonObject focus = ExploreCodec.writeFocusRow(witness.anchor,
                witness.anchor, witness.seedSessionId,
                Collections.<OccurrenceAddress>emptyList(),
                Obligation.confirming(OBLIGATION_ID, OBLIGATION_ID,
                        witness.pathId, world.assignments, world.answers,
                        Collections.<String>emptyList()),
                Collections.<Corpus.Flip>emptyList(), world.clockDeltas,
                world.mints, Collections.<String, String>emptyMap(), cut);
        // {@code flip: null} is the statement: serialize nulls.
        Files.write(out.resolve(ObligationDir.FOCUSED_TASK),
                (new GsonBuilder().serializeNulls().create().toJson(focus)
                        + "\n").getBytes(StandardCharsets.UTF_8));

        JsonObject summary = witness.summary();
        summary.addProperty("rootAssignments", world.assignments.size());
        summary.addProperty("clockDeltas", world.clockDeltas.size());
        summary.addProperty("expectedEdges", edges.size());
        summary.add("schedulePrefix", cut.toJson());
        return summary;
    }

    /**
     * The witness a claim's model chose, read off the claim, its manifest
     * and the sessions: the selected path and its arms, the session whose
     * world it runs in, the anchor's join closure up to where the path
     * decided and the writes the model chose there that the fatal rests on,
     * and the model's moved roots.  CONFIRM's replay ({@link #write}) and a
     * native reproduction's plant ({@link #writePlant}) are both made of
     * it, so a native run plants what CONFIRM's world plants.
     */
    static final class Witness {
        final JsonObject decided;
        final JsonObject manifest;
        final int ordinal;
        final String pathId;
        final String sessionId;
        final String seedSessionId;
        final OccurrenceAddress anchor;
        /** Where the selected path decided ({@link StateClosure}). */
        final long cutoff;
        final List<JsonObject> arms;
        final SessionReader session;
        final SessionReader recording;
        final StateClosure closure;
        final Map<String, WriteRow> chosen;
        final Set<String> restsOn;
        /** The selected session's obligation world (its focus row). */
        final JsonObject world;
        final Moved moved;
        /** Whether the session's reads saw every write the model chose. */
        final boolean sawChosen;

        private Witness(JsonObject claim, JsonObject manifest, Path iteration)
                throws IOException {
            this.manifest = manifest;
            decided = claim.getAsJsonObject("claim");
            ordinal = decided.get("valuationOrdinal").getAsInt();
            JsonObject valuation = valuation(claim, ordinal);
            pathId = optionalString(valuation, "selectedPathId");
            sessionId = optionalString(valuation, "selectedSessionId");
            if (pathId.isEmpty() || sessionId.isEmpty()) {
                throw new Refused("valuation " + ordinal
                        + " selected no path, so there is nothing to "
                        + "confirm");
            }
            anchor = OccurrenceAddress.parse(optionalString(claim, "anchor"));
            if (anchor == null) {
                throw new Refused("the claim states no parseable anchor");
            }
            seedSessionId = optionalString(claim, "seedSessionId");
            // Only the selected path's arms (others are free in the model),
            // joined by the path ordinal in the composer's selector names.
            String ordinalOfPath = "";
            restsOn = new LinkedHashSet<String>();
            boolean stated = false;
            long decidedAt = -1L;
            for (JsonElement element : array(manifest, "paths")) {
                JsonObject path = element.getAsJsonObject();
                if (pathId.equals(optionalString(path, "pathId"))) {
                    ordinalOfPath = ordinalOf(optionalString(path,
                            "selector"));
                    stated = path.has("restsOn");
                    restsOn.addAll(strings(path, "restsOn"));
                    decidedAt = path.has("cutoff")
                            ? path.get("cutoff").getAsLong() : -1L;
                }
            }
            cutoff = decidedAt;
            if (ordinalOfPath.isEmpty() || !stated || cutoff < 0L) {
                throw new Refused("the manifest states no selector, no "
                        + "restsOn or no cutoff for the selected path "
                        + pathId);
            }
            arms = new ArrayList<JsonObject>();
            for (JsonElement element : array(valuation, "selectedArms")) {
                JsonObject arm = element.getAsJsonObject();
                if (ordinalOfPath.equals(
                        ordinalOf(optionalString(arm, "selector")))) {
                    arms.add(arm);
                }
            }
            session = SessionReader.read(iteration, sessionId);
            recording = SessionReader.read(iteration, seedSessionId);
            // The writes the model chose for the anchor's join closure, up
            // to where the path decided: its target row, or the way guard
            // it left the way to the throw at -- a witness that turns that
            // guard never reached the anchor in its own run, and is planted
            // and judged as any other.
            closure = new StateClosure(session, anchor, cutoff);
            chosen = closure.chosen(arms);
            // A choice at a location the fatal does not rest on is the
            // solver's free pick among the formula's alternatives, not the
            // witness.
            chosen.keySet().removeIf(reader -> !restsOn.contains(
                    SmtLowering.locationKey(closure.readers.get(reader)
                            .location())));
            world = obligationWorld(iteration, sessionId);
            moved = moved(decided, manifest, session, recording);
            sawChosen = closure.ran(chosen);
        }

        static Witness of(Path iteration, JsonObject claim,
                          JsonObject manifest) throws IOException {
            return new Witness(claim, manifest, iteration);
        }

        /** The world the claim is confirmed in: the selected session's own
         *  obligation world under the model's moved roots ({@link Moved}). */
        World planted() {
            World planted = new World(world);
            moved.plant(planted.assignments, planted.clockDeltas,
                    planted.mints);
            return planted;
        }

        /**
         * The edges the model chose over {@code planted}: WIRE per consumer
         * of each selected message arm, STATE and ORDER over the join
         * closure at the locations the fatal rests on, the rows that hold
         * the pairings the world plants ({@link #holding}), MARKER per
         * planted marker, ANCHOR.
         */
        List<JsonObject> edges(Path iteration, World planted)
                throws IOException {
            Map<String, SessionReader> armSessions =
                    new LinkedHashMap<String, SessionReader>();
            armSessions.put(sessionId, session);
            for (JsonObject arm : arms) {
                String armSession = optionalString(arm, "sessionId");
                if (armSession.isEmpty()
                        || armSessions.containsKey(armSession)) {
                    continue;
                }
                armSessions.put(armSession, SessionReader.read(iteration,
                        armSession));
            }
            List<JsonObject> edges = new ArrayList<JsonObject>();
            edges.addAll(wireEdges(arms, armSessions, anchor));
            List<ReadRow> resting = new ArrayList<ReadRow>();
            for (ReadRow read : closure.readers.values()) {
                if (restsOn.contains(SmtLowering.locationKey(
                        read.location()))) {
                    resting.add(read);
                }
            }
            edges.addAll(stateEdges(closure, resting, chosen, false).edges);
            // The pairings the selected session's world planted are its
            // world as much as its roots: held by the rows its replay was
            // held to.
            edges.addAll(holding(session, ExploreCodec.map(object(world,
                    "pairings"))).edges);
            heldOnce(edges);
            edges.addAll(markerEdges(manifest, planted.assignments));
            JsonObject anchorRow = new JsonObject();
            anchorRow.addProperty("kind", "ANCHOR");
            anchorRow.addProperty("occurrence", anchor.id());
            anchorRow.addProperty("seq", cutoff);
            edges.add(anchorRow);
            return edges;
        }

        /** Where every root of the world is minted, and what it is. */
        Map<String, RootCategory> categories() {
            Map<String, RootCategory> categories =
                    new LinkedHashMap<String, RootCategory>();
            for (SessionReader rows : Arrays.asList(recording, session)) {
                for (RootMintRow row : rows.roots()) {
                    categories.putIfAbsent(row.rootId(), row.category());
                }
            }
            return categories;
        }

        JsonObject summary() {
            return ConfirmMain.summary(anchor, pathId, sessionId, ordinal);
        }
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

    /**
     * A native reproduction's plant ({@code runtime.RecordingPlant}): what
     * CONFIRM's world plants and holds ({@link Witness}), as rows a run of
     * the recording weave on a stock JDK applies, each numbered so the run
     * can say it applied it -- a ROOT per root the world assigns, naming
     * the occurrence id it is minted at (a FAULT marker answered true or
     * false at the call site its plan input action names, a tree HOOK's
     * field written), the world's ORDER rows as CONFIRM holds them, each
     * pair once, and one TARGET per guard of the scope map's TARGET_SITE
     * rows, its fatal arm at the claim's anchor: the one question a native
     * run answers.  Whatever CONFIRM decided, and whether or not it
     * replayed.  A world the recording weave cannot plant is refused by name
     * ({@code NATIVE_PLANT_UNSUPPORTED}): a clock skew, an attach's answer,
     * a root of another category (a configuration, an unwoven accessor's
     * read), a marker of no single site or no boolean value, a root with no
     * mint; so is one that plants nothing, which would repeat the
     * recording, and a scope map that states no fatal arm.
     */
    static JsonObject writePlant(Path iteration, Path claimFile,
                                 Path manifestFile, Path scopeMap, Path out)
            throws IOException {
        JsonObject claim = ExploreCodec.readObject(claimFile);
        Witness witness = Witness.of(iteration, claim,
                ExploreCodec.readObject(manifestFile));
        World world = witness.planted();
        if (!world.clockDeltas.isEmpty() || !world.answers.isEmpty()) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: a native run plants "
                    + "no clock and answers no attach, and this world skews "
                    + "clocks " + world.clockDeltas.keySet()
                    + " and answers attaches " + world.answers.keySet());
        }
        Map<String, RootCategory> categories = witness.categories();
        Map<String, Set<String>> sites = inputSites(
                iteration.resolve("execution_task_plan.jsonl"));
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<String, String> assigned
                : world.assignments.entrySet()) {
            String rootId = assigned.getKey();
            RootCategory category = categories.get(rootId);
            Set<String> site = sites.getOrDefault(rootId,
                    Collections.<String>emptySet());
            OccurrenceAddress mint = OccurrenceAddress.parse(
                    world.mints.getOrDefault(rootId, ""));
            String value = assigned.getValue().trim();
            if (mint == null || !(category == RootCategory.HOOK
                    || category == RootCategory.FAULT && site.size() == 1
                    && ("true".equals(value) || "false".equals(value)))) {
                throw new Refused("NATIVE_PLANT_UNSUPPORTED: root " + rootId
                        + " is " + category + " at '" + value + "', called at "
                        + site + ", minted at '" + world.mints.get(rootId)
                        + "'; a native run plants a fault marker of one call "
                        + "site at true or false, or a tree hook's field, at "
                        + "an occurrence it is minted at");
            }
            JsonObject row = new JsonObject();
            row.addProperty(RecordingPlant.KIND, RecordingPlant.ROOT);
            row.addProperty(RecordingPlant.CATEGORY, category.name());
            row.addProperty(RecordingPlant.ROOT_ID, rootId);
            row.addProperty(RecordingPlant.OCCURRENCE, mint.id());
            if (category == RootCategory.FAULT) {
                row.addProperty(RecordingPlant.SITE, site.iterator().next());
            }
            row.addProperty(RecordingPlant.VALUE, value);
            rows.add(row);
        }
        // One row per order: CONFIRM's closure and its pairings may state
        // one twice, and a run holds it once.
        Set<String> orders = new LinkedHashSet<String>();
        for (JsonObject edge : witness.edges(iteration, world)) {
            if (RecordingPlant.ORDER.equals(optionalString(edge, "kind"))
                    && orders.add(optionalString(edge, "before") + "\n"
                    + optionalString(edge, "after"))) {
                rows.add(edge);
            }
        }
        if (rows.isEmpty()) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: the world plants no "
                    + "root and holds no order, so a native run would "
                    + "repeat the recording");
        }
        int planted = rows.size();
        for (StaticScopeMap.Site target
                : StaticScopeMap.read(scopeMap).targetSites()) {
            for (int index = 0; index < target.guards.size()
                    && index < target.guardOutcomes.size(); index++) {
                if (target.guardOutcomes.get(index) == null) continue;
                JsonObject row = new JsonObject();
                row.addProperty(RecordingPlant.KIND, RecordingPlant.TARGET);
                row.addProperty(RecordingPlant.OCCURRENCE, witness.anchor.id());
                row.addProperty(RecordingPlant.SITE, target.guards.get(index));
                row.addProperty(RecordingPlant.VALUE,
                        target.guardOutcomes.get(index));
                rows.add(row);
            }
        }
        if (rows.size() == planted) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: " + scopeMap
                    + " states no fatal arm of a TARGET_SITE guard, so a "
                    + "native run could not tell whether it reproduced");
        }
        for (int index = 0; index < rows.size(); index++) {
            rows.get(index).addProperty(RecordingPlant.ROW, index);
        }
        RowCodec.writeJsonl(out, rows);
        JsonObject summary = witness.summary();
        summary.addProperty("roots", world.assignments.size());
        summary.addProperty("orders", planted - world.assignments.size());
        summary.addProperty("fatalArms", rows.size() - planted);
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

    /** The claim's moved roots over the manifest's clock readings (every
     *  CLOCK root it anchors), as {@link Moved} names them. */
    private static Moved moved(JsonObject decided, JsonObject manifest,
                               SessionReader session,
                               SessionReader recording) {
        Map<String, String> readings = new LinkedHashMap<String, String>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            if ("CLOCK".equals(optionalString(root, "kind"))) {
                readings.put(optionalString(root, "rootId"),
                        optionalString(root, "recordedValue"));
            }
        }
        return Moved.of(ExploreCodec.map(object(decided, "movedRoots")),
                readings, session, recording);
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
     * address computes.  Only (b) REFUTES the model, and only where the
     * replay ran it: every root the claim moved minted at the model's value
     * (a clock's cell minted) and no plant refused ({@link #unplanted}).  A
     * run that took an edge the model did not choose (a), or ran without
     * the model's plant, or did not run (not ADMITTED, no readable session)
     * answers nothing about it: a defect of the run (RUN_DEFECT).
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
            return confirmation(false, false, "the confirmation replay was "
                    + (verdict.isEmpty() ? "not run" : verdict) + ": "
                    + optionalString(result, "detail"), sessionId);
        }
        Path session = sessions.resolve(sessionId);
        if (sessionId.isEmpty() || !Files.isDirectory(session)) {
            return confirmation(false, false, "the confirmation replay names "
                    + "session " + sessionId + ", which " + sessions
                    + " does not hold", sessionId);
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
            return confirmation(false, false, "the run's session could not be"
                    + " read, so it answers nothing: " + unread.getMessage(),
                    sessionId);
        }
        for (JsonObject gap : gaps) {
            if ("CONFIRM_MISMATCH".equals(optionalString(gap, "kind"))) {
                return confirmation(false, false, "the run took an edge the"
                        + " model did not choose, so it did not run the"
                        + " model: " + optionalString(gap, "detail"),
                        sessionId);
            }
        }
        JsonObject claim;
        OccurrenceAddress anchor;
        try {
            claim = ExploreCodec.readObject(claimFile);
            anchor = OccurrenceAddress.parse(optionalString(claim, "anchor"));
        } catch (RuntimeException unparsed) {
            return confirmation(false, false, "the claim states no parseable"
                    + " anchor: " + unparsed.getMessage(), sessionId);
        }
        int elsewhere = 0;
        for (TargetRow target : targets) {
            if (!target.reachedAnchor() || !target.observedFatal()) continue;
            if (target.occurrence().id().equals(anchor.id())) {
                return confirmation(true, false, "every edge the model chose"
                        + " was taken, and the claim's anchor observed the"
                        + " fatal", sessionId);
            }
            elsewhere++;
        }
        String why = "the run published no target row at the claim's"
                + " anchor " + anchor.id() + " that reached it and observed"
                + " the fatal" + (elsewhere == 0 ? ""
                : " (" + elsewhere + " row(s) at other occurrences did)");
        String unplanted;
        try {
            unplanted = unplanted(claim, gaps, published(session.resolve(
                    SessionDir.ROOTS)));
        } catch (IOException | RuntimeException unread) {
            unplanted = "its root rows could not be read: "
                    + unread.getMessage();
        }
        return unplanted.isEmpty() ? confirmation(false, true, why, sessionId)
                : confirmation(false, false, why + ", and " + unplanted
                + ", so it did not run the model", sessionId);
    }

    /**
     * Why a confirmation run did not run the claim's model, or "": a plant
     * it refused ({@code ASSIGNMENT_UNPLANTED}), or a root the claim moved
     * that it minted at no row, or (not a clock) at another value than the
     * model's.  A moved root is named as the claim names it, by root id or
     * by its cell's symbol.
     */
    static String unplanted(JsonObject claim, List<JsonObject> gaps,
                            List<JsonObject> roots) {
        for (JsonObject gap : gaps) {
            if ("ASSIGNMENT_UNPLANTED".equals(optionalString(gap, "kind"))) {
                return "it refused a plant (" + optionalString(gap,
                        "subject") + ")";
            }
        }
        Map<String, RootMintRow> minted =
                new LinkedHashMap<String, RootMintRow>();
        for (JsonObject row : roots) {
            RootMintRow root = RowCodec.readRootMint(row);
            minted.putIfAbsent(root.rootId(), root);
            minted.putIfAbsent(root.symbol(), root);
        }
        for (Map.Entry<String, JsonElement> moved : object(claim.getAsJsonObject(
                "claim"), "movedRoots").entrySet()) {
            RootMintRow root = minted.get(moved.getKey());
            if (root == null) {
                return "it minted no row of the moved root "
                        + moved.getKey();
            }
            String model = moved.getValue().getAsString().trim();
            if (root.kind() != RootKind.CLOCK && !root.recordedValue().trim()
                    .equalsIgnoreCase(model)) {
                return "it ran the moved root " + moved.getKey() + " at "
                        + root.recordedValue() + ", not the model's " + model;
            }
        }
        return "";
    }

    /** A session file's rows; one the replay did not publish is refused (its
     *  publisher creates every file at open, so absent is "not published"). */
    private static List<JsonObject> published(Path file) throws IOException {
        if (!Files.isReadable(file)) {
            throw new IOException("it published no readable " + file);
        }
        return RowCodec.readJsonl(file);
    }

    /**
     * The one shape of final/confirm.json; {@code refutes}: the program ran
     * the model and disagreed, so the campaign excludes it
     * ({@code compose.Refutations}).
     */
    private static JsonObject confirmation(boolean confirmed, boolean refutes,
                                           String reason, String sessionId) {
        JsonObject confirmation = new JsonObject();
        confirmation.addProperty("schemaVersion", 1);
        confirmation.addProperty("kind", "CONFIRMATION");
        confirmation.addProperty("confirmed", confirmed);
        confirmation.addProperty("refutes", refutes);
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

    /** Why the selected session is itself the confirming run, or "": all
     *  chosen arms are its own deliveries and its reads saw every write the
     *  model chose ({@code sawChosen}, {@link StateClosure#ran}: another
     *  writer, or another state of a delivered object, is a run a replay
     *  has to make), a target row of it at the anchor reached it and
     *  observed the fatal ({@link #decide}'s rule), and it ran the model's
     *  world ({@link Moved#ranBy}: no pairing planted, every moved root at
     *  the model's value, no other root planted off its recorded value, its
     *  clocks the model's jumps and nothing else). */
    static String realizedBy(Moved moved, JsonObject world, String sessionId,
                             List<JsonObject> arms, SessionReader session,
                             OccurrenceAddress anchor, boolean sawChosen) {
        boolean fatal = false;
        for (TargetRow row : session.targets()) {
            fatal |= row.occurrence().id().equals(anchor.id())
                    && row.reachedAnchor() && row.observedFatal();
        }
        if (!fatal || !sawChosen || !ownDeliveries(sessionId, arms)
                || !moved.ranBy(ExploreCodec.readWorld(world), session)) {
            return "";
        }
        int count = moved.count();
        return "the selected session " + sessionId + " is itself the run: "
                + "it took every edge the model chose (" + arms.size()
                + " arm(s), all its own deliveries), ran "
                + (count == 0 ? "no moved root"
                : "every moved root at the model's value")
                + ", and observed the fatal at the anchor";
    }

    /** Whether every arm the model chose is a delivery of this session. */
    private static boolean ownDeliveries(String sessionId,
                                         List<JsonObject> arms) {
        for (JsonObject arm : arms) {
            if (!sessionId.equals(optionalString(arm, "sessionId"))) {
                return false;
            }
        }
        return true;
    }

    /** The focus row of the obligation whose replay is {@code sessionId}; empty
     *  for the recording. */
    static JsonObject obligationWorld(Path iteration, String sessionId)
            throws IOException {
        JsonObject world = ObligationDir.worlds(
                ObligationDir.workersIn(iteration)).get(sessionId);
        return world == null ? new JsonObject() : world;
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
     *  arm's session recorded; a held leaf's (a consumer of the anchor) with
     *  the text the model's valuation of it delivers ({@code texts},
     *  COMPOSE's);
     *  a consumer of the anchor's, where the arm's own session answered the
     *  anchor by its question, with its producer's question
     *  ({@link #question}): only there did another chain of the question's
     *  shape carry the delivery the model chose. */
    private static List<JsonObject> wireEdges(
            List<JsonObject> arms, Map<String, SessionReader> armSessions,
            OccurrenceAddress anchor) throws IOException {
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
                edge.addProperty("consumer",
                        Confirmation.id(paired.endpoint()));
                edge.addProperty("producer",
                        Confirmation.id(paired.producer()));
                edge.addProperty("selector", selector);
                if (paired.endpoint().occurrence().id().equals(anchor.id())
                        && producerSession.answered().contains(
                        anchor.render())) {
                    edge.add(Confirmation.PRODUCER_QUESTION,
                            question(paired.producer(), producerSession));
                }
                // A held leaf: what must arrive there.
                JsonObject texts = object(arm, ComposeMain.TEXTS);
                if (texts.has(consumerId)) {
                    edge.add("value", texts.get(consumerId));
                }
                edges.add(edge);
            }
        }
        return edges;
    }

    /**
     * The question {@code producer} answers (IDENTITY §9): its occurrence,
     * its site, site index and attempt, and its context's shape over the
     * SEND stances of the session that paired it, as a replay shapes its own
     * ({@code runtime.ScheduleLog#shape}).  The anchor is answered by its question,
     * so a delivery into it is too: which turn of a daemon or an iteration
     * carried the message to it is the run's timing (hdfs-11741 V6: the
     * witness's second move to dn1 rode the balancer's next dispatcher
     * iteration, its CONFIRM run the first, as recorded).
     */
    private static JsonObject question(Endpoint producer,
                                       SessionReader session)
            throws IOException {
        Map<String, ContextShape.Stance> senders =
                new LinkedHashMap<String, ContextShape.Stance>();
        for (ScheduleEvent event : session.schedule()) {
            if (event.kind() != ScheduleEvent.Kind.SEND
                    || event.endpoint().isEmpty()) {
                continue;
            }
            ContextShape.Stance stance =
                    ContextShape.Stance.ofSend(event.context());
            if (stance != null) senders.put(event.endpoint(), stance);
        }
        JsonObject question = new JsonObject();
        question.addProperty("occurrence", producer.occurrence().render());
        question.addProperty("site", producer.site());
        question.addProperty("siteIndex", producer.siteIndex().hash());
        question.addProperty("attempt", producer.attempt());
        JsonArray shape = new JsonArray();
        for (String hop : ContextShape.of(producer.occurrence().context(),
                senders::get)) {
            shape.add(hop);
        }
        question.add("shape", shape);
        return question;
    }

    /**
     * The anchor's join closure in the selected session, COMPOSE's P3
     * closure ({@code compose.RestsOn#closure}, the anchor's reads cut where
     * the path decided -- its target row, or its way guard): every read of
     * each reached occurrence before its cutoff with the write it joined,
     * the reads past it; every write of the session, by location and by
     * version.
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
        /** Occurrence id -> the session's activation of it. */
        private final Map<String, ActivationRow> activations =
                new LinkedHashMap<String, ActivationRow>();
        /** Occurrence id -> where its events sat: activation frames, seq. */
        private final Map<String, List<Placed>> placed =
                new LinkedHashMap<String, List<Placed>>();
        /** Occurrence id -> the seq of its last recorded event. */
        private final Map<String, Long> last = new HashMap<String, Long>();

        /** One event's activation frames and its place in the order. */
        private static final class Placed {
            private final List<Frame> frames;
            private final long seq;

            private Placed(Endpoint at, long seq) {
                this.frames = at.activationFrames();
                this.seq = seq;
            }
        }

        private void place(Endpoint at, long seq) {
            if (at == null) return;
            placed.computeIfAbsent(at.occurrence().id(),
                    key -> new ArrayList<Placed>()).add(new Placed(at, seq));
            last(at.occurrence(), seq);
        }

        private void last(OccurrenceAddress occurrence, long seq) {
            last.merge(occurrence.id(), seq, Math::max);
        }

        /**
         * The close of an occurrence as an ORDER waits for it: entered at
         * its opening, exited at its close ({@code runtime.Identity}), which
         * the session ran at its last recorded event -- so a writer the
         * session ran before that, whose ORDER puts it after, is reordered
         * ({@link #order}).
         */
        private Exit closing(OccurrenceAddress occurrence) {
            return new Exit(occurrence, Collections.<Frame>emptyList(),
                    last.get(occurrence.id()));
        }

        /**
         * The activation {@code first} names exits before {@code then}'s
         * event, unless one occurrence holds both: it runs on one thread,
         * whose program order already orders them.  The hold is the last
         * activation entry before the event on its thread
         * ({@link #holdBefore}), or the send that started claimed work
         * ({@link #held}).  Where the session ran {@code then} first, the
         * order moves the held occurrence's events after {@code first}'s:
         * it is {@code reordered}.
         */
        private void order(Holding holding, Exit first, Endpoint then,
                           long thenSeq) {
            if (first.occurrence.equals(then.occurrence().id())) return;
            Hold hold = held(then, thenSeq);
            holding.orders.add(first.activation + "\n" + hold.activation);
            if (thenSeq < first.seq) holding.reordered.add(hold.occurrence);
        }

        /** What an ORDER waits for to exit, the occurrence it is of, and
         *  where the session ran it. */
        private static final class Exit {
            private final String activation;
            private final String occurrence;
            private final long seq;

            private Exit(OccurrenceAddress occurrence, List<Frame> frames,
                         long seq) {
                this.activation = Confirmation.activation(occurrence,
                        ExecutionIndex.of(frames));
                this.occurrence = occurrence.id();
                this.seq = seq;
            }
        }

        /**
         * What an ORDER after this event waits for: the activation it stood
         * in, or -- where that is its occurrence's outermost
         * ({@link #outermost}) -- the occurrence's close.  The outermost
         * activation of a loop body's occurrence is the loop's method, which
         * spans every turn and never exits while the loop runs
         * (hdfs-bugs-slowdisk-zero SD8: the anchor held until the detector's
         * {@code run()} exited, past the order's timeout); a method's
         * occurrence closes as its root activation exits.
         */
        private Exit exit(Endpoint event, long seq) {
            return outermost(event) ? closing(event.occurrence())
                    : new Exit(event.occurrence(), event.activationFrames(),
                    seq);
        }

        /** Whether an event stood in its occurrence's outermost activation:
         *  no event of the occurrence stood on fewer frames. */
        private boolean outermost(Endpoint event) {
            int depth = event.activationFrames().size();
            List<Placed> events = placed.get(event.occurrence().id());
            for (Placed other : events == null
                    ? Collections.<Placed>emptyList() : events) {
                if (other.frames.size() < depth) return false;
            }
            return true;
        }

        /** Where an event is held: the activation entry, and the
         *  occurrence it is of. */
        private static final class Hold {
            private final String occurrence;
            private final String activation;

            private Hold(OccurrenceAddress occurrence, List<Frame> frames) {
                this.occurrence = occurrence.id();
                this.activation = Confirmation.activation(occurrence,
                        ExecutionIndex.of(frames));
            }
        }

        /**
         * Where {@code event} is held: before it in its own occurrence
         * ({@link #holdBefore}), or, where that runs as claimed work on a
         * consumer thread, at the entry of the send that started it
         * ({@link Confirmation#submitter}, the one rule): ZooKeeper's
         * server applies a getData on the thread that must apply the
         * delete ordered before it, so the client's getData is held.
         */
        private Hold held(Endpoint event, long seq) {
            Endpoint send;
            try {
                send = Confirmation.submitter(event.occurrence(),
                        activations::get);
            } catch (IllegalStateException unheld) {
                throw new Refused(unheld.getMessage());
            }
            return send == null ? holdBefore(event, seq)
                    : new Hold(send.occurrence(), send.activationFrames());
        }

        /**
         * Where a run is held so that an event comes after what the model
         * orders before it: the entry of the last activation its thread
         * entered before the event -- the last call the event's own
         * activation made before it, else that activation's entry.  An
         * activation that runs while what it waits for is made (SOLR-18413
         * s13a: MigrateCmd#migrateKey offers the routing rule, then polls
         * the cluster state until the watcher's parse of it lands) cannot be
         * held at its own entry: the writer follows that entry, and holding
         * it there waits out the order's timeout.  The last call before the
         * read (the poll's {@code getRoutingRules}) is entered after.  With
         * no such call, an event in its occurrence's outermost activation
         * is held at the occurrence's opening: a loop body's turn enters no
         * activation of its own ({@link #exit}).
         */
        private Hold holdBefore(Endpoint event, long seq) {
            List<Frame> own = event.activationFrames();
            List<Frame> hold = own;
            long latest = Long.MIN_VALUE;
            List<Placed> events = placed.get(event.occurrence().id());
            for (Placed other : events == null
                    ? Collections.<Placed>emptyList() : events) {
                if (other.seq >= seq || other.seq <= latest
                        || other.frames.size() <= own.size()
                        || !other.frames.subList(0, own.size()).equals(own)) {
                    continue;
                }
                latest = other.seq;
                hold = other.frames.subList(0, own.size() + 1);
            }
            if (hold == own && outermost(event)) {
                hold = Collections.<Frame>emptyList();
            }
            return new Hold(event.occurrence(), hold);
        }

        /** Where the session's events sat, and its writes: what an ORDER is
         *  built from ({@link #order}), with no closure. */
        private StateClosure(SessionReader session) {
            for (ActivationRow activation : session.activations()) {
                activations.putIfAbsent(activation.occurrence().id(),
                        activation);
            }
            for (ReadRow read : session.reads()) {
                place(read.endpoint(), read.seq());
            }
            for (ExportRow export : session.exports()) {
                place(export.endpoint(), export.seq());
            }
            for (AttachRow attach : session.attaches()) {
                place(attach.endpoint(), attach.seq());
            }
            for (DecisionRow decision : session.decisions()) {
                last(decision.occurrence(), decision.seq());
            }
            for (WriteRow write : session.writes()) {
                // An INITIAL is no event of the access its row stands at
                // (Endpoint#initialSite): its frames name no activation the
                // run enters, so no hold is placed by it (hdfs-bugs-
                // slowdisk-zero SD4: the reconfiguration held at a
                // reflective accessor's frame, which never waits).
                if (!write.initial()) place(write.endpoint(), write.seq());
                writes.put(version(write.location(), write.version()), write);
                byLocation.computeIfAbsent(SmtLowering.locationKey(
                        write.location()),
                        key -> new ArrayList<WriteRow>()).add(write);
            }
        }

        private StateClosure(SessionReader session, OccurrenceAddress anchor,
                             long cutoff) {
            this(session);
            Map<String, List<ReadRow>> readsOn =
                    new LinkedHashMap<String, List<ReadRow>>();
            for (ReadRow read : session.reads()) {
                readsOn.computeIfAbsent(read.endpoint().occurrence().id(),
                        key -> new ArrayList<ReadRow>()).add(read);
            }
            // COMPOSE's closure over this session's rows, the anchor's own
            // reads cut where the path decided (RestsOn#closure).
            RestsOn.closure(new RestsOn.Log() {
                @Override
                public List<ReadRow> readsOn(String occurrenceId) {
                    return readsOn.getOrDefault(occurrenceId,
                            Collections.<ReadRow>emptyList());
                }

                @Override
                public WriteRow writeOf(String locationKey, long version) {
                    return writes.get(locationKey + "@" + version);
                }

                @Override
                public List<WriteRow> writesOf(String locationKey) {
                    return byLocation.getOrDefault(locationKey,
                            Collections.<WriteRow>emptyList());
                }
            }, anchor, anchor, cutoff, null, false, new RestsOn.Reads() {
                @Override
                public void joined(ReadRow read, WriteRow write) {
                    // A version no row wrote (a store outside every region)
                    // joins nothing; the model may still choose its writer.
                    readers.put(read.endpoint().id(), read);
                    if (write != null) joined.put(read.endpoint().id(), write);
                }

                @Override
                public void past(ReadRow read) {
                    past.add(read.endpoint().id());
                }
            });
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
     * The rows that hold a replay to pairings, and the occurrences the
     * order they need moves: {@code reordered}, each held where the session
     * ran it before what the order puts first.
     */
    static final class Holding {
        final List<JsonObject> edges = new ArrayList<JsonObject>();
        final Set<String> reordered = new LinkedHashSet<String>();
        /** Each ORDER as "before\nafter", once. */
        private final Set<String> orders = new LinkedHashSet<String>();
    }

    /**
     * STATE and ORDER edges for {@code reads}: CONFIRM's over the join
     * closure at the locations the fatal rests on, an obligation's over the
     * reads its world pairs ({@link #holding}).  Each read is held to the
     * write chosen for it or else the one it joined -- the run is held to no
     * recorded order, so a pinned join is the model's as much as a choice.
     * A read elsewhere holds no value the witness needs; under a moved root
     * the run may make it at another endpoint or not at all (r7 hdfs-17960:
     * the fsimage's name maps, re-serialized after the flip).  A read no
     * row answers is held only where a writer was chosen for it; otherwise
     * its outside store is the run's own -- and so is an INITIAL the run
     * joined ({@link WriteRow#initial}).  A chosen INITIAL is the version
     * the read must observe ({@link Confirmation#INITIAL}), and every write
     * of its location goes after the read -- after its activation, or, a
     * {@code block}, after its occurrence closes: a flip query binds the
     * reads one occurrence made of a location as one choice (IDENTITY §4),
     * and the flipped world may read it again after the recorded read
     * (hdfs-bugs-slowdisk-zero SD5: the detector turn's {@code limit(max)}
     * re-read the bound after the reconfiguration had landed, so the turn
     * read 1 at its guard and 0 at its limit).  Endpoints and activations
     * are named as every delivery of their stored message is
     * ({@link Confirmation#id}).
     */
    private static Holding stateEdges(StateClosure closure,
                                      List<ReadRow> reads,
                                      Map<String, WriteRow> chosen,
                                      boolean block) {
        Holding holding = new Holding();
        for (ReadRow read : reads) {
            // What a writer the read must precede waits for: the read's
            // activation, or, where the reads of the location are a block,
            // its whole occurrence -- a read the flip adds after the one
            // recorded is the block's too.
            StateClosure.Exit reading = block
                    ? closure.closing(read.endpoint().occurrence())
                    : closure.exit(read.endpoint(), read.seq());
            String reader = read.endpoint().id();
            WriteRow held = chosen.containsKey(reader) ? chosen.get(reader)
                    : closure.joined.get(reader);
            // A join to the INITIAL the run took holds nothing: no
            // occurrence wrote it, only whichever access first observed the
            // location, which is the run's own history.
            if (held == null || !chosen.containsKey(reader)
                    && held.initial()) {
                continue;
            }
            String location = SmtLowering.locationKey(held.location());
            // A mint read lands on whichever racing occurrence reads the cell
            // first, so it is checked by the writer and the location
            // (runtime/Confirmation), not the reader, and holds no order: a
            // placeholder at the anchor joins the write it was laid over, so
            // a family may choose the location's INITIAL for it.
            boolean mint = read.mintVersion() != ReadRow.UNKNOWN_VERSION;
            JsonObject edge = new JsonObject();
            edge.addProperty("kind", "STATE");
            edge.addProperty("reader", Confirmation.id(read.endpoint()));
            edge.addProperty("readerAnyTurn",
                    Confirmation.anyTurn(read.endpoint()));
            edge.addProperty("mint", mint);
            edge.addProperty("writer", writer(held));
            edge.addProperty("version", held.version());
            edge.addProperty("location", location);
            holding.edges.add(edge);
            if (mint) continue;
            if (!held.initial()) {
                closure.order(holding, closure.exit(held.endpoint(),
                        held.seq()), read.endpoint(), read.seq());
            }
            // No other writer of the location it reads between the two: one
            // recorded before the write goes before it, any other after the
            // read.
            for (WriteRow other : closure.byLocation.get(location)) {
                if (other.endpoint().equals(held.endpoint())
                        || other.initial()) {
                    continue;
                }
                if (!held.initial() && other.seq() < held.seq()) {
                    closure.order(holding, closure.exit(
                            other.endpoint(), other.seq()), held.endpoint(),
                            held.seq());
                } else {
                    closure.order(holding, reading, other.endpoint(),
                            other.seq());
                }
            }
        }
        for (String order : holding.orders) {
            String[] ends = order.split("\n", 2);
            JsonObject row = new JsonObject();
            row.addProperty("kind", "ORDER");
            row.addProperty("before", ends[0]);
            row.addProperty("after", ends[1]);
            holding.edges.add(row);
        }
        return holding;
    }

    /**
     * One read, one writer: the model's choice and the world's pairing
     * holding one read to two writers is no model a run can take, refused
     * by name ({@code STATE_CONFLICT}), never the later row's.
     *
     * @throws Refused naming the read and its writers
     */
    private static void heldOnce(List<JsonObject> edges) {
        Map<String, String> writers = new LinkedHashMap<String, String>();
        for (JsonObject edge : edges) {
            if (!"STATE".equals(optionalString(edge, "kind"))) continue;
            String reader = optionalString(edge, "reader");
            String writer = optionalString(edge, "writer");
            String held = writers.put(reader, writer);
            if (held != null && !held.equals(writer)) {
                throw new Refused("STATE_CONFLICT: read " + reader
                        + " is held to writers " + held + " and " + writer
                        + ": the model's choice and the selected session's"
                        + " world disagree");
            }
        }
    }

    /** The writer a STATE row names: its endpoint as {@link Confirmation#id}
     *  names it, or {@link Confirmation#INITIAL}, which no occurrence
     *  wrote. */
    static String writer(WriteRow write) {
        return write.initial() ? Confirmation.INITIAL
                : Confirmation.id(write.endpoint());
    }

    /**
     * What holds an obligation replay to the pairings its world plants
     * ({@code ObligationFactory}: reader -> writer, each as {@link #writer}
     * names it): CONFIRM's rows ({@link #stateEdges}) over the session its
     * path was cut from, which the replay compares and holds
     * ({@code runtime.Confirmation}).  A pairing's write is the reader's
     * location's write by that writer, the one the read observed else the
     * last ({@code smt.Arms#stateArms}), or its INITIAL; the reader's reads
     * of the location are a block ({@link #stateEdges}).
     *
     * @throws Refused naming a pairing whose read or write the session does
     *         not state
     */
    static Holding holding(SessionReader session,
                           Map<String, String> pairings) {
        StateClosure closure = new StateClosure(session);
        List<ReadRow> reads = new ArrayList<ReadRow>();
        Map<String, WriteRow> chosen = new LinkedHashMap<String, WriteRow>();
        Set<String> found = new LinkedHashSet<String>();
        for (ReadRow read : session.reads()) {
            String reader = Confirmation.id(read.endpoint());
            String writer = pairings.get(reader);
            if (writer == null) continue;
            WriteRow held = null;
            for (WriteRow write : closure.byLocation.getOrDefault(
                    SmtLowering.locationKey(read.location()),
                    Collections.<WriteRow>emptyList())) {
                if (!writer.equals(writer(write))
                        || held != null && held.version()
                        == read.observedVersion()) {
                    continue;
                }
                if (held == null || write.version() == read.observedVersion()
                        || write.seq() > held.seq()) {
                    held = write;
                }
            }
            if (held == null) {
                throw new Refused("PAIRING_UNSTATED: the world pairs read "
                        + reader + " with writer " + writer + ", which "
                        + "session " + session.sessionId() + " states no "
                        + "write of " + read.location() + " by");
            }
            found.add(reader);
            reads.add(read);
            chosen.put(read.endpoint().id(), held);
        }
        Set<String> unread = new LinkedHashSet<String>(pairings.keySet());
        unread.removeAll(found);
        if (!unread.isEmpty()) {
            throw new Refused("PAIRING_UNSTATED: the world pairs read(s) "
                    + unread + ", which session " + session.sessionId()
                    + " states no read at");
        }
        return stateEdges(closure, reads, chosen, true);
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
