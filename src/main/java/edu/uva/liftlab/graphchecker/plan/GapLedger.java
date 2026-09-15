package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The one register of every gap code this pipeline can publish.
 *
 * <p>Design point 5 says a missing chain link is a reported gap that blocks
 * the claim.  Before this class there were two registers: a small blocking
 * set assembled in the shell out of {@code finalStatusRefusals} and the
 * solver's own gaps, and a much larger {@code telemetryGaps} array that no
 * claim ever read.  A loop whose body count nothing checked, a region whose
 * causal anchor was never observed, a map carrier with no map, a fault the
 * composer named and moved on from -- all of those landed in the second
 * register and none of them withheld anything.</p>
 *
 * <p>So there is one register, and it is fail-closed in three separate
 * senses:</p>
 *
 * <ul>
 *   <li>Every code is classed here, in this file, and nowhere else.</li>
 *   <li>A code nobody registered is {@link GapClass#BLOCKING}.  Adding a new
 *       gap to some stage therefore withholds claims until somebody comes
 *       here and writes down why it cannot break a chain.</li>
 *   <li>{@link GapClass#DIAGNOSTIC} requires a stated justification, and the
 *       registry refuses an entry without one.  "Provably cannot change the
 *       chain" is the only admissible reason, and it has to fit in a
 *       sentence a reader can check.</li>
 * </ul>
 *
 * <p>Two readers consume this table.  the claim policy reads
 * {@link #blocking(String)} for every gap the composition manifest and the
 * reach report publish, so the Java claim and the published gap count rest on
 * one classification.  {@code run_engine.sh} reads the JSON this class emits
 * ({@code --output}) so that the stages the claim cannot see -- IMPORT,
 * EXPLORE and CLASSIFY -- are partitioned by the same table.</p>
 *
 * <p>A gap code says a chain link is missing.  It is not the place to say a
 * <em>mechanism</em> is out of scope, and one is: {@code ROTATION_RACE} --
 * the fatal read taking the program's own last writer while the same
 * location is written again later -- was retired from
 * the claim's finding kinds rather than registered here.  No
 * gap replaces it, because nothing is missing from any chain this pipeline
 * builds: each replay fixes its own interleaving of that write and that
 * read, the merge is a disjunction over replays that ran, and no path can
 * exhibit a rotation order different from the one it executed.  Nothing here
 * explores thread schedules; doing so would be a separate feature, and it
 * would come with its own statement of which interleavings were searched --
 * at which point the unsearched ones, not the mechanism, are what a gap code
 * would be about.</p>
 */
public final class GapLedger {
    /** Artifact kind of the published ledger. */
    public static final String KIND = "GAP_LEDGER";
    public static final int SCHEMA_VERSION = 1;

    /** What a gap code does to a claim. */
    public enum GapClass {
        /**
         * A missing chain element, or freedom nobody accounted for.  The
         * claim is withheld while one of these is open.  This is the class
         * of every code nobody registered.
         */
        BLOCKING,
        /**
         * Provably cannot change the chain the claim rests on.  Every entry
         * of this class carries the proof sketch in {@link Entry#reason}.
         */
        DIAGNOSTIC
    }

    /**
     * What a registered code's class depends on.
     *
     * <p>Most codes answer the same way wherever they are raised.  A few
     * are decided by the campaign fold, which can see the composed formula
     * the readers in this JVM cannot.</p>
     */
    public enum Scope {
        /** The class in the entry, wherever the code is raised. */
        ALWAYS
    }

    /** One registered code. */
    public static final class Entry {
        public final String code;
        /** The producing stage/source pair this code is published under. */
        public final String source;
        public final GapClass gapClass;
        public final Scope scope;
        /** Why the class is what it is; required for DIAGNOSTIC. */
        public final String reason;
        /**
         * Why this code is DIAGNOSTIC on a flip-wave row, or {@code ""}.
         *
         * <p>A qualifier, not a scope: it answers a different question from
         * {@link #scope} and the two compose.  It applies only to a row
         * whose subject is a flip-replay task, and only the campaign fold
         * can see that, so every reader that cannot keeps answering with
         * {@link #gapClass}.</p>
         */
        public final String flipWaveReason;

        Entry(String code, String source, GapClass gapClass, Scope scope,
              String reason, String flipWaveReason) {
            this.code = code;
            this.source = source;
            this.gapClass = gapClass;
            this.scope = scope;
            this.reason = reason;
            this.flipWaveReason = flipWaveReason;
        }

        JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("code", code);
            row.addProperty("source", source);
            row.addProperty("class", gapClass.name());
            row.addProperty("scope", scope.name());
            row.addProperty("reason", reason);
            if (!flipWaveReason.isEmpty()) {
                row.addProperty("flipWaveClass",
                        GapClass.DIAGNOSTIC.name());
                row.addProperty("flipWaveReason", flipWaveReason);
            }
            return row;
        }
    }

    private static final Map<String, Entry> REGISTRY = new LinkedHashMap<>();

    private static void blocking(String source, String code, String reason) {
        register(new Entry(code, source, GapClass.BLOCKING, Scope.ALWAYS,
                reason, ""));
    }

    private static void diagnostic(String source, String code,
                                   String reason) {
        requireReason(code, reason);
        register(new Entry(code, source, GapClass.DIAGNOSTIC, Scope.ALWAYS,
                reason, ""));
    }

    private static void requireReason(String code, String reason) {
        if (reason == null || reason.trim().isEmpty()) {
            throw new IllegalStateException(
                    "a gap code whose class is anything but the blocking"
                            + " default states why: " + code);
        }
    }

    private static void register(Entry entry) {
        Entry previous = REGISTRY.put(entry.code, entry);
        if (previous != null && previous.gapClass != entry.gapClass) {
            throw new IllegalStateException(
                    "gap code registered twice with different classes: "
                            + entry.code);
        }
    }

    static {
        // ------------------------------------------------------------------
        // COMPOSE / COMPOSER -- the AcceptanceGate's own refusals.  Every one
        // of these already withheld a claim before this ledger existed; they
        // are named here so the table is the whole vocabulary and not the
        // part of it somebody thought was interesting.
        // ------------------------------------------------------------------
        String composer = "COMPOSE/COMPOSER";
        blocking(composer, "COMPOSITION_GAP",
                "the emitter refused a term it could not lower, so the"
                        + " formula does not contain the step it refused");
        blocking(composer, "FORMULA_SAT_AT_RECORDED_VALUATION",
                "the composed formula is satisfiable with every declared root"
                        + " at the value the recording read, on a run whose"
                        + " recording took the healthy arm: a formula that"
                        + " answers yes to the execution that did not fail"
                        + " answers nothing about the one that would");
        // The acceptance gate spells a refusal CODE[subject] or CODE:subject
        // and publishes it under one COMPOSITION_GAP kind; run_engine.sh
        // decodes that spelling before classing the row, so the ledger sees
        // the reason the emitter actually named.  All of them refuse, which
        // is what makes them blocking -- they are listed so the vocabulary is
        // written down rather than left to the default.
        for (String code : new String[]{
                "WIRE_FLOW_VALUE_UNBOUND",
                "MODEL_SEMANTICS_MISSING"}) {
            blocking(composer, code,
                    "a refusal the composer made: the step it refused is not in"
                            + " the formula the witness satisfies");
        }

        // ------------------------------------------------------------------
        // COMPOSE / BOUNDED_LOOP -- the per-case
        // loop-count reasons the importer copies out of the replay.  A loop
        // whose body count this composition cannot check against a declared
        // bound is a step of the chain stated at an unknown multiplicity.
        // ------------------------------------------------------------------
        String loops = "COMPOSE/BOUNDED_LOOP";
        blocking(loops, "BOUNDED_LOOP_COMPOSITION_GAP",
                "a retained loop this composition could not check");
        blocking(loops, "BOUNDED_LOOP_BODY_BOUND_DISAGREES",
                "two declarations state different K_L for one loop, so the"
                        + " modelled prefix is not the one the replay ran");
        // Under path merging each path is one concrete execution, in which
        // every loop ran a definite number of times; the formula states that
        // execution, not a modelled prefix of it.  Completeness over
        // root-dependent behaviour is CLOSURE_INCOMPLETE instead -- a loop
        // guard that depends on a root is a branch, and a branch gets
        // flipped.  An undeclared bound on a loop no root reaches changes no
        // element of the chain, so this is a coverage note.
        diagnostic(loops, "BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
                "a loop runs under an inherited resource ceiling nobody"
                        + " declared: each merged path ran it a definite"
                        + " number of times, and a root-dependent guard is"
                        + " a branch the exploration flips, so what is"
                        + " unstated here is coverage rather than a step"
                        + " of the chain");
        blocking(loops, "BOUNDED_LOOP_CLASSIFICATION_UNDECLARED",
                "a retained loop has no supported classification, so nothing"
                        + " decides how its body count is bounded");
        blocking(loops, "BOUNDED_LOOP_CLASSIFICATION_DISAGREES",
                "declarations disagree on a loop's kind");
        diagnostic(loops, "BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT",
                "one nest's guards classify differently, so the nest has no"
                        + " single kind and its published kind is the weaker"
                        + " of two answers -- which decides how a bound would"
                        + " be checked, not what any merged path executed");
        blocking(loops, "BOUNDED_LOOP_OBSERVED_UNDECLARED",
                "the replay traversed a retained loop this composition"
                        + " declared no bound for");
        blocking(loops, "BOUNDED_LOOP_SITE_UNDECLARED",
                "a retained loop names no loop site, so no declaration can"
                        + " reach it");
        blocking(loops, "BOUNDED_LOOP_BODY_BOUND_OUT_OF_RANGE",
                "a declared K_L outside the admissible range is refused by"
                        + " name rather than clamped");
        blocking(loops, "BOUNDED_LOOP_BODY_BOUND_SITE_UNDECLARED",
                "a declared K_L names no retained loop, so some loop the"
                        + " campaign meant to bound is unbounded");
        blocking(loops, "PATH_LOCAL_LOOP_COUNT_MISSING",
                "a replayed case published no body count for a retained"
                        + " loop");
        blocking(loops, "PATH_LOCAL_LOOP_COUNT_AMBIGUOUS",
                "one case published two body counts for one loop");
        blocking(loops, "PATH_LOCAL_LOOP_COUNT_OUT_OF_BOUND",
                "a replayed body count exceeds the declared bound, so the"
                        + " modelled prefix is shorter than the execution");
        blocking(loops, "PATH_LOCAL_LOOP_REACHABILITY_MISSING",
                "nothing states whether the case entered the loop at all");
        blocking(loops, "PATH_LOCAL_ARRAY_CARDINALITY_MISSING",
                "an indexed loop has no dense exact cardinality vector"
                        + " covering its body count, so the number of times"
                        + " its body ran is not pinned by the recording");

        // ------------------------------------------------------------------
        // COMPOSE / SYMBOLIC_PROPAGATION.  Each
        // of these is a read whose writer, arm, case or payload the closure
        // could not name; that is exactly a link of the read-from chain.
        // ------------------------------------------------------------------
        // The consumer-boundary family is gone with the arms that built it:
        // nineteen codes -- CONSUMER_BOUNDARY_* and
        // RPC_CONSUMER_BOUNDARY_MALFORMED -- were defined nowhere but here,
        // naming producer-case linking and boundary families that no stage
        // raises any more.  A handoff is now one variable v_H at one
        // occurrence H, and what can be missing about it is stated on the
        // row by the attach's own fault check.
        String propagation = "COMPOSE/SYMBOLIC_PROPAGATION";
        for (String code : new String[]{
                "RPC_ATTACH_SENDER_EXPRESSION_MISSING"}) {
            blocking(propagation, code,
                    "a read whose writer, arm, case, version or payload the"
                            + " propagation closure could not name is a link"
                            + " of the read-from chain the formula leaves"
                            + " unconstrained");
        }

        diagnostic(propagation, "INITIAL_CONTAINER_SNAPSHOT_TRUNCATED",
                "a container whose initial content the recording did not"
                        + " watch being produced: the value is still the"
                        + " value, and a carrier the fatal read never touches"
                        + " is not on the chain a witness stands on -- so"
                        + " promoting"
                        + " the row itself would replace a per-witness proof"
                        + " with a coarser guess, not add one");

        // ------------------------------------------------------------------
        // COMPOSE / FAULT_CONTROL.  The marker is the experiment's own
        // hypothesis; a read the marker starves, or a selector the driver may
        // pin, decides the marker outside the formula.
        // ------------------------------------------------------------------
        String fault = "COMPOSE/FAULT_CONTROL";

        // ------------------------------------------------------------------
        // COMPOSE / COVERAGE.
        // ------------------------------------------------------------------
        diagnostic("COMPOSE/COVERAGE", "SELECTED_PATH_SET_INCOMPLETE",
                "path-set completeness is required only to close an UNSAT"
                        + " refutation, and the claim policy already withholds"
                        + " that conclusion by name through"
                        + " UNSAT_CLOSURE_INCOMPLETE, so this row can never"
                        + " be the only thing between a SAT witness and its"
                        + " chain");

        // ------------------------------------------------------------------
        // SOLVE / SOLVER.
        // ------------------------------------------------------------------
        String solver = "SOLVE/SOLVER";
        blocking(solver, "SOLVER_TIMEOUT",
                "a flip query the solver never answered leaves the root it"
                        + " was asked about unresolved");

        // ------------------------------------------------------------------
        // EXPLORE / PATH_WORKLIST.
        // ------------------------------------------------------------------
        String explore = "EXPLORE/PATH_WORKLIST";
        blocking(explore, "SHARED_STATE_GAP",
                "a shared-state carrier whose map, receiver locator or"
                        + " access anchor is missing is a read with no"
                        + " stated source");
        blocking(explore, "NO_OBSERVED_PATH_SEED",
                "nothing observed seeds this region's path space");
        // The sibling-path family.  Every one of these says some path other
        // than the one the witness walks was not explored, and every one of
        // them lands in a summary's coverageGaps, which run_engine.sh reads
        // as pathSetClosed=false (see campaign_explore); the composer then
        // publishes pathSetComplete=false and the claim policy withholds
        // UNSAT_CLOSED by name under UNSAT_CLOSURE_INCOMPLETE.  So the one
        // conclusion these can falsify is already withheld by name, and the
        // chain a SAT witness reports contains no sibling path by
        // construction.  This is also why BOUND_REACHED had to start firing
        // at the worklist's task ceiling: an unexplored path that published
        // no row left coverageState reading CLOSED, and then nothing
        // withheld the UNSAT conclusion either.
        for (String code : new String[]{
                "PATH_FLIP_REPLAY_NOT_ADMITTED",
                "PATH_FLIP_SOLVER_TIMEOUT",
                "REGION_PATH_WAVE_BUDGET_REACHED",
                "REGION_PATH_CLOSURE_NO_PROGRESS"}) {
            diagnostic(explore, code,
                    "an unexplored sibling path is not a link of the chain"
                            + " the witness walks, and the one conclusion it"
                            + " can falsify -- a closed UNSAT -- is withheld"
                            + " by name, because this row makes the"
                            + " summary's path set unclosed and the claim policy"
                            + " blocks UNSAT_CLOSURE_INCOMPLETE on exactly"
                            + " that");
        }

        // ------------------------------------------------------------------
        // IMPORT / IMPORTER.
        // ------------------------------------------------------------------
        String importer = "IMPORT/IMPORTER";
        // Slice-aware, not blanket.  The static plan over-approximates: it
        // admits every region the backward walk reaches, and the replay
        // slice then keeps the ones root dependence actually selected.  A
        // planned region that never ran is a broken chain when the slice
        // kept it and an over-approximation of the plan when it did not.
        blocking(importer, "ROOT_LOOP_OCCURRENCE_UNADDRESSED",
                "a loop-body task whose planned occurrence names no k: a"
                        + " bounded loop publishes the activations some task"
                        + " addresses, so an unaddressed one would have to be"
                        + " defaulted to the first or to any, and neither is"
                        + " something the recording said");
        // ------------------------------------------------------------------
        // IMPORT / PUBLICATION_CONTRACT -- one pass at the end of IMPORT over
        // what the replay wave actually published.  Each code names a link
        // the plan asked for and the corpus does not carry, so each is
        // BLOCKING and the campaign stops before EXPLORE rather than meeting
        // the same hole there as an unexecutable worklist.
        // ------------------------------------------------------------------
        String contract = "IMPORT/PUBLICATION_CONTRACT";
        blocking(contract, "PUBLICATION_TASK_ANSWERED_BY_NO_RUN",
                "every run this task was offered to declined it for being"
                        + " addressed elsewhere and none answered it, so its"
                        + " region was not replayed at all");
        diagnostic(importer, "PLANNED_HANDOFF_NOT_REPRODUCED",
                "a selected communication binding this replay did not"
                        + " reproduce is an admission gap of this epoch, not"
                        + " a new topology: the paths it did publish still"
                        + " extend the epoch");
        diagnostic(importer, "TOPOLOGY_DIVERGENCE",
                "a flip that changes the topology found a new one: the"
                        + " handoff or occurrence it ran is exact evidence"
                        + " the plan had not addressed, so the bundle is"
                        + " kept whole, held out of this epoch's"
                        + " composition, and SEEDS EPOCH e+1, where that"
                        + " replay's own trace is the recording and PLAN,"
                        + " INSTRUMENT and REPLAY run again on it --"
                        + " withholding the claim on it would refuse the run"
                        + " for having learned something, and composing it"
                        + " with this epoch would merge two causal graphs");
        blocking(importer, "TARGET_REACH_NOT_OBSERVED",
                "the replay published no observation of the target this"
                        + " task was addressed at");
        for (String code : new String[]{
                "REPLAY_LOOP_RESOURCE_CAP",
                "LOOP_BOUND_PATH_CUT",
                "CONCOLIC_RESULT_REPLAY_GROUP_MISSING"}) {
            blocking(importer, code,
                    "a planned region, task or event the replay did not produce, or"
                            + " produced in a shape the importer could not read, contributes no"
                            + " case to the selected path set");
        }

        // ------------------------------------------------------------------
        // CLASSIFY / IMPORTER -- topology deltas.
        // ------------------------------------------------------------------
        String classify = "CLASSIFY/IMPORTER";
        blocking(classify, "COVERAGE_GAP",
                "a planned task produced no result, so a case the plan"
                        + " demanded is not in the recording");

        // ------------------------------------------------------------------
        // REPLAY / TASK_ADMISSION -- the one row a replay publishes about a
        // planned task no activation of it answered.
        // ------------------------------------------------------------------
        diagnostic("REPLAY/TASK_ADMISSION", "TASK_UNANSWERED",
                "a task nothing answered published no activation, no"
                        + " decision and no term, so no path of the composed"
                        + " formula cites it and this row cannot remove a"
                        + " link from a chain that was built -- the one"
                        + " absence that can, the declared target"
                        + " occurrence, is refused at REPLAY's own target"
                        + " coverage gate, which reads the target row");

        // ------------------------------------------------------------------
        // REPLAY / COMMUNICATION -- the message envelope's own findings.  A

        // ------------------------------------------------------------------
        // PLAN / STATIC -- the static catalog and the runtime-selected region
        // finalizer.  These used to be published to a seed artifact nothing
        // downstream read.
        // ------------------------------------------------------------------
        String plan = "PLAN/STATIC";
        diagnostic(plan, "BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED",
                "an array-indexed loop's trip count is its array length, and"
                        + " the loop-bound policy checks every replayed case"
                        + " of it against a dense exact cardinality vector"
                        + " covering the body count -- raising the blocking"
                        + " PATH_LOCAL_ARRAY_CARDINALITY_MISSING where the"
                        + " replay published none, and the blocking"
                        + " BOUNDED_LOOP_OBSERVED_UNDECLARED where no bounded"
                        + " loop was admitted for it at all -- so this static"
                        + " row names which loops rest on that check and the"
                        + " case where the count is missing is withheld by"
                        + " name");
        blocking(plan, "BOUND_INSUFFICIENT",
                "one static site demanded more activation-local accesses"
                        + " than the finalizer retains, so the port below it"
                        + " is under-approximated and the accesses it"
                        + " dropped are invisible to every later stage");
        diagnostic(plan, "SYMBOLIC_INPUT_REGION_ID_DECLARATION",
                "the manual root is declared and admitted either way: this"
                        + " says only that the campaign spelled the region as"
                        + " a planner-minted hash rather than as the static"
                        + " site it belongs to, and a hash moves when the"
                        + " retained selection moves -- the root itself is in"
                        + " the plan, so no chain link is missing and the"
                        + " site form is the thing to rewrite");

        // ------------------------------------------------------------------
        // CAMPAIGN.
        // ------------------------------------------------------------------
        blocking("CLASSIFY/CAMPAIGN", "ITERATION_BOUND_REACHED",
                "the campaign stopped at its declared iteration bound with"
                        + " the topology still diverging, so no candidate"
                        + " was composed");
    }

    private GapLedger() {
    }

    /**
     * The class of {@code code}.  An unregistered code is BLOCKING: a gap
     * nobody classified is not a reason to stop withholding on it.
     */
    public static GapClass classOf(String code) {
        Entry entry = code == null ? null : REGISTRY.get(code.trim());
        return entry == null ? GapClass.BLOCKING : entry.gapClass;
    }

    /** Whether {@code code} withholds a claim. */
    public static boolean blocking(String code) {
        return classOf(code) == GapClass.BLOCKING;
    }

    /** The registered blocking codes, in registration order. */
    public static Set<String> blockingCodes() {
        return codesOf(GapClass.BLOCKING);
    }

    /** The registered diagnostic codes, in registration order. */
    public static Set<String> diagnosticCodes() {
        return codesOf(GapClass.DIAGNOSTIC);
    }

    private static Set<String> codesOf(GapClass gapClass) {
        Set<String> codes = new LinkedHashSet<>();
        for (Entry entry : REGISTRY.values()) {
            if (entry.gapClass == gapClass) codes.add(entry.code);
        }
        return Collections.unmodifiableSet(codes);
    }

    /** Every registered entry, in registration order. */
    public static List<Entry> entries() {
        return Collections.unmodifiableList(
                new ArrayList<>(REGISTRY.values()));
    }

    /**
     * The ledger as the shell reads it.
     *
     * <p>{@code diagnostic} is the whole exception list: {@code run_engine.sh}
     * treats every code outside it as blocking, which is the same default
     * {@link #classOf(String)} applies, so a code added to one stage and
     * forgotten here withholds claims in both readers.</p>
     */
    public static JsonObject toJson() {
        JsonObject ledger = new JsonObject();
        ledger.addProperty("schemaVersion", SCHEMA_VERSION);
        ledger.addProperty("kind", KIND);
        ledger.addProperty("defaultClass", GapClass.BLOCKING.name());
        JsonArray rows = new JsonArray();
        for (Entry entry : REGISTRY.values()) rows.add(entry.toJson());
        ledger.add("entries", rows);
        JsonArray diagnostic = new JsonArray();
        for (String code : diagnosticCodes()) diagnostic.add(code);
        ledger.add("diagnostic", diagnostic);
        JsonObject reasons = new JsonObject();
        for (Entry entry : REGISTRY.values()) {
            reasons.addProperty(entry.code, entry.reason);
        }
        ledger.add("reasonByCode", reasons);
        JsonArray blocking = new JsonArray();
        for (String code : blockingCodes()) blocking.add(code);
        ledger.add("blocking", blocking);
        return ledger;
    }

    /** Publishes the ledger so the shell classes gaps from the same table. */
    public static void main(String[] argv) throws Exception {
        Path output = null;
        for (int index = 0; argv != null && index < argv.length; index++) {
            if (!"--output".equals(argv[index]) || index + 1 >= argv.length) {
                throw new IllegalArgumentException(
                        "Expected --output path, got " + argv[index]);
            }
            output = Paths.get(argv[++index]);
        }
        Gson gson = new GsonBuilder().disableHtmlEscaping()
                .setPrettyPrinting().create();
        String json = gson.toJson(toJson());
        if (output == null) {
            System.out.println(json);
            return;
        }
        Path parent = output.getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(output, (json + System.lineSeparator())
                .getBytes(StandardCharsets.UTF_8));
    }
}
