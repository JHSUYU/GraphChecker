package edu.uva.liftlab.graphchecker.contract;

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
 * <p>Two readers consume this table.  {@code ClaimPolicy} reads
 * {@link #blocking(String)} for every gap the composition manifest and the
 * reach report publish, so the Java claim and the published gap count rest on
 * one classification.  {@code run_engine.sh} reads the JSON this class emits
 * ({@code --output}) so that the stages the claim cannot see -- IMPORT,
 * EXPLORE and CLASSIFY -- are partitioned by the same table.</p>
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
     * <p>Most codes answer the same way wherever they are raised.  Three do
     * not: a planned region that never ran is a broken chain when the replay
     * slice kept that region, and an over-approximation of the static plan
     * when root dependence never selected it.  Those carry
     * {@link #KEPT_SLICE} and are decided against the slice the campaign
     * actually ran.</p>
     */
    public enum Scope {
        /** The class in the entry, wherever the code is raised. */
        ALWAYS,
        /**
         * BLOCKING when the row's subject names a task or occurrence the
         * replay slice kept -- a task the plan said must run and publish,
         * for one of TARGET_REACH, ROOT_SITE, CARRIER_WRITER,
         * ROOT_DEPENDENT_FLOW or FATAL_READ_WRITER -- and DIAGNOSTIC when it
         * names a statically planned region the slice pruned.  Where the
         * slice is unknown, withheld, or the subject maps to no planned
         * occurrence, the answer is BLOCKING.
         */
        KEPT_SLICE
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

        Entry(String code, String source, GapClass gapClass, Scope scope,
              String reason) {
            this.code = code;
            this.source = source;
            this.gapClass = gapClass;
            this.scope = scope;
            this.reason = reason;
        }

        JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("code", code);
            row.addProperty("source", source);
            row.addProperty("class", gapClass.name());
            row.addProperty("scope", scope.name());
            row.addProperty("reason", reason);
            return row;
        }
    }

    private static final Map<String, Entry> REGISTRY = new LinkedHashMap<>();

    private static void blocking(String source, String code, String reason) {
        register(new Entry(code, source, GapClass.BLOCKING, Scope.ALWAYS,
                reason));
    }

    private static void diagnostic(String source, String code,
                                   String reason) {
        requireReason(code, reason);
        register(new Entry(code, source, GapClass.DIAGNOSTIC, Scope.ALWAYS,
                reason));
    }

    /**
     * Blocking on the kept replay slice, diagnostic off it.
     *
     * <p>The entry's own class is BLOCKING, which is what every reader that
     * cannot see the slice answers.</p>
     */
    private static void onKeptSlice(String source, String code,
                                    String reason) {
        requireReason(code, reason);
        register(new Entry(code, source, GapClass.BLOCKING, Scope.KEPT_SLICE,
                reason));
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
        blocking(composer, "TARGET_REACH_QUERY_ABSENT",
                "no target reach query means the formula asks no question"
                        + " about the target");
        blocking(composer, "MissingTargetInstanceSymbolicContext",
                "the target activation carries no symbolic context, so no"
                        + " root reaches it");
        blocking(composer, "GUARDED_READ_ORDER_UNKNOWN",
                "a read whose candidate writers admit no single program"
                        + " order carries no last-writer-wins axiom, so its"
                        + " arms do not describe a sequence of writes");
        blocking(composer, "FAULT_IDLE_INITIAL_HOST_UNKNOWN",
                "an INITIAL arm that names no activation whose entry took"
                        + " the snapshot leaves the fault claiming something"
                        + " about a version nobody observed");
        // The acceptance gate spells a refusal CODE[subject] or CODE:subject
        // and publishes it under one COMPOSITION_GAP kind; run_engine.sh
        // decodes that spelling before classing the row, so the ledger sees
        // the reason the emitter actually named.  All of them refuse, which
        // is what makes them blocking -- they are listed so the vocabulary is
        // written down rather than left to the default.
        for (String code : new String[]{
                "EXECUTION_DIVERGENCE",
                "GUARDED_READ_WRITER_CASE_UNLINKED",
                "WIRE_FLOW_VALUE_UNBOUND",
                "WIRE_FLOW_CONSUMER_FIELD_UNATTACHED",
                "StructuralWitnessExecutionScopeMissing",
                "StructuralWitnessExecutionScopeConflict",
                "StructuralWitnessIdentityMissing",
                "StructuralWitnessContainerShapeConflict",
                "RequestFaultControlAmbiguous",
                "RequestFaultControlMarkerMissing",
                "SymbolicSourceAuthorityMissing",
                "SymbolicSourceEvidenceMalformed",
                "ConfiguredSourceMaterializationConflict",
                "ConfiguredSourceMaterializationMissing",
                "ConfiguredSourceMaterializationSortConflict",
                "ConfiguredSourceMaterializationSourceKeyMissing",
                "ConfiguredSourcePhaseEventConflict",
                "ConfiguredSourceRecordedEventConflict",
                "ContainerOperandSort",
                "GuardedMergeArmSortConflict",
                "GuardedMergeCycle",
                "GuardedMergeMalformed",
                "ManualSourceMaterializationConflict",
                "ManualSourceMaterializationMissing",
                "ManualSourceMaterializationSortConflict",
                "MODEL_SEMANTICS_MISSING",
                "PlaceholderExpression",
                "SelectedConcreteTargetObservationMalformed",
                "SelectedConcreteTargetObservationMissing",
                "SelectedConcreteTargetReachEventMismatch",
                "SelectedTargetPathWitnessMalformed",
                "SelectedTargetPathWitnessMismatch",
                "SelectedTargetPathWitnessMissing",
                "SelectedTargetPredicateMismatch",
                "SelectedTargetReachEventMalformed",
                "SelectedTargetReachEventMismatch",
                "SelectedTargetReachEventMissing",
                "SelectedTargetSourceAttestationMalformed",
                // A value the replay did not determine, and a merge over
                // another region's cases: both are the propagation cut
                // arriving at a lowering, refused rather than chosen
                // between.  The nine refusals that used to name which part
                // of a read's arm set could not be stated are retired with
                // the arms.
                "UNRESOLVED_SHARED_READ",
                "CASE_MERGE_IN_PATH",
                "UnconstrainedContainerRead"}) {
            blocking(composer, code,
                    "a refusal the composer made: the step it refused is not in"
                            + " the formula the witness satisfies");
        }

        // ------------------------------------------------------------------
        // COMPOSE / BOUNDED_LOOP -- BoundedLoopComposition, and the per-case
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
        blocking(loops, "BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
                "a loop runs under an inherited resource ceiling nobody"
                        + " declared, so its prefix is unstated");
        blocking(loops, "BOUNDED_LOOP_CLASSIFICATION_UNDECLARED",
                "a retained loop has no supported classification, so nothing"
                        + " decides how its body count is bounded");
        blocking(loops, "BOUNDED_LOOP_CLASSIFICATION_DISAGREES",
                "declarations disagree on a loop's kind");
        blocking(loops, "BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT",
                "one nest's guards classify differently, so the nest has no"
                        + " single kind and its published kind is the weaker"
                        + " of two answers");
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
        // COMPOSE / SYMBOLIC_PROPAGATION -- SymbolicPropagationClosure.  Each
        // of these is a read whose writer, arm, case or payload the closure
        // could not name; that is exactly a link of the read-from chain.
        // ------------------------------------------------------------------
        String propagation = "COMPOSE/SYMBOLIC_PROPAGATION";
        for (String code : new String[]{
                "CASE_CLOSURE_IDENTITY_MISSING",
                "CASE_CLOSURE_IDENTITY_AMBIGUOUS",
                "CONSUMER_BOUNDARY_ARM_BOUND",
                "CONSUMER_BOUNDARY_ARM_INCOMPLETE",
                "CONSUMER_BOUNDARY_EVENT_AMBIGUOUS",
                "CONSUMER_BOUNDARY_FAMILY_CYCLE",
                "CONSUMER_BOUNDARY_FAMILY_EPOCH_CONFLICT",
                "CONSUMER_BOUNDARY_FAMILY_MISSING",
                "CONSUMER_BOUNDARY_FAMILY_TYPE_CONFLICT",
                "CONSUMER_BOUNDARY_FAMILY_TYPE_MISSING",
                "CONSUMER_BOUNDARY_FAMILY_UNOBSERVED",
                "CONSUMER_BOUNDARY_LOCATION_UNSTABLE",
                "CONSUMER_BOUNDARY_OBSERVATION_AMBIGUOUS",
                "CONSUMER_BOUNDARY_OBSERVATION_MISSING",
                "CONSUMER_BOUNDARY_OBSERVATION_SCOPE_MISSING",
                "CONSUMER_BOUNDARY_OWNER_CASE_AMBIGUOUS",
                "CONSUMER_BOUNDARY_OWNER_CASE_MISSING",
                "CONSUMER_BOUNDARY_PAYLOAD_TRUNCATED",
                "CONSUMER_BOUNDARY_PRODUCER_CASE_AMBIGUOUS",
                "CONSUMER_BOUNDARY_PRODUCER_CASE_MISSING",
                "INITIAL_SNAPSHOT_HOST_UNKNOWN",
                "LOCAL_CASE_OBSERVATION_AMBIGUOUS",
                "LOCAL_CASE_OBSERVATION_MISSING",
                "LOCAL_CASE_OBSERVATION_PC_MISSING",
                "LOCAL_CASE_OBSERVATION_SCOPE_MISSING",
                "READ_CHOICE_IDENTITY_MISSING",
                "READ_FROM_CANDIDATE_IDENTITY_MISSING",
                "READ_FROM_CANDIDATE_SNAPSHOT_MISMATCH",
                "READ_FROM_INITIAL_SOURCE_MISSING",
                "READ_FROM_SNAPSHOT_INCOMPLETE",
                "READ_FROM_SNAPSHOT_MISMATCH",
                "READ_FROM_WRITER_CASE_AMBIGUOUS",
                "READ_FROM_WRITER_CASE_CLOSURE_EMPTY",
                "READ_FROM_WRITER_CASE_CLOSURE_MISMATCH",
                "READ_FROM_WRITER_CASE_CLOSURE_MISSING",
                "READ_FROM_WRITER_CASE_CLOSURE_OMITS_WRITER",
                "READ_FROM_WRITER_CASE_MISSING",
                "READ_FROM_WRITER_CASE_PARTITION_INCOMPLETE",
                "READ_FROM_WRITER_CASE_PC_MISSING",
                "READ_FROM_WRITER_VERSION_AMBIGUOUS",
                "RPC_ATTACH_SENDER_EXPRESSION_MISSING",
                "RPC_CONSUMER_BOUNDARY_MALFORMED"}) {
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
        blocking(fault, "FAULT_IDLE_NO_RETAINED_ARM",
                "the fault idles every candidate writer of a read and the"
                        + " location published no retained prior version, so"
                        + " the reading case observes nothing");
        blocking(fault, "FAULT_IDLE_INITIAL_HOST_IDLED",
                "the marker idles the activation whose entry took the"
                        + " INITIAL snapshot, so the snapshot holds a JVM"
                        + " default rather than the version the fault"
                        + " retained");
        blocking(fault, "FAULT_PARTITION_UNSPLIT",
                "a fault-controlled selector the reach driver may pin would"
                        + " freeze the marker the claim is about");

        // ------------------------------------------------------------------
        // COMPOSE / COVERAGE.
        // ------------------------------------------------------------------
        diagnostic("COMPOSE/COVERAGE", "SELECTED_PATH_SET_INCOMPLETE",
                "path-set completeness is required only to close an UNSAT"
                        + " refutation, and ClaimPolicy already withholds"
                        + " that conclusion by name through"
                        + " UNSAT_CLOSURE_INCOMPLETE, so this row can never"
                        + " be the only thing between a SAT witness and its"
                        + " chain");

        // ------------------------------------------------------------------
        // SOLVE / SOLVER.
        // ------------------------------------------------------------------
        String solver = "SOLVE/SOLVER";
        blocking(solver, "COMPOSITION_MANIFEST_NOT_CANDIDATE_MODEL_ELIGIBLE",
                "the manifest the solver was handed is not a candidate"
                        + " model, so its answer is about something other"
                        + " than an accepted composition");
        blocking(solver, "SOLVER_TIMEOUT",
                "a flip query the solver never answered leaves the root it"
                        + " was asked about unresolved");
        // These two are published as CODE:detail, so the row's code carries a
        // suffix and falls through classOf to the blocking default.  They are
        // named here so the vocabulary is complete and the default is not the
        // only thing documenting them.
        blocking(solver, "ROOT_BOOLEAN_INPUT_LIMIT_EXCEEDED",
                "the Boolean root space was larger than the enumeration"
                        + " bound, so the valuations below it are a sample"
                        + " and not the space");
        blocking(solver, "BOOLEAN_VALUATION_LIMIT_EXCEEDED",
                "the enumeration stopped short of the valuations the root"
                        + " space has, so an unsat answer is about the"
                        + " sample");
        for (String code : new String[]{
                "COMPOSED_SMT_EMPTY",
                "CASE_PATH_CONDITION_DEPENDENCIES_MISSING",
                "CASE_SELECTOR_PARTITIONS_MISSING",
                "CASE_SELECTOR_PARTITION_MALFORMED",
                "CASE_SELECTOR_PARTITION_DUPLICATE",
                "CASE_PATH_CONDITION_DEPENDENCY_MALFORMED",
                "CASE_PATH_CONDITION_ARM_MALFORMED",
                "INITIAL_SOURCE_DEPENDENCY_MALFORMED",
                "CASE_DEPENDENCY_TARGET_GUARD_NOT_UNIQUE",
                "CASE_DEPENDENCY_SELECTOR_PARTITION_NOT_UNIQUE",
                "CASE_DEPENDENCY_SELECTOR_DECLARATION_MISSING",
                "CASE_DEPENDENCY_BASE_SELECTOR_DECLARATION_MISSING",
                "CASE_DEPENDENCY_TARGET_DEFINITION_MISSING",
                "CASE_DEPENDENCY_PC_DEFINITION_MISSING",
                "CASE_DEPENDENCY_BASE_DEFINITION_MISSING",
                "CONFIGURED_SOURCE_TERM_NOT_DECLARED_OR_SORT_MISMATCH",
                "MANUAL_SYMBOLIC_ROOT_TERM_NOT_DECLARED_OR_SORT_MISMATCH",
                "SYMBOLIC_ROOT_TERM_AUTHORITY_CONFLICT",
                "MANUAL_SYMBOLIC_ROOT_LEDGER_MISSING",
                "MANUAL_SYMBOLIC_ROOT_MALFORMED",
                "MANUAL_SYMBOLIC_ROOT_CONFLICT",
                "CONFIGURED_SOURCE_MATERIALIZATIONS_MISSING",
                "CONFIGURED_SOURCE_MATERIALIZATION_MALFORMED",
                "CONFIGURED_SOURCE_MATERIALIZATION_CONFLICT",
                "UNDECIDED_SOLVER_VALUATIONS",
                "DEGENERATE_UNCONSTRAINED_ROOT_SPACE"}) {
            blocking(solver, code,
                    "the reach extractor could not read the model it was handed, so"
                            + " its reachability answer is about the artifact rather than the"
                            + " target");
        }

        // ------------------------------------------------------------------
        // EXPLORE / PATH_WORKLIST.
        // ------------------------------------------------------------------
        String explore = "EXPLORE/PATH_WORKLIST";
        blocking(explore, "SHARED_STATE_GAP",
                "a shared-state carrier whose map, receiver locator or"
                        + " access anchor is missing is a read with no"
                        + " stated source");
        blocking(explore, "INVALID_BRANCH_MAPPING_SCHEMA",
                "a branch mapping the worklist cannot read is a decision it"
                        + " cannot flip");
        blocking(explore, "TARGET_PREFIX_TASK_MISSING",
                "the prefix task that reaches the target is absent");
        blocking(explore, "TARGET_PREFIX_FATAL_MAPPING_INVALID",
                "the fatal read's branch mapping is unusable");
        blocking(explore, "TARGET_PREFIX_FATAL_EVENT_INVALID",
                "the fatal read's recorded event is unusable");
        blocking(explore, "TARGET_PREFIX_CONCRETE_OUTCOME_MISMATCH",
                "the concrete outcome disagrees with the recorded one, so"
                        + " the prefix is not the execution it claims");
        blocking(explore, "MULTIPLE_REGION_SCOPE",
                "one task spans several regions, so no single region owns"
                        + " the path");
        blocking(explore, "NO_OBSERVED_PATH_SEED",
                "nothing observed seeds this region's path space");
        blocking(explore, "MULTIPLE_EXPLORATION_SCOPE",
                "one task spans several exploration scopes");
        for (String code : new String[]{
                "RPC_HANDOFF_GAP",
                "REPLAY_DIVERGENCE",
                "TOPOLOGY_DIVERGENCE"}) {
            blocking(explore, code,
                    "an alignment gap on a path the replay actually walked:"
                            + " the recorded evidence for a step of that"
                            + " path is missing or disagrees with the model"
                            + " the plan was built on");
        }
        // The sibling-path family.  Every one of these says some path other
        // than the one the witness walks was not explored, and every one of
        // them lands in a summary's coverageGaps, which run_engine.sh reads
        // as pathSetClosed=false (see campaign_explore); the composer then
        // publishes pathSetComplete=false and ClaimPolicy withholds
        // UNSAT_CLOSED by name under UNSAT_CLOSURE_INCOMPLETE.  So the one
        // conclusion these can falsify is already withheld by name, and the
        // chain a SAT witness reports contains no sibling path by
        // construction.  This is also why BOUND_REACHED had to start firing
        // at the worklist's task ceiling: an unexplored path that published
        // no row left coverageState reading CLOSED, and then nothing
        // withheld the UNSAT conclusion either.
        for (String code : new String[]{
                "BOUND_REACHED",
                "UNSUPPORTED_PATH_FLIP",
                "PATH_FLIP_MATERIALIZATION_GAP",
                "PATH_FLIP_REPLAY_NOT_ADMITTED",
                "PATH_FLIP_REPLAY_ENGINE_UNAVAILABLE",
                "PATH_FLIP_REPLAY_PRODUCED_NO_RESULT",
                "PATH_FLIP_SOLVER_TIMEOUT",
                "LINKED_REPLAY_LEFT_TOPOLOGY_EPOCH",
                "REGION_PATH_WAVE_BUDGET_REACHED",
                "REGION_PATH_CLOSURE_NO_PROGRESS"}) {
            diagnostic(explore, code,
                    "an unexplored sibling path is not a link of the chain"
                            + " the witness walks, and the one conclusion it"
                            + " can falsify -- a closed UNSAT -- is withheld"
                            + " by name, because this row makes the"
                            + " summary's path set unclosed and ClaimPolicy"
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
        onKeptSlice(importer, "REGION_CAUSAL_ANCHOR_NOT_OBSERVED",
                "a region whose causal anchor was never observed contributes"
                        + " no case: on the kept slice that is a link the"
                        + " plan said must run and publish and the model does"
                        + " not contain, off it the static plan simply named"
                        + " a region root dependence never selected");
        onKeptSlice(importer, "REGION_OCCURRENCE_ANCHOR_UNMATCHED",
                "compatible activations did not answer the addressed"
                        + " occurrence: on the kept slice the region the"
                        + " chain names is not the region that ran, off it no"
                        + " chain element was addressed there");
        blocking(importer, "REGION_REPLAY_PREFIX_UNMATCHED",
                "the replay did not follow the prefix the plan addressed");
        onKeptSlice(importer, "REGION_TASK_NO_PUBLISHED_ACTIVATION",
                "a planned task published neither an activation nor a skip:"
                        + " on the kept slice its region contributes no case"
                        + " to a path set the chain runs through, off it the"
                        + " task was an over-approximation that produced"
                        + " nothing");
        blocking(importer, "TARGET_REACH_NO_ACTIVATION_REACHED_TARGET",
                "no activation of this region executed the target site, so"
                        + " the region states nothing about the target --"
                        + " an activation that ran the site and decided"
                        + " against the failure has stated something, and is"
                        + " not this");
        blocking(importer, "TARGET_REACH_NOT_OBSERVED",
                "the replay published no observation of the target this"
                        + " task was addressed at");
        for (String code : new String[]{
                "SKIPPED_RUNTIME_EVENT",
                "REGION_NOT_STARTED",
                "REGION_UNAPPLIED_MODEL_ASSIGNMENT",
                "REGION_RESULT_PUBLICATION_FAILED",
                "REGION_ANCHOR_EPOCH_NOT_REACHED",
                "REGION_TERMINAL_NEVER_REACHED",
                "UNKNOWN_EXECUTION_TASK",
                "UNKNOWN_REGION",
                "LOCATION_NOT_NAMED_ACROSS_SESSIONS",
                "SHARED_STATE_MAP_STATE_IDENTITY_MISSING",
                "SHARED_STATE_MAP_STATE_IDENTITY_AMBIGUOUS",
                "DUPLICATE_ACTIVATION_ORDINAL",
                "VM_SUMMARY_ACTIVATION_MISMATCH",
                "SYMBOLIC_EXECUTION_ABORTED",
                "REPLAY_LOOP_RESOURCE_CAP",
                "LOOP_BOUND_PATH_CUT",
                "BRANCH_REPLAY_MISMATCH",
                "REGION_PATH_ADMISSION_REJECTED",
                "PATH_REPLAY_ADMISSION_REJECTED",
                "DUPLICATE_SUMMARY",
                "INCOMPLETE_RELATION",
                "CONCOLIC_RESULT_SCHEMA_UNSUPPORTED",
                "CONCOLIC_RESULT_ACTIVATION_TUPLE_MALFORMED",
                "CONCOLIC_RESULT_REPLAY_GROUP_MISSING",
                "SYMBOLIZED_INPUT_ROW_MALFORMED",
                "TARGET_REACH_EVENT_MISSING",
                "TARGET_REACH_EVENT_MALFORMED",
                "TARGET_REACH_EVENT_MISMATCH",
                "AMBIENT_PATH_CONDITION_NOT_ADMITTED",
                "AUXILIARY_PATH_CONDITION_MISSING",
                "MALFORMED_BRANCH_MAPPING",
                "OMITTED_PATH_CONDITION_AUTHORITY_MISSING",
                "OMITTED_PATH_CONDITION_ENGINE_INACTIVE",
                "OMITTED_PATH_CONDITION_NOT_EMPTY",
                "SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MALFORMED",
                "SYMBOLIC_SOURCE_PHASE_RUNTIME_LEDGER_MISSING"}) {
            blocking(importer, code,
                    "a planned region, task or event the replay did not produce, or"
                            + " produced in a shape the importer could not read, contributes no"
                            + " case to the selected path set");
        }
        diagnostic(importer, "REGION_LOOP_OCCURRENCES_BOUNDED",
                "the occurrence set of a loop-body region is bounded by the"
                        + " declared K_L rather than truncated: the"
                        + " iterations past it are outside the model this"
                        + " campaign declared, and BoundedLoopComposition"
                        + " checks every replayed case against that same"
                        + " declaration, so the marker states the declared"
                        + " bound and never hides a case inside it");

        // ------------------------------------------------------------------
        // CLASSIFY / IMPORTER -- topology deltas.
        // ------------------------------------------------------------------
        String classify = "CLASSIFY/IMPORTER";
        onKeptSlice(classify, "COVERAGE_GAP",
                "a planned task produced no result: on the kept slice that is"
                        + " a case the plan demanded and the recording does"
                        + " not contain, off it a task root dependence never"
                        + " selected produced nothing, which is what the"
                        + " slice already said about it");
        blocking(classify, "TOPOLOGY_DIVERGENCE",
                "the composed iteration's topology still diverges from the"
                        + " one it was planned against");

        // ------------------------------------------------------------------
        // REPLAY / COMMUNICATION -- the message envelope's own findings.  A
        // declared port is one pair of bytecode sites, and a protocol sends
        // many unrelated values through it, so each leaf is addressed by its
        // element ordinal within its message.  These two say the two sides
        // of one message disagreed about which elements exist.
        // ------------------------------------------------------------------
        String messages = "REPLAY/COMMUNICATION";
        blocking(messages, "WIRE_LEAVES_UNATTACHED",
                "the sender put a value in the message and no decode on the"
                        + " receiving side looked it up, so whatever that"
                        + " value feeds is a leaf with no producer and the"
                        + " chain the message was carrying stops there");
        blocking(messages, "WIRE_LEAF_MISSING",
                "a decode asked its message for an element the sender never"
                        + " staged, so the value it went on to use carries"
                        + " no expression from the node that produced it");

        // ------------------------------------------------------------------
        // PLAN / STATIC -- the static catalog and the runtime-selected region
        // finalizer.  These used to be published to a seed artifact nothing
        // downstream read.
        // ------------------------------------------------------------------
        String plan = "PLAN/STATIC";
        diagnostic(plan, "BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED",
                "an array-indexed loop's trip count is its array length, and"
                        + " BoundedLoopComposition checks every replayed case"
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
        blocking(plan, "SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY_REACHED",
                "an accessor-return stream hit the container snapshot"
                        + " capacity, so later reads of that container were"
                        + " never minted as ports");

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
     * The class of {@code code} for a reader that cannot see the replay
     * slice.  An unregistered code is BLOCKING, and so is every
     * {@link Scope#KEPT_SLICE} code, because not knowing whether a row is on
     * the slice is not a reason to stop withholding on it.
     */
    public static GapClass classOf(String code) {
        Entry entry = code == null ? null : REGISTRY.get(code.trim());
        return entry == null ? GapClass.BLOCKING : entry.gapClass;
    }

    /**
     * The class of {@code code} for a row whose slice membership is known.
     *
     * @param onKeptSlice whether the row's subject names a task or
     *                    occurrence the replay slice kept
     */
    public static GapClass classOf(String code, boolean onKeptSlice) {
        Entry entry = code == null ? null : REGISTRY.get(code.trim());
        if (entry == null) return GapClass.BLOCKING;
        if (entry.scope != Scope.KEPT_SLICE) return entry.gapClass;
        return onKeptSlice ? GapClass.BLOCKING : GapClass.DIAGNOSTIC;
    }

    /** Whether {@code code} is decided against the replay slice. */
    public static boolean sliceConditional(String code) {
        Entry entry = code == null ? null : REGISTRY.get(code.trim());
        return entry != null && entry.scope == Scope.KEPT_SLICE;
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
        // Read by run_engine.sh, which is the reader that can see the slice.
        JsonArray conditional = new JsonArray();
        for (Entry entry : REGISTRY.values()) {
            if (entry.scope != Scope.KEPT_SLICE) continue;
            conditional.add(entry.code);
        }
        ledger.add("sliceConditional", conditional);
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
