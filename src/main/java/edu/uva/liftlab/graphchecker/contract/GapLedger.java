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

    /** One registered code. */
    public static final class Entry {
        public final String code;
        /** The producing stage/source pair this code is published under. */
        public final String source;
        public final GapClass gapClass;
        /** Why the class is what it is; required for DIAGNOSTIC. */
        public final String reason;

        Entry(String code, String source, GapClass gapClass, String reason) {
            this.code = code;
            this.source = source;
            this.gapClass = gapClass;
            this.reason = reason;
        }

        JsonObject toJson() {
            JsonObject row = new JsonObject();
            row.addProperty("code", code);
            row.addProperty("source", source);
            row.addProperty("class", gapClass.name());
            row.addProperty("reason", reason);
            return row;
        }
    }

    private static final Map<String, Entry> REGISTRY = new LinkedHashMap<>();

    private static void blocking(String source, String code, String reason) {
        register(new Entry(code, source, GapClass.BLOCKING, reason));
    }

    private static void diagnostic(String source, String code,
                                   String reason) {
        if (reason == null || reason.trim().isEmpty()) {
            throw new IllegalStateException(
                    "a DIAGNOSTIC gap code states why it cannot change a"
                            + " chain: " + code);
        }
        register(new Entry(code, source, GapClass.DIAGNOSTIC, reason));
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
                "SelectedTargetSourceAttestationMalformed"}) {
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
                "INITIAL_CONTAINER_SNAPSHOT_TRUNCATED",
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
        blocking(explore, "BOUND_REACHED",
                "a region, path or task ceiling truncated the worklist, so"
                        + " the paths it did not plan are unexplained"
                        + " freedom rather than paths it ruled out");
        blocking(explore, "SHARED_STATE_GAP",
                "a shared-state carrier whose map, receiver locator or"
                        + " access anchor is missing is a read with no"
                        + " stated source");
        blocking(explore, "PATH_FLIP_MATERIALIZATION_GAP",
                "an exploration obligation that produced no replay leaves"
                        + " the sibling path it was meant to decide open");
        blocking(explore, "PATH_FLIP_REPLAY_NOT_ADMITTED",
                "a satisfying flip model whose replay was not admitted"
                        + " leaves the path it names neither walked nor"
                        + " excluded");
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
        blocking(explore, "PATH_FLIP_SOLVER_TIMEOUT",
                "the flip query for this path was never answered, so the"
                        + " path it names is neither walked nor excluded");
        // Written by run_engine.sh's closure loop onto every pending
        // worklist, which is why they are classed here rather than in the
        // shell that raises them.
        blocking(explore, "REGION_PATH_WAVE_BUDGET_REACHED",
                "the closure loop stopped at its wave budget with"
                        + " obligations still pending");
        blocking(explore, "REGION_PATH_CLOSURE_NO_PROGRESS",
                "a closure wave repeated its predecessor's signature with"
                        + " obligations still pending, so the paths they"
                        + " name were never decided");
        for (String code : new String[]{
                "UNSUPPORTED_PATH_FLIP",
                "PATH_FLIP_REPLAY_ENGINE_UNAVAILABLE",
                "PATH_FLIP_REPLAY_PRODUCED_NO_RESULT",
                "LINKED_REPLAY_LEFT_TOPOLOGY_EPOCH",
                "RPC_HANDOFF_GAP",
                "REPLAY_DIVERGENCE",
                "TOPOLOGY_DIVERGENCE"}) {
            blocking(explore, code,
                    "an obligation the worklist raised and no replay answered leaves"
                            + " the path it names neither walked nor excluded");
        }

        // ------------------------------------------------------------------
        // IMPORT / IMPORTER.
        // ------------------------------------------------------------------
        String importer = "IMPORT/IMPORTER";
        blocking(importer, "REGION_CAUSAL_ANCHOR_NOT_OBSERVED",
                "a planned region whose causal anchor was never observed"
                        + " contributes no case, so a link the plan named is"
                        + " absent from the model");
        blocking(importer, "REGION_OCCURRENCE_ANCHOR_UNMATCHED",
                "compatible activations did not answer the addressed"
                        + " occurrence, so the region the chain names was"
                        + " not the region that ran");
        blocking(importer, "REGION_REPLAY_PREFIX_UNMATCHED",
                "the replay did not follow the prefix the plan addressed");
        blocking(importer, "REGION_TASK_NO_PUBLISHED_ACTIVATION",
                "a planned task published neither an activation nor a skip,"
                        + " so its region contributes no case to the"
                        + " selected path set");
        blocking(importer, "TARGET_REACH_NO_ACTIVATION_REACHED_TARGET",
                "no activation of this region reached the target, so the"
                        + " region states nothing about the target");
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
        blocking(classify, "COVERAGE_GAP",
                "a planned task that produced no result is a case the plan"
                        + " demanded and the recording does not contain");
        blocking(classify, "TOPOLOGY_DIVERGENCE",
                "the composed iteration's topology still diverges from the"
                        + " one it was planned against");

        // ------------------------------------------------------------------
        // PLAN / STATIC -- the static catalog and the runtime-selected region
        // finalizer.  These used to be published to a seed artifact nothing
        // downstream read.
        // ------------------------------------------------------------------
        String plan = "PLAN/STATIC";
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

    /** The class of {@code code}; an unregistered code is BLOCKING. */
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
