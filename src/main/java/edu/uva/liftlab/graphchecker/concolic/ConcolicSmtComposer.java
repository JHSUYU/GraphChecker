package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;

import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.GuardedReadUse;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Sort;
import edu.uva.liftlab.graphchecker.concolic.VmTermLowering.Term;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.floatingKind;
import static edu.uva.liftlab.graphchecker.concolic.VmTermLowering.numeric;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmetic;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.arithmeticOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.bitwiseOperator;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.comparison;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.constantPayload;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.exactIntLiteral;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.flattenConcat;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isJavaParseInt;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isJavaSplitElement;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.isPrimitiveIntExpression;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.quote;
import static edu.uva.liftlab.graphchecker.concolic.VmExpressionIr.shiftOperator;

/**
 * Composes a fatal-region query after direct symbolic value propagation.
 * The causal graph selects relevant summaries. Receiver-owned boundary
 * families and region-local path conditions provide the value formula.
 */
public final class ConcolicSmtComposer {
    /** Expression node the VM serializes one guarded read-from arm as. */
    /** Prefix of the one value term of one guarded read. */
    static final String READ_VALUE_PREFIX = "rf_value__";
    /** Prefix of one dependent read through a reference-typed carrier. */
    static final String REFERENCE_FIELD_PREFIX = "reference_field__";
    /**
     * The pseudo-scope content-addressed map states are canonicalized under.
     * It is deliberately not one replay execution, so identities in it say
     * nothing about which objects a single JVM allocated.
     */
    private static final String CANONICAL_MAP_STATE_SCOPE =
            "canonical-map-state";
    private static final Pattern SMT_ATOM = Pattern.compile("[^()\\s]+");

    /**
     * The value of one dependent read through a reference-typed carrier.
     *
     * <p>Read outward from the default: an owner identity this formula knows
     * nothing else about keeps {@code projection}, the uninterpreted
     * {@code container_field__} of that owner -- a named freedom, and never
     * a Java default.  An identity whose own field is versioned takes that
     * family's value.  The object this execution actually read from takes
     * what it was observed to hold, and takes it outermost, because direct
     * evidence about this very read beats a family that merely describes the
     * same slot of some other object.</p>
     *
     * <p>The arms are <em>ordered</em>, and deliberately carry no claim that
     * the identities they name are different objects.  The engine briefly
     * asserted one -- {@code (distinct ...)} over every {@code REF}
     * structural witness of each scope carrying such a read -- so that an
     * inner arm could not be swallowed by an outer one.  Nothing recorded
     * supports it: a structural witness is scoped by the replay
     * <em>group</em>, which on HDFS-17899 is 27 to 36 executions, and the
     * axiom made the bug3 composition {@code unsat} in every polarity
     * (plain, both marker flips and all four root valuations), its whole
     * unsat core being those four {@code distinct} rows.  What it collided
     * with is real and is not this binding's to fix: several recorded
     * {@code BlockKey#keyId} reads are read-from one merged boundary value,
     * so the model must identify key objects the recording separates.
     * Until that holds, arm order is an over-approximation -- an inner arm
     * may collapse onto the observed value -- which admits models rather
     * than refuting them, and that is the safe direction for a tool whose
     * {@code unsat} is the strong claim.  The bug the routing was built for
     * is unaffected: an owner this formula knows nothing about still keeps
     * the free projection, never the Java default zero.</p>
     *
     * @param routes owner-witness/value pairs, each {@code {witness, value}}
     */
    static String referenceFieldBinding(String owner, String concreteOwner,
                                        String observed, String projection,
                                        List<String[]> routes) {
        String body = projection;
        for (int index = routes.size() - 1; index >= 0; index--) {
            body = "(ite (= " + owner + " " + routes.get(index)[0] + ") "
                    + routes.get(index)[1] + " " + body + ")";
        }
        return "(ite (= " + owner + " " + concreteOwner + ") " + observed
                + " " + body + ")";
    }

    /** Identity of one value selected by a recorded selector family. */
    private static String projectionTermIdentity(
            String kind, String authorityId, String expectedSort,
            String projectionIdentity) {
        return kind + "\u0000" + authorityId + "\u0000"
                + firstNonBlank(expectedSort, "INFER") + "\u0000"
                + firstNonBlank(projectionIdentity, "DIRECT");
    }

    static final String UNSAT_CLOSURE_AUTHORITY =
            "SELECTED_CAUSAL_PATH_UNSAT_CLOSURE_V1";
    static final String UNSAT_CLOSURE_COMPLETE =
            "unsatClosureComplete";
    static final String UNSAT_CLOSURE_EVIDENCE =
            "unsatClosureEvidence";
    /** The target published no reach query this composition could start at. */
    static final String TARGET_REACH_QUERY_ABSENT =
            "TARGET_REACH_QUERY_ABSENT";
    /** Every observed occurrence of the annotated target, and its status. */
    public static final String TARGET_REACH_OCCURRENCES =
            "targetReachOccurrences";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_FIELD =
            "configuredSourceMaterializations";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_KIND =
            "CONFIGURED_SYMBOLIC_SOURCE_MATERIALIZATION";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY =
            "COMPOSER_CONFIGURED_SOURCE_PHASE_TERM_V3";
    static final String MANUAL_SOURCE_MATERIALIZATION_FIELD =
            "manualSymbolicRootMaterializations";
    static final String MANUAL_SOURCE_MATERIALIZATION_KIND =
            "MANUAL_SYMBOLIC_ROOT_MATERIALIZATION";
    static final String MANUAL_SOURCE_MATERIALIZATION_AUTHORITY =
            "COMPOSER_MANUAL_SYMBOLIC_ROOT_TERM_V1";
    /** Per unnamed VM reference stored into a container: the witness that
     *  stands for it, scoped to the mutation that stored it. */
    static final String UNTRACKED_ELEMENT_WITNESSES_FIELD =
            "untrackedElementWitnesses";
    static final String UNTRACKED_ELEMENT_WITNESS_KIND =
            "UNTRACKED_ELEMENT_WITNESS";
    private static final String CASE_REGION_ID = "_caseRegionId";
    /** Whether this artifact may be accepted as the milestone result. */
    public static final String FINAL_STATUS = "finalStatus";
    /** Whether all selected producer and target path sets were explored. */
    /** Per lowered root: what it returned when it was recorded. */
    public static final String RECORDED_ROOT_VALUES = "recordedRootValues";
    /**
     * On a configured-source materialization: what the field actually held.
     *
     * <p>Carried from the runtime's own mint, which is the only place the
     * concrete value exists -- a configured source has no port and no
     * {@code symbolize} row, so the plan states nothing about it. Without
     * this the recorded-root ledger can say nothing about a configured root
     * and a reader has to default its polarity.</p>
     */
    public static final String RECORDED_SOURCE_VALUE = "recordedValue";
    /** Per declared value handoff: whether its family reached a term. */
    public static final String WIRE_FLOW_BINDINGS = "wireFlowBindings";
    /**
     * One declared value handoff whose consumer boundary family the closure
     * built and this composition never lowered, so the value the wire carried
     * constrains nothing in the emitted formula.
     */
    public static final String WIRE_FLOW_VALUE_UNBOUND =
            "WIRE_FLOW_VALUE_UNBOUND";
    /**
     * One consumer boundary family the recorded evidence carries and no
     * lowered expression in this composition referred to.
     *
     * <p>This is not a defect by itself: a family observed in a region the
     * causal slice never composed legitimately constrains nothing here. It
     * is published so that it is <em>counted</em> rather than dropped in
     * silence -- the ledger row carries {@code valueBound: false}, and it is
     * the claim gate, reading one row per declared flow, that decides
     * whether a flow with no bound family anywhere is unrealized.</p>
     */
    public static final String CONSUMER_BOUNDARY_FAMILY_UNREFERENCED =
            "CONSUMER_BOUNDARY_FAMILY_UNREFERENCED";
    /**
     * A read of the field a declared wire flow says its consumer assigns the
     * value to, at the consuming node, that no arm ties to the wire.
     *
     * <p>{@link #WIRE_FLOW_VALUE_UNBOUND} asks the question once per port and
     * one bound family answers it, because one flow is many handoffs and the
     * causal slice only has to carry one of them.  That is the right question
     * for the flow and the wrong one for the value: a receiver whose own
     * handoff went unreferenced still has the field, and the composition
     * serves it from whatever else the recording left at that location --
     * here, the constant the deserialiser had already written into the
     * message object before the region was entered.  The formula then reads
     * as "the wire carried this" while the term is one execution's literal,
     * free of the producer's expression and of every root behind it.</p>
     *
     * <p>Asked per read, on the consuming node only: the same field on the
     * producer is where the value comes from, not where it arrives.</p>
     */
    public static final String WIRE_FLOW_CONSUMER_FIELD_UNATTACHED =
            "WIRE_FLOW_CONSUMER_FIELD_UNATTACHED";
    /** One row per (read, declared flow) the wire never reached. */
    public static final String UNATTACHED_CONSUMER_READS_FIELD =
            "unattachedConsumerReads";
    /**
     * One merged consumer boundary whose case dispatch is not total: the
     * arms it carries are not covered by any partition this formula asserts
     * unconditionally, so a model may satisfy none of them and the merged
     * value falls through to a term nothing binds.
     *
     * <p>This is the shape that let an HDFS-17897 witness index a DataNode's
     * key map with a key id no node ever held: the dispatch was read as
     * "one of these observations", the last arm stood in as an unguarded
     * default, and the value it carried was pinned only under a read
     * selector the model left false.</p>
     */
    public static final String UNBOUND_WIRE_VALUE = "UNBOUND_WIRE_VALUE";
    /** Prefix of the term a non-total boundary dispatch falls through to. */
    static final String UNBOUND_BOUNDARY_PREFIX = "unbound_boundary__";
    /** One row per merged consumer boundary: is its case dispatch total? */
    public static final String BOUNDARY_DISPATCH_TOTALITY =
            "boundaryDispatchTotality";
    /**
     * One row per associative read that can answer null because the key it
     * was made with is in no PUT of the chain and in none of the state the
     * chain starts from.
     */
    public static final String ABSENT_KEY_DEFAULTS = "absentKeyDefaults";
    /** Prefix of the Boolean term that says one read took that default. */
    static final String ABSENT_KEY_DEFAULT_PREFIX = "absent_key_default__";
    /**
     * Case partitions the formula asserts only under a condition, so a
     * consumer must not pin them: doing so decides the condition silently.
     */
    public static final String CONDITIONAL_CASE_PARTITIONS =
            "conditionalCaseSelectorPartitions";
    /** What each fault marker idles, and what that leaves without a value. */
    public static final String FAULT_CONTROL_CLOSURE_FIELD =
            "faultControlClosure";
    /** Advisory rows from the fault-control closure, for gaps.json. */
    public static final String FAULT_CONTROL_GAPS_FIELD = "faultControlGaps";
    static final String FAULT_CONTROL_CLOSURE_KIND = "FAULT_CONTROL_CLOSURE";
    /**
     * A read every one of whose candidate writers the fault idles.
     *
     * <p>The location published no retained prior version and no INITIAL
     * arm, so with the marker true the reading case has nothing to observe.
     * The closure idles that case too rather than leaving the formula
     * contradictory, and this row says which location lost its value.</p>
     */
    static final String FAULT_IDLE_NO_RETAINED_ARM =
            "FAULT_IDLE_NO_RETAINED_ARM";
    /** A fault-controlled selector the manifest still offers for pinning. */
    static final String FAULT_PARTITION_UNSPLIT = "FAULT_PARTITION_UNSPLIT";
    /**
     * An INITIAL arm the fault leaves as a read's only survivor while the
     * marker idles the very activation whose entry took the snapshot.
     *
     * <p>The snapshot of an instance field is the value the object had when
     * that activation was entered; an activation the marker says never ran
     * never took it, and for an object the activation itself allocated the
     * value is the JVM's zero default of a field nothing constructed.  Such
     * an arm is not a retained prior version, so the read starves instead of
     * materialising the default, and the composition refuses rather than
     * present the default as the value the fault left behind.</p>
     */
    public static final String FAULT_IDLE_INITIAL_HOST_IDLED =
            "FAULT_IDLE_INITIAL_HOST_IDLED";
    /**
     * The replay executions merged into this formula recorded different
     * values for one location.
     *
     * <p>Every {@code REPLAY.GROUP} is one independent run of the workload,
     * and a location's value in one run says nothing about its value in
     * another.  The closure keys a location's arms by replay-independent
     * identities (reader case, writer case, INITIAL owner) and the composer
     * offers every group's literal at that identity, each behind its own
     * observation selector, with nothing tying the group chosen here to the
     * group chosen anywhere else.  A witness may therefore take one
     * location's value from one run and the next location's from another,
     * which is not a state any execution was ever in.</p>
     *
     * <p>The gate compares the literal each group recorded at one
     * group-independent identity and refuses when they differ <em>and</em>
     * the fatal read's value is built from that location (see {@link
     * #REACHES_FATAL_READ}); off that slice the row is telemetry.  Agreement
     * is what makes the merge harmless, so a workload pinned to one value
     * per location passes; a value that is genuinely per-execution -- a wall
     * clock, a fresh random -- has to enter as a symbolic root instead, and a
     * root the experiment declared but the composition never minted shows up
     * here as its constants.</p>
     */
    public static final String EXECUTION_DIVERGENCE = "EXECUTION_DIVERGENCE";
    /** One row per identity whose recorded values diverge across groups. */
    public static final String EXECUTION_DIVERGENCE_FIELD =
            "executionDivergence";
    /**
     * Whether the fatal read's value is built from the diverging location.
     *
     * <p>Divergence off that slice is real and recorded, but it cannot
     * change what the target observes, so it is telemetry: refusing it would
     * refuse every composition of a workload whose replays differ anywhere
     * at all, which is every multi-run corpus.  On the slice the same fact
     * decides the verdict, and the composition fails closed.</p>
     */
    public static final String REACHES_FATAL_READ = "reachesFatalRead";
    /**
     * A case of a writer occurrence that recorded a write to a read's
     * location and owns no arm of that read.
     *
     * <p>The read's candidate arms are the versions retained at the read in
     * the executions where its reader case was observed.  A case of the same
     * writer occurrence that was only observed in other executions still
     * enters the occurrence's exactly-one partition, so pinning it leaves
     * every writer arm inactive and the read falls to INITIAL as if that case
     * had not written -- while its own evidence says it did.  The gate names
     * that case instead of letting the default stand in for its write.</p>
     *
     * <p>A read the writer region performs on itself is the exception: it is
     * lowered once per local case and merged over the occurrence's
     * exactly-one partition, so it does not exist under its own siblings and
     * no sibling can leave it at INITIAL.  {@link
     * #writerCaseExclusiveOfRead} decides that, and such a row is recorded
     * with {@code refused: false} rather than refused.</p>
     */
    public static final String GUARDED_READ_WRITER_CASE_UNLINKED =
            "GUARDED_READ_WRITER_CASE_UNLINKED";
    /**
     * One row per (read, unlinked writer case); {@code refused} says whether
     * the row also refused the composition.
     */
    public static final String UNLINKED_WRITER_CASES_FIELD =
            "unlinkedWriterCases";
    public static final String PATH_SET_COMPLETE = "pathSetComplete";
    public static final String FINAL_READY = "FINAL_READY";
    /**
     * One guarded read whose candidate writers admit no single program order,
     * and which therefore carries no last-writer-wins axiom.
     */
    public static final String GUARDED_READ_ORDER_UNKNOWN =
            "GUARDED_READ_ORDER_UNKNOWN";
    public static final String FINAL_REFUSED = "FINAL_REFUSED";

    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().serializeNulls().setPrettyPrinting()
            .create();
    private ConcolicSmtComposer() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = compose(arguments);
        ArtifactIO.replace(arguments.output, result.smtLib);
        ArtifactIO.replaceJson(arguments.manifest, result.manifest, GSON);
    }

    public static Result compose(Arguments arguments) throws IOException {
        require(arguments.runtimePlan, "runtime plan");
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.runtimePlan);

        if (!Files.isRegularFile(arguments.fatalQueries)) {
            return refusedComposition(arguments, arguments.fatalQueries
                    + " does not exist: the target task published no reach"
                    + " query at all");
        }
        List<JsonObject> queryRows;
        try {
            queryRows = SharedExpressionTable.expandAll(
                    ArtifactIO.readJsonl(arguments.fatalQueries));
        } catch (IllegalArgumentException malformed) {
            throw new IOException("Malformed target reach expression table "
                    + arguments.fatalQueries, malformed);
        }
        List<RelationSummary> summaries = readRelationSummaries(arguments);
        JsonObject fatal = selectFatalQuery(queryRows, arguments);
        if (fatal.size() == 0) {
            return refusedComposition(arguments, arguments.fatalQueries
                    + " exists with " + queryRows.size() + " row(s) and holds"
                    + " no ready reach query for region="
                    + arguments.fatalRegion + " occurrence="
                    + arguments.occurrenceId);
        }
        requireCanonicalFatalQuerySchema(fatal);
        String fatalSite = optionalString(fatal, "targetSiteId");

        // Every path in this query is backed by the runtime's exact target
        // event.  The replay seed only fixes the selected branch identity; it
        JsonObject rawContext = object(fatal, "symbolicContext");
        // Runtime-confirmed first-hop demands are authoritative.  CLI bounds
        // describe supplied summaries; they must never erase a demanded edge
        JsonObject resolutionContext = rawContext.deepCopy();
        boolean instanceScopedContext = resolutionContext.size() > 0
                && !optionalString(resolutionContext, "occurrenceId").isEmpty();

        // Keep the original case evidence long enough to register every exact
        // symbolic source. Value closure below uses VM boundary observations
        // and region-local path conditions.
        List<JsonObject> allCaseEvidenceRows = caseEvidenceRows(
                summaries, fatal);
        List<RelationSummary> loweredRelations = new ArrayList<>(summaries);
        // The VM already propagated values. Runtime evidence only normalizes
        // receiver-side boundary observations into stable guarded families;
        // the causal graph contributes scope, never value equalities.
        SymbolicPropagationClosure.Result propagation =
                SymbolicPropagationClosure.rewrite(loweredRelations, fatal);
        fatal = propagation.fatal();
        loweredRelations = decodeRelationSummaries(
                propagation.summaries());
        Emitter emitter = new Emitter(new InvocationKey(
                optionalString(fatal, "regionId"),
                optionalString(resolutionContext, "occurrenceId")));
        emitter.registerInitialSnapshotHosts(
                propagation.initialSnapshotHosts());
        emitter.registerConfiguredSourcePlan(runtimePlan.regionPlans());
        emitter.begin(fatal);
        // A configured source may reach a selected downstream relation
        // through VM value handoff without making its own summary a lowered
        emitter.registerExecutionScopes(loweredRelations, fatal,
                propagation.caseDependencies());
        emitter.registerSymbolicSources(allCaseEvidenceRows);
        if (!instanceScopedContext) {
            // Named against the target the context is missing for, like every
            // other composition gap: the row's kind is not its subject.
            emitter.unsupported.add("MissingTargetInstanceSymbolicContext:"
                    + firstNonBlank(optionalString(fatal, "occurrenceId"), fatalSite,
                    optionalString(fatal, "regionId")));
        }
        BoundedLoopComposition loops = lowerBoundedLoops(runtimePlan, fatal,
                loweredRelations);
        for (RelationSummary selection : loweredRelations) {
            emitter.lowerRelation(selection);
        }
        lowerFatalTargetPaths(emitter, fatal, fatalSite);
        JsonObject clockPhysics = emitter.lowerClockRoots(
                runtimePlan.plans(), arguments.clockSkewMillis);
        emitter.finishGuardedReadSelections();
        // Before finish(): an unbound handoff is a refusal, and a refusal has
        // to reach the emitted formula's fail-closed marker too.
        JsonObject guardedReads = emitter.guardedReadModel();
        // The same join the gate makes: a declared flow whose value left the
        // wire on arrival is carried by the field its consumer assigned it
        // to, so a read of that field is the term the wire's value reaches.
        JsonArray wireFlowBindings = emitter.wireFlowBindings(
                propagation.caseDependencies(),
                declaredWireFlowPorts(runtimePlan.plans()),
                ClaimPolicy.WireFlowEvidence.read(arguments.mappings, "")
                        .consumerFieldsByPortSuffix(),
                ClaimPolicy.guardedReadFields(guardedReadCarrier(
                        guardedReads)));
        emitter.finish();
        String composedSmt = emitter.render();
        // An arm the formula itself refutes is stated up front, so a solver
        // is not left to discover it inside the arm's own cone; nothing
        // recorded is assumed.  Without a solver the formula is untouched.
        DeadCaseLemmas.Result deadCases;
        try {
            deadCases = DeadCaseLemmas.prove(composedSmt,
                    emitter.unconditionalCasePartitions(), arguments.z3,
                    arguments.deadCaseArmRlimit);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("dead-case probing interrupted",
                    interrupted);
        }
        composedSmt = deadCases.smtLib;

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", fatalSite);
        manifest.addProperty("symbolicPropagationComplete",
                propagation.complete());
        manifest.add("symbolicPropagationGaps", propagation.gaps());
        manifest.add("casePathConditionDependencies",
                propagation.caseDependencies());
        manifest.add("targetReachLedger", emitter.targetReachLedger());
        manifest.add(TARGET_REACH_OCCURRENCES,
                targetReachOccurrences(runtimePlan.regionPlans(), fatal));
        // Only the partitions the formula asserts unconditionally.  A
        // consumer that pins one of these is restating something the formula
        // already says; pinning a conditional one silently decides the
        // condition, which is how a fault marker got frozen to its recorded
        // value during root-polarity evaluation.
        manifest.add("caseSelectorPartitions",
                GSON.toJsonTree(emitter.unconditionalCasePartitions()));
        manifest.add(CONDITIONAL_CASE_PARTITIONS,
                GSON.toJsonTree(emitter.conditionalCasePartitions()));
        manifest.add(DeadCaseLemmas.MANIFEST_FIELD, deadCases.ledger);
        manifest.add(FAULT_CONTROL_CLOSURE_FIELD,
                emitter.faultControlClosureLedger());
        manifest.add(FAULT_CONTROL_GAPS_FIELD, emitter.faultControlGaps());
        manifest.add(CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                emitter.configuredSourceMaterializationLedger());
        manifest.add(MANUAL_SOURCE_MATERIALIZATION_FIELD,
                emitter.manualSourceMaterializationLedger());
        manifest.add(UNTRACKED_ELEMENT_WITNESSES_FIELD,
                emitter.untrackedElementWitnessLedger());
        manifest.add(BoundedLoopComposition.MANIFEST_FIELD,
                loops.manifest());
        manifest.add("guardedReadModel", guardedReads);
        if (arguments.taskPlan != null) {
            // Every family is VM evidence over a carrier the replay
            // selected; the ledger states that against the plan that
            // declared the carriers, and names the families a narrower
            // plan would not have produced.
            manifest.add(CarrierDeclarationLedger.MANIFEST_FIELD,
                    CarrierDeclarationLedger.of(
                            ArtifactIO.readJsonl(arguments.taskPlan),
                            guardedReads, artifact(arguments.taskPlan)));
        }
        manifest.add(ClockRootPhysics.MANIFEST_FIELD, clockPhysics);
        manifest.add(WIRE_FLOW_BINDINGS, wireFlowBindings);
        manifest.add(EXECUTION_DIVERGENCE_FIELD, emitter.executionDivergence);
        manifest.add(UNATTACHED_CONSUMER_READS_FIELD,
                emitter.unattachedConsumerReads);
        manifest.add(UNLINKED_WRITER_CASES_FIELD,
                emitter.unlinkedWriterCases);
        manifest.add(BOUNDARY_DISPATCH_TOTALITY,
                emitter.boundaryDispatchTotality);
        manifest.add(ABSENT_KEY_DEFAULTS, emitter.absentKeyDefaults);
        manifest.add(RECORDED_ROOT_VALUES,
                emitter.recordedRootLedger(runtimePlan.plans()));
        JsonArray gaps = new JsonArray();
        appendGaps(gaps, "COMPOSITION_GAP", emitter.unsupported,
                emitter.unsupportedDetail);
        // A loop the replay traversed that no declared bound covers is a
        // property of this formula, not coverage telemetry it can outlive.
        for (JsonObject loopGap : loops.compositionGaps()) {
            gaps.add(loopGap);
        }
        manifest.add("gaps", gaps);
        manifest.addProperty("state", gaps.size() == 0
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        boolean guardedReadModelComplete = propagation.complete()
                && emitter.unsupported.isEmpty();
        manifest.addProperty("guardedReadModelComplete",
                guardedReadModelComplete);
        // This verdict says whether the emitted candidate formula itself is
        // usable. Coverage closure is recorded separately and is required
        // only before concluding that an UNSAT result is globally closed.
        AcceptanceGate gate = new AcceptanceGate();
        for (JsonElement element : gaps) {
            JsonObject gap = element.getAsJsonObject();
            gate.refuse(optionalString(gap, "kind"), optionalString(gap, "subject"),
                    optionalString(gap, "detail"));
        }
        boolean selectedPathSetComplete =
                pathSetComplete(loweredRelations, fatal);
        manifest.addProperty(PATH_SET_COMPLETE, selectedPathSetComplete);
        String finalStatus = gate.finalStatus();
        boolean finalReady = FINAL_READY.equals(finalStatus);
        manifest.addProperty(FINAL_STATUS, finalStatus);
        manifest.add("finalStatusRefusals", gate.refusals);
        JsonObject unsatClosure = unsatClosureEvidence(
                guardedReadModelComplete, loweredRelations, fatal, finalReady,
                0);
        manifest.addProperty(UNSAT_CLOSURE_COMPLETE, unsatClosureComplete(
                guardedReadModelComplete, unsatClosure));
        manifest.add(UNSAT_CLOSURE_EVIDENCE, unsatClosure);
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                composedSmt.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        return new Result(composedSmt,
                SharedExpressionTable.compact(manifest));
    }

    private static List<RelationSummary> readRelationSummaries(
            Arguments arguments) throws IOException {
        List<RelationSummary> summaries = new ArrayList<>();
        for (Path summaryFile : arguments.summaries) {
            List<JsonObject> encodedRows = ArtifactIO.readJsonl(summaryFile);
            List<JsonObject> expandedRows;
            try {
                expandedRows = SharedExpressionTable.expandAll(encodedRows);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed relation summaries "
                        + summaryFile, malformed);
            }
            int row = 0;
            for (JsonObject encoded : expandedRows) {
                try {
                    if (ClosureGoalKind.fromTask(encoded)
                            .capturesTargetReach()) {
                        row++;
                        continue;
                    }
                    RelationSummary summary =
                            RelationSummary.decodeExpanded(encoded);
                    summaries.add(summary);
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("Malformed relation summary "
                            + summaryFile + " row " + row, malformed);
                }
                row++;
            }
        }
        return summaries;
    }

    private static BoundedLoopComposition lowerBoundedLoops(
            RuntimePlanArtifact runtimePlan, JsonObject fatal,
            List<RelationSummary> loweredRelations) {
        List<JsonObject> selectedSummaryRows = summaryRows(loweredRelations);
        List<JsonObject> scopedPlanRows = targetScopedPlanRows(
                runtimePlan.plans(), fatal, loweredRelations);
        List<JsonObject> loopBoundAuthorities =
                new ArrayList<>(selectedSummaryRows);
        loopBoundAuthorities.add(fatal);
        BoundedLoopComposition loops =
                BoundedLoopComposition.ofPlanRows(scopedPlanRows,
                        loopBoundAuthorities);
        for (RelationSummary relation : loweredRelations) {
            loops.observeCase(relation.occurrenceId(),
                    relation.pathCaseView());
        }
        observeFatalLoopCases(loops, fatal);

        return loops;
    }

    private static void lowerFatalTargetPaths(Emitter emitter,
                                               JsonObject fatal,
                                               String fatalSite) {
        List<String> fatalTerms = new ArrayList<>();
        List<String> fatalPathSelectors = new ArrayList<>();
        String previousFatalScope = emitter.enterSymbolScope("fatal:"
                + firstNonBlank(optionalString(fatal, "occurrenceId"), fatalSite,
                optionalString(fatal, "regionId"), "selected"));
        try {
            int pathOrdinal = 0;
            for (JsonElement element : array(fatal, "paths")) {
                JsonObject path = element.getAsJsonObject();
                int selectedPathOrdinal = pathOrdinal++;
                String label = "fatal target path " + selectedPathOrdinal;
                List<String> pathTerms = new ArrayList<>();
                JsonArray constraints = array(path, "constraints");
                String pathOwner = targetPathCaseOwner(fatal, path,
                        selectedPathOrdinal);
                String previousPathScope = emitter.enterSymbolScope(
                        pathOwner);
                String pathSelector = LocalCaseIdentity.selector(pathOwner);
                emitter.declare(pathSelector, Sort.BOOL);
                String previousPathGuard = emitter.enterGuard(pathSelector);
                try {
                    for (int constraintIndex = 0;
                         constraintIndex < constraints.size();
                         constraintIndex++) {
                        pathTerms.add(emitter.constraint(
                                constraints.get(constraintIndex), label));
                    }
                } finally {
                    emitter.restoreGuard(previousPathGuard);
                    emitter.restoreSymbolScope(previousPathScope);
                }
                String pathTerm = and(pathTerms);
                fatalTerms.add(pathTerm);
                String selectedCase = emitter.bindTargetPathCase(fatal, path,
                        selectedPathOrdinal, pathTerm);
                emitter.recordTargetReach(selectedPathOrdinal, path,
                        selectedCase, fatal);
                fatalPathSelectors.add(selectedCase);
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.bindTargetReachAssertion();
        emitter.bindFatalPathAssertion(or(fatalTerms));
        emitter.bindTargetPathPartition(fatalPathSelectors);
    }

    /** Publishes an absent target query as the Composer's own refusal. */
    private static Result refusedComposition(Arguments arguments,
                                             String detail)
            throws IOException {
        String subject = firstNonBlank(arguments.occurrenceId,
                arguments.fatalRegion, String.valueOf(arguments.fatalQueries));
        String smtLib = String.join(System.lineSeparator(),
                "; GraphChecker composed concolic query",
                "; composition refused: " + TARGET_REACH_QUERY_ABSENT
                        + " " + subject,
                "(set-logic ALL)") + System.lineSeparator();
        AcceptanceGate gate = new AcceptanceGate();
        gate.refuse(TARGET_REACH_QUERY_ABSENT, subject, detail);
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", "");
        manifest.addProperty("guardedReadModelComplete", false);
        // Nothing was lowered, so no path set was ranged over and none can be
        // called complete.
        manifest.addProperty(PATH_SET_COMPLETE, false);
        manifest.addProperty("symbolicPropagationComplete", false);
        manifest.add("symbolicPropagationGaps", new JsonArray());
        manifest.add("casePathConditionDependencies", new JsonArray());
        manifest.add(CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        manifest.add(MANUAL_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        manifest.add(TARGET_REACH_OCCURRENCES, new JsonArray());
        // No port was occupied and no model was produced, so this artifact
        // is not a candidate model a later stage may conclude from.
        manifest.addProperty("state", "CANDIDATE_WITH_GAPS");
        manifest.addProperty(FINAL_STATUS, FINAL_REFUSED);
        manifest.add("finalStatusRefusals", gate.refusals);
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                smtLib.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        return new Result(smtLib, manifest);
    }

    /**
     * States whether an unsatisfiable selected formula closes every path set
     */
    static JsonObject unsatClosureEvidence(
            boolean guardedReadModelComplete,
            Collection<RelationSummary> selected,
            JsonObject fatal, boolean finalReady,
            int compositionCoverageGapCount) {
        JsonArray partialRelations = partialProducerSummaryIds(selected);
        int targetCoverageGapCount = array(fatal, "coverageGaps").size();
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        evidence.addProperty("authority", UNSAT_CLOSURE_AUTHORITY);
        // The guarded-read verdict is stated once, at the top level of the
        // manifest.  Closure of the producer paths and of the composition
        // coverage is exactly "the counted list beside it is empty", and the
        // whole closure verdict is the conjunction of the components below:
        // none of the three is restated here.
        evidence.addProperty("targetPathsClosed", targetPathsClosed(fatal));
        evidence.addProperty("finalStatusReady", finalReady);
        evidence.addProperty("targetCoverageGapCount",
                targetCoverageGapCount);
        evidence.addProperty("compositionCoverageGapCount",
                compositionCoverageGapCount);
        evidence.add("partialProducerSummaryIds", partialRelations);
        return evidence;
    }

    /** The Composer's own UNSAT closure verdict over one evidence row. */
    private static boolean unsatClosureComplete(
            boolean guardedReadModelComplete, JsonObject evidence) {
        return guardedReadModelComplete
                && array(evidence, "partialProducerSummaryIds").size() == 0
                && optionalBool(evidence, "targetPathsClosed", false)
                && optionalInteger(evidence, "compositionCoverageGapCount", -1) == 0
                && optionalBool(evidence, "finalStatusReady", false);
    }

    /** Producer summaries whose local path coverage remains open. */
    private static JsonArray partialProducerSummaryIds(
            Collection<RelationSummary> selected) {
        JsonArray partial = new JsonArray();
        for (RelationSummary summary : Objects.requireNonNull(selected,
                "selected")) {
            if (!summary.pathSetClosed()) {
                partial.add(summary.summaryId());
            }
        }
        return partial;
    }

    /** Whether the target query named no gap in its own path set. */
    private static boolean targetPathsClosed(JsonObject fatal) {
        return array(fatal, "coverageGaps").size() == 0;
    }

    /** Whether producer and target path coverage are both closed. */
    private static boolean pathSetComplete(
            Collection<RelationSummary> selected, JsonObject fatal) {
        return partialProducerSummaryIds(selected).size() == 0
                && targetPathsClosed(fatal);
    }

    /** Adds each fatal replay path's own loop-count vector to the audit. */
    static void observeFatalLoopCases(BoundedLoopComposition loops,
                                      JsonObject fatal) {
        String occurrence = optionalString(fatal, "occurrenceId");
        JsonArray paths = array(fatal, "paths");
        for (int index = 0; index < paths.size(); index++) {
            if (!paths.get(index).isJsonObject()) continue;
            JsonObject path = shallowCopy(
                    paths.get(index).getAsJsonObject());
            if (optionalString(path, "caseId").isEmpty()) {
                path.addProperty("caseId", "TARGET_PATH." + index);
            }
            loops.observeCase(occurrence, path);
        }
    }

    static final class AcceptanceGate {
        private final JsonArray refusals = new JsonArray();
        private final Set<String> named = new LinkedHashSet<>();

        void refuse(String code, String subject, String detail) {
            if (!named.add(code + "\n" + subject)) return;
            JsonObject row = new JsonObject();
            row.addProperty("code", code);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            refusals.add(row);
        }

        int size() {
            return refusals.size();
        }

        String finalStatus() {
            return size() == 0 ? FINAL_READY : FINAL_REFUSED;
        }
    }

    /** The selected summaries' rows, as the recorded model reads them. */
    private static List<JsonObject> summaryRows(
            Collection<RelationSummary> selected) {
        List<JsonObject> rows = new ArrayList<>();
        for (RelationSummary summary : selected) {
            rows.add(summary.immutableJson());
        }
        return rows;
    }

    private static List<RelationSummary> decodeRelationSummaries(
            Collection<JsonObject> encoded) {
        List<RelationSummary> summaries = new ArrayList<>();
        for (JsonObject row : Objects.requireNonNull(encoded, "encoded")) {
            summaries.add(RelationSummary.decodeExpanded(row));
        }
        return summaries;
    }

    private static List<JsonObject> caseEvidenceRows(
            Collection<RelationSummary> relations, JsonObject fatal) {
        List<JsonObject> rows = new ArrayList<>();
        for (RelationSummary relation : Objects.requireNonNull(relations,
                "relations")) {
            JsonObject item = relation.pathCaseView();
            String caseOccurrence = optionalString(item, "occurrenceId");
            item.addProperty("toOccurrenceId", caseOccurrence);
            item.addProperty(CASE_REGION_ID, relation.regionId());
            item.addProperty("sourceKey", relation.sourceKey());
            JsonObject relationRow = relation.immutableJson();
            item.addProperty("taskId", firstNonBlank(
                    optionalString(item, "taskId"), optionalString(relationRow, "taskId")));
            item.addProperty("boundarySessionScope", firstNonBlank(
                    optionalString(item, "boundarySessionScope"),
                    optionalString(relationRow, "boundarySessionScope")));
            item.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                    firstNonBlank(optionalString(item,
                                    VmExpressionIr.TOPOLOGY_EPOCH),
                            optionalString(relationRow,
                                    VmExpressionIr.TOPOLOGY_EPOCH)));
            String owner = LocalCaseIdentity.owner(relationRow);
            item = retainCaseOwner(item, owner);
            rows.add(item);
        }
        if (fatal != null) {
            JsonObject target = shallowCopy(fatal);
            target.addProperty("toOccurrenceId",
                    optionalString(fatal, "occurrenceId"));
            rows.add(target);
            JsonArray paths = array(fatal, "paths");
            for (int index = 0; index < paths.size(); index++) {
                if (!paths.get(index).isJsonObject()) continue;
                JsonObject path = shallowCopy(
                        paths.get(index).getAsJsonObject());
                // Pure target constraints are lowered by the target query.
                // This list carries only runtime value/root evidence into the
                // direct propagation closure.
                if (VmHandoffEvidence.eventsOf(path).isEmpty()
                        && object(path, SharedStateEvidence.RECORDED_FIELD)
                        .size() == 0
                        && array(path, SymbolicSourceEvidence.FIELD)
                        .size() == 0
                        && array(path, ConcolicSummaryImporter
                        .MANUAL_INPUT_OBSERVATION_FIELD).size() == 0) {
                    continue;
                }
                path.addProperty("toOccurrenceId",
                        firstNonBlank(optionalString(path, "occurrenceId"),
                                optionalString(fatal, "occurrenceId")));
                path.addProperty(CASE_REGION_ID,
                        optionalString(fatal, "regionId"));
                path.addProperty("regionId", optionalString(fatal, "regionId"));
                path.addProperty("occurrenceId", firstNonBlank(
                        optionalString(path, "occurrenceId"),
                        optionalString(fatal, "occurrenceId")));
                path.addProperty("boundarySessionScope", firstNonBlank(
                        optionalString(path, "boundarySessionScope"),
                        optionalString(fatal, "boundarySessionScope")));
                path.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                        firstNonBlank(optionalString(path,
                                        VmExpressionIr.TOPOLOGY_EPOCH),
                                optionalString(fatal,
                                        VmExpressionIr.TOPOLOGY_EPOCH)));
                path.addProperty("sourceKey", optionalString(fatal, "sourceKey"));
                path = retainCaseOwner(path, targetPathCaseOwner(fatal, path,
                        index));
                rows.add(path);
            }
        }
        return rows;
    }

    /** Stable ownership shared by target-path lowering and evidence scan. */
    private static String targetPathCaseOwner(JsonObject fatal,
                                              JsonObject path,
                                              int ordinal) {
        return LocalCaseIdentity.owner(
                optionalString(fatal, "regionId"), firstNonBlank(
                        optionalString(path, "occurrenceId"),
                        optionalString(fatal, "occurrenceId")),
                firstNonBlank(optionalString(path, "caseId"),
                        "TARGET_PATH." + ordinal), ordinal);
    }

    /**
     * Reused manual expressions are roots observed at an exact frozen action,
     * not new mints.  Index them by replay session and VM spelling so cases
     * from independent JVMs can never acquire the same solver term merely
     * because their native symbol counters restarted at the same number.
     */
    static Map<String, List<JsonObject>> exactReusedManualRootAuthorities(
            Iterable<JsonObject> owners,
            Map<String, String> executionScopesByCase) {
        Map<String, List<JsonObject>> admitted = new LinkedHashMap<>();
        if (owners == null) return Collections.emptyMap();
        for (JsonObject owner : owners) {
            if (owner == null) continue;
            String ownerKey = optionalString(owner, LocalCaseIdentity.OWNER);
            String session = firstNonBlank(
                    executionScopesByCase == null ? ""
                            : executionScopesByCase.get(ownerKey),
                    optionalString(owner, "boundarySessionScope"));
            for (JsonElement element : array(owner,
                    ConcolicSummaryImporter
                            .MANUAL_INPUT_OBSERVATION_FIELD)) {
                if (!element.isJsonObject()) continue;
                JsonObject observation = element.getAsJsonObject();
                if (!ConcolicSummaryImporter
                        .MANUAL_INPUT_OBSERVATION_KIND.equals(
                        optionalString(observation, "kind"))) {
                    continue;
                }
                boolean claimsExactAuthority = ConcolicSummaryImporter
                        .MANUAL_INPUT_OBSERVATION_AUTHORITY.equals(
                        optionalString(observation, "authority"));
                JsonElement minted = observation.get("minted");
                JsonElement reused = observation.get(
                        SymbolicSourceEvidence.REUSED);
                boolean exactFlags = minted != null
                        && minted.isJsonPrimitive()
                        && minted.getAsJsonPrimitive().isBoolean()
                        && reused != null && reused.isJsonPrimitive()
                        && reused.getAsJsonPrimitive().isBoolean()
                        && minted.getAsBoolean() != reused.getAsBoolean();
                if (!claimsExactAuthority || !exactFlags) {
                    throw new IllegalArgumentException(
                            "manual input observation has malformed reused"
                                    + " authority");
                }
                if (!reused.getAsBoolean()) continue;

                JsonObject expression = observation.has("expression")
                        && observation.get("expression").isJsonObject()
                        ? observation.getAsJsonObject("expression") : null;
                String raw = optionalString(observation, "rawSymbol");
                String javaType = optionalString(observation, "javaType");
                // Exact actions may reuse a compound propagated value.  It
                // remains useful boundary evidence, but there is no scalar
                // root for this registry to authorize.
                if (expression == null
                        || !"SymbolExpression".equals(
                        optionalString(expression, "_type"))
                        || raw.isEmpty()) {
                    continue;
                }
                String occurrence = optionalString(observation, "occurrenceId");
                String planned = optionalString(observation,
                        "plannedOccurrenceId");
                String port = optionalString(observation, "portId");
                String actionDigest = optionalString(observation, "actionDigest");
                String ownerOccurrence = optionalString(owner, "occurrenceId");
                String sourceKey = optionalString(owner, "sourceKey");
                String region = firstNonBlank(optionalString(owner, CASE_REGION_ID),
                        optionalString(owner, "regionId"));
                boolean exactRoot = raw.equals(optionalString(expression, "_exp"))
                        && !raw.isEmpty() && raw.startsWith("M_")
                        && !javaType.isEmpty()
                        && javaTypeDescriptor(javaType).equals(
                        javaTypeDescriptor(optionalString(expression,
                                "_java_type")));
                if (session.isEmpty() || sourceKey.isEmpty()
                        || region.isEmpty() || port.isEmpty()
                        || actionDigest.isEmpty()
                        || !port.equals(optionalString(observation, "symbol"))
                        || occurrence.isEmpty()
                        || !occurrence.equals(ownerOccurrence)
                        || !planned.equals(
                        OccurrenceId.parse(occurrence).planned())
                        || !exactRoot) {
                    throw new IllegalArgumentException(
                            "manual input observation has incomplete exact"
                                    + " reused-root identity: "
                                    + firstNonBlank(raw, port, "UNKNOWN")
                                    + ":session=" + !session.isEmpty()
                                    + ":source=" + !sourceKey.isEmpty()
                                    + ":region=" + !region.isEmpty()
                                    + ":port=" + !port.isEmpty()
                                    + ":digest=" + !actionDigest.isEmpty()
                                    + ":symbol=" + port.equals(optionalString(
                                    observation, "symbol"))
                                    + ":occurrence=" + occurrence.equals(
                                    ownerOccurrence)
                                    + ":planned=" + planned.equals(
                                    OccurrenceId.parse(
                                            occurrence).planned())
                                    + ":root=" + exactRoot);
                }
                String identity = "MANUAL." + CanonicalJson.sha256(
                        sourceKey + "\n" + region + "\n" + planned
                                + "\n" + port);
                JsonObject normalized = shallowCopy(observation);
                normalized.addProperty("sourceIdentity", identity);
                String key = session + "\u0000" + raw;
                List<JsonObject> events = admitted.computeIfAbsent(key,
                        ignored -> new ArrayList<>());
                for (JsonObject held : events) {
                    if (!javaTypeDescriptor(optionalString(held, "javaType"))
                            .equals(javaTypeDescriptor(javaType))) {
                        throw new IllegalArgumentException(
                                "one reused manual VM root has incompatible"
                                        + " Java types: " + raw);
                    }
                }
                boolean duplicate = false;
                for (JsonObject held : events) {
                    if (identity.equals(optionalString(held, "sourceIdentity"))) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) events.add(normalized);
            }
        }
        List<String> keys = new ArrayList<>(admitted.keySet());
        Collections.sort(keys);
        Map<String, List<JsonObject>> ordered = new LinkedHashMap<>();
        for (String key : keys) {
            List<JsonObject> events = admitted.get(key);
            events.sort(Comparator.comparing(event ->
                    optionalString(event, "sourceIdentity")));
            ordered.put(key, Collections.unmodifiableList(events));
        }
        return Collections.unmodifiableMap(ordered);
    }

    /**
     * Wave 3 C1/C3: a raw VM symbol normally denotes one SMT root.  Before
     * reaching this method, spellings from overlapping region projections are
     * canonicalized only when the plan joins them to the same exact recorded
     * source event.  Every other configured mint remains a separate root.
     */
    private static String symbolScopeKey(String raw, String scope,
                                         String sourceIdentity) {
        return sourceIdentity == null
                ? firstNonBlank(scope, "global") + "\u0000" + raw
                : "configured-source\u0000" + raw;
    }

    /** Stamps every case-local evidence family with its exact owner. */
    private static JsonObject retainCaseOwner(JsonObject item, String owner) {
        CaseOwnerCarrier carrier = new CaseOwnerCarrier(owner);
        JsonObject result = carrier.object(item);
        JsonObject state = object(item, SharedStateEvidence.RECORDED_FIELD);
        if (state.size() > 0) {
            result.add(SharedStateEvidence.RECORDED_FIELD,
                    carrier.object(state));
        }
        retainCaseOwners(result, item, RelationSummary.INTERACTION_EVENTS,
                carrier);
        retainCaseOwners(result, item, VmHandoffEvidence.FIELD, carrier);
        return result;
    }

    /** Copies only evidence carriers which receive case ownership. */
    private static void retainCaseOwners(JsonObject result, JsonObject source,
                                         String field,
                                         CaseOwnerCarrier carrier) {
        JsonElement encoded = source == null ? null : source.get(field);
        if (encoded == null || !encoded.isJsonArray()) return;
        result.add(field, carrier.array(encoded.getAsJsonArray()));
    }

    /** Identity-memo carrier copy; nested expression DAGs remain shared. */
    private static final class CaseOwnerCarrier {
        private final String owner;
        private final java.util.IdentityHashMap<JsonElement, JsonElement> copies =
                new java.util.IdentityHashMap<>();

        private CaseOwnerCarrier(String owner) {
            this.owner = owner;
        }

        private JsonObject object(JsonObject source) {
            JsonElement held = copies.get(source);
            if (held != null) return held.getAsJsonObject();
            JsonObject result = shallowCopy(source);
            copies.put(source, result);
            LocalCaseIdentity.stamp(result, owner);
            return result;
        }

        private JsonArray array(JsonArray source) {
            JsonElement held = copies.get(source);
            if (held != null) return held.getAsJsonArray();
            JsonArray result = new JsonArray();
            copies.put(source, result);
            for (JsonElement element : source) {
                result.add(element != null && element.isJsonObject()
                        ? object(element.getAsJsonObject()) : element);
            }
            return result;
        }
    }

    /**
     * The plan rows in composition scope: the selected region occurrences.
     *
     * <p>A plan row is addressed by its <em>planned</em> occurrence, while a
     * relation summary is addressed by the activation of it that ran
     * ({@code …#1#a1}).  Both sides are reduced to the planned address before
     * they are matched; comparing the two spellings directly selected nothing
     * but the fatal region's own row and silently emptied the bounded-loop
     * model.</p>
     */
    static List<JsonObject> targetScopedPlanRows(
            Collection<JsonObject> planRows, JsonObject fatal,
            Collection<RelationSummary> loweredRelations) {
        Set<String> selected = new LinkedHashSet<>();
        for (RelationSummary relation : Objects.requireNonNull(
                loweredRelations, "loweredRelations")) {
            String occurrence = relation.occurrenceId();
            if (!occurrence.isEmpty()) {
                selected.add(OccurrenceId.parse(occurrence).planned());
            }
        }
        // Do not recursively scan the whole target query: it may embed
        // propagated expression evidence. Only its explicit target members
        addOccurrence(fatal, "occurrenceId", selected);
        collectOccurrences(object(fatal, "selectedTargetOccurrence"),
                selected);
        List<JsonObject> scoped = new ArrayList<>();
        Set<String> held = new LinkedHashSet<>();
        for (JsonObject row : Objects.requireNonNull(planRows, "planRows")) {
            if (row == null) continue;
            String occurrence = OccurrenceId.parse(
                    optionalString(row, "occurrenceId")).planned();
            if (occurrence.isEmpty() || !selected.contains(occurrence)
                    || !held.add(occurrence)) {
                continue;
            }
            scoped.add(row);
        }
        return scoped;
    }

    /** Collects direct and from/to occurrence ids without admitting them. */
    private static void collectOccurrences(JsonElement element,
                                           Set<String> selected) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectOccurrences(child, selected);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject row = element.getAsJsonObject();
        addOccurrence(row, "occurrenceId", selected);
        addOccurrence(row, "fromOccurrenceId", selected);
        addOccurrence(row, "toOccurrenceId", selected);
        for (Map.Entry<String, JsonElement> member : row.entrySet()) {
            collectOccurrences(member.getValue(), selected);
        }
    }

    private static void addOccurrence(JsonObject row, String field,
                                      Set<String> selected) {
        String occurrence = optionalString(row, field);
        if (!occurrence.isEmpty()) {
            selected.add(OccurrenceId.parse(occurrence).planned());
        }
    }

    /** Wraps the model so the gate's own field reader can walk it. */
    private static JsonObject guardedReadCarrier(JsonObject guardedReads) {
        JsonObject carrier = new JsonObject();
        carrier.add("guardedReadModel", guardedReads);
        return carrier;
    }

    /**
     * Whether a declared flow reached no term at all.
     *
     * <p>Asked per flow, never per family. One flow is observed as many
     * boundary families as the recording saw handoffs on its port, and the
     * composition only has to lower one of them for the wire's value to be in
     * the formula; the rest are observations of the same wire this causal
     * slice did not need. Asked per family, a flow with three of eleven
     * families lowered was called unbound eight times over.</p>
     *
     * <p>The second route is the field the consumer assigns the value to: when
     * the value leaves the wire on arrival, a read of that field is where it
     * ends up and the port's own family is a term nobody was going to build.
     * That route is only open on a node the wire delivered to; see {@link
     * #consumerFieldReadOnReceiver}.
     */
    static boolean wireFlowRefusable(boolean anyFamilyBound,
                                     boolean consumerFieldRead) {
        return !anyFamilyBound && !consumerFieldRead;
    }

    /**
     * Whether a read of the consumer's field stands for this delivery.
     *
     * <p>The producer assigns the same field from its own state, before the
     * value is ever put on the wire, so a read there says nothing about what
     * arrived: taking it as evidence excused a flow whose families all went
     * unreferenced, and the formula then served the consumer's field from a
     * value that never crossed. Only a read on a node this family's delivery
     * reached realizes it.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static boolean consumerFieldReadOnReceiver(
            String consumerField, String receiverNode,
            Map<String, Set<String>> readFieldNodes) {
        if (consumerField == null || consumerField.isEmpty()
                || receiverNode == null || receiverNode.isEmpty()
                || readFieldNodes == null) {
            return false;
        }
        Set<String> nodes = readFieldNodes.get(consumerField);
        return nodes != null && nodes.contains(receiverNode);
    }

    /**
     * Whether one writer case can never be selected while a read is demanded.
     *
     * <p>A region case is lowered once per local case, and a read the region
     * itself performs is lowered inside that case: it gets its own read
     * identity, its own arms and an activation guard that is the case it
     * belongs to, and the consumer merges the per-case reads with an
     * {@code ite} over the occurrence's exactly-one partition. Such a read
     * does not exist under its partition siblings, so a sibling that wrote the
     * location cannot leave <em>this</em> read at INITIAL -- selecting the
     * sibling selects the sibling's own read of the same location, which does
     * carry the write. Asking the unlinked-writer question per read rather
     * than per case therefore names every sibling of every case-private read,
     * which is the whole partition minus one, and refuses a composition that
     * represents each case correctly.</p>
     *
     * <p>The exclusion holds only when the read belongs to this partition and
     * to nothing else. A read of the same location from another region -- the
     * fatal read over a map another occurrence fills, say -- is demanded no
     * matter which case of the writer runs, so every case of that partition
     * has to own an arm of it and a missing one is a real gap.</p>
     */
    static boolean writerCaseExclusiveOfRead(Collection<String> partition,
                                             Collection<String> readCases,
                                             String caseSelector) {
        if (partition == null || readCases == null || readCases.isEmpty()) {
            return false;
        }
        return partition.containsAll(readCases)
                && !readCases.contains(caseSelector);
    }

    /**
     * The declared ports whose flow reached no term, over a whole ledger.
     *
     * <p>The ledger has one row per boundary family and a flow has as many
     * families as the recording saw handoffs on its port, so the rows are
     * folded onto their port before the question is asked. A port with one
     * bound family is a realized flow however many of its other families went
     * unreferenced.</p>
     */
    static List<String> unboundDeclaredPorts(JsonArray ledger) {
        Map<String, Boolean> bound = new LinkedHashMap<>();
        Map<String, Boolean> fieldRead = new LinkedHashMap<>();
        for (JsonElement element : ledger) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            if (!optionalBool(row, "declaredWireFlow", false)) {
                continue;
            }
            String port = optionalString(row, "portId");
            if (port.isEmpty()) {
                continue;
            }
            bound.merge(port, optionalBool(row, "valueBound", false),
                    Boolean::logicalOr);
            fieldRead.merge(port,
                    optionalBool(row, "consumerFieldRead", false),
                    Boolean::logicalOr);
        }
        List<String> unbound = new ArrayList<>();
        for (Map.Entry<String, Boolean> port : bound.entrySet()) {
            if (wireFlowRefusable(Boolean.TRUE.equals(port.getValue()),
                    Boolean.TRUE.equals(fieldRead.get(port.getKey())))) {
                unbound.add(port.getKey());
            }
        }
        Collections.sort(unbound);
        return unbound;
    }

    /**
     * The field declared for the flow this port carries.
     *
     * <p>A port is spelled {@code XCH.<site>.<req|resp>.<flow>} and the
     * mapping keys its field by the flow id, so the join is on the suffix.
     */
    static String consumerFieldOf(String portId,
                                  Map<String, String> consumerFields) {
        if (portId == null || portId.isEmpty() || consumerFields == null) {
            return "";
        }
        for (Map.Entry<String, String> declared : consumerFields.entrySet()) {
            if (portId.endsWith("." + declared.getKey())) {
                return firstNonBlank(declared.getValue());
            }
        }
        return "";
    }

    /**
     * Every exchange port the experiment declared a value handoff for.
     *
     * <p>The planner writes one {@code communicationHandoffs} entry per
     * declared {@code WIRE_FLOW} side, so the plan already carries what the
     * mappings file said without this stage reading it again. The set matters
     * because it is the line between two facts that look identical in the
     * manifest: a boundary family nothing referred to because its region was
     * outside this causal slice, which is telemetry, and one nothing referred
     * to on a port the experiment declared, which is a hole in the very flow
     * the experiment is about.</p>
     */
    static Set<String> declaredWireFlowPorts(List<JsonObject> plans) {
        Set<String> ports = new LinkedHashSet<>();
        for (JsonObject plan : plans == null
                ? Collections.<JsonObject>emptyList() : plans) {
            if (plan == null) {
                continue;
            }
            for (JsonElement handoff : array(plan, "communicationHandoffs")) {
                if (!handoff.isJsonObject()) {
                    continue;
                }
                String port = optionalString(handoff.getAsJsonObject(),
                        "portId");
                if (!port.isEmpty()) {
                    ports.add(port);
                }
            }
        }
        return ports;
    }

    private static void appendGaps(JsonArray target, String kind,
                                   Set<String> subjects,
                                   Map<String, String> details) {
        for (String subject : subjects) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("subject", subject);
            // A refusal states why it was made.  Every subject that reaches
            // here has one; an empty string would be a refusal that hid its
            // own finding, which is what this member exists to prevent.
            gap.addProperty("detail", detailOf(details, subject));
            target.add(gap);
        }
    }

    /** The stated reason for one refusal subject. */
    private static String detailOf(Map<String, String> details,
                                   String subject) {
        String detail = details == null ? null : details.get(subject);
        return detail == null || detail.isEmpty()
                ? "the composition refused " + subject
                + " and stated no further reason"
                : detail;
    }

    /**
     * Admits the canonical target-reach query at the stage boundary.
     */
    private static void requireCanonicalFatalQuerySchema(JsonObject fatal)
            throws IOException {
        if (optionalInteger(fatal, "schemaVersion", -1)
                != TargetReachPathQueryBuilder.SCHEMA_VERSION
                || !"TARGET_REACH_PATH_SET_QUERY".equals(
                        optionalString(fatal, "kind"))
                || optionalString(fatal, "queryKey").isEmpty()) {
            throw new IOException("Unsupported canonical fatal query schema");
        }
        if (JsonFields.exactInteger(fatal, "targetOccurrence", -1) < 1) {
            throw new IOException(
                    "Target reach query has no exact branch decision");
        }
        boolean concreteTarget = fatal.has(TargetReachPathQueryBuilder
                .TARGET_CONCRETE_OBSERVATION);
        boolean replayTarget = fatal.has("seedReplayContract");
        if (concreteTarget == replayTarget) {
            throw new IOException("Target reach query must have exactly one "
                    + "branch authority");
        }
        JsonArray paths = array(fatal, "paths");
        if (paths.size() == 0) {
            throw new IOException(
                    "Closed target reach query contains no path");
        }
        for (JsonElement element : paths) {
            if (!element.isJsonObject()) {
                throw new IOException(
                        "Malformed target reach path query member");
            }
            JsonObject path = element.getAsJsonObject();
            boolean pathConcrete = path.has(TargetReachPathQueryBuilder
                    .TARGET_CONCRETE_OBSERVATION);
            boolean pathWitness = path.has(TargetReachPathQueryBuilder
                    .TARGET_BRANCH_WITNESS);
            if (pathConcrete == pathWitness
                    || pathConcrete != concreteTarget
                    || !path.has("constraints")
                    || !path.get("constraints").isJsonArray()
                    || path.getAsJsonArray("constraints").size() == 0
                    && !pathConcrete) {
                throw new IOException(
                        "Malformed target reach path query member");
            }
            if (!path.has(
                    PathObservation.TargetReachEvent.FIELD)) {
                throw new IOException(
                        "Target reach path has no exact attestation "
                                + "authority");
            }
        }
    }

    /**
     * Every observed occurrence of the annotated target, and which one this
     * composition lowered.
     *
     * <p>An annotated failure site executes as many times as the workload
     * runs it, and the planner plants a {@code TARGET_REACH_CLOSURE} goal on
     * each of those occurrences -- hdfs-17897 observes the SASL handshake
     * twice, hdfs-11741 four times.  Everything downstream then narrows to
     * one of them: {@code RuntimeWorkflowDiscovery} elects a single
     * {@code TARGET} member, the campaign builds a reach query for that
     * member alone, and this composition is handed exactly that query.  The
     * narrowing is invisible in the published artifacts, so a verdict about
     * one execution of the site reads as a verdict about the site -- and
     * when the elected occurrence is the wrong one, the chain the experiment
     * is about is off the slice entirely, with nothing naming why.
     * hdfs-17897 elected {@code REGION.53092d3e#2}, the DataNode's own
     * handshake, while the bug ends at {@code #1}, the client's.</p>
     *
     * <p>So the composition states the whole set: one row per planned target
     * occurrence, naming its goal, its failure sites, and whether this
     * formula lowered it.  Nothing about the lowered formula changes -- the
     * SMT is byte-identical -- but the claim can report per occurrence, and
     * {@link ClaimPolicy} raises a finding for every occurrence the
     * composition did not reach.</p>
     */
    static JsonArray targetReachOccurrences(
            List<RegionInstancePlan> regionPlans, JsonObject fatal) {
        String composedOccurrence = OccurrenceId.parse(
                optionalString(fatal, "occurrenceId")).planned();
        String composedGoal = optionalString(fatal, "goalId");
        JsonArray result = new JsonArray();
        for (RegionInstancePlan plan : regionPlans) {
            for (RegionInstancePlan.Goal goal : plan.goals()) {
                if (!goal.kind().capturesTargetReach()) continue;
                String occurrence = OccurrenceId.parse(
                        plan.occurrenceId()).planned();
                JsonObject row = new JsonObject();
                row.addProperty("occurrenceId", occurrence);
                row.addProperty("regionId", plan.regionId());
                row.addProperty("goalId", goal.goalId());
                row.add("failureSites", observedFailureSites(goal));
                // The goal is the exact address; the occurrence is the
                // fallback for a query that names no goal of its own.
                row.addProperty("composed", composedGoal.isEmpty()
                        ? occurrence.equals(composedOccurrence)
                        : composedGoal.equals(goal.goalId()));
                result.add(row);
            }
        }
        return result;
    }

    /** The failure guards this goal actually observed taking a decision. */
    private static JsonArray observedFailureSites(
            RegionInstancePlan.Goal goal) {
        Set<String> sites = new java.util.LinkedHashSet<>();
        for (JsonElement element : goal.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            if (!JsonFields.optionalBool(branch, "failureTarget", false)
                    || JsonFields.optionalBool(branch, "loopControlGuard",
                    false)
                    || !JsonFields.optionalBool(branch, "observed", false)
                    || !branch.has("requiredOutcome")
                    || branch.get("requiredOutcome").isJsonNull()) {
                continue;
            }
            String site = optionalString(branch, "siteId");
            if (!site.isEmpty()) sites.add(site);
        }
        JsonArray result = new JsonArray();
        for (String site : sites) result.add(site);
        return result;
    }

    private static JsonObject selectFatalQuery(List<JsonObject> rows,
                                               Arguments arguments) {
        for (JsonObject row : rows) {
            if (!arguments.fatalRegion.isEmpty()
                    && !arguments.fatalRegion.equals(optionalString(row,
                    "regionId"))) {
                continue;
            }
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(optionalString(row,
                    "occurrenceId"))) {
                continue;
            }
            if ("TARGET_REACH_PATH_SET_QUERY".equals(
                    optionalString(row, "kind"))) {
                return row;
            }
        }
        return new JsonObject();
    }

    /** Region occurrence identity used only for case-local SMT scoping. */
    /** One lowered writer arm of a read, as the consumer-field gate sees it. */
    private static final class ConsumerArm {
        private final String selector;
        private final String term;
        private final String sourceKey;
        private final String occurrence;

        private ConsumerArm(String selector, String term, String sourceKey,
                            String occurrence) {
            this.selector = selector;
            this.term = term;
            this.sourceKey = sourceKey;
            this.occurrence = occurrence;
        }
    }

    /**
     * The node an occurrence address names, or "".
     *
     * <p>An occurrence is spelled {@code <sourceKey>/region/...}; the node is
     * everything before that, which is how the wire flow's receiver and a
     * read's writer are compared for "same side of the wire".</p>
     */
    static String occurrenceSourceKey(String occurrenceId) {
        if (occurrenceId == null) return "";
        int index = occurrenceId.indexOf("/region/");
        return index < 0 ? "" : occurrenceId.substring(0, index);
    }

    /** What each replay group recorded for one group-independent identity. */
    private static final class ExecutionRecording {
        private final String subject;
        private final Map<String, Set<String>> valuesByScope =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> selectorsByScope =
                new LinkedHashMap<>();

        private ExecutionRecording(String subject) {
            this.subject = subject;
        }
    }

    /** One SMT identifier, as this composer mints them. */
    private static final Pattern SMT_IDENTIFIER =
            Pattern.compile("[A-Za-z_][A-Za-z0-9_]*");

    private static final Pattern LITERAL_TERM = Pattern.compile(
            "-?[0-9]+|\\(- [0-9]+\\)|true|false|\"(?:[^\"]|\"\")*\"|"
                    + "\\(V(?:Int|Long|Bool|Str) (?:-?[0-9]+|\\(- [0-9]+\\)"
                    + "|true|false|\"(?:[^\"]|\"\")*\")\\)");

    /**
     * Whether one lowered term is a recorded literal two replay groups can
     * be compared on: an integer, Boolean or String constant, plain or in
     * the container codec's value box.  Anything else is either the same
     * symbolic expression in every group or a per-group VM witness.
     */
    static boolean isLiteralTerm(String text) {
        return text != null && LITERAL_TERM.matcher(text.trim()).matches();
    }

    /** The local-case part of one case owner, for a readable subject. */
    private static String caseTail(String owner) {
        if (owner == null) return "";
        int index = owner.lastIndexOf("case:");
        return index < 0 ? owner : owner.substring(index + "case:".length());
    }

    private static final class InvocationKey {
        private final String regionId;
        private final String instanceId;

        private InvocationKey(String regionId, String instanceId) {
            this.regionId = firstNonBlank(regionId);
            this.instanceId = firstNonBlank(instanceId);
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof InvocationKey)) return false;
            InvocationKey value = (InvocationKey) other;
            return regionId.equals(value.regionId)
                    && instanceId.equals(value.instanceId);
        }

        @Override public int hashCode() {
            return 31 * regionId.hashCode() + instanceId.hashCode();
        }
    }

    private static String and(List<String> terms) {
        return VmTermLowering.and(terms);
    }

    /** Pure encoding shared by final composition and focused regression tests. */
    static String conditionalExactlyOne(String activation,
                                        Collection<String> selectors) {
        List<String> ordered = new ArrayList<>(selectors);
        Collections.sort(ordered);
        if (ordered.isEmpty()) {
            throw new IllegalArgumentException(
                    "an active guarded choice needs a candidate");
        }
        StringBuilder count = new StringBuilder("(= (+");
        for (String selector : ordered) {
            count.append(" (ite ").append(selector).append(" 1 0)");
        }
        count.append(") 1)");
        return "(=> " + firstNonBlank(activation, "true") + " "
                + count + ")";
    }

    /**
     * Each recorded chain restricted to the arms one use can observe.
     *
     * <p>A chain is one read event's candidate list in version order, and a
     * read identity may cover several events. Only the part of a chain that
     * this use's own candidates appear in is evidence about which of them
     * overwrites which; the rest belongs to another event and orders nothing
     * here. Keeping the unrelated arms in was what left a read whose events
     * each have their own candidates with no order at all - no single chain
     * ordered every pair, so last-writer-wins was abandoned for the whole
     * read and its INITIAL arm became selectable with its writer active.</p>
     *
     * <p>Order within a chain is preserved, and chains that contribute
     * nothing to this use are dropped rather than returned empty.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static List<List<String>> scopedChains(List<List<String>> chains,
                                           Collection<String> scope) {
        Set<String> wanted = new LinkedHashSet<>(scope);
        List<List<String>> restricted = new ArrayList<>();
        for (List<String> chain : chains) {
            List<String> kept = new ArrayList<>();
            for (String selector : chain) {
                if (wanted.contains(selector)) kept.add(selector);
            }
            if (!kept.isEmpty()) restricted.add(kept);
        }
        return restricted;
    }

    /**
     * Last writer wins, as one formula per candidate arm.
     *
     * {@code selectors} is the read's candidate arms in program order,
     * earliest first, and {@code activity} the condition under which each of
     * those writers ran.  Selecting arm k asserts that its writer ran and that
     * no writer published after it did, which is what makes the arm the *last*
     * write the read could have seen.  The earliest arm is the location's
     * INITIAL version, so selecting it forbids every tracked writer.
     *
     * The last arm's entry is empty: it has nothing later to forbid, and its
     * positive obligation is already asserted by its writer obligation.
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static List<String> lastWriterWins(List<String> selectors,
                                       List<String> activity) {
        if (selectors.size() != activity.size()) {
            throw new IllegalArgumentException(
                    "one activity condition per ordered candidate arm");
        }
        List<String> axioms = new ArrayList<>(selectors.size());
        for (int index = 0; index < selectors.size(); index++) {
            List<String> obligation = new ArrayList<>();
            obligation.add(activity.get(index));
            for (int later = index + 1; later < selectors.size(); later++) {
                obligation.add("(not " + activity.get(later) + ")");
            }
            axioms.add(obligation.size() == 1 ? ""
                    : "(=> " + selectors.get(index) + " " + and(obligation)
                    + ")");
        }
        return axioms;
    }

    /**
     * One region occurrence's case partition when a fault can idle it.
     *
     * <p>The marker true says the request never completed, so none of the
     * occurrence's cases ran; the marker false leaves the ordinary
     * exactly-one partition in place.  Idling is deliberately not the same
     * as writing a bottom value: a case that never ran publishes nothing, so
     * every read of a location it would have written falls back to that
     * location's previous version through last-writer-wins.</p>
     *
     * <p>{@code marker} may be a disjunction when several faults can idle the
     * same occurrence.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static String faultControlledPartition(String marker,
                                           Collection<String> selectors) {
        List<String> ordered = new ArrayList<>(selectors);
        Collections.sort(ordered);
        if (ordered.isEmpty()) {
            throw new IllegalArgumentException(
                    "a fault-controlled partition needs a case");
        }
        List<String> idle = new ArrayList<>(ordered.size());
        for (String selector : ordered) {
            idle.add("(not " + selector + ")");
        }
        return "(and (=> " + marker + " " + and(idle) + ") (=> (not "
                + marker + ") " + conditionalExactlyOne("true", ordered)
                + "))";
    }

    /** Every case selector a request-fault control assertion names. */
    private static final Pattern CASE_SELECTOR_SYMBOL =
            Pattern.compile("case_selector__[A-Za-z0-9_]+");

    /** Every case name a guard can be written in terms of. */
    private static final Pattern CASE_GUARD_SYMBOL = Pattern.compile(
            "case_(?:selector|observation)__[A-Za-z0-9_]+");

    /**
     * The case names one activation guard is written in terms of.
     *
     * <p>A guard is either a case name on its own or a conjunction of one
     * with the read selector that reached it, so the names are read out of
     * the text rather than tracked alongside it.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static Set<String> caseGuardsIn(String activation) {
        Set<String> names = new LinkedHashSet<>();
        if (activation == null) return names;
        Matcher matcher = CASE_GUARD_SYMBOL.matcher(activation);
        while (matcher.find()) {
            names.add(matcher.group());
        }
        return names;
    }

    /**
     * The case selectors this formula lets a fault marker decide.
     *
     * <p>Reads the emitted artifact rather than the emitter's own state, so
     * the same check can be run against a composed formula from any build.
     * </p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static Set<String> faultControlledSelectorsIn(String composedSmt) {
        Set<String> selectors = new LinkedHashSet<>();
        for (String line : firstNonBlank(composedSmt).split("\\R")) {
            if (!line.contains(":named request_fault_control")) continue;
            Matcher matcher = CASE_SELECTOR_SYMBOL.matcher(line);
            while (matcher.find()) {
                selectors.add(matcher.group());
            }
        }
        return selectors;
    }

    /**
     * Fault-controlled selectors a manifest still offers for pinning.
     *
     * <p>The contract is one sentence: a selector a fault marker decides
     * belongs in the conditional partitions and nowhere else.  A consumer
     * pinning an unconditional partition restates what the formula already
     * asserts; pinning one of these answers for the marker instead, and the
     * fault-true half of the root space then comes back unsat for a reason
     * about the driver rather than the program.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static List<String> unsplitFaultControlledSelectors(
            Collection<String> asserted,
            Collection<? extends Collection<String>> unconditional,
            Collection<? extends Collection<String>> conditional) {
        Set<String> open = new LinkedHashSet<>();
        for (Collection<String> partition : unconditional) {
            open.addAll(partition);
        }
        Set<String> decided = new LinkedHashSet<>();
        for (Collection<String> partition : conditional) {
            decided.addAll(partition);
        }
        List<String> violations = new ArrayList<>();
        for (String selector : asserted) {
            if (decided.contains(selector) && !open.contains(selector)) {
                continue;
            }
            violations.add(selector);
        }
        return violations;
    }

    /**
     * What one confirmed request-fault control edge decides: which marker,
     * raised on which node, inside which request transaction.
     *
     * <p>The edge id is not that identity.  One response message may carry
     * several declared wire flows, and the finalizer mints one control edge
     * per retained response value edge, so a single fault over a single
     * request reaches one controlled occurrence once per flow -- rows
     * identical but for {@code controlledResponseEdgeId}, and therefore for
     * the {@code edgeId} hashed over it.  Comparing edge ids read that as an
     * ambiguity and refused the whole composition, although both rows state
     * the same control fact and the emitter asserts it once from the row it
     * holds either way.  Two rows are genuinely ambiguous -- suppressing the
     * occurrence on either would forbid a run the other allows -- only when
     * the fault they name differs, which is what this compares.</p>
     *
     * <p>Pure encoding shared by final composition and focused regression
     * tests.</p>
     */
    static String requestFaultIdentity(JsonObject edge) {
        if (edge == null) return "";
        return OccurrenceId.parse(
                optionalString(edge, "fromOccurrenceId")).planned()
                + "\n" + optionalString(edge, "faultPortId")
                + "\n" + optionalString(edge, "symbolicName")
                + "\n" + optionalString(edge, "sourceKey")
                + "\n" + optionalString(edge, "requestKey")
                + "\n" + optionalString(edge, "exchangeTransaction");
    }

    /**
     * The VM address of a guarded read the closure left unnamed.
     *
     * <p>A read with no stable read/case identity used to be reported as
     * {@code UnadmittedGuardedRead:unnamed}, which says that some read
     * somewhere was refused and nothing more: every such refusal collapses
     * onto one subject, so neither the count nor the site survives into the
     * gap ledger.  The VM location and read event the node still carries are
     * exactly what {@link SharedStateEvidence#guardedReadFault} already
     * required of it, so a refused read can always say where it happened
     * even when the closure could name no identity for it.</p>
     */
    static String vmReadAddress(JsonObject node) {
        if (node == null) return "unnamed";
        String location = SharedStateEvidence.locationKey(node);
        long event = optionalLongInteger(node, "readEventId", 0L);
        if (location.isEmpty() && event <= 0L) return "unnamed";
        return (location.isEmpty() ? "unlocated" : location)
                + "#event" + event;
    }

    /** What one fault marker idles, once the consequences are followed. */
    static final class FaultIdleClosure {
        /** Region cases the marker forces false. */
        final Set<String> idledCaseSelectors;
        /** Reads the marker leaves with no surviving candidate writer. */
        final Set<String> starvedReads;
        /**
         * Read -> INITIAL arms the marker made unselectable by idling every
         * case of the activation whose entry took the snapshot.
         */
        final Map<String, List<String>> hostIdledInitialArms;

        FaultIdleClosure(Set<String> idledCaseSelectors,
                         Set<String> starvedReads) {
            this(idledCaseSelectors, starvedReads, Collections.emptyMap());
        }

        FaultIdleClosure(Set<String> idledCaseSelectors,
                         Set<String> starvedReads,
                         Map<String, ? extends List<String>>
                                 hostIdledInitialArms) {
            this.idledCaseSelectors = Collections.unmodifiableSet(
                    new LinkedHashSet<>(idledCaseSelectors));
            this.starvedReads = Collections.unmodifiableSet(
                    new LinkedHashSet<>(starvedReads));
            Map<String, List<String>> copy = new LinkedHashMap<>();
            for (Map.Entry<String, ? extends List<String>> entry
                    : hostIdledInitialArms.entrySet()) {
                copy.put(entry.getKey(), Collections.unmodifiableList(
                        new ArrayList<>(entry.getValue())));
            }
            this.hostIdledInitialArms = Collections.unmodifiableMap(copy);
        }
    }

    /**
     * Whether a marker's idled set makes one arm unselectable.
     *
     * <p>A writer arm dies when any case of its writer closure is idled: the
     * write happened inside those cases.  An INITIAL arm of an instance
     * field dies when <em>every</em> case of the activation whose entry took
     * the snapshot is idled: the activation never ran, so it never observed
     * the object -- and for an object it allocated itself, there is no
     * object.  {@code hostCases} is empty for arms without such a host.</p>
     */
    static boolean armIdled(Collection<String> writerCases,
                            Collection<String> hostCases,
                            Collection<String> idled) {
        if (writerCases != null && !Collections.disjoint(writerCases, idled)) {
            return true;
        }
        return hostCases != null && !hostCases.isEmpty()
                && idled.containsAll(hostCases);
    }

    /**
     * Everything one fault marker idles, not only its own consumer.
     *
     * <p>The control edge names the occurrence that consumed the response,
     * but idling that occurrence alone leaves the regions downstream of it
     * still carrying an unconditional exactly-one partition.  Those cases
     * read locations only the idled occurrence writes, so with the marker
     * true they are forced to run and cannot: the formula is then
     * contradictory by construction and every fault-true valuation comes
     * back unsat for a reason that is about the model rather than the
     * program.</p>
     *
     * <p>The fixpoint follows the same two facts the formula already
     * encodes.  An arm of a guarded read carries its writer's case closure,
     * so an arm whose closure meets an idled case cannot be selected.  A
     * read all of whose arms are unselectable starves, and a case that
     * demanded a starved read cannot run either -- which can idle further
     * arms, so the two steps repeat until nothing changes.  An INITIAL arm
     * is owned by no region case, so it never meets the idled set: a
     * location with a retained prior version keeps its reads alive, which is
     * exactly the retention a caught transport failure implements.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static FaultIdleClosure faultIdleClosure(
            Collection<String> seedCaseSelectors,
            Map<String, ? extends Map<String, ? extends Collection<String>>>
                    readArmWriterCases,
            Map<String, ? extends Collection<String>> readOwnerCases) {
        return faultIdleClosure(seedCaseSelectors, readArmWriterCases,
                readOwnerCases, Collections.emptyMap());
    }

    /**
     * As {@link #faultIdleClosure(Collection, Map, Map)}, with {@code
     * initialArmHostCases} naming, per INITIAL arm selector, the case
     * partition of the activation whose entry took that arm's snapshot; see
     * {@link #armIdled}.
     */
    static FaultIdleClosure faultIdleClosure(
            Collection<String> seedCaseSelectors,
            Map<String, ? extends Map<String, ? extends Collection<String>>>
                    readArmWriterCases,
            Map<String, ? extends Collection<String>> readOwnerCases,
            Map<String, ? extends Collection<String>> initialArmHostCases) {
        Set<String> idled = new LinkedHashSet<>(seedCaseSelectors);
        Set<String> starved = new LinkedHashSet<>();
        Map<String, List<String>> hostIdled = new LinkedHashMap<>();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<String,
                    ? extends Map<String, ? extends Collection<String>>> read
                    : readArmWriterCases.entrySet()) {
                if (read.getValue().isEmpty()) continue;
                if (starved.contains(read.getKey())) continue;
                boolean alive = false;
                for (Map.Entry<String, ? extends Collection<String>> arm
                        : read.getValue().entrySet()) {
                    if (!armIdled(arm.getValue(),
                            initialArmHostCases.get(arm.getKey()), idled)) {
                        alive = true;
                        break;
                    }
                }
                if (alive) continue;
                starved.add(read.getKey());
                changed = true;
                for (Map.Entry<String, ? extends Collection<String>> arm
                        : read.getValue().entrySet()) {
                    Collection<String> host = initialArmHostCases.get(
                            arm.getKey());
                    if (host == null || host.isEmpty()
                            || !idled.containsAll(host)) {
                        continue;
                    }
                    hostIdled.computeIfAbsent(read.getKey(),
                            ignored -> new ArrayList<>()).add(arm.getKey());
                }
                Collection<String> owners = readOwnerCases.get(read.getKey());
                if (owners != null) idled.addAll(owners);
            }
        }
        return new FaultIdleClosure(idled, starved, hostIdled);
    }

    /** One read's surviving version, once a marker idles some of its arms. */
    static final class RetainedVersion {
        /** The read whose candidate arms the marker thinned. */
        final String readIdentity;
        /** The ordered scope the arms were ranked in: read plus use. */
        final String orderScope;
        /** Arms the marker made unselectable, in program order. */
        final List<String> idledArms;
        /**
         * The latest arm the marker left selectable, or empty when it left
         * none -- the starved read {@link
         * ConcolicSmtComposer#FAULT_IDLE_NO_RETAINED_ARM} reports.
         */
        final String retainedArm;

        RetainedVersion(String readIdentity, String orderScope,
                        List<String> idledArms, String retainedArm) {
            this.readIdentity = readIdentity;
            this.orderScope = orderScope;
            this.idledArms = Collections.unmodifiableList(
                    new ArrayList<>(idledArms));
            this.retainedArm = retainedArm;
        }
    }

    /**
     * What each read keeps when a marker idles one of its writers.
     *
     * <p>Idling is not writing a bottom value: the arm whose writer case the
     * marker forces false simply cannot be selected, and last-writer-wins
     * then hands the read the latest candidate that is still active -- its
     * predecessor in the order, or the location's INITIAL arm when the
     * marker idles every tracked writer.  {@code orders} is each scope's
     * arms earliest first, so the surviving arm scanned last is the latest
     * one, which is the version the fault retained.</p>
     *
     * <p>Only scopes the marker actually thinned are reported; a read none
     * of whose arms the marker touches keeps exactly the encoding it had and
     * has nothing to narrate.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static List<RetainedVersion> retainedVersions(
            Map<String, ? extends List<String>> orders,
            Map<String, ? extends Map<String, ? extends Collection<String>>>
                    readArmWriterCases,
            Collection<String> idledCaseSelectors) {
        return retainedVersions(orders, readArmWriterCases,
                idledCaseSelectors, Collections.emptyMap());
    }

    /** As above, honouring INITIAL arm hosts as {@link #armIdled} does. */
    static List<RetainedVersion> retainedVersions(
            Map<String, ? extends List<String>> orders,
            Map<String, ? extends Map<String, ? extends Collection<String>>>
                    readArmWriterCases,
            Collection<String> idledCaseSelectors,
            Map<String, ? extends Collection<String>> initialArmHostCases) {
        List<RetainedVersion> retained = new ArrayList<>();
        for (Map.Entry<String, ? extends List<String>> entry
                : orders.entrySet()) {
            String scope = entry.getKey();
            int split = scope.indexOf('\n');
            String read = split < 0 ? scope : scope.substring(0, split);
            Map<String, ? extends Collection<String>> byArm =
                    readArmWriterCases.get(read);
            if (byArm == null) continue;
            List<String> idledArms = new ArrayList<>();
            String surviving = "";
            for (String selector : entry.getValue()) {
                Collection<String> writerCases = byArm.get(selector);
                if (writerCases == null) continue;
                if (!armIdled(writerCases, initialArmHostCases.get(selector),
                        idledCaseSelectors)) {
                    surviving = selector;
                } else {
                    idledArms.add(selector);
                }
            }
            if (idledArms.isEmpty()) continue;
            retained.add(new RetainedVersion(read, scope, idledArms,
                    surviving));
        }
        return retained;
    }

    /**
     * The first container arm that says nothing about its container, or -1.
     *
     * <p>{@code values} are one container read's lowered arm value
     * expressions in candidate order and {@code initial} says which of them
     * name the location's INITIAL version.  A read over a selected
     * container's whole state lowers each arm through that version's own
     * mutation chain, so two arms agree only where the mutations between them
     * cannot change the value.  Two shapes mean the chain was lost rather
     * than lowered: every arm reducing to one expression, which makes the
     * read-from choice vacuous, and a writer arm reducing to an INITIAL arm's
     * expression, which claims a write ran and then reads the untouched
     * state.  Either way the container's size domain is all that is left
     * constraining it.</p>
     *
     * Pure encoding shared by final composition and focused regression tests.
     */
    static int collapsedContainerArm(List<String> values,
                                     List<Boolean> initial) {
        if (values.size() != initial.size()) {
            throw new IllegalArgumentException(
                    "one INITIAL flag per container arm value");
        }
        if (values.size() < 2) return -1;
        if (new LinkedHashSet<>(values).size() == 1) return 0;
        Set<String> initialValues = new LinkedHashSet<>();
        for (int index = 0; index < values.size(); index++) {
            if (initial.get(index)) initialValues.add(values.get(index));
        }
        for (int index = 0; index < values.size(); index++) {
            if (!initial.get(index)
                    && initialValues.contains(values.get(index))) {
                return index;
            }
        }
        return -1;
    }

    /** One target-local predicate qualified by its exact causal case. */

    private static String or(List<String> terms) {
        return VmTermLowering.or(terms);
    }

    /** Covers the two flat positive guard forms emitted by this composer. */

    /**
     * One physical configured-source hook execution in the baseline trace.
     * Region projection may give it several phase ids; source and event are
     * the identity, while the remaining members must agree across projections.
     */
    private static final class RecordedConfiguredSource {
        private final String sourceKey;
        private final long eventSeq;
        private final long invocationId;
        private final long ownerCallId;
        private final String sourceId;
        private final String fieldSignature;
        private final String siteId;
        private final String phase;
        private final String declaredCallee;

        private RecordedConfiguredSource(
                RegionInstancePlan plan,
                ConfiguredSourcePhaseContract.Occurrence occurrence) {
            sourceKey = plan.sourceKey();
            eventSeq = occurrence.runtimeEventSeq();
            invocationId = occurrence.runtimeInvocationId();
            ownerCallId = occurrence.enclosingCallIds().get(0);
            sourceId = occurrence.sourceId();
            fieldSignature = occurrence.fieldSignature();
            siteId = occurrence.siteId();
            phase = occurrence.phase().name();
            declaredCallee = occurrence.runtimeDeclaredCallee();
        }

        private String identity() {
            return sourceKey + "\u0000" + eventSeq;
        }

        private boolean sameObservation(RecordedConfiguredSource other) {
            return other != null
                    && identity().equals(other.identity())
                    && invocationId == other.invocationId
                    && ownerCallId == other.ownerCallId
                    && sourceId.equals(other.sourceId)
                    && fieldSignature.equals(other.fieldSignature)
                    && siteId.equals(other.siteId)
                    && phase.equals(other.phase)
                    && declaredCallee.equals(other.declaredCallee);
        }

        private boolean matches(JsonObject event) {
            return sourceKey.equals(optionalString(event, "sourceKey"))
                    && sourceId.equals(optionalString(event, "sourceId"))
                    && fieldSignature.equals(optionalString(event, "fieldSignature"));
        }
    }

    static final class Emitter extends VmLoweringCore {
        private final SmtSymbolTable smtSymbols = new SmtSymbolTable();
        private final List<String> preamble = new ArrayList<>();
        private final Map<String, String> declarations =
                new LinkedHashMap<>();
        private final Map<String, Term> definitions =
                new LinkedHashMap<>();
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> assertionNames = new LinkedHashSet<>();
        private final Map<String, String> assertedFormulas =
                new LinkedHashMap<>();
        private final Map<String, Integer> guardedAssertionIndexes =
                new LinkedHashMap<>();
        private final Map<String, List<String>> guardedAssertionGuards =
                new LinkedHashMap<>();
        private final Map<String, String> guardedAssertionNames =
                new LinkedHashMap<>();
        private final Map<String, RawSymbol> rawSymbols =
                new LinkedHashMap<>();
        /** Concrete VM objects/arrays used only as execution witnesses. */
        private final Map<String, Term> structuralWitnesses =
                new LinkedHashMap<>();
        /** The mutation whose stored element is being lowered, if any. */
        private JsonObject currentElementMutation;
        /** Mutation node -> content digest, so one insertion is one name. */
        private final Map<JsonObject, String> mutationDigests =
                new java.util.IdentityHashMap<>();
        /** Witness key -> ledger row, first-seen order. */
        private final Map<String, JsonObject> untrackedElementWitnesses =
                new LinkedHashMap<>();
        /** Case/observation selector -> replay scope whose VM ids it owns. */
        private final Map<String, String> executionScopesByCase =
                new LinkedHashMap<>();
        /** Group-independent recording identity -> what each group recorded. */
        private final Map<String, ExecutionRecording> executionRecordings =
                new LinkedHashMap<>();
        /** One row per identity whose groups disagree; see finish(). */
        private final JsonArray executionDivergence = new JsonArray();
        /** Symbol -> the text its value is read back from, for the slice. */
        private final Map<String, StringBuilder> valueDependencyText =
                new LinkedHashMap<>();
        /** The fatal predicate, as lowered; the slice's seed. */
        private String fatalPathTerm = "";
        /** Memoized {@link #fatalValueSlice()}. */
        private Set<String> fatalSlice;
        /** INITIAL arm selector -> activations whose entry took its snapshot. */
        private final Map<String, Set<InvocationKey>> guardedReadInitialHosts =
                new LinkedHashMap<>();
        /** INITIAL source case owner -> the activations, from the closure. */
        private final Map<String, Set<InvocationKey>> initialSnapshotHosts =
                new LinkedHashMap<>();
        /** Read identity -> content-addressed location it reads. */
        private final Map<String, String> guardedReadLocations =
                new LinkedHashMap<>();
        /** Read identity -> writer activations owning its non-INITIAL arms. */
        private final Map<String, Set<InvocationKey>>
                guardedReadWriterInvocations = new LinkedHashMap<>();
        /** Read identity -> base case selectors owning its non-INITIAL arms. */
        private final Map<String, Set<String>> guardedReadWriterSelectors =
                new LinkedHashMap<>();
        /** Base case selector -> content-addressed locations it wrote. */
        private final Map<String, Set<String>> writtenLocationsByCase =
                new LinkedHashMap<>();
        /** One row per (read, writer case with no arm); see finish(). */
        private final JsonArray unlinkedWriterCases = new JsonArray();
        /** Read identity -> the declared field that read observes. */
        private final Map<String, String> guardedReadFields =
                new LinkedHashMap<>();
        /** Read identity -> its non-INITIAL arms, as lowered. */
        private final Map<String, List<ConsumerArm>> guardedReadWriterArms =
                new LinkedHashMap<>();
        /** One row per read a declared flow never reached; see finish(). */
        private final JsonArray unattachedConsumerReads = new JsonArray();
        /** One allocated container cannot have two unrelated state shapes. */
        private final Map<String, Sort> structuralStateSorts =
                new LinkedHashMap<>();
        /**
         * Dependent reads through a reference-typed carrier, held until
         * every guarded read has been lowered.
         *
         * <p>The owner of such a read is a choice between the object
         * identities the recorded writers installed, and the field it
         * projects may itself be a carrier of the object that was installed.
         * Which families exist is only known once the whole formula has been
         * lowered -- relation order decides nothing about it -- so the read
         * lowers to a declared constant here and the constant is bound to
         * its owner-indexed value in {@link #finish()}.</p>
         */
        private final List<ReferenceFieldRead> referenceFieldReads =
                new ArrayList<>();
        /**
         * {@code executionScope \0 oop:<ownerSymRid> \0 slot \0 descriptor}
         * -> the lowered value of that object's own guarded read of the
         * field.  This is the family a dependent read routes to when its
         * owner turns out to be that object.
         */
        private final Map<String, String> guardedReadFieldFamilies =
                new LinkedHashMap<>();
        /**
         * Java references whose declared type is String need two solver
         */
        private final Set<String> unsupported = new LinkedHashSet<>();
        /** Why each subject in {@link #unsupported} was refused. */
        private final Map<String, String> unsupportedDetail =
                new LinkedHashMap<>();

        /** Records one refusal together with why the emitter made it. */
        private void refuse(String subject, String detail) {
            unsupported.add(subject);
            if (detail != null && !detail.isEmpty()) {
                unsupportedDetail.put(subject, detail);
            }
        }

        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> javaIntegralRangeAssertions =
                new LinkedHashSet<>();
        /** One value term per stable guarded-read projection. */
        private final Map<String, Term> guardedReadTerms =
                new LinkedHashMap<>();
        /** Read and arm activation is accumulated before exactly-one emits. */
        private final Map<String, Set<String>> guardedReadActivations =
                new LinkedHashMap<>();
        private final Map<String, Set<String>> guardedReadSelectors =
                new LinkedHashMap<>();
        /** Each use keeps its own activation and candidate set. */
        private final Map<String, Map<String, GuardedReadUse>> guardedReadUses =
                new LinkedHashMap<>();
        private final Map<String, Map<String, Set<String>>>
                guardedSelectorActivations = new LinkedHashMap<>();
        private final Map<String, String> guardedChoiceAssertions =
                new LinkedHashMap<>();
        private final Map<String, String> guardedActivationAssertions =
                new LinkedHashMap<>();
        /**
         * Program order of one read's candidate writers, earliest first.
         *
         * The VM appends one immutable version per store to a selected
         * location and stamps it with a session-monotonic field version id,
         * and {@code plan_read} hands a read the whole retained list under the
         * version lock.  Every candidate was therefore published before the
         * read, and the ids order them exactly.
         */
        private final Map<String, List<List<String>>> guardedReadChains =
                new LinkedHashMap<>();
        private final Map<String, List<String>> guardedReadOrders =
                new LinkedHashMap<>();
        /** Reads whose candidate writers admit no single program order. */
        private final Map<String, String> guardedReadOrderGaps =
                new LinkedHashMap<>();
        /** {@code active(w)} per arm: its writer obligation's conjunction. */
        private final Map<String, String> guardedReadArmActivity =
                new LinkedHashMap<>();
        /** Per read: each arm selector's writer case closure. */
        private final Map<String, Map<String, List<String>>>
                guardedReadArmWriterCases = new LinkedHashMap<>();
        /** Per read: the region cases whose lowering demanded it. */
        private final Map<String, Set<String>> guardedReadOwnerCases =
                new LinkedHashMap<>();
        private final Map<String, String> guardedOrderAssertions =
                new LinkedHashMap<>();
        private final Set<String> emittedGuardedReadArms =
                new LinkedHashSet<>();
        private boolean guardedReadComplete = true;
        /** One SMT definition per propagated guarded output. */
        /** Wire port each boundary family carries, for naming a gap. */
        private final Map<String, String> boundaryPortsByFamily =
                new LinkedHashMap<>();
        /** Receiving occurrence each boundary family was observed at. */
        private final Map<String, String> boundaryReceiversByFamily =
                new LinkedHashMap<>();
        /** Boundary families this composition lowered, and to what term. */
        private final Map<String, String> loweredBoundaryFamilies =
                new LinkedHashMap<>();
        private final Map<String, Term> guardedMergeTerms =
                new LinkedHashMap<>();
        /**
         * Content-addressed SMT DAG nodes.  The imported VM expression is a
         * DAG, but naïvely concatenating child text turns repeated container
         * updates and their path conditions back into an exponential tree.
         * Large lowered nodes receive one zero-argument definition and every
         * parent refers to that name.
         */
        private static final int SHARED_TERM_THRESHOLD = 1024;
        private final Set<String> activeGuardedMerges =
                new LinkedHashSet<>();
        /**
         * The read whose arms are currently being lowered.
         */
        private final Deque<String> readFromContext = new ArrayDeque<>();
        /** Compact evidence for each direct read-from arm in the formula. */
        private final JsonArray guardedReadChoices = new JsonArray();

        private final Set<String> loweredRegionCaseOwners =
                new LinkedHashSet<>();
        private final Map<InvocationKey, Set<String>> casePartitions =
                new LinkedHashMap<>();
        /** Base case selector -> its replay-specific PC observations. */
        private final Map<String, Set<String>> observationsByBaseCase =
                new LinkedHashMap<>();
        /** Every merged consumer boundary this composition dispatched. */
        private final List<BoundaryDispatch> boundaryDispatches =
                new ArrayList<>();
        /** One row per dispatch: whether a partition makes it total. */
        private final JsonArray boundaryDispatchTotality = new JsonArray();
        /** One row per associative read that can fall to an absent key. */
        private final JsonArray absentKeyDefaults = new JsonArray();
        private final Set<String> absentKeyDefaultKeys =
                new LinkedHashSet<>();

        /** Exact runtime target events and the fatal case that owns each. */
        private final JsonArray targetReachEvents = new JsonArray();
        /** SMT root name -> the one raw VM symbol that owns it. */
        private final Map<String, String> configuredSourceRoots =
                new LinkedHashMap<>();
        /** Writable configured roots and their exact emitted SMT terms. */
        private final Map<String, JsonObject>
                configuredSourceMaterializations = new LinkedHashMap<>();
        private final Map<String, JsonObject>
                manualSourceMaterializations = new LinkedHashMap<>();
        /** Raw VM root -> stable explicit task-input identity. */
        private Map<String, String> manualSourceIdentities =
                Collections.emptyMap();
        private Map<String, JsonObject> manualSourceEvents =
                Collections.emptyMap();
        /**
         * Exact manual actions that encountered an already-propagated VM
         * root.  They authorize and materialize that existing root, but stay
         * separate from {@link #manualSourceIdentities}: observing a reused
         * expression is not a second mint.
         */
        private Map<String, List<JsonObject>> reusedManualSourceEvents =
                Collections.emptyMap();
        private final List<String> targetReachCaseTerms = new ArrayList<>();
        /** Definedness facts collected while lowering one container term. */
        private Set<String> currentContainerRequirements;
        private String currentGuard = "";
        /** Target selector whose constraints are currently being lowered. */
        private String currentSymbolScope = "global";
        /** Raw VM symbol -> exact configured program-source identity. */
        private Map<String, String> symbolicSourceIdentities =
                Collections.emptyMap();
        /**
         * VM roots a declared read only NAMED, by the mint identity that
         * named them.  Deliberately separate from the root registry: a named
         * root keeps the SMT name and the domain guard its own mint gave it,
         * and gains only a materialization row.
         */
        private Map<String, String> namedSourceIdentities =
                Collections.emptyMap();
        /** Configured mint identity -> the canonical raw VM root it minted. */
        private Map<String, String> configuredSourceRawByIdentity =
                Collections.emptyMap();
        /** Configured mint identity -> its authoritative non-reused row. */
        private Map<String, JsonObject> configuredSourceEventByIdentity =
                Collections.emptyMap();
        /** Mint identity -> canonical identity for one recorded hook event. */
        private Map<String, String> configuredSourceCanonicalIdentityByIdentity =
                Collections.emptyMap();
        /** Every observed VM spelling -> its component's canonical spelling. */
        private Map<String, String> configuredSourceCanonicalRawByObservedRaw =
                Collections.emptyMap();
        /** Every observed VM spelling -> its component's canonical mint. */
        private Map<String, String>
                configuredSourceCanonicalIdentityByObservedRaw =
                Collections.emptyMap();
        private Map<String, JsonObject> symbolicSourceEvents =
                Collections.emptyMap();
        /** Region-specific phase id -> its physical baseline hook event. */
        private final Map<String, RecordedConfiguredSource>
                configuredSourceRecordedByPhase = new LinkedHashMap<>();
        /** Exact (source,event) identity -> consistency authority. */
        private final Map<String, RecordedConfiguredSource>
                configuredSourceRecordedByEvent = new LinkedHashMap<>();
        private InvocationKey currentInvocation;
        /**
         * The base case selector currently being lowered.
         *
         * <p>A guarded read belongs to the case that demanded it, which is
         * what makes "this case cannot run because that read has no surviving
         * writer" a statement the closure can make.</p>
         */
        private String currentCaseSelector = "";

        // The shared lowering's policies.
        @Override
        public Term lower(JsonElement expression, Sort expected,
                          String origin) {
            return term(expression, expected);
        }

        @Override
        public Term refuse(VmTermLowering.Reason reason, String origin,
                           String detail, Sort sort) {
            unsupported.add(reason.composedSubject(origin, detail));
            return unsupportedTerm(sort);
        }

        @Override
        public Sort castSort(String descriptor) {
            return ConcolicSmtComposer.castSort(descriptor);
        }

        @Override
        Sort sortOfJavaType(String javaType) {
            return sortOfJava(javaType);
        }

        /**
         * Composition threads Java evaluation definedness through the term
         * rather than asserting it, so that an operation whose operands are
         * only conditionally evaluated constrains nothing where Java never
         * ran it.
         */
        @Override
        Term definedResult(String text, Sort sort, IntegralWidth width,
                           String definedness, Term... inputs) {
            return dependent(Term.of(text, sort, width, "", "", definedness),
                    inputs);
        }

        @Override
        Term shortCircuit(String text, Term left, Term right,
                          boolean conjunction) {
            String rightEvaluated = conjunction ? left.text
                    : "(not " + left.text + ")";
            return Term.of(text, Sort.BOOL).withPrecondition(
                    and(Arrays.asList(left.precondition, "(=> "
                            + rightEvaluated + " " + right.precondition
                            + ")")));
        }

        @Override
        String stringDefinedness(String origin, String operation,
                                 List<Term> dereferenced,
                                 List<Term> evaluated) {
            List<String> values = new ArrayList<>();
            for (Term value : dereferenced) {
                if (value == null || value.sort != Sort.STRING) {
                    values.add("false");
                    continue;
                }
                values.add(value.precondition);
                values.add(stringNonNull(value));
            }
            for (Term value : evaluated) {
                values.add(value == null ? "false" : value.precondition);
            }
            return and(values);
        }

        /** The composer always declares java_int_to_string. */
        @Override
        void noteJavaIntToString() {
        }

        /** One recorded String.split prefix the codec could not close. */
        private Term splitElementGap(String gap) {
            return VmTermLowering.codecGap(this,
                    "java/lang/String.splitElement", gap, "", Sort.STRING);
        }

        @Override
        public VmTermLowering.RenderedInteger renderedInteger(
                JsonElement element, String origin) {
            SplitSegment match = exactSplitSegment(element);
            if (!match.complete()) {
                return new VmTermLowering.RenderedInteger(null,
                        "ROUNDTRIP_NOT_PROVED_" + match.gap);
            }
            // parseInt inverts Integer.toString only when the element is
            // that rendering and nothing else; surrounding text would need
            // a parser rather than a proof.
            SplitPiece source = match.singleIntegerPiece();
            if (source == null) {
                return new VmTermLowering.RenderedInteger(null,
                        "ROUNDTRIP_ELEMENT_NOT_ONE_INT_RENDERING");
            }
            return new VmTermLowering.RenderedInteger(
                    integerPieceTerm(source), "");
        }

        private Emitter(InvocationKey fatalInvocation) {
            this.currentInvocation = fatalInvocation;
        }

        /**
         * Registers baseline identities before summary evidence is lowered.
         * The same physical event may occur in several overlapping regions,
         * but every non-projection member must still describe the same hook.
         */
        private void registerConfiguredSourcePlan(
                Collection<RegionInstancePlan> plans) {
            for (RegionInstancePlan plan : Objects.requireNonNull(
                    plans, "plans")) {
                for (ConfiguredSourcePhaseContract.Occurrence phase
                        : plan.configuredSourcePhases()) {
                    RecordedConfiguredSource recorded =
                            new RecordedConfiguredSource(plan, phase);
                    RecordedConfiguredSource heldEvent =
                            configuredSourceRecordedByEvent.putIfAbsent(
                                    recorded.identity(), recorded);
                    if (heldEvent != null
                            && !heldEvent.sameObservation(recorded)) {
                        unsupported.add("ConfiguredSourceRecordedEventConflict:"
                                + recorded.sourceKey + ":"
                                + recorded.eventSeq);
                    }
                    RecordedConfiguredSource heldPhase =
                            configuredSourceRecordedByPhase.putIfAbsent(
                                    phase.phaseId(), recorded);
                    if (heldPhase != null
                            && !heldPhase.sameObservation(recorded)) {
                        unsupported.add("ConfiguredSourcePhaseEventConflict:"
                                + phase.phaseId());
                    }
                }
            }
        }

        /**
         * VM allocation ids restart in each replay JVM.  The imported
         * boundary-session scope is the authority for that JVM and may span
         * several linked task summaries.
         */
        private void registerExecutionScopes(
                Collection<RelationSummary> summaries, JsonObject fatal,
                JsonArray caseDependencies) {
            for (RelationSummary summary : Objects.requireNonNull(
                    summaries, "summaries")) {
                JsonObject row = summary.pathCaseView();
                JsonObject summaryRow = summary.immutableJson();
                String owner = firstNonBlank(optionalString(row,
                                LocalCaseIdentity.OWNER),
                        LocalCaseIdentity.owner(summaryRow));
                registerExecutionScope(owner, row, summaryRow);
                indexWrittenLocations(owner, summaryRow);
            }
            int ordinal = 0;
            for (JsonElement element : array(fatal, "paths")) {
                if (!element.isJsonObject()) {
                    ordinal++;
                    continue;
                }
                JsonObject path = element.getAsJsonObject();
                registerExecutionScope(targetPathCaseOwner(fatal, path,
                        ordinal++), path, fatal);
            }
            for (JsonElement dependencyElement : caseDependencies) {
                if (!dependencyElement.isJsonObject()) continue;
                JsonObject dependency = dependencyElement.getAsJsonObject();
                for (JsonElement armElement : array(dependency, "arms")) {
                    if (!armElement.isJsonObject()) continue;
                    JsonObject arm = armElement.getAsJsonObject();
                    if (firstNonBlank(optionalString(arm,
                                    SymbolicPropagationClosure
                                            .OBSERVATION_SCOPE),
                            optionalString(arm, "boundarySessionScope")).isEmpty()) {
                        continue;
                    }
                    registerExecutionScope(optionalString(arm, "caseOwner"), arm,
                            dependency);
                }
            }
        }

        /**
         * Which locations one case's own activation published a version of.
         *
         * <p>A summary's version store lists every version its activation
         * observed, including versions other occurrences wrote; a case is a
         * writer of a location only through versions its own occurrence
         * published, and an INITIAL snapshot is an observation, not a
         * write.</p>
         */
        private void indexWrittenLocations(String owner,
                                           JsonObject summaryRow) {
            if (owner.isEmpty() || summaryRow == null) return;
            String selector = LocalCaseIdentity.selector(owner);
            String occurrence = optionalString(summaryRow, "occurrenceId");
            JsonObject recorded = object(summaryRow,
                    SharedStateEvidence.RECORDED_FIELD);
            for (JsonElement element : array(recorded, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String location = optionalString(row, "locationKey");
                if (location.isEmpty()) continue;
                for (JsonElement encoded : array(object(row, "envelope"),
                        "versions")) {
                    if (!encoded.isJsonObject()) continue;
                    JsonObject version = encoded.getAsJsonObject();
                    if ("INITIAL".equals(optionalString(version,
                            "versionKind"))) {
                        continue;
                    }
                    if (!occurrence.isEmpty() && !occurrence.equals(
                            optionalString(version,
                                    SharedStateEvidence
                                            .WRITER_OCCURRENCE_ID))) {
                        continue;
                    }
                    writtenLocationsByCase.computeIfAbsent(selector,
                            ignored -> new LinkedHashSet<>()).add(location);
                    break;
                }
            }
        }

        /** The replay scope one arm's recorded value came from, or "". */
        private String armExecutionScope(JsonObject arm, String owner) {
            String observationSelector = optionalString(arm,
                    SymbolicPropagationClosure.OBSERVATION_SELECTOR);
            return firstNonBlank(
                    optionalString(arm,
                            SymbolicPropagationClosure.OBSERVATION_SCOPE),
                    optionalString(arm, "boundarySessionScope"),
                    executionScopesByCase.getOrDefault(
                            firstNonBlank(observationSelector, owner), ""));
        }

        /**
         * Notes what one replay group recorded for one group-independent
         * identity, when that value is a literal the groups can be compared
         * on.  Symbolic values are the same expression in every group by
         * construction; VM allocation witnesses are scoped per group and
         * never compare.
         */
        private void noteExecutionRecording(String key, String subject,
                                            String scope, String selector,
                                            Term value) {
            if (key.isEmpty() || scope.isEmpty() || value == null
                    || !isLiteralTerm(value.text)) {
                return;
            }
            ExecutionRecording recording = executionRecordings.computeIfAbsent(
                    key, ignored -> new ExecutionRecording(subject));
            recording.valuesByScope.computeIfAbsent(scope,
                    ignored -> new LinkedHashSet<>()).add(value.text);
            recording.selectorsByScope.computeIfAbsent(scope,
                    ignored -> new LinkedHashSet<>()).add(selector);
        }

        /**
         * Every symbol whose value the fatal predicate can be read back
         * from.
         *
         * <p>A backward walk over the value graph this composition emitted:
         * a defined constant depends on the symbols of its definition, and a
         * guarded read's value depends on each arm's term and the selector
         * that chooses it.  Nothing else is followed -- a case partition, a
         * domain bound or an order axiom constrains a symbol without ever
         * carrying a value into the target -- so a symbol outside the walk
         * cannot change what the fatal read observes, whatever else it may
         * decide.</p>
         */
        private Set<String> fatalValueSlice() {
            if (fatalSlice != null) return fatalSlice;
            Set<String> known = new LinkedHashSet<>(definitions.keySet());
            for (String key : declarations.keySet()) {
                if (key.startsWith("const:")) known.add(key.substring(6));
            }
            Map<String, Set<String>> edges = new LinkedHashMap<>();
            for (Map.Entry<String, Term> entry : definitions.entrySet()) {
                edges.computeIfAbsent(entry.getKey(),
                        ignored -> new LinkedHashSet<>()).addAll(
                        symbolsIn(entry.getValue().text, known));
            }
            for (Map.Entry<String, StringBuilder> entry
                    : valueDependencyText.entrySet()) {
                edges.computeIfAbsent(entry.getKey(),
                        ignored -> new LinkedHashSet<>()).addAll(
                        symbolsIn(entry.getValue().toString(), known));
            }
            Set<String> reached = new LinkedHashSet<>(
                    symbolsIn(fatalPathTerm, known));
            Deque<String> pending = new ArrayDeque<>(reached);
            while (!pending.isEmpty()) {
                for (String next : edges.getOrDefault(pending.removeFirst(),
                        Collections.<String>emptySet())) {
                    if (reached.add(next)) pending.addLast(next);
                }
            }
            fatalSlice = Collections.unmodifiableSet(reached);
            return fatalSlice;
        }

        /** The declared or defined names one lowered term mentions. */
        static Set<String> symbolsIn(String text, Set<String> known) {
            Set<String> found = new LinkedHashSet<>();
            if (text == null || text.isEmpty()) return found;
            Matcher matcher = SMT_IDENTIFIER.matcher(text);
            while (matcher.find()) {
                String name = matcher.group();
                if (known.contains(name)) found.add(name);
            }
            return found;
        }

        /**
         * Refuses every identity whose replay groups recorded different
         * literals; see {@link ConcolicSmtComposer#EXECUTION_DIVERGENCE}.
         */
        private void checkExecutionDivergence() {
            for (Map.Entry<String, ExecutionRecording> entry
                    : executionRecordings.entrySet()) {
                ExecutionRecording recording = entry.getValue();
                if (recording.valuesByScope.size() < 2) continue;
                Set<Set<String>> distinct = new LinkedHashSet<>(
                        recording.valuesByScope.values());
                if (distinct.size() < 2) continue;
                JsonArray groups = new JsonArray();
                List<String> narrated = new ArrayList<>();
                for (Map.Entry<String, Set<String>> scope
                        : recording.valuesByScope.entrySet()) {
                    JsonObject row = new JsonObject();
                    row.addProperty("replayScope", scope.getKey());
                    row.add("values", GSON.toJsonTree(scope.getValue()));
                    row.add("selectors", GSON.toJsonTree(
                            recording.selectorsByScope.get(scope.getKey())));
                    groups.add(row);
                    narrated.add(scopeToken(scope.getKey()) + "="
                            + scope.getValue());
                }
                Set<String> slice = fatalValueSlice();
                boolean reaches = false;
                for (Set<String> selectors
                        : recording.selectorsByScope.values()) {
                    for (String selector : selectors) {
                        if (slice.contains(selector)) reaches = true;
                    }
                }
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 2);
                row.addProperty("kind", EXECUTION_DIVERGENCE);
                row.addProperty("identity", entry.getKey());
                row.addProperty("subject", recording.subject);
                row.addProperty(REACHES_FATAL_READ, reaches);
                row.add("groups", groups);
                executionDivergence.add(row);
                if (!reaches) continue;
                refuse(EXECUTION_DIVERGENCE + "[" + recording.subject + "]",
                        "the replay executions merged into this formula"
                                + " recorded different values for one"
                                + " location the fatal read's value is built"
                                + " from, and nothing ties the group a"
                                + " witness picks here to the one it picks"
                                + " elsewhere, so the merged arms describe no"
                                + " single execution: " + String.join("; ",
                                narrated));
            }
        }

        /**
         * The region cases one read is activated under, as base cases.
         *
         * <p>A read lowered inside a local case is guarded by that case, or
         * -- where the case was observed in several replays and kept its
         * per-observation guards -- by each of that case's observations.
         * Both spellings answer the same question, so the observations are
         * folded back onto the case they belong to.</p>
         */
        private Set<String> readActivationCases(
                String read, Map<String, String> baseCaseByObservation) {
            Set<String> cases = new LinkedHashSet<>();
            for (String activation : guardedReadActivations.getOrDefault(
                    read, Collections.<String>emptySet())) {
                for (String name : caseGuardsIn(activation)) {
                    cases.add(baseCaseByObservation.getOrDefault(name, name));
                }
            }
            return cases;
        }

        /**
         * Refuses every writer case that recorded a write to a read's
         * location and owns no arm of the read; see {@link
         * ConcolicSmtComposer#GUARDED_READ_WRITER_CASE_UNLINKED}.
         */
        private void checkUnlinkedWriterCases() {
            Map<String, String> baseCaseByObservation = new LinkedHashMap<>();
            for (Map.Entry<String, Set<String>> entry
                    : observationsByBaseCase.entrySet()) {
                for (String observation : entry.getValue()) {
                    baseCaseByObservation.put(observation, entry.getKey());
                }
            }
            for (Map.Entry<String, Set<InvocationKey>> entry
                    : guardedReadWriterInvocations.entrySet()) {
                String read = entry.getKey();
                String location = guardedReadLocations.getOrDefault(read, "");
                if (location.isEmpty()) continue;
                Set<String> linked = guardedReadWriterSelectors.getOrDefault(
                        read, Collections.emptySet());
                Set<String> readCases = readActivationCases(read,
                        baseCaseByObservation);
                for (InvocationKey writer : entry.getValue()) {
                    Set<String> partition = casePartitions.get(writer);
                    if (partition == null) continue;
                    for (String caseSelector : partition) {
                        if (linked.contains(caseSelector)) continue;
                        Set<String> written = writtenLocationsByCase.get(
                                caseSelector);
                        if (written == null || !written.contains(location)) {
                            continue;
                        }
                        boolean exclusive = writerCaseExclusiveOfRead(
                                partition, readCases, caseSelector);
                        JsonObject row = new JsonObject();
                        row.addProperty("schemaVersion", 2);
                        row.addProperty("kind",
                                GUARDED_READ_WRITER_CASE_UNLINKED);
                        row.addProperty("readIdentity", read);
                        row.addProperty("locationKey", location);
                        row.addProperty("writerRegionId", writer.regionId);
                        row.addProperty("writerOccurrenceId",
                                writer.instanceId);
                        row.addProperty("caseSelector", caseSelector);
                        row.add("linkedCaseSelectors",
                                GSON.toJsonTree(linked));
                        row.add("readActivationCases",
                                GSON.toJsonTree(readCases));
                        row.addProperty("refused", !exclusive);
                        unlinkedWriterCases.add(row);
                        if (exclusive) continue;
                        refuse(GUARDED_READ_WRITER_CASE_UNLINKED + "["
                                        + read + ":" + caseSelector + "]",
                                "case " + caseSelector + " of writer "
                                        + writer.instanceId + " recorded a"
                                        + " write to " + location
                                        + " but owns no arm of this read, so"
                                        + " selecting it would let the read"
                                        + " fall to INITIAL as if the case"
                                        + " had not written");
                    }
                }
            }
        }

        private void registerExecutionScope(String owner, JsonObject local,
                                            JsonObject parent) {
            if (owner.isEmpty()) return;
            String boundarySessionScope = firstNonBlank(
                    optionalString(local,
                            SymbolicPropagationClosure.OBSERVATION_SCOPE),
                    optionalString(local, "boundarySessionScope"),
                    optionalString(parent,
                            SymbolicPropagationClosure.OBSERVATION_SCOPE),
                    optionalString(parent, "boundarySessionScope"));
            String observationSelector = firstNonBlank(optionalString(local,
                            SymbolicPropagationClosure.OBSERVATION_SELECTOR),
                    optionalString(parent,
                            SymbolicPropagationClosure.OBSERVATION_SELECTOR));
            String scopeOwner = firstNonBlank(observationSelector, owner);
            if (boundarySessionScope.isEmpty()) {
                refuse("StructuralWitnessExecutionScopeMissing:" + scopeOwner,
                        "case has no linked replay boundary-session scope");
                return;
            }
            String held = executionScopesByCase.putIfAbsent(scopeOwner,
                    boundarySessionScope);
            // A replay-independent local case can be observed in many JVM
            // sessions. SymbolicPropagationClosure leaves it on the base
            // selector only after those observations have the same symbolic
            // PC/value, and relation lowering deliberately keeps one such
            // representative. Its VM object ids therefore use that first
            // representative's scope. An observation selector, in contrast,
            // names one physical replay and must never cross session scopes.
            if (!observationSelector.isEmpty()
                    && held != null && !held.equals(boundarySessionScope)) {
                refuse("StructuralWitnessExecutionScopeConflict:"
                                + scopeOwner,
                        "one case observation names two replay-session"
                                + " scopes");
            }
        }

        private InvocationKey enterInvocation(InvocationKey invocation) {
            InvocationKey previous = currentInvocation;
            currentInvocation = invocation;
            return previous;
        }

        private void restoreInvocation(InvocationKey invocation) {
            currentInvocation = invocation;
        }

        private String enterSymbolScope(String scope) {
            String previous = currentSymbolScope;
            currentSymbolScope = firstNonBlank(scope, "global");
            return previous;
        }

        private void restoreSymbolScope(String scope) {
            currentSymbolScope = firstNonBlank(scope, "global");
        }

        private String enterGuard(String guard) {
            String previous = currentGuard;
            currentGuard = firstNonBlank(guard);
            return previous;
        }

        private void restoreGuard(String guard) {
            currentGuard = firstNonBlank(guard);
        }

        private void begin(JsonObject fatal) {
            preamble.add("; GraphChecker composed concolic query");
            preamble.add("; fatal region: " + optionalString(fatal, "regionId"));
            preamble.add("(set-logic ALL)");
            preamble.addAll(VmTermLowering.preamble(false));
            preamble.add(VmTermLowering.JAVA_INT_TO_STRING);
            // Java integral bytecodes wrap in two's-complement arithmetic.
            // Keeping the public scalar carrier as SMT Int is convenient for
            preamble.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            preamble.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        }

        /** Both names and the Java field of every selected location. */
        private Map<String, SharedStateEvidence.LocationProvenance>
                locationProvenance = Collections.emptyMap();
        /** Manual symbolic root raw symbol, by the port that mints it. */
        private final Map<String, String> manualRawByPort =
                new LinkedHashMap<>();
        /** Emitted SMT name of each manual root, by its raw symbol. */
        private final Map<String, String> manualRootNames =
                new LinkedHashMap<>();
        /** Confirmed request-fault control edges, by controlled occurrence. */
        private final Map<String, JsonObject> requestFaultControlEdges =
                new LinkedHashMap<>();
        /** Region instances whose partition the fault control edge owns. */
        private final Set<InvocationKey> faultControlledInstances =
                new LinkedHashSet<>();
        /** Every case selector a request-fault control assertion names. */
        private final Set<String> faultControlAssertedSelectors =
                new LinkedHashSet<>();
        /** One row per marker: what it idles and what it starves. */
        private final JsonArray faultControlClosureRows = new JsonArray();
        /** Advisory rows: starved reads and any unsplit partition. */
        private final JsonArray faultControlTelemetry = new JsonArray();
        private final Set<String> faultControlGapKeys = new LinkedHashSet<>();

        private String recordManualRootName(String raw, String name) {
            manualRootNames.put(raw, name);
            return name;
        }

        /**
         * What each lowered root actually returned when it was recorded.
         *
         * <p>A witness is only readable next to this: a Boolean marker that
         * came back {@code true} where the recording says {@code false} is an
         * injected fault, and a clock 90 seconds off its recorded value is
         * clock skew.  Without the recorded value a reader cannot tell either
         * from an ordinary free choice, which is how {@code Long.MIN_VALUE}
         * clocks were reported as mechanisms.</p>
         *
         * <p>Two kinds of root reach it by two routes, because the recording
         * states them in two places.  A manual root is planned: the plan's
         * own {@code symbolize} row carries the {@code primitiveValue} the
         * call returned, keyed by the port that returned it.  A configured
         * source has no port and no plan row -- the value exists only at the
         * VM mint that read the field -- so it arrives on its materialization
         * row instead, and is keyed by the solver term both routes agree on.
         * A configured source that states none is left out rather than
         * defaulted: a ledger with no row is what tells a reader the polarity
         * is unknown.</p>
         */
        private JsonArray recordedRootLedger(List<JsonObject> planRows) {
            JsonArray rows = new JsonArray();
            Set<String> seen = new LinkedHashSet<>();
            Set<String> seenTerms = new LinkedHashSet<>();
            for (JsonObject plan : planRows == null
                    ? Collections.<JsonObject>emptyList() : planRows) {
                if (plan == null) continue;
                for (JsonElement goal : array(plan, "closureGoals")) {
                    if (!goal.isJsonObject()) continue;
                    for (JsonElement encoded
                            : array(goal.getAsJsonObject(), "symbolize")) {
                        if (!encoded.isJsonObject()) continue;
                        JsonObject row = encoded.getAsJsonObject();
                        String port = optionalString(row, "portId");
                        String recorded = optionalString(row,
                                "primitiveValue");
                        if (port.isEmpty() || recorded.isEmpty()
                                || !seen.add(port)) {
                            continue;
                        }
                        String raw = manualRawByPort.get(port);
                        String term = raw == null ? ""
                                : firstNonBlank(manualRootNames.get(raw));
                        if (term.isEmpty() || !seenTerms.add(term)) continue;
                        JsonObject out = new JsonObject();
                        out.addProperty("portId", port);
                        out.addProperty("sourceKey",
                                optionalString(row, "sourceKey"));
                        out.addProperty("siteId",
                                optionalString(row, "siteId"));
                        out.addProperty("javaType",
                                optionalString(row, "javaType"));
                        out.addProperty("eventSeq",
                                optionalLongInteger(row, "eventSeq", -1L));
                        out.addProperty("recordedValue", recorded);
                        out.addProperty("solverTerm", term);
                        out.addProperty("wallClock",
                                ClockRootPhysics.clockCallee(optionalString(
                                        row, "declaredCallee")));
                        rows.add(out);
                    }
                }
            }
            for (JsonObject source
                    : configuredSourceMaterializations.values()) {
                String term = optionalString(source, "solverTerm");
                String recorded = optionalString(source,
                        RECORDED_SOURCE_VALUE);
                if (term.isEmpty() || recorded.isEmpty()
                        || !seenTerms.add(term)) {
                    continue;
                }
                JsonObject out = new JsonObject();
                // A configured source has no port; the field it reads is
                // where a reader chasing "which value was this" has to land,
                // so the field signature is its site.
                out.addProperty("portId", "");
                out.addProperty("sourceKey",
                        optionalString(source, "sourceKey"));
                out.addProperty("siteId",
                        optionalString(source, "fieldSignature"));
                out.addProperty("sourceId", optionalString(source,
                        "sourceId"));
                out.addProperty("sourceOccurrenceId",
                        optionalString(source, "sourceOccurrenceId"));
                out.addProperty("fieldSignature",
                        optionalString(source, "fieldSignature"));
                out.addProperty("javaType",
                        optionalString(source, "javaTypeDescriptor"));
                out.addProperty("eventSeq", -1L);
                out.addProperty("recordedValue", recorded);
                out.addProperty("solverTerm", term);
                // A configuration field is not a clock, whatever it holds.
                out.addProperty("wallClock", false);
                rows.add(out);
            }
            return rows;
        }

        /**
         * Which declared value handoffs actually constrain this formula.
         *
         * <p>A value crossing a wire is not lowered as an equality between
         * two port symbols -- the VM propagated the producer's expression
         * into the consumer's own storage, so the consumer's reference *is*
         * the producer's expression and the closure substitutes it.  The
         * observable form is one boundary family per handoff, lowered by
         * {@link #caseMergeTerm} into a {@code merged_boundary__} constant.
         * The failure mode this ledger catches is a family the closure built
         * from the recorded handoff and no lowered expression ever referred
         * to: the wire's value then constrains nothing, silently, and the
         * consumer's own read is free.</p>
         */
        private JsonArray wireFlowBindings(
                JsonArray dependencies, Set<String> declaredPorts,
                Map<String, String> consumerFields,
                Map<String, Set<String>> readFieldNodes) {
            Map<String, JsonObject> byFamily = new LinkedHashMap<>();
            for (JsonElement element : dependencies) {
                if (!element.isJsonObject()) continue;
                JsonObject dependency = element.getAsJsonObject();
                if (!VmExpressionIr.RPC_ATTACH.equals(optionalString(
                        dependency, "boundaryKind"))) {
                    continue;
                }
                String familyKey = optionalString(dependency, "familyKey");
                if (!familyKey.isEmpty()) {
                    byFamily.putIfAbsent(familyKey, dependency);
                }
            }
            // Seed from every family the recorded handoff evidence carries,
            // not only from the ones that produced a dependency row: a
            // family the closure never resolved has no row at all, and
            // iterating rows alone is exactly how such a family used to
            // leave no trace.
            List<String> families = new ArrayList<>(byFamily.keySet());
            for (String observed : boundaryPortsByFamily.keySet()) {
                if (!byFamily.containsKey(observed)) families.add(observed);
            }
            Collections.sort(families);
            JsonArray rows = new JsonArray();
            for (String familyKey : families) {
                JsonObject dependency = byFamily.get(familyKey);
                boolean referenced = dependency != null;
                boolean bound = loweredBoundaryFamilies.containsKey(
                        familyKey);
                JsonObject row = new JsonObject();
                row.addProperty("familyKey", familyKey);
                row.addProperty("boundaryKind", VmExpressionIr.RPC_ATTACH);
                row.addProperty("portId", boundaryPortsByFamily
                        .getOrDefault(familyKey, ""));
                row.addProperty("receiverOccurrenceId",
                        boundaryReceiversByFamily.getOrDefault(familyKey,
                                ""));
                row.addProperty("armCount", referenced
                        ? array(dependency, "arms").size() : 0);
                row.addProperty("referenced", referenced);
                row.addProperty("valueBound", bound);
                row.addProperty("solverTerm",
                        loweredBoundaryFamilies.getOrDefault(familyKey, ""));
                String port = boundaryPortsByFamily.getOrDefault(
                        familyKey, "");
                boolean declared = declaredPorts.contains(port);
                String consumerField = consumerFieldOf(port, consumerFields);
                String receiverNode = occurrenceSourceKey(
                        boundaryReceiversByFamily.getOrDefault(familyKey,
                                ""));
                boolean fieldRead = consumerFieldReadOnReceiver(
                        consumerField, receiverNode, readFieldNodes);
                row.addProperty("declaredWireFlow", declared);
                if (!consumerField.isEmpty()) {
                    row.addProperty(ClaimPolicy.CONSUMER_FIELD,
                            consumerField);
                    row.addProperty("consumerFieldRead", fieldRead);
                }
                if (!referenced) {
                    row.addProperty("reason",
                            CONSUMER_BOUNDARY_FAMILY_UNREFERENCED);
                }
                rows.add(row);
            }
            // Asked once per declared port, over the ledger this method just
            // built, because one flow is many families and the composition
            // only has to lower one of them. The families that reached no
            // term stay in the ledger as telemetry: which observation was
            // lowered is worth knowing even when the flow itself is fine.
            for (String declaredPort : unboundDeclaredPorts(rows)) {
                refuse(WIRE_FLOW_VALUE_UNBOUND + "[" + declaredPort + "]",
                        "a declared value handoff reached the composition with"
                                + " no consumer boundary family any lowered"
                                + " expression refers to and no read of the"
                                + " field its consumer assigns, so the value"
                                + " the wire carried constrains nothing");
            }
            checkUnattachedConsumerReads(rows, consumerFields);
            return rows;
        }

        /**
         * Refuses every read of a declared flow's consumer field, on the
         * consuming node, that no arm ties to that flow's wire.
         *
         * <p>The ledger says which handoffs were lowered; this asks the
         * complementary question the ledger cannot: of the reads that carry
         * the flow's value onward, which ones got it from the wire.  A read
         * passes as soon as one writer arm is, or contains, the lowered term
         * of an {@code RPC_ATTACH} family of a port that declares this field
         * -- one handoff is enough, since the arms partition the executions
         * and the cases.  A read all of whose arms avoid every such term is
         * serving the field from something the wire did not carry.</p>
         *
         * <p>Only reads written on a node that receives the flow are asked.
         * The producer assigns the same field from its own state, which is
         * where the value is made, and refusing that would refuse the flow's
         * own source.</p>
         */
        private void checkUnattachedConsumerReads(
                JsonArray ledger, Map<String, String> consumerFields) {
            Map<String, Set<String>> termsByField = new LinkedHashMap<>();
            Map<String, Set<String>> receiverNodesByField =
                    new LinkedHashMap<>();
            Map<String, Set<String>> portsByField = new LinkedHashMap<>();
            for (JsonElement element : ledger) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String field = optionalString(row,
                        ClaimPolicy.CONSUMER_FIELD);
                if (field.isEmpty()) continue;
                portsByField.computeIfAbsent(field,
                        ignored -> new LinkedHashSet<>()).add(
                        optionalString(row, "portId"));
                String node = occurrenceSourceKey(optionalString(row,
                        "receiverOccurrenceId"));
                if (!node.isEmpty()) {
                    receiverNodesByField.computeIfAbsent(field,
                            ignored -> new LinkedHashSet<>()).add(node);
                }
                String term = optionalString(row, "solverTerm");
                if (!term.isEmpty()) {
                    termsByField.computeIfAbsent(field,
                            ignored -> new LinkedHashSet<>()).add(term);
                }
            }
            if (receiverNodesByField.isEmpty()) return;
            for (Map.Entry<String, List<ConsumerArm>> read
                    : guardedReadWriterArms.entrySet()) {
                String field = guardedReadFields.getOrDefault(read.getKey(),
                        "");
                Set<String> nodes = receiverNodesByField.get(field);
                if (nodes == null || read.getValue().isEmpty()) continue;
                Set<String> terms = termsByField.getOrDefault(field,
                        Collections.emptySet());
                boolean consuming = false;
                boolean attached = false;
                Set<String> writers = new LinkedHashSet<>();
                for (ConsumerArm arm : read.getValue()) {
                    if (!nodes.contains(arm.sourceKey)) continue;
                    consuming = true;
                    writers.add(arm.occurrence);
                    for (String term : terms) {
                        if (arm.term.contains(term)) attached = true;
                    }
                }
                if (!consuming || attached) continue;
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", WIRE_FLOW_CONSUMER_FIELD_UNATTACHED);
                row.addProperty("readIdentity", read.getKey());
                row.addProperty(ClaimPolicy.CONSUMER_FIELD, field);
                row.add("writerOccurrences", GSON.toJsonTree(writers));
                row.add("declaredPorts", GSON.toJsonTree(
                        portsByField.getOrDefault(field,
                                Collections.emptySet())));
                row.add("boundFlowTerms", GSON.toJsonTree(terms));
                unattachedConsumerReads.add(row);
                refuse(WIRE_FLOW_CONSUMER_FIELD_UNATTACHED + "[" + field
                                + "@" + read.getKey() + "]",
                        "this read observes the field a declared wire flow"
                                + " assigns its value to, on the node that"
                                + " receives the flow, and no writer arm of"
                                + " it is that flow's boundary: the value it"
                                + " serves was written at " + writers
                                + " from something the wire did not carry");
            }
        }

        /**
         * The case partitions this formula asserts unconditionally.
         *
         * <p>A fault-controlled occurrence keeps no unconditional
         * exactly-one partition -- its predecessor's marker decides whether
         * any of its cases runs -- so advertising one would invite a consumer
         * to pin it and freeze the marker.</p>
         */
        private List<Collection<String>> unconditionalCasePartitions() {
            return casePartitionsBy(false);
        }

        private List<Collection<String>> conditionalCasePartitions() {
            return casePartitionsBy(true);
        }

        private List<Collection<String>> casePartitionsBy(boolean conditional) {
            List<Collection<String>> rows = new ArrayList<>();
            for (Map.Entry<InvocationKey, Set<String>> entry
                    : casePartitions.entrySet()) {
                if (faultControlledInstances.contains(entry.getKey())
                        == conditional) {
                    rows.add(entry.getValue());
                }
            }
            return rows;
        }

        /**
         * Constrains each symbolized wall-clock read to what a clock can have
         * returned: within a configured skew of the value that read actually
         * returned, and non-decreasing across one node's recorded order.
         *
         * <p>Without this a {@code Timer.now()} root carried only the 64-bit
         * integral domain, so a witness could answer {@code Long.MIN_VALUE}
         * at one read and a negative millisecond count at the next.  Nothing
         * is pinned to its recorded value: cross-node clock skew is a real
         * failure mechanism for these workloads, so each node's window is
         * anchored on its own reads and two nodes may sit up to twice the
         * skew apart.</p>
         *
         * <p>A clock read the plan declares but this composition never
         * lowered as a root contributes no constraint and is recorded with an
         * empty solver term, so the ledger says which reads are governed.</p>
         */
        private JsonObject lowerClockRoots(List<JsonObject> planRows,
                                           long skewMillis) {
            Map<String, List<ClockRootPhysics.ClockRead>> byNode =
                    ClockRootPhysics.readsByNode(planRows);
            List<JsonObject> ledger = new ArrayList<>();
            String previousGuard = enterGuard("");
            try {
                for (Map.Entry<String, List<ClockRootPhysics.ClockRead>> node
                        : byNode.entrySet()) {
                    String previousTerm = "";
                    for (ClockRootPhysics.ClockRead read : node.getValue()) {
                        String raw = manualRawByPort.get(read.portId);
                        String term = raw == null ? null
                                : manualRootNames.get(raw);
                        if (term == null || term.isEmpty()) {
                            ledger.add(ClockRootPhysics.ledgerRow(read, "",
                                    "", ""));
                            continue;
                        }
                        String windowAssertion = assertNamed(
                                smtSymbols.mint("clock_window__",
                                        read.portId, 16),
                                ClockRootPhysics.window(term,
                                        read.recordedValue, skewMillis));
                        String orderAssertion = "";
                        if (!previousTerm.isEmpty()
                                && !previousTerm.equals(term)) {
                            orderAssertion = assertNamed(
                                    smtSymbols.mint("clock_monotonic__",
                                            node.getKey() + "\n"
                                                    + read.portId, 16),
                                    "(<= " + previousTerm + " " + term + ")");
                        }
                        previousTerm = term;
                        ledger.add(ClockRootPhysics.ledgerRow(read, term,
                                windowAssertion, orderAssertion));
                    }
                }
            } finally {
                restoreGuard(previousGuard);
            }
            return ClockRootPhysics.manifest(skewMillis, ledger);
        }

        /**
         * Indexes each confirmed request-fault control edge and the manual
         * root its fault port mints.
         *
         * <p>A request-fault control edge names no value port on purpose: the
         * fault marker is an independent symbolic input and the request
         * transaction is the membership proof.  Nothing lowered the control
         * dependence, so the marker sat in the formula as an isolated
         * component -- its declaration, its two case definitions and the
         * exactly-one partition -- and neither polarity could reach the
         * successor region it decides.</p>
         */
        private void indexRequestFaultControl(List<JsonObject> owners) {
            for (JsonObject owner : owners == null
                    ? Collections.<JsonObject>emptyList() : owners) {
                if (owner == null) continue;
                for (JsonObject event
                        : SymbolicSourceEvidence.eventsOf(owner)) {
                    if (!SymbolicSourceEvidence.isManual(event)) continue;
                    String port = optionalString(event, "portId");
                    String raw = optionalString(event, "rawSymbol");
                    if (!port.isEmpty() && !raw.isEmpty()) {
                        manualRawByPort.putIfAbsent(port, raw);
                    }
                }
                for (JsonElement element : array(owner, "edgeBindings")) {
                    if (!element.isJsonObject()) continue;
                    JsonObject edge = element.getAsJsonObject();
                    if (!AutomaticRegionEdge.trustedRequestFaultControl(edge)
                            || !"CONFIRMED_REQUEST_CONTROL".equals(
                            optionalString(edge, "state"))) {
                        continue;
                    }
                    String controlled = OccurrenceId.parse(optionalString(
                            edge, "toOccurrenceId")).planned();
                    if (controlled.isEmpty()) continue;
                    JsonObject held = requestFaultControlEdges.putIfAbsent(
                            controlled, edge);
                    if (held != null && !requestFaultIdentity(held)
                            .equals(requestFaultIdentity(edge))) {
                        // Two faults controlling one occurrence: suppressing
                        // it on either would forbid a run the other allows.
                        refuse("RequestFaultControlAmbiguous:" + controlled,
                                "one controlled occurrence has two confirmed"
                                        + " request-fault control edges naming"
                                        + " different faults");
                    }
                }
            }
        }

        /**
         * Ties a controlled region's cases to its predecessor's fault marker.
         *
         * <p>A region instance is otherwise partitioned unconditionally --
         * exactly one of its cases is always active -- so "this region did not
         * run" could not be said at all.  For an occurrence a confirmed
         * request-fault control edge governs, the fault decides instead: the
         * marker true forbids every case of the controlled occurrence, and the
         * marker false keeps the ordinary exactly-one partition.  The edge's
         * own evidence is what licenses both directions, since it proves the
         * request was sent, the fault point passed, and the response was
         * received and consumed in that order.</p>
         *
         * <p>Fail closed: an edge whose fault marker is not a lowered manual
         * root leaves the unconditional partition exactly as it was and
         * refuses, rather than weakening the partition for nothing.</p>
         */
        private void emitRequestFaultControl() {
            Map<InvocationKey, String> directMarker = new LinkedHashMap<>();
            Map<InvocationKey, String> directEdge = new LinkedHashMap<>();
            Map<String, Integer> edgeInstanceCount = new LinkedHashMap<>();
            for (Map.Entry<String, JsonObject> entry
                    : requestFaultControlEdges.entrySet()) {
                JsonObject edge = entry.getValue();
                String edgeId = optionalString(edge, "edgeId");
                String raw = manualRawByPort.get(optionalString(edge,
                        "faultPortId"));
                String fault = raw == null ? null : manualRootNames.get(raw);
                List<InvocationKey> instances = new ArrayList<>();
                for (Map.Entry<InvocationKey, Set<String>> partition
                        : casePartitions.entrySet()) {
                    if (partition.getValue().isEmpty()) continue;
                    if (!entry.getKey().equals(OccurrenceId.parse(
                            partition.getKey().instanceId).planned())) {
                        continue;
                    }
                    instances.add(partition.getKey());
                }
                if (instances.isEmpty()) continue;
                if (fault == null || fault.isEmpty()) {
                    refuse("RequestFaultControlMarkerMissing:" + edgeId,
                            "controlled occurrence has no lowered fault"
                                    + " marker to depend on");
                    continue;
                }
                edgeInstanceCount.put(edgeId, instances.size());
                for (InvocationKey instance : instances) {
                    directMarker.put(instance, fault);
                    directEdge.put(instance, edgeId);
                }
            }
            if (directMarker.isEmpty()) return;

            Map<InvocationKey, Set<String>> markersByInstance =
                    new LinkedHashMap<>();
            List<String> markers = new ArrayList<>(
                    new LinkedHashSet<>(directMarker.values()));
            Collections.sort(markers);
            for (String marker : markers) {
                Set<String> seed = new LinkedHashSet<>();
                for (Map.Entry<InvocationKey, String> entry
                        : directMarker.entrySet()) {
                    if (!marker.equals(entry.getValue())) continue;
                    Set<String> cases = casePartitions.get(entry.getKey());
                    if (cases != null) seed.addAll(cases);
                }
                FaultIdleClosure closure = faultIdleClosure(seed,
                        guardedReadArmWriterCases, guardedReadOwnerCases,
                        initialArmHostCases());
                for (Map.Entry<InvocationKey, Set<String>> partition
                        : casePartitions.entrySet()) {
                    if (partition.getValue().isEmpty()) continue;
                    if (!closure.idledCaseSelectors.containsAll(
                            partition.getValue())) {
                        continue;
                    }
                    markersByInstance.computeIfAbsent(partition.getKey(),
                            ignored -> new LinkedHashSet<>()).add(marker);
                }
                recordFaultControlClosure(marker, seed, closure);
            }

            for (Map.Entry<InvocationKey, Set<String>> entry
                    : markersByInstance.entrySet()) {
                InvocationKey instance = entry.getKey();
                Set<String> selectors = casePartitions.get(instance);
                if (selectors == null || selectors.isEmpty()) continue;
                List<String> instanceMarkers =
                        new ArrayList<>(entry.getValue());
                Collections.sort(instanceMarkers);
                String marker = instanceMarkers.size() == 1
                        ? instanceMarkers.get(0) : or(instanceMarkers);
                String edgeId = directEdge.get(instance);
                String name;
                if (edgeId == null || edgeId.isEmpty()) {
                    name = "request_fault_control_closure__"
                            + smtName(instance.regionId) + "_"
                            + smtName(instance.instanceId);
                } else if (edgeInstanceCount.getOrDefault(edgeId, 1) > 1) {
                    name = "request_fault_control__" + smtName(edgeId) + "_"
                            + smtName(instance.instanceId);
                } else {
                    name = "request_fault_control__" + smtName(edgeId);
                }
                assertNamed(name,
                        faultControlledPartition(marker, selectors));
                faultControlAssertedSelectors.addAll(selectors);
                faultControlledInstances.add(instance);
            }
        }

        /**
         * INITIAL arm selector -> case partition of the activation whose
         * entry took the snapshot, for every INITIAL arm of an instance field
         * whose host this composition lowered.
         */
        private Map<String, Set<String>> initialArmHostCases() {
            Map<String, Set<String>> hosts = new LinkedHashMap<>();
            for (Map.Entry<String, Set<InvocationKey>> entry
                    : guardedReadInitialHosts.entrySet()) {
                Set<String> cases = new LinkedHashSet<>();
                boolean complete = true;
                for (InvocationKey host : entry.getValue()) {
                    Set<String> partition = casePartitions.get(host);
                    // An activation this composition never lowered has no
                    // cases to idle, so nothing can say it did not run: the
                    // arm keeps whatever standing it had.
                    if (partition == null || partition.isEmpty()) {
                        complete = false;
                        break;
                    }
                    cases.addAll(partition);
                }
                if (!complete || cases.isEmpty()) continue;
                hosts.put(entry.getKey(), cases);
            }
            return hosts;
        }

        /** One auditable row per marker, plus a row per starved read. */
        private void recordFaultControlClosure(String marker,
                                               Set<String> seed,
                                               FaultIdleClosure closure) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", FAULT_CONTROL_CLOSURE_KIND);
            row.addProperty("marker", marker);
            row.add("directlyIdledCaseSelectors", GSON.toJsonTree(seed));
            row.add("idledCaseSelectors",
                    GSON.toJsonTree(closure.idledCaseSelectors));
            row.add("starvedReads",
                    GSON.toJsonTree(closure.starvedReads));
            row.add("retained", retainedRows(closure));
            faultControlClosureRows.add(row);
            for (String read : closure.starvedReads) {
                faultControlGap(FAULT_IDLE_NO_RETAINED_ARM, read,
                        "the fault idles every candidate writer of this read"
                                + " and the location published no retained"
                                + " prior version, so the marker true leaves"
                                + " the reading case with nothing to observe"
                                + " (marker " + marker + ")");
                List<String> hostIdled = closure.hostIdledInitialArms.get(
                        read);
                if (hostIdled == null || hostIdled.isEmpty()) continue;
                List<String> hosts = new ArrayList<>();
                for (String arm : hostIdled) {
                    Set<InvocationKey> host = guardedReadInitialHosts.get(arm);
                    if (host == null || host.isEmpty()) {
                        hosts.add(arm);
                        continue;
                    }
                    for (InvocationKey key : host) hosts.add(key.instanceId);
                }
                String detail = "the marker idles every case of the"
                        + " activation whose entry took this read's INITIAL"
                        + " snapshot (" + String.join(", ", hosts) + "), so"
                        + " the snapshot names no value of an object that"
                        + " activation observed; the JVM default it holds is"
                        + " not the version the fault retained (marker "
                        + marker + ")";
                faultControlGap(FAULT_IDLE_INITIAL_HOST_IDLED, read, detail);
            }
        }

        /**
         * The retained pairs this marker leaves behind, with their evidence.
         *
         * <p>{@link ConcolicSmtComposer#retainedVersions} decides which arm
         * survives; this adds what a reader narrating the witness needs to
         * see next to it -- the location the fault left a stale version in,
         * the field that names it, and the term the surviving arm binds.  An
         * empty {@code retainedArm} is a read the marker starved, which
         * {@link ConcolicSmtComposer#FAULT_IDLE_NO_RETAINED_ARM} reports as
         * a gap as well.</p>
         */
        private JsonArray retainedRows(FaultIdleClosure closure) {
            Map<String, JsonObject> arms = new LinkedHashMap<>();
            for (JsonElement element : guardedReadChoices) {
                if (!element.isJsonObject()) continue;
                JsonObject arm = element.getAsJsonObject();
                arms.put(optionalString(arm, "readIdentity") + "\n"
                        + optionalString(arm, "selector"), arm);
            }
            JsonArray rows = new JsonArray();
            for (RetainedVersion retained : retainedVersions(
                    guardedReadOrders, guardedReadArmWriterCases,
                    closure.idledCaseSelectors, initialArmHostCases())) {
                JsonObject arm = arms.get(retained.readIdentity + "\n"
                        + retained.retainedArm);
                JsonObject idled = arms.get(retained.readIdentity + "\n"
                        + retained.idledArms.get(0));
                JsonObject row = new JsonObject();
                row.addProperty("readIdentity", retained.readIdentity);
                row.addProperty("orderScope", retained.orderScope);
                row.addProperty("locationKey", optionalString(
                        idled == null ? arm : idled, "locationKey"));
                row.addProperty("declaredField", optionalString(
                        idled == null ? arm : idled, "declaredField"));
                row.add("idledArms", GSON.toJsonTree(retained.idledArms));
                row.addProperty("retainedArm", retained.retainedArm);
                String owner = optionalString(arm, "writerCaseOwner");
                row.addProperty("retainedWriterCaseOwner", owner);
                row.addProperty("retainedIsInitialVersion",
                        owner.startsWith(SymbolicPropagationClosure
                                .INITIAL_SOURCE_CASE_PREFIX));
                row.addProperty("retainedValueTerm",
                        optionalString(arm, "valueTerm"));
                rows.add(row);
            }
            return rows;
        }

        /**
         * Records one fault-control gap -- and refuses on it.
         *
         * <p>Two of the three reasons used to record and return. A read the
         * marker starves observes nothing, and a fault-controlled selector
         * the reach driver may pin freezes the marker the claim is about;
         * both decide the experiment's own hypothesis outside the formula,
         * which is the same thing {@code FAULT_IDLE_INITIAL_HOST_IDLED}
         * already refused for. So all three refuse, and the caller that used
         * to pair this with its own {@code refuse} no longer has to.</p>
         */
        private void faultControlGap(String reason, String subject,
                                     String detail) {
            if (!faultControlGapKeys.add(reason + "\n" + subject)) return;
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("reason", reason);
            row.addProperty("subject", subject);
            row.addProperty("detail", detail);
            faultControlTelemetry.add(row);
            refuse(reason + "[" + subject + "]", detail);
        }

        /**
         * The contract the frontier driver depends on, checked here.
         *
         * <p>Every case selector a request-fault control assertion names is
         * decided by that marker, so it must be advertised as a conditional
         * partition and must not appear among the unconditional ones.  A
         * consumer that pins an unconditional partition is restating what the
         * formula already says; pinning one of these would silently decide the
         * marker, which is how a fault-true valuation came back unsat for a
         * reason about the driver rather than the program.</p>
         */
        private void checkFaultPartitionSplit() {
            if (faultControlAssertedSelectors.isEmpty()) return;
            Set<String> unconditional = new LinkedHashSet<>();
            for (Collection<String> partition
                    : unconditionalCasePartitions()) {
                unconditional.addAll(partition);
            }
            Set<String> conditional = new LinkedHashSet<>();
            for (Collection<String> partition : conditionalCasePartitions()) {
                conditional.addAll(partition);
            }
            for (String selector : unsplitFaultControlledSelectors(
                    faultControlAssertedSelectors,
                    Collections.singletonList(unconditional),
                    Collections.singletonList(conditional))) {
                faultControlGap(FAULT_PARTITION_UNSPLIT, selector,
                        "a fault-controlled case selector is "
                                + (unconditional.contains(selector)
                                ? "advertised as an unconditional partition"
                                : "advertised in no conditional partition")
                                + ", so the reach driver may pin it and"
                                + " freeze the marker it decides");
            }
        }

        JsonObject faultControlClosureLedger() {
            checkFaultPartitionSplit();
            JsonObject ledger = new JsonObject();
            ledger.addProperty("schemaVersion", 1);
            ledger.addProperty("kind", FAULT_CONTROL_CLOSURE_KIND);
            ledger.add("markers", faultControlClosureRows.deepCopy());
            ledger.add("gaps", faultControlTelemetry.deepCopy());
            return ledger;
        }

        JsonArray faultControlGaps() {
            return faultControlTelemetry.deepCopy();
        }

        /**
         * Takes the closure's INITIAL snapshot hosts: which activation's
         * region entry published each INITIAL source case.
         */
        private void registerInitialSnapshotHosts(JsonArray hosts) {
            for (JsonElement element : hosts) {
                if (!element.isJsonObject()) continue;
                JsonObject row = element.getAsJsonObject();
                String owner = optionalString(row,
                        SymbolicPropagationClosure.INITIAL_HOST_OWNER);
                String region = optionalString(row,
                        SymbolicPropagationClosure.INITIAL_HOST_REGION_ID);
                String occurrence = optionalString(row,
                        SymbolicPropagationClosure
                                .INITIAL_HOST_OCCURRENCE_ID);
                if (owner.isEmpty() || region.isEmpty()
                        || occurrence.isEmpty()) {
                    continue;
                }
                initialSnapshotHosts.computeIfAbsent(owner,
                        ignored -> new LinkedHashSet<>()).add(
                        new InvocationKey(region, occurrence));
            }
        }

        private void registerSymbolicSources(List<JsonObject> owners) {
            locationProvenance = SharedStateEvidence.locationProvenance(
                    owners);
            indexRequestFaultControl(owners);
            for (JsonObject owner : owners == null
                    ? Collections.<JsonObject>emptyList() : owners) {
                for (JsonObject event : VmHandoffEvidence.eventsOf(owner)) {
                    String family = optionalString(event,
                            VmHandoffEvidence.BOUNDARY_FAMILY_KEY);
                    String port = optionalString(event, "portId");
                    if (!family.isEmpty() && !port.isEmpty()) {
                        boundaryPortsByFamily.putIfAbsent(family, port);
                        String receiver = optionalString(event,
                                "consumerOccurrenceId");
                        if (!receiver.isEmpty()) {
                            boundaryReceiversByFamily.putIfAbsent(family,
                                    receiver);
                        }
                    }
                }
            }
            try {
                symbolicSourceIdentities =
                        SymbolicSourceEvidence.rawSymbolIdentities(owners,
                                false);
                manualSourceIdentities =
                        SymbolicSourceEvidence.rawSymbolIdentities(owners,
                                true);
                for (String raw : manualSourceIdentities.keySet()) {
                    if (symbolicSourceIdentities.containsKey(raw)) {
                        throw new IllegalArgumentException(
                                "one VM symbol has both manual and configured"
                                        + " root authority: " + raw);
                    }
                }
                Map<String, JsonObject> manualEvents = new LinkedHashMap<>();
                Map<String, JsonObject> events = new LinkedHashMap<>();
                List<JsonObject> observedEvents = new ArrayList<>();
                Map<String, Set<String>> namedCandidates =
                        new LinkedHashMap<>();
                for (JsonObject owner : Objects.requireNonNull(owners,
                        "owners")) {
                    String sourceKey = optionalString(owner, "sourceKey");
                    for (JsonObject event
                            : SymbolicSourceEvidence.eventsOf(owner)) {
                        String raw = optionalString(event, "rawSymbol");
                        JsonObject registered = shallowCopy(event);
                        registered.addProperty("sourceKey", sourceKey);
                        if (SymbolicSourceEvidence.isManual(event)) {
                            JsonObject held = manualEvents.putIfAbsent(raw,
                                    registered);
                            if (held != null
                                    && !optionalString(held, "sourceIdentity").equals(
                                    optionalString(registered, "sourceIdentity"))) {
                                throw new IllegalArgumentException(
                                        "one VM symbol names two manual"
                                                + " task inputs: " + raw);
                            }
                            continue;
                        }
                        observedEvents.add(registered);
                        JsonObject held = events.putIfAbsent(raw, registered);
                        if (held == null) {
                            if (SymbolicSourceEvidence.isReused(event)) {
                                namedCandidates.computeIfAbsent(raw,
                                        ignored -> new LinkedHashSet<>()).add(
                                        SymbolicSourceEvidence.identity(event));
                            }
                            continue;
                        }
                        boolean heldNames =
                                SymbolicSourceEvidence.isReused(held);
                        boolean namesRoot =
                                SymbolicSourceEvidence.isReused(registered);
                        if (heldNames != namesRoot) {
                            if (!optionalString(held, "sourceId").equals(
                                    optionalString(registered, "sourceId"))
                                    || !optionalString(held, "fieldSignature").equals(
                                    optionalString(registered, "fieldSignature"))
                                    || !optionalString(held, "javaType").equals(
                                    optionalString(registered, "javaType"))) {
                                throw new IllegalArgumentException(
                                        "one VM symbol is minted and named"
                                                + " as different configured"
                                                + " sources: " + raw);
                            }
                            // The site that MINTED the symbol is its
                            // authority; a read that only named it defers.
                            if (heldNames) events.put(raw, registered);
                            continue;
                        }
                        if (namesRoot) {
                            namedCandidates.computeIfAbsent(raw,
                                    ignored -> new LinkedHashSet<>()).add(
                                    SymbolicSourceEvidence.identity(event));
                            // One propagated root reaching several declared
                            // reads is what propagation IS: the occurrence,
                            // the phase and the producing summary all differ
                            // by construction, and the first read registered
                            // names it for everyone.  Only a different SOURCE
                            // behind one symbol is corruption.
                            if (!optionalString(held, "sourceId").equals(
                                    optionalString(event, "sourceId"))
                                    || !optionalString(held, "fieldSignature").equals(
                                    optionalString(event, "fieldSignature"))
                                    || !optionalString(held, "javaType").equals(
                                    optionalString(event, "javaType"))) {
                                throw new IllegalArgumentException(
                                        "one VM symbol names two configured"
                                                + " sources: " + raw);
                            }
                            continue;
                        }
                        if (!optionalString(held, "sourceId").equals(
                                optionalString(event, "sourceId"))
                                || !optionalString(held, "sourceKey").equals(
                                sourceKey)
                                || !optionalString(held, "sourcePhaseId").equals(
                                optionalString(event, "sourcePhaseId"))
                                || !optionalString(held, "fieldSignature").equals(
                                optionalString(event, "fieldSignature"))
                                || !optionalString(held, "javaType").equals(
                                optionalString(event, "javaType"))) {
                            throw new IllegalArgumentException(
                                    "one VM symbol has inconsistent configured"
                                            + " source metadata: " + raw);
                        }
                    }
                }
                Map<String, String> mintRawByIdentity =
                        new LinkedHashMap<>();
                Map<String, JsonObject> mintEventByIdentity =
                        new LinkedHashMap<>();
                for (Map.Entry<String, String> mint
                        : symbolicSourceIdentities.entrySet()) {
                    String heldRaw = mintRawByIdentity.putIfAbsent(
                            mint.getValue(), mint.getKey());
                    JsonObject event = events.get(mint.getKey());
                    if (heldRaw != null && !heldRaw.equals(mint.getKey())) {
                        throw new IllegalArgumentException(
                                "one configured source mint identity names"
                                        + " two VM roots: " + mint.getValue());
                    }
                    if (event != null) {
                        mintEventByIdentity.putIfAbsent(mint.getValue(),
                                event);
                    }
                }
                Map<String, String> canonicalRawByIdentity =
                        new LinkedHashMap<>(mintRawByIdentity);
                Map<String, String> canonicalIdentityByIdentity =
                        new LinkedHashMap<>();
                Map<String, String> canonicalRawByObservedRaw =
                        new LinkedHashMap<>();
                Map<String, String> canonicalIdentityByObservedRaw =
                        new LinkedHashMap<>();
                Map<String, Set<String>> rawAliases = new LinkedHashMap<>();
                Map<String, List<String>> rawByRecordedEvent =
                        new LinkedHashMap<>();
                for (Map.Entry<String, String> mint
                        : mintRawByIdentity.entrySet()) {
                    String identity = mint.getKey();
                    canonicalIdentityByIdentity.put(identity, identity);
                }
                // A broad region can mint a root at event A and only observe
                // it again at event B, while a nested projection mints its own
                // VM spelling at that same B.  Use every observation, including
                // REUSED rows, to connect those spellings.
                for (JsonObject event : observedEvents) {
                    String phaseId = optionalString(event, "sourcePhaseId");
                    RecordedConfiguredSource recorded =
                            configuredSourceRecordedByPhase.get(
                                    phaseId);
                    if (recorded == null) {
                        unsupported.add(
                                "ConfiguredSourcePlanPhaseMissing:"
                                        + firstNonBlank(phaseId,
                                        "MISSING") + ":"
                                        + optionalString(event, "rawSymbol"));
                        continue;
                    }
                    if (!recorded.matches(event)) {
                        throw new IllegalArgumentException(
                                "configured source evidence disagrees with"
                                        + " recorded event: "
                                        + optionalString(event, "sourcePhaseId"));
                    }
                    String raw = optionalString(event, "rawSymbol");
                    rawAliases.computeIfAbsent(raw,
                            ignored -> new LinkedHashSet<>());
                    rawByRecordedEvent.computeIfAbsent(recorded.identity(),
                            ignored -> new ArrayList<>()).add(raw);
                }
                for (List<String> aliases : rawByRecordedEvent.values()) {
                    if (aliases.isEmpty()) continue;
                    String first = aliases.get(0);
                    for (String alias : aliases) {
                        rawAliases.computeIfAbsent(first,
                                ignored -> new LinkedHashSet<>()).add(alias);
                        rawAliases.computeIfAbsent(alias,
                                ignored -> new LinkedHashSet<>()).add(first);
                    }
                }
                Set<String> visitedRaw = new LinkedHashSet<>();
                List<String> roots = new ArrayList<>(
                        symbolicSourceIdentities.keySet());
                Collections.sort(roots);
                for (String root : roots) {
                    if (!visitedRaw.add(root)) continue;
                    Set<String> component = new LinkedHashSet<>();
                    Deque<String> pending = new ArrayDeque<>();
                    pending.add(root);
                    while (!pending.isEmpty()) {
                        String raw = pending.removeFirst();
                        component.add(raw);
                        for (String alias : rawAliases.getOrDefault(raw,
                                Collections.emptySet())) {
                            if (visitedRaw.add(alias)) pending.addLast(alias);
                        }
                    }
                    List<String> minted = new ArrayList<>();
                    for (String raw : component) {
                        if (symbolicSourceIdentities.containsKey(raw)) {
                            minted.add(raw);
                        }
                    }
                    if (minted.isEmpty()) continue;
                    Collections.sort(minted);
                    String canonicalRaw = minted.get(0);
                    String canonicalIdentity =
                            symbolicSourceIdentities.get(canonicalRaw);
                    String canonicalJavaType = optionalString(
                            mintEventByIdentity.get(canonicalIdentity),
                            "javaType");
                    for (String raw : minted) {
                        String identity = symbolicSourceIdentities.get(raw);
                        JsonObject event = mintEventByIdentity.get(identity);
                        if (!canonicalJavaType.equals(optionalString(event,
                                "javaType"))) {
                            throw new IllegalArgumentException(
                                    "one recorded configured source event has"
                                            + " incompatible Java types");
                        }
                        canonicalRawByIdentity.put(identity, canonicalRaw);
                        canonicalIdentityByIdentity.put(identity,
                                canonicalIdentity);
                    }
                    for (String raw : component) {
                        canonicalRawByObservedRaw.put(raw, canonicalRaw);
                        canonicalIdentityByObservedRaw.put(raw,
                                canonicalIdentity);
                    }
                }
                Map<String, String> named = new LinkedHashMap<>();
                for (Map.Entry<String, Set<String>> candidate
                        : namedCandidates.entrySet()) {
                    List<String> importedMints = new ArrayList<>();
                    for (String identity : candidate.getValue()) {
                        if (mintRawByIdentity.containsKey(identity)) {
                            importedMints.add(identity);
                        }
                    }
                    if (importedMints.size() > 1
                            || importedMints.isEmpty()
                            && candidate.getValue().size() > 1) {
                        throw new IllegalArgumentException(
                                "one named VM root has no unique configured"
                                        + " source mint: " + candidate.getKey());
                    }
                    named.put(candidate.getKey(), importedMints.isEmpty()
                            ? candidate.getValue().iterator().next()
                            : importedMints.get(0));
                }
                symbolicSourceEvents = Collections.unmodifiableMap(events);
                manualSourceEvents = Collections.unmodifiableMap(
                        manualEvents);
                namedSourceIdentities = Collections.unmodifiableMap(named);
                configuredSourceRawByIdentity = Collections.unmodifiableMap(
                        canonicalRawByIdentity);
                configuredSourceEventByIdentity = Collections.unmodifiableMap(
                        mintEventByIdentity);
                configuredSourceCanonicalIdentityByIdentity =
                        Collections.unmodifiableMap(
                                canonicalIdentityByIdentity);
                configuredSourceCanonicalRawByObservedRaw =
                        Collections.unmodifiableMap(canonicalRawByObservedRaw);
                configuredSourceCanonicalIdentityByObservedRaw =
                        Collections.unmodifiableMap(
                                canonicalIdentityByObservedRaw);
                reusedManualSourceEvents =
                        exactReusedManualRootAuthorities(owners,
                                executionScopesByCase);
            } catch (IllegalArgumentException malformed) {
                symbolicSourceIdentities = Collections.emptyMap();
                manualSourceIdentities = Collections.emptyMap();
                symbolicSourceEvents = Collections.emptyMap();
                manualSourceEvents = Collections.emptyMap();
                namedSourceIdentities = Collections.emptyMap();
                configuredSourceRawByIdentity = Collections.emptyMap();
                configuredSourceEventByIdentity = Collections.emptyMap();
                configuredSourceCanonicalIdentityByIdentity =
                        Collections.emptyMap();
                configuredSourceCanonicalRawByObservedRaw =
                        Collections.emptyMap();
                configuredSourceCanonicalIdentityByObservedRaw =
                        Collections.emptyMap();
                reusedManualSourceEvents = Collections.emptyMap();
                unsupported.add("SymbolicSourceEvidenceMalformed:"
                        + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            }
        }

        private void bindFatalPathAssertion(String pathTerm) {
            fatalPathTerm = pathTerm;
            assertNamed("fatal_path", pathTerm);
        }

        /** Notes that {@code name}'s value is read back from {@code text}. */
        private void noteValueDependency(String name, String text) {
            if (name == null || name.isEmpty() || text == null
                    || text.isEmpty()) {
                return;
            }
            valueDependencyText.computeIfAbsent(name,
                    ignored -> new StringBuilder()).append(' ').append(text);
        }

        /**
         * Files one case-local source attestation after checking it against
         */
        private void recordTargetReach(int pathOrdinal, JsonObject path,
                                       String caseGuard, JsonObject fatal) {
            JsonElement encoded = path.get(
                    PathObservation.TargetReachEvent.FIELD);
            if (encoded == null) {
                unsupported.add("SelectedTargetReachEventMissing:path:"
                        + pathOrdinal);
                return;
            }
            final PathObservation.TargetReachEvent event;
            try {
                event = PathObservation.TargetReachEvent.decode(encoded);
            } catch (IllegalArgumentException malformed) {
                unsupported.add("SelectedTargetReachEventMalformed:path:"
                        + pathOrdinal + ":" + firstNonBlank(
                        malformed.getMessage(), "UNKNOWN"));
                return;
            }
            JsonElement required = fatal.get("requiredTakenOutcome");
            boolean exactRequired = required != null
                    && required.isJsonPrimitive()
                    && required.getAsJsonPrimitive().isBoolean();
            JsonElement desired = path.get("desiredTakenOutcome");
            boolean exactDesired = desired != null
                    && desired.isJsonPrimitive()
                    && desired.getAsJsonPrimitive().isBoolean();
            JsonElement encodedConcrete = path.get(
                    TargetReachPathQueryBuilder
                            .TARGET_CONCRETE_OBSERVATION);
            if (encodedConcrete != null) {
                recordConcreteTargetReach(pathOrdinal, path, caseGuard,
                        fatal, event, required, exactRequired, desired,
                        exactDesired, encodedConcrete);
                return;
            }
            final BranchReplayContract replay;
            try {
                replay = BranchReplayContract.fromJson(
                        object(fatal, "seedReplayContract"));
            } catch (IllegalArgumentException malformed) {
                unsupported.add("SelectedTargetSourceAttestationMalformed:"
                        + "path:" + pathOrdinal + ":" + firstNonBlank(
                        malformed.getMessage(), "UNKNOWN"));
                return;
            }
            BranchWitness source = replay.source();
            int occurrence = JsonFields.exactInteger(fatal,
                    "targetOccurrence", -1);
            String attestationRole = optionalString(path,
                    TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE);
            boolean sourceAttestation = TargetReachPathQueryBuilder
                    .SOURCE_TARGET_REACH_EVENT.equals(attestationRole);
            boolean requiredAttestation = TargetReachPathQueryBuilder
                    .REQUIRED_TARGET_REACH_EVENT.equals(attestationRole);
            JsonArray constraints = array(path, "constraints");
            JsonElement selectedPredicate = constraints.size() == 0
                    ? null : constraints.get(constraints.size() - 1);
            final BranchWitness pathWitness;
            JsonElement encodedPathWitness = path.get(
                    TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS);
            if (encodedPathWitness == null
                    || !encodedPathWitness.isJsonObject()) {
                unsupported.add("SelectedTargetPathWitnessMissing:path:"
                        + pathOrdinal);
                return;
            }
            try {
                pathWitness = BranchWitness.fromJson(
                        encodedPathWitness.getAsJsonObject());
            } catch (IllegalArgumentException malformed) {
                unsupported.add("SelectedTargetPathWitnessMalformed:path:"
                        + pathOrdinal + ":" + firstNonBlank(
                        malformed.getMessage(), "UNKNOWN"));
                return;
            }
            if (!pathWitness.decisionIdentity().equals(
                    source.decisionIdentity())
                    || pathWitness.sourceTakenOutcome()
                    != event.outcome()) {
                unsupported.add("SelectedTargetPathWitnessMismatch:path:"
                        + pathOrdinal);
                return;
            }
            JsonElement expectedPredicate;
            if (sourceAttestation) {
                // Compared against the selected predicate and then dropped.
                // A copy here restated the propagated DAG as a tree once per
                // target path, which is what exhausted the composer's heap.
                expectedPredicate = BranchPredicateAlgebra.complementView(
                        pathWitness.sourceSatisfiedPredicate());
            } else {
                expectedPredicate = pathWitness.sourceSatisfiedPredicate();
            }
            if (selectedPredicate == null
                    || !BranchPredicateAlgebra.equivalent(
                    selectedPredicate,
                    expectedPredicate)) {
                unsupported.add("SelectedTargetPredicateMismatch:path:"
                        + pathOrdinal);
                return;
            }
            boolean matchingEvent = sourceAttestation
                    && event.matches(source.siteId(), source.occurrence(),
                    source.sourceTakenOutcome())
                    || requiredAttestation
                    && exactRequired
                    && event.matches(optionalString(fatal, "targetSiteId"),
                    occurrence, required.getAsBoolean());
            boolean matchingPolarity = exactRequired
                    && (sourceAttestation
                    && required.getAsBoolean()
                    == replay.requiredTakenOutcome()
                    || requiredAttestation);
            if (!exactRequired || !exactDesired
                    || desired.getAsBoolean() != required.getAsBoolean()
                    || !matchingPolarity
                    || !optionalString(fatal, "targetSiteId").equals(
                    source.siteId())
                    || occurrence != source.occurrence()
                    || !matchingEvent) {
                unsupported.add("SelectedTargetReachEventMismatch:path:"
                        + pathOrdinal + ":" + event.siteId() + "#"
                        + event.occurrence() + "=" + event.outcome());
                return;
            }
            JsonObject row = event.toJson();
            row.addProperty("attestationRole", attestationRole);
            row.addProperty("sourceObservedOutcome", event.outcome());
            row.addProperty("desiredTakenOutcome",
                    required.getAsBoolean());
            row.addProperty("pathOrdinal", pathOrdinal);
            row.addProperty("caseGuard", caseGuard);
            targetReachEvents.add(row);
            targetReachCaseTerms.add(caseGuard);
        }

        /** Records a required branch that the VM attested had no predicate. */
        private void recordConcreteTargetReach(
                int pathOrdinal, JsonObject path, String caseGuard,
                JsonObject fatal, PathObservation.TargetReachEvent event,
                JsonElement required, boolean exactRequired,
                JsonElement desired, boolean exactDesired,
                JsonElement encodedPathObservation) {
            JsonElement encodedSeedObservation = fatal.get(
                    TargetReachPathQueryBuilder
                            .TARGET_CONCRETE_OBSERVATION);
            if (!encodedPathObservation.isJsonObject()
                    || encodedSeedObservation == null
                    || !encodedSeedObservation.isJsonObject()) {
                unsupported.add("SelectedConcreteTargetObservationMissing:"
                        + "path:" + pathOrdinal);
                return;
            }
            final ExactConcreteBranchObservation pathObservation;
            final ExactConcreteBranchObservation seedObservation;
            try {
                pathObservation = ExactConcreteBranchObservation.fromJson(
                        encodedPathObservation.getAsJsonObject());
                seedObservation = ExactConcreteBranchObservation.fromJson(
                        encodedSeedObservation.getAsJsonObject());
            } catch (IllegalArgumentException malformed) {
                unsupported.add("SelectedConcreteTargetObservationMalformed:"
                        + "path:" + pathOrdinal + ":" + firstNonBlank(
                        malformed.getMessage(), "UNKNOWN"));
                return;
            }
            int occurrence = JsonFields.exactInteger(fatal,
                    "targetOccurrence", -1);
            String targetSite = optionalString(fatal, "targetSiteId");
            String attestationRole = optionalString(path,
                    TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE);
            boolean sameAuthority = pathObservation.siteId().equals(
                    seedObservation.siteId())
                    && pathObservation.occurrence()
                    == seedObservation.occurrence()
                    && pathObservation.sourceTakenOutcome()
                    == seedObservation.sourceTakenOutcome();
            boolean exactOutcome = exactRequired && exactDesired
                    && desired.getAsBoolean() == required.getAsBoolean()
                    && required.getAsBoolean()
                    == pathObservation.sourceTakenOutcome();
            boolean matchingEvent = event.matches(pathObservation.siteId(),
                    pathObservation.occurrence(),
                    pathObservation.sourceTakenOutcome());
            if (!sameAuthority || !exactOutcome || !matchingEvent
                    || !targetSite.equals(pathObservation.siteId())
                    || occurrence != pathObservation.occurrence()
                    || !TargetReachPathQueryBuilder
                    .REQUIRED_TARGET_REACH_EVENT.equals(attestationRole)
                    || !TargetReachPathQueryBuilder
                    .REQUIRED_CONCRETE_BRANCH_AUTHORITY.equals(optionalString(path,
                    "fatalBranchConditionAuthority"))) {
                unsupported.add("SelectedConcreteTargetReachEventMismatch:"
                        + "path:" + pathOrdinal + ":" + event.siteId() + "#"
                        + event.occurrence() + "=" + event.outcome());
                return;
            }
            JsonObject row = event.toJson();
            row.addProperty("attestationRole", attestationRole);
            row.addProperty("sourceObservedOutcome", event.outcome());
            row.addProperty("desiredTakenOutcome",
                    required.getAsBoolean());
            row.addProperty("pathOrdinal", pathOrdinal);
            row.addProperty("caseGuard", caseGuard);
            targetReachEvents.add(row);
            targetReachCaseTerms.add(caseGuard);
        }

        private void bindTargetReachAssertion() {
            if (targetReachCaseTerms.isEmpty()) {
                unsupported.add("SelectedTargetReachEventMissing:selected");
            }
            assertNamed("target_reach_event", or(targetReachCaseTerms));
        }

        private JsonArray targetReachLedger() {
            return targetReachEvents.deepCopy();
        }

        private JsonArray configuredSourceMaterializationLedger() {
            List<Map.Entry<String, JsonObject>> rows = new ArrayList<>(
                    configuredSourceMaterializations.entrySet());
            rows.sort(Map.Entry.comparingByKey());
            JsonArray result = new JsonArray();
            for (Map.Entry<String, JsonObject> row : rows) {
                result.add(row.getValue().deepCopy());
            }
            return result;
        }

        private JsonArray manualSourceMaterializationLedger() {
            List<Map.Entry<String, JsonObject>> rows = new ArrayList<>(
                    manualSourceMaterializations.entrySet());
            rows.sort(Map.Entry.comparingByKey());
            JsonArray result = new JsonArray();
            for (Map.Entry<String, JsonObject> row : rows) {
                result.add(row.getValue().deepCopy());
            }
            return result;
        }

        private String bindTargetPathCase(JsonObject fatal, JsonObject path,
                                          int pathOrdinal, String pathTerm) {
            String owner = targetPathCaseOwner(fatal, path, pathOrdinal);
            String selector = LocalCaseIdentity.selector(owner);
            declare(selector, Sort.BOOL);
            // Several distributed replays can produce the same target-local
            assertNamed("target_path_selector_definition_" + pathOrdinal,
                    "(=> " + selector + " " + pathTerm + ")");
            return selector;
        }

        /** One concrete target replay follows exactly one recorded path. */
        private void bindTargetPathPartition(List<String> selectors) {
            if (selectors == null || selectors.isEmpty()) return;
            StringBuilder exactlyOne = new StringBuilder("(= (+");
            for (String selector : selectors) {
                exactlyOne.append(" (ite ").append(selector)
                        .append(" 1 0)");
            }
            assertNamed("target_path_selector_partition",
                    exactlyOne.append(") 1)").toString());
        }

        private String constraint(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                return unknownConstraint(origin, expression);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("MethodExpression".equals(type)) {
                return methodConstraint(object);
            }
            Term term = term(expression, null);
            if (term.sort == Sort.BOOL) return condition(term);
            return unknownConstraint(origin + ": non-boolean " + type,
                    expression);
        }

        /** A term may denote a Java expression that is defined only under a
         * reference guard (for example {@code s.length()} requires
         * cases. */
        private String condition(Term term) {
            return and(Arrays.asList(term.precondition, term.text));
        }

        @Override
        public Term dependent(Term result, Term... inputs) {
            List<String> values = new ArrayList<>();
            values.add(result.precondition);
            if (inputs != null) {
                for (Term input : inputs) {
                    if (input != null) values.add(input.precondition);
                }
            }
            return result.withPrecondition(and(values));
        }

        /**
         * Lowers one recorded expression.
         */
        private Term term(JsonElement expression, Sort expected) {
            return shareLargeTerm(dispatch(expression, expected, ""));
        }

        @Override
        Term symbolTerm(JsonObject expression, Sort expected,
                        String origin) {
            return symbol(expression, expected);
        }

        /**
         * The custom VM restarts placeholder ordinals for every replay
         * task, so #1 identifies an event only inside one replay scope.
         */
        @Override
        Term placeholderTerm(JsonObject expression, String origin) {
            String function = optionalString(expression,
                    "_place_holder_func");
            int count = optionalInteger(expression, "_count", -1);
            if (!"currentTimeMills".equals(function) || count < 1) {
                unsupported.add("PlaceholderExpression:"
                        + firstNonBlank(function, "unknown") + "#" + count);
                return unsupportedTerm(Sort.INT);
            }
            String identity = function + "#" + count;
            String name = smtSymbols.mint(
                    scopedName("environment", identity) + "__",
                    currentSymbolScope + "\u0000" + identity, 10);
            declare(name, Sort.INT);
            assertJavaIntegralDomain(name, Sort.INT, "J", identity);
            return Term.of(name, Sort.INT, IntegralWidth.JAVA_LONG);
        }

        @Override
        Term guardedReadTerm(JsonObject expression, Sort expected,
                             String origin) {
            return lowerGuardedReadTerm(expression, expected);
        }

        @Override
        Term caseMergeTerm(JsonObject expression, Sort expected,
                           String origin) {
            return lowerCaseMergeTerm(expression, expected);
        }

        @Override
        Term containerTerm(JsonObject expression, boolean field,
                           String origin) {
            return lowerContainerTerm(expression, field);
        }

        @Override
        Term splitElementTerm(JsonObject expression, String origin) {
            return lowerSplitElementTerm(expression);
        }

        /** A refused call still carries the sort of the value it returned. */
        @Override
        Sort methodResultSort(JsonObject expression, String origin) {
            return term(expression.get("_res_exp"), null).sort;
        }

        /**
         * Names a large value, nullness condition, or Java definedness
         * condition exactly once.  A definition is a pure abbreviation, so
         * this changes neither selector ownership nor solver freedom.
         */
        private Term shareLargeTerm(Term value) {
            if (value == null) return null;
            String text = shareLargeExpression(value.text, value.sort);
            String nullness = value.sort == Sort.STRING
                    ? shareLargeExpression(value.stringNullness, Sort.BOOL)
                    : value.stringNullness;
            String precondition = shareLargeExpression(
                    value.precondition, Sort.BOOL);
            if (text.equals(value.text)
                    && nullness.equals(value.stringNullness)
                    && precondition.equals(value.precondition)) {
                return value;
            }
            return Term.of(text, value.sort, value.integralWidth, nullness,
                    value.stringReferenceOrigin, precondition);
        }

        private String shareLargeExpression(String expression, Sort sort) {
            if (expression == null
                    || expression.length() < SHARED_TERM_THRESHOLD) {
                return expression;
            }
            String digest = CanonicalJson.sha256(sort.name() + "\u0000"
                    + expression);
            String name = "expression_dag__" + digest;
            Term held = definitions.get(name);
            if (held == null) {
                defineConstant(name, sort, expression);
            } else if (held.sort != sort || !held.text.equals(expression)) {
                throw new IllegalStateException(
                        "content-addressed SMT definition collision: "
                                + name);
            }
            return name;
        }

        private Term lowerGuardedReadTerm(JsonObject node, Sort expected) {
            JsonObject selectedViewState = ContainerSmtCodec
                    .selectedReadViewState(node);
            if (selectedViewState != null) {
                node = selectedViewState;
                expected = Sort.MAP;
            }
            String fault = SharedStateEvidence.guardedReadFault(node);
            String readIdentity = optionalString(node,
                    SymbolicPropagationClosure.READ_CHOICE_IDENTITY);
            String readOwner = optionalString(node,
                    SymbolicPropagationClosure.READ_CHOICE_OWNER);
            String readCaseSelector = LocalCaseIdentity.selector(readOwner);
            if (!fault.isEmpty() || readIdentity.isEmpty()
                    || readOwner.isEmpty()) {
                refuseGuardedRead("UnadmittedGuardedRead:"
                                + firstNonBlank(readIdentity,
                                vmReadAddress(node)),
                        fault.isEmpty()
                                ? "guarded read has no stable "
                                + (readIdentity.isEmpty()
                                ? "read identity" : "reader case")
                                + " (" + vmReadAddress(node) + ")"
                                : fault);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }

            String activation = currentGuard.isEmpty()
                    ? readCaseSelector : currentGuard;
            String javaType = guardedReadJavaType(node);
            Sort want = guardedReadSort(node, expected,
                    Collections.emptyList());
            if (readFromContext.contains(readIdentity)) {
                refuseGuardedRead("RecursiveGuardedRead:" + readIdentity,
                        "one guarded read recursively contains itself");
                return unsupportedTerm(want == null ? Sort.VALUE : want);
            }

            List<DirectReadArm> arms = new ArrayList<>();
            readFromContext.push(readIdentity);
            try {
                for (JsonElement encoded : array(node, "candidates")) {
                    if (!encoded.isJsonObject()) continue;
                    DirectReadArm arm = lowerDirectReadArm(readIdentity,
                            encoded.getAsJsonObject(), want);
                    if (arm != null) arms.add(arm);
                }
            } finally {
                readFromContext.pop();
            }
            if (arms.size() != array(node, "candidates").size()
                    || arms.isEmpty()) {
                refuseGuardedRead("GuardedReadArmMissing:" + readIdentity,
                        "not every VM candidate has a stable writer case and"
                                + " value expression");
                return unsupportedTerm(want == null ? Sort.VALUE : want);
            }

            List<Sort> armSorts = new ArrayList<>(arms.size());
            for (DirectReadArm arm : arms) armSorts.add(arm.term.sort);
            Sort sort = guardedReadSort(node, expected, armSorts);
            if (sort == null) {
                Sort conflicting = armSorts.stream()
                        .filter(candidate -> candidate != want)
                        .findFirst().orElse(armSorts.get(0));
                refuseGuardedRead("GuardedReadArmSortConflict:"
                                + readIdentity,
                        "one guarded read mixes " + want + " and "
                                + conflicting);
                return unsupportedTerm(want == null ? Sort.VALUE : want);
            }
            String projectionIdentity = projectionTermIdentity(
                    "READ", readIdentity, sort.name(),
                    GuardedReadNaming.projectionIdentity(node));

            Term result = guardedReadTerms.get(projectionIdentity);
            if (result == null) {
                String value = smtSymbols.mint(READ_VALUE_PREFIX
                        + smtName(readIdentity) + "__",
                        projectionIdentity, 16);
                declare(value, sort);
                String previousGuard = enterGuard("");
                try {
                    assertJavaIntegralDomain(value, sort, javaType,
                            "guarded read " + readIdentity);
                } finally {
                    restoreGuard(previousGuard);
                }
                result = Term.of(value, sort,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
                guardedReadTerms.put(projectionIdentity, result);
            }

            recordGuardedReadFieldFamily(node, result);
            guardedReadActivations.computeIfAbsent(readIdentity,
                    ignored -> new LinkedHashSet<>()).add(activation);
            Set<String> selectors = guardedReadSelectors.computeIfAbsent(
                    readIdentity, ignored -> new LinkedHashSet<>());
            Map<String, Set<String>> selectorGuards =
                    guardedSelectorActivations.computeIfAbsent(readIdentity,
                            ignored -> new LinkedHashMap<>());
            Set<String> useSelectors = new LinkedHashSet<>();
            Map<String, List<String>> armWriterCases =
                    guardedReadArmWriterCases.computeIfAbsent(readIdentity,
                            ignored -> new LinkedHashMap<>());
            if (!currentCaseSelector.isEmpty()) {
                guardedReadOwnerCases.computeIfAbsent(readIdentity,
                        ignored -> new LinkedHashSet<>())
                        .add(currentCaseSelector);
            }
            String readLocation = SharedStateEvidence.locationKey(node);
            SharedStateEvidence.LocationProvenance readProvenance =
                    locationProvenance.get(readLocation);
            String canonicalLocation = readProvenance == null
                    ? readLocation : readProvenance.locationKey;
            String readField = readProvenance == null
                    || readProvenance.declaredField.isEmpty()
                    ? canonicalLocation : readProvenance.declaredField;
            guardedReadLocations.putIfAbsent(readIdentity, canonicalLocation);
            guardedReadFields.putIfAbsent(readIdentity, readField);
            for (DirectReadArm arm : arms) {
                selectors.add(arm.selector);
                useSelectors.add(arm.selector);
                armWriterCases.put(arm.selector,
                        new ArrayList<>(arm.writerCaseClosure));
                noteReadArmProvenance(readIdentity, readField,
                        canonicalLocation, arm);
                selectorGuards.computeIfAbsent(arm.selector,
                        ignored -> new LinkedHashSet<>()).add(activation);
                emitDirectReadArm(node, readIdentity, projectionIdentity,
                        result.text, activation, arm);
            }
            recordGuardedReadOrder(node, readIdentity, arms);
            requireDistinguishedContainerArms(node, readIdentity, arms);
            recordGuardedReadUse(readIdentity, projectionIdentity, activation,
                    useSelectors);
            return result;
        }

        /**
         * Records what one read arm says about its execution: the group it
         * was recorded in and its literal value, for the divergence gate;
         * its writer activation and case, for the unlinked-writer gate; and
         * for an INITIAL arm of an instance field, the activation whose
         * entry took the snapshot, for the fault-idle closure.
         */
        private void noteReadArmProvenance(String readIdentity,
                                           String readField,
                                           String canonicalLocation,
                                           DirectReadArm arm) {
            JsonObject candidate = arm.candidate;
            String owner = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER);
            boolean initial = owner.startsWith(
                    SymbolicPropagationClosure.INITIAL_SOURCE_CASE_PREFIX);
            String version = initial
                    ? SymbolicPropagationClosure.INITIAL_SOURCE_CASE_PREFIX
                    : owner;
            noteExecutionRecording("READ\n" + readIdentity + "\n" + version,
                    readField + " read " + readIdentity + (initial
                            ? " INITIAL" : " writer " + caseTail(owner)),
                    armExecutionScope(candidate, owner), arm.selector,
                    arm.term);
            if (initial) {
                Set<InvocationKey> hosts = initialSnapshotHosts.get(owner);
                if (hosts != null && !hosts.isEmpty()
                        && "INSTANCE_FIELD".equals(SharedStateEvidence
                        .locationKindOf(canonicalLocation))) {
                    guardedReadInitialHosts.putIfAbsent(arm.selector,
                            new LinkedHashSet<>(hosts));
                }
                return;
            }
            String region = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_REGION_ID);
            String occurrence = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OCCURRENCE_ID);
            String selector = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
            if (region.isEmpty() || occurrence.isEmpty()
                    || selector.isEmpty()) {
                return;
            }
            guardedReadWriterInvocations.computeIfAbsent(readIdentity,
                    ignored -> new LinkedHashSet<>()).add(
                    new InvocationKey(region, occurrence));
            guardedReadWriterSelectors.computeIfAbsent(readIdentity,
                    ignored -> new LinkedHashSet<>()).add(selector);
            guardedReadWriterArms.computeIfAbsent(readIdentity,
                    ignored -> new ArrayList<>()).add(new ConsumerArm(
                    arm.selector, arm.term == null ? "" : arm.term.text,
                    occurrenceSourceKey(occurrence), occurrence));
        }

        /**
         * Refuses a container read whose arms say nothing about the container.
         *
         * <p>A read over a selected container's whole state lowers each arm
         * through that version's own mutation chain, so two arms agree on a
         * value only where the mutations between them cannot change it.  Two
         * shapes mean the chain was lost rather than lowered: every arm
         * reducing to one value expression, which makes the read-from choice
         * vacuous, and a writer arm reducing to the same expression as an
         * INITIAL arm, which claims a write ran and then reads the untouched
         * state.  Either way the only thing left constraining the container is
         * its size domain, and a fail-closed refusal is the honest answer.</p>
         */
        private void requireDistinguishedContainerArms(
                JsonObject node, String readIdentity,
                List<DirectReadArm> arms) {
            String location = SharedStateEvidence.locationKey(node);
            String kind = SharedStateEvidence.locationKindOf(location);
            boolean container = SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    .equals(kind) || "ARRAY_ELEMENT".equals(kind);
            if (!container) return;
            List<String> values = new ArrayList<>(arms.size());
            List<Boolean> initial = new ArrayList<>(arms.size());
            for (DirectReadArm arm : arms) {
                values.add(arm.term.text);
                initial.add(optionalString(arm.candidate,
                        SymbolicPropagationClosure.WRITER_CASE_OWNER)
                        .startsWith(SymbolicPropagationClosure
                                .INITIAL_SOURCE_CASE_PREFIX));
            }
            int collapsed = collapsedContainerArm(values, initial);
            if (collapsed >= 0) {
                refuseGuardedRead("UnconstrainedContainerRead:"
                                + readIdentity + ":"
                                + arms.get(collapsed).candidateIdentity,
                        initial.get(collapsed)
                                ? "every candidate arm of one container read"
                                + " lowers to the same value expression"
                                : "a container writer arm lowers to the same"
                                + " value expression as the untouched"
                                + " initial state");
            }
        }

        /**
         * Records the program order of one read's candidate writers.
         *
         * The order is the VM's own: every candidate carries the
         * session-monotonic {@code fieldVersionId} of the version it names, and
         * a read's candidate list is the location's retained version list taken
         * at the read, so each id is below the read's own event id.  Ids minted
         * in different symbolic sessions do not compare, so one lowering
         * contributes one chain and the chains are merged only where they
         * agree; see {@link #mergeGuardedReadOrder}.
         */
        private void recordGuardedReadOrder(JsonObject node,
                                            String readIdentity,
                                            List<DirectReadArm> arms) {
            if (guardedReadOrderGaps.containsKey(readIdentity)) return;
            long readEvent = optionalLongInteger(node, "readEventId", -1L);
            Set<Long> seen = new LinkedHashSet<>();
            for (DirectReadArm arm : arms) {
                long version = optionalLongInteger(arm.candidate,
                        "fieldVersionId", -1L);
                if (version <= 0L || readEvent <= 0L || version >= readEvent
                        || !seen.add(version)) {
                    orderUnknown(readIdentity,
                            "candidate writers carry no distinct field version"
                                    + " below this read's event id");
                    return;
                }
            }
            List<DirectReadArm> ordered = new ArrayList<>(arms);
            ordered.sort(Comparator.comparingLong(arm -> optionalLongInteger(
                    arm.candidate, "fieldVersionId", -1L)));
            List<String> chain = new ArrayList<>(ordered.size());
            for (DirectReadArm arm : ordered) chain.add(arm.selector);
            guardedReadChains.computeIfAbsent(readIdentity,
                    ignored -> new ArrayList<>()).add(chain);
        }

        /**
         * Merges one read's per-lowering chains into a single program order.
         *
         * Two sessions may each see only part of the location's history -- one
         * lowering's chain can be shorter than another's -- so the chains are
         * merged rather than compared.  Each chain contributes the precedences
         * it witnessed; the merge succeeds only when no two chains disagree
         * about a pair and when every pair of arms is ordered by some chain,
         * because an unordered pair is exactly the case where last-writer-wins
         * cannot say which of the two overwrites the other.
         */
        private List<String> mergeGuardedReadOrder(String scope, String read,
                                                   List<String> lowered) {
            List<List<String>> recorded = guardedReadChains.getOrDefault(read,
                    Collections.emptyList());
            if (recorded.isEmpty()) return null;
            List<List<String>> chains = scopedChains(recorded, lowered);
            if (chains.isEmpty()) return null;
            Set<String> before = new LinkedHashSet<>();
            Set<String> nodes = new LinkedHashSet<>();
            for (List<String> chain : chains) {
                nodes.addAll(chain);
                for (int index = 0; index < chain.size(); index++) {
                    for (int later = index + 1; later < chain.size();
                         later++) {
                        before.add(chain.get(index) + "\n"
                                + chain.get(later));
                    }
                }
            }
            if (!nodes.equals(new LinkedHashSet<>(lowered))) {
                orderUnknown(scope, "the merged chains do not cover every"
                        + " lowered candidate arm");
                return null;
            }
            List<String> order = new ArrayList<>(nodes);
            Collections.sort(order);
            for (int left = 0; left < order.size(); left++) {
                for (int right = left + 1; right < order.size(); right++) {
                    boolean forward = before.contains(order.get(left) + "\n"
                            + order.get(right));
                    boolean backward = before.contains(order.get(right) + "\n"
                            + order.get(left));
                    if (forward == backward) {
                        orderUnknown(scope, forward
                                ? "two lowerings order one pair of candidate"
                                + " writers in opposite directions"
                                : "two candidate writers are ordered by no"
                                + " single session");
                        return null;
                    }
                }
            }
            order.sort((left, right) -> before.contains(left + "\n" + right)
                    ? -1 : 1);
            return order;
        }

        /** {@code scope} is one read's use, or the read while lowering. */
        private void orderUnknown(String scope, String detail) {
            guardedReadOrders.remove(scope);
            guardedReadOrderGaps.putIfAbsent(scope, detail);
        }

        private void recordGuardedReadUse(String readIdentity,
                                          String projectionIdentity,
                                          String activation,
                                          Set<String> selectors) {
            VmTermLowering.recordGuardedReadUse(guardedReadUses,
                    readIdentity, projectionIdentity, activation, selectors,
                    identity -> refuseGuardedRead(
                            "GuardedReadUseAmbiguous:" + identity,
                            "one stable read use has two candidate sets"));
        }

        private DirectReadArm lowerDirectReadArm(String readIdentity,
                                                  JsonObject candidate,
                                                  Sort expected) {
            String candidateIdentity = optionalString(candidate,
                    SymbolicPropagationClosure.READ_CANDIDATE_IDENTITY);
            String selector = optionalString(candidate, "selector");
            String owner = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER);
            String writerCaseSelector = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
            String expectedSelector = GuardedReadNaming.selector(
                    readIdentity, candidateIdentity);
            if (candidateIdentity.isEmpty() || owner.isEmpty()
                    || !writerCaseSelector.equals(
                    LocalCaseIdentity.selector(owner))
                    || !selector.equals(expectedSelector)) {
                refuseGuardedRead("GuardedReadCandidateIdentity:"
                                + readIdentity,
                        "candidate selector is not derived from its stable"
                                + " read and writer-case identities");
                return null;
            }
            List<String> writerCaseClosure = writerCaseClosureSelectors(
                    readIdentity, candidate, owner, writerCaseSelector);
            if (writerCaseClosure.isEmpty()) return null;
            declare(selector, Sort.BOOL);
            Term value = inReadArmOwner(candidate,
                    () -> lowerChoiceArm(selector,
                            () -> term(candidate.get("expression"),
                                    expected)));
            return new DirectReadArm(candidate, candidateIdentity, selector,
                    value, writerCaseClosure);
        }

        private List<String> writerCaseClosureSelectors(
                String readIdentity, JsonObject candidate,
                String writerOwner, String writerSelector) {
            JsonArray encoded = array(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_CLOSURE);
            Set<String> selectors = new LinkedHashSet<>();
            boolean containsWriter = false;
            for (JsonElement element : encoded) {
                if (!element.isJsonObject()) {
                    refuseGuardedRead("GuardedReadWriterClosure:"
                                    + readIdentity,
                            "writer case closure contains a non-object");
                    return Collections.emptyList();
                }
                JsonObject owner = element.getAsJsonObject();
                String caseOwner = optionalString(owner,
                        SymbolicPropagationClosure.WRITER_CASE_OWNER);
                String selector = optionalString(owner,
                        SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
                if (caseOwner.isEmpty()
                        || !selector.equals(
                        LocalCaseIdentity.selector(caseOwner))
                        || optionalString(owner, SymbolicPropagationClosure
                        .WRITER_CASE_REGION_ID).isEmpty()
                        || optionalString(owner, SymbolicPropagationClosure
                        .WRITER_CASE_OCCURRENCE_ID).isEmpty()
                        || !selectors.add(selector)) {
                    refuseGuardedRead("GuardedReadWriterClosure:"
                                    + readIdentity,
                            "writer case closure has an invalid or duplicate"
                                    + " local-case identity");
                    return Collections.emptyList();
                }
                containsWriter |= writerOwner.equals(caseOwner)
                        && writerSelector.equals(selector);
            }
            if (!containsWriter) {
                refuseGuardedRead("GuardedReadWriterClosure:" + readIdentity,
                        "writer case closure omits its writer case");
                return Collections.emptyList();
            }
            return new ArrayList<>(selectors);
        }

        private <T> T inReadArmOwner(JsonObject candidate,
                                     Supplier<T> body) {
            String owner = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER);
            String observationSelector = optionalString(candidate,
                    SymbolicPropagationClosure.OBSERVATION_SELECTOR);
            String observationScope = optionalString(candidate,
                    SymbolicPropagationClosure.OBSERVATION_SCOPE);
            String region = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_REGION_ID);
            String occurrence = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OCCURRENCE_ID);
            InvocationKey previousInvocation = currentInvocation;
            String previousSymbolScope = currentSymbolScope;
            String previousCaseSelector = currentCaseSelector;
            if (!owner.isEmpty()) {
                // A read reached through a writer arm belongs to that
                // writer's case, not to the case that opened the arm.
                currentCaseSelector = LocalCaseIdentity.selector(owner);
            }
            if (!region.isEmpty() && !occurrence.isEmpty()) {
                enterInvocation(new InvocationKey(region, occurrence));
            }
            if (!observationSelector.isEmpty()
                    || !observationScope.isEmpty()) {
                registerExecutionScope(owner, candidate, candidate);
            }
            String symbolScope = firstNonBlank(observationSelector, owner);
            if (!symbolScope.isEmpty()) {
                enterSymbolScope(symbolScope);
            }
            try {
                return body.get();
            } finally {
                currentCaseSelector = previousCaseSelector;
                restoreSymbolScope(previousSymbolScope);
                restoreInvocation(previousInvocation);
            }
        }

        private void emitDirectReadArm(JsonObject node,
                                       String readIdentity,
                                       String projectionIdentity,
                                       String value,
                                       String activation,
                                       DirectReadArm arm) {
            String emittedKey = projectionIdentity + "\n" + arm.selector;
            JsonObject candidate = arm.candidate;
            String writerCaseSelector = optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_SELECTOR);
            List<String> writerGuards = new ArrayList<>();
            for (String caseSelector : arm.writerCaseClosure) {
                declare(caseSelector, Sort.BOOL);
                writerGuards.add(caseSelector);
            }
            JsonElement pathGuard = candidate.get("pathGuard");
            if (pathGuard == null) {
                writerGuards.add("false");
                refuseGuardedRead("GuardedReadWriterGuardMissing:"
                                + readIdentity + ":" + arm.candidateIdentity,
                        "candidate omits its explicit writer path guard");
            } else if (!SharedStateEvidence.unguarded(pathGuard)) {
                String previousGuard = enterGuard(and(Arrays.asList(
                        activation, arm.selector)));
                try {
                    writerGuards.add(inReadArmOwner(candidate,
                            () -> constraint(pathGuard,
                                    "writer guard "
                                            + arm.candidateIdentity)));
                } finally {
                    restoreGuard(previousGuard);
                }
            }
            // One arm is active exactly when its writer case closure ran and
            // the branches at the write itself were taken.  The order axiom
            // negates this same condition for every later writer, so it is
            // recorded before the emit-once guard below.
            String activity = and(writerGuards);
            String activityKey = readIdentity + "\n" + arm.selector;
            String heldActivity = guardedReadArmActivity.putIfAbsent(
                    activityKey, activity);
            if (heldActivity != null && !heldActivity.equals(activity)) {
                orderUnknown(readIdentity,
                        "one candidate writer has two activity conditions");
            }
            // Nested reads in the writer guard above must observe every use,
            // even though this stable arm's value semantics emit only once.
            if (!emittedGuardedReadArms.add(emittedKey)) return;
            noteValueDependency(value, arm.term.text + " " + arm.selector);
            String valueAssertion = assertWithoutCurrentGuard(
                    smtSymbols.mint("guarded_read_value__", emittedKey, 16),
                    "(=> " + arm.selector + " "
                            + and(Arrays.asList(arm.term.precondition,
                            "(= " + value + " " + arm.term.text + ")"))
                            + ")");
            String guardAssertion = assertWithoutCurrentGuard(
                    smtSymbols.mint("guarded_read_writer__", emittedKey, 16),
                    "(=> " + arm.selector + " " + and(writerGuards) + ")");

            JsonObject evidence = new JsonObject();
            evidence.addProperty("kind", "DIRECT_GUARDED_READ_ARM");
            evidence.addProperty("authority",
                    SharedStateEvidence.GUARDED_READ_AUTHORITY);
            evidence.addProperty("readIdentity", readIdentity);
            evidence.addProperty("candidateIdentity", arm.candidateIdentity);
            evidence.addProperty("selector", arm.selector);
            String location = SharedStateEvidence.locationKey(node);
            SharedStateEvidence.LocationProvenance provenance =
                    locationProvenance.get(location);
            evidence.addProperty("locationKey",
                    provenance == null ? location : provenance.locationKey);
            evidence.addProperty(SharedStateEvidence.SESSION_LOCATION_FIELD,
                    provenance == null ? location
                            : provenance.sessionLocationKey);
            evidence.addProperty("declaredField",
                    provenance == null ? "" : provenance.declaredField);
            evidence.addProperty("writerCaseOwner", optionalString(candidate,
                    SymbolicPropagationClosure.WRITER_CASE_OWNER));
            // The recorded order, kept where a reader of the manifest can use
            // it: the session-monotonic version this writer published and the
            // event id of the read that retained it. A read's own arms are all
            // below its event id, so "written after this read" is only ever
            // visible by comparing one read's event against another read's
            // arms -- which is exactly the rotation race in HDFS-17899, where
            // the target datanode installs the fresh key after the allKeys
            // read that goes looking for it.
            evidence.addProperty(RecordedOrderRace.WRITER_VERSION,
                    optionalLongInteger(candidate, "fieldVersionId", -1L));
            evidence.addProperty(RecordedOrderRace.READ_EVENT,
                    optionalLongInteger(node, "readEventId", -1L));
            evidence.addProperty("writerCaseSelector", writerCaseSelector);
            evidence.add("writerCaseClosure",
                    GSON.toJsonTree(arm.writerCaseClosure));
            evidence.addProperty("valueTerm", value);
            evidence.addProperty("valueAssertion", valueAssertion);
            evidence.addProperty("writerGuardAssertion", guardAssertion);
            guardedReadChoices.add(evidence);
        }

        private void finishGuardedReadSelections() {
            List<String> reads = new ArrayList<>(
                    guardedReadActivations.keySet());
            Collections.sort(reads);
            for (String read : reads) {
                List<String> selectors = new ArrayList<>(
                        guardedReadSelectors.getOrDefault(read,
                                Collections.emptySet()));
                Collections.sort(selectors);
                if (selectors.isEmpty()) {
                    refuseGuardedRead("GuardedReadChoiceMissing:" + read,
                            "active guarded read has no candidate selector");
                    continue;
                }
                Map<String, GuardedReadUse> uses = guardedReadUses.get(read);
                if (uses == null || uses.isEmpty()) {
                    refuseGuardedRead("GuardedReadUseMissing:" + read,
                            "active guarded read has no exact use");
                    continue;
                }
                List<String> useIds = new ArrayList<>(uses.keySet());
                Collections.sort(useIds);
                for (String useId : useIds) {
                    GuardedReadUse use = uses.get(useId);
                    String assertion = assertWithoutCurrentGuard(
                            smtSymbols.mint("guarded_read_choice__",
                                    useId, 16),
                            conditionalExactlyOne(use.activation,
                                    use.selectors));
                    guardedChoiceAssertions.put(useId, assertion);
                }
                Map<String, Set<String>> selectorGuards =
                        guardedSelectorActivations.get(read);
                for (String selector : selectors) {
                    String key = read + "\n" + selector;
                    String activationAssertion = assertWithoutCurrentGuard(
                            smtSymbols.mint("guarded_read_activation__",
                                    key, 16),
                            "(=> " + selector + " " + or(new ArrayList<>(
                                    selectorGuards.get(selector))) + ")");
                    guardedActivationAssertions.put(key,
                            activationAssertion);
                }
                // One order per use, not one per read identity: a use is one
                // read event with its own candidate list, and only candidates
                // of the same event overwrite each other.  Arms of different
                // events are never both live at one read, so demanding a
                // single order over their union leaves reads that have one
                // per event with no order at all.
                for (String useId : useIds) {
                    emitGuardedReadOrder(read, useId,
                            new ArrayList<>(uses.get(useId).selectors));
                }
            }
        }

        /**
         * Last writer wins, for one guarded read.
         *
         * The per-arm {@code guarded_read_writer} obligation says only that the
         * selected arm's writer ran.  On its own that lets a *later* writer to
         * the same location run as well, so a read could observe a value its
         * own program order has already overwritten -- and the INITIAL arm
         * could be selected with every tracked writer active, which detaches a
         * read from the writes that must precede it.  Selecting arm k therefore
         * also forbids every candidate published after k.
         *
         * Nothing is emitted for the last arm in the chain: it has no later
         * writer to forbid, and its positive obligation is already asserted.
         */
        private void emitGuardedReadOrder(String read, String useId,
                                          List<String> lowered) {
            String scope = read + "\n" + useId;
            if (guardedReadOrderGaps.containsKey(scope)) return;
            Collections.sort(lowered);
            List<String> chain = mergeGuardedReadOrder(scope, read, lowered);
            if (chain == null) return;
            List<String> activity = new ArrayList<>(chain.size());
            for (String selector : chain) {
                String held = guardedReadArmActivity.get(read + "\n"
                        + selector);
                if (held == null) {
                    orderUnknown(scope, "one candidate writer has no recorded"
                            + " activity condition");
                    return;
                }
                activity.add(held);
            }
            guardedReadOrders.put(scope, chain);
            List<String> axioms = lastWriterWins(chain, activity);
            for (int index = 0; index < chain.size(); index++) {
                if (axioms.get(index).isEmpty()) continue;
                String key = scope + "\n" + chain.get(index);
                guardedOrderAssertions.put(key, assertWithoutCurrentGuard(
                        smtSymbols.mint("guarded_read_order__", key, 16),
                        axioms.get(index)));
            }
        }

        private void refuseGuardedRead(String subject, String detail) {
            guardedReadComplete = false;
            refuse(subject, detail);
        }

        private JsonObject guardedReadModel() {
            JsonObject model = new JsonObject();
            model.addProperty("schemaVersion", 1);
            model.addProperty("kind", "DIRECT_GUARDED_READ_MODEL");
            model.addProperty("authority",
                    "VM_READ_TIME_CANDIDATE_SNAPSHOT_V1");
            model.addProperty("complete", guardedReadComplete);
            JsonArray reads = new JsonArray();
            List<String> identities = new ArrayList<>(
                    guardedReadActivations.keySet());
            Collections.sort(identities);
            for (String identity : identities) {
                JsonObject read = new JsonObject();
                read.addProperty("readIdentity", identity);
                JsonArray activations = new JsonArray();
                List<String> guards = new ArrayList<>(
                        guardedReadActivations.get(identity));
                Collections.sort(guards);
                for (String guard : guards) activations.add(guard);
                read.add("activationGuards", activations);
                // One ordered chain per use: the rows name which read event
                // the order belongs to, because two events of one read need
                // not order the same arms.
                JsonArray writerOrder = new JsonArray();
                List<String> orderedScopes = new ArrayList<>();
                for (String scope : guardedReadOrders.keySet()) {
                    if (scope.startsWith(identity + "\n")) {
                        orderedScopes.add(scope);
                    }
                }
                Collections.sort(orderedScopes);
                for (String scope : orderedScopes) {
                    String useId = scope.substring(identity.length() + 1);
                    for (String selector : guardedReadOrders.get(scope)) {
                        JsonObject row = new JsonObject();
                        row.addProperty("useIdentity", useId);
                        row.addProperty("selector", selector);
                        row.addProperty("orderAssertion",
                                guardedOrderAssertions.getOrDefault(
                                        scope + "\n" + selector, ""));
                        writerOrder.add(row);
                    }
                }
                read.add("writerOrder", writerOrder);
                JsonArray uses = new JsonArray();
                Map<String, GuardedReadUse> useRows = guardedReadUses
                        .getOrDefault(identity, Collections.emptyMap());
                List<String> useIds = new ArrayList<>(useRows.keySet());
                Collections.sort(useIds);
                for (String useId : useIds) {
                    GuardedReadUse use = useRows.get(useId);
                    JsonObject row = new JsonObject();
                    row.addProperty("useIdentity", useId);
                    row.addProperty("activationGuard", use.activation);
                    JsonArray selectors = new JsonArray();
                    for (String selector : use.selectors) {
                        selectors.add(selector);
                    }
                    row.add("selectors", selectors);
                    row.addProperty("choiceAssertion",
                            guardedChoiceAssertions.getOrDefault(useId, ""));
                    uses.add(row);
                }
                read.add("uses", uses);
                JsonArray arms = new JsonArray();
                for (JsonElement encoded : guardedReadChoices) {
                    JsonObject arm = encoded.getAsJsonObject();
                    if (!identity.equals(optionalString(arm, "readIdentity"))) {
                        continue;
                    }
                    JsonObject copy = shallowCopy(arm);
                    copy.addProperty("activationAssertion",
                            guardedActivationAssertions.getOrDefault(
                                    identity + "\n"
                                            + optionalString(arm, "selector"), ""));
                    arms.add(copy);
                }
                read.add("arms", arms);
                reads.add(read);
            }
            model.add("reads", reads);
            // Telemetry, not a refusal: a read with no single writer order
            // keeps the model it had before last-writer-wins, and says so.
            JsonArray orderGaps = new JsonArray();
            List<String> ungrouped = new ArrayList<>(
                    guardedReadOrderGaps.keySet());
            Collections.sort(ungrouped);
            for (String scope : ungrouped) {
                JsonObject row = new JsonObject();
                row.addProperty("reason", GUARDED_READ_ORDER_UNKNOWN);
                int split = scope.indexOf('\n');
                row.addProperty("readIdentity",
                        split < 0 ? scope : scope.substring(0, split));
                row.addProperty("useIdentity",
                        split < 0 ? "" : scope.substring(split + 1));
                row.addProperty("detail",
                        guardedReadOrderGaps.get(scope));
                orderGaps.add(row);
            }
            model.add("orderGaps", orderGaps);
            model.addProperty("orderedReads", guardedReadOrders.size());
            return model;
        }

        /** One dependent read through a reference-typed carrier. */
        private static final class ReferenceFieldRead {
            private final String name;
            private final Sort sort;
            private final String javaType;
            private final int fieldOffset;
            private final String executionScope;
            private final String owner;
            private final String concreteOwner;
            private final String observed;
            private final String projection;
            private final String guard;

            private ReferenceFieldRead(String name, Sort sort,
                                       String javaType, int fieldOffset,
                                       String executionScope, String owner,
                                       String concreteOwner,
                                       String observed, String projection,
                                       String guard) {
                this.name = name;
                this.sort = sort;
                this.javaType = javaType;
                this.fieldOffset = fieldOffset;
                this.executionScope = executionScope;
                this.owner = owner;
                this.concreteOwner = concreteOwner;
                this.observed = observed;
                this.projection = projection;
                this.guard = guard;
            }
        }

        private static final class DirectReadArm {
            private final JsonObject candidate;
            private final String candidateIdentity;
            private final String selector;
            private final Term term;
            private final List<String> writerCaseClosure;

            private DirectReadArm(JsonObject candidate,
                                  String candidateIdentity,
                                  String selector, Term term,
                                  Collection<String> writerCaseClosure) {
                this.candidate = candidate;
                this.candidateIdentity = candidateIdentity;
                this.selector = selector;
                this.term = term;
                this.writerCaseClosure = new ArrayList<>(writerCaseClosure);
            }
        }

        /** Lowers one shared, n-ary guarded output without case products. */
        private Term lowerCaseMergeTerm(JsonObject node, Sort expected) {
            String mergeId = optionalString(node, "mergeId");
            JsonArray encoded = array(node, "arms");
            if (mergeId.isEmpty() || encoded.size() == 0) {
                unsupported.add("GuardedMergeMalformed:"
                        + firstNonBlank(mergeId, "unnamed"));
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            String projectionIdentity = projectionTermIdentity(
                    "MERGE", mergeId,
                    expected == null ? "" : expected.name(), "");
            String familyKey = optionalString(node,
                    VmExpressionIr.FAMILY_KEY);
            if (!familyKey.isEmpty()) {
                loweredBoundaryFamilies.putIfAbsent(familyKey, "");
            }
            Term held = guardedMergeTerms.get(projectionIdentity);
            if (held != null) return held;
            if (!activeGuardedMerges.add(mergeId)) {
                unsupported.add("GuardedMergeCycle:" + mergeId);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                List<String> selectors = new ArrayList<>();
                List<Term> values = new ArrayList<>();
                List<JsonObject> armRows = new ArrayList<>();
                for (JsonElement element : encoded) {
                    if (!element.isJsonObject()) continue;
                    JsonObject arm = element.getAsJsonObject();
                    String observationSelector = optionalString(arm,
                            SymbolicPropagationClosure.OBSERVATION_SELECTOR);
                    String selector = firstNonBlank(observationSelector,
                            optionalString(arm, "selector"));
                    JsonElement expression = arm.get("expression");
                    String owner = optionalString(arm, "caseOwner");
                    String occurrence = optionalString(arm, "occurrenceId");
                    if (selector.isEmpty() || owner.isEmpty()
                            || occurrence.isEmpty()
                            || expression == null) continue;
                    // A replay-independent arm may retain one representative
                    // expression after equal observations are folded.  Its
                    // allocated VM references still belong to that physical
                    // replay, whose scope travels on the arm itself.
                    if (!firstNonBlank(optionalString(arm,
                                    SymbolicPropagationClosure
                                            .OBSERVATION_SCOPE),
                            optionalString(arm, "boundarySessionScope")).isEmpty()) {
                        registerExecutionScope(owner, arm, node);
                    }
                    declare(selector, Sort.BOOL);
                    selectors.add(selector);
                    armRows.add(arm);
                    values.add(lowerChoiceArm(selector, () -> {
                        InvocationKey previousInvocation = enterInvocation(
                                new InvocationKey(optionalString(arm, "regionId"),
                                        occurrence));
                        String previousScope = enterSymbolScope(firstNonBlank(
                                observationSelector, owner));
                        try {
                            return term(expression, expected);
                        } finally {
                            restoreSymbolScope(previousScope);
                            restoreInvocation(previousInvocation);
                        }
                    }));
                }
                if (values.size() != encoded.size() || values.isEmpty()) {
                    unsupported.add("GuardedMergeMalformed:" + mergeId);
                    return unsupportedTerm(expected == null
                            ? Sort.VALUE : expected);
                }
                String family = firstNonBlank(familyKey, mergeId);
                String port = boundaryPortsByFamily.getOrDefault(familyKey,
                        "");
                for (int index = 0; index < armRows.size(); index++) {
                    JsonObject arm = armRows.get(index);
                    String owner = optionalString(arm, "caseOwner");
                    String occurrence = optionalString(arm, "occurrenceId");
                    noteExecutionRecording("MERGE\n" + family + "\n"
                                    + occurrence + "\n" + owner,
                            "family " + family + (port.isEmpty() ? ""
                                    : " port " + port) + " at " + occurrence
                                    + " case " + caseTail(owner),
                            armExecutionScope(arm, owner),
                            selectors.get(index), values.get(index));
                }
                Sort sort = values.get(0).sort;
                IntegralWidth width = values.get(0).integralWidth;
                List<String> defined = new ArrayList<>();
                for (int index = 0; index < values.size(); index++) {
                    Term value = values.get(index);
                    if (value.sort != sort) {
                        unsupported.add("GuardedMergeArmSortConflict:"
                                + mergeId + ":" + sort + "!="
                                + value.sort);
                        return unsupportedTerm(sort);
                    }
                    if (value.integralWidth != width) {
                        width = IntegralWidth.NONE;
                    }
                    defined.add("(=> " + selectors.get(index) + " "
                            + value.precondition + ")");
                }
                defined.add(or(selectors));
                // Every arm carries its own guard, including the last: an
                // unguarded final arm makes the merge take that arm's value
                // whenever no observation of the family holds at all, which
                // reads as "the wire carried this" while nothing said so.
                // The fall-through is a named unbound term instead, and
                // whether it is reachable is decided structurally in
                // requireTotalBoundaryDispatch().
                String unbound = smtSymbols.mint(UNBOUND_BOUNDARY_PREFIX,
                        projectionIdentity, 20);
                declare(unbound, sort);
                String value = unbound;
                String nullness = "";
                if (sort == Sort.STRING) {
                    nullness = unbound + "__unbound_is_null";
                    declare(nullness, Sort.BOOL);
                }
                for (int index = values.size() - 1; index >= 0; index--) {
                    value = "(ite " + selectors.get(index) + " "
                            + values.get(index).text + " " + value + ")";
                    if (sort == Sort.STRING) {
                        nullness = "(ite " + selectors.get(index) + " "
                                + values.get(index).stringNullness + " "
                                + nullness + ")";
                    }
                }
                String name = smtSymbols.mint("merged_boundary__",
                        projectionIdentity, 20);
                boundaryDispatches.add(new BoundaryDispatch(mergeId,
                        familyKey, name, unbound, selectors));
                if (!familyKey.isEmpty()) {
                    loweredBoundaryFamilies.put(familyKey, name);
                }
                defineConstant(name, sort, value);
                if (sort == Sort.STRING) {
                    defineConstant(name + "__is_null", Sort.BOOL, nullness);
                    nullness = name + "__is_null";
                }
                Term result = Term.of(name, sort, width, nullness, "",
                        and(defined));
                guardedMergeTerms.put(projectionIdentity, result);
                return result;
            } finally {
                currentGuard = previousGuard;
                activeGuardedMerges.remove(mergeId);
            }
        }

        /**
         * Lowers one guarded alternative without leaking Java definedness
         * requirements into its siblings.  Container lowering uses a shared
         * accumulator because its compact codec term does not carry a
         * precondition.  At a selector boundary those requirements belong to
         * the arm term, whose caller already emits the exact implication.
         */
        private Term lowerChoiceArm(String selector, Supplier<Term> body) {
            String previousGuard = currentGuard;
            enterGuard(and(Arrays.asList(previousGuard, selector)));
            Set<String> parentRequirements = currentContainerRequirements;
            Set<String> armRequirements = parentRequirements == null
                    ? null : new LinkedHashSet<>();
            if (armRequirements != null) {
                currentContainerRequirements = armRequirements;
            }
            try {
                Term result = body.get();
                if (result == null || armRequirements == null
                        || armRequirements.isEmpty()) {
                    return result;
                }
                return result.withPrecondition(and(Arrays.asList(
                        result.precondition,
                        and(new ArrayList<>(armRequirements)))));
            } finally {
                currentContainerRequirements = parentRequirements;
                restoreGuard(previousGuard);
            }
        }

        private Term lowerContainerTerm(JsonObject expression,
                                        boolean field) {
            boolean owner = currentContainerRequirements == null;
            if (owner) currentContainerRequirements = new LinkedHashSet<>();
            try {
                Term result = fromContainerTerm(field
                        ? ContainerSmtCodec.field(expression, containerHost())
                        : ContainerSmtCodec.term(expression, containerHost()));
                if (!owner || result == null) return result;
                return result.withPrecondition(and(Arrays.asList(
                        result.precondition,
                        and(new ArrayList<>(currentContainerRequirements)))));
            } finally {
                if (owner) currentContainerRequirements = null;
            }
        }

        private ContainerSmtCodec.Host containerHost() {
            return new ContainerSmtCodec.Host() {
                @Override
                public ContainerSmtCodec.Term state(
                        JsonElement identity,
                        ContainerSmtCodec.Sort shape) {
                    Sort required = shape == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE : Sort.MAP;
                    Term identityTerm = term(identity, required);
                    retainContainerPrecondition(identityTerm);
                    if (identityTerm != null
                            && identityTerm.sort == required) {
                        return new ContainerSmtCodec.Term(identityTerm.text,
                                shape, identityTerm.integralWidth);
                    }
                    if (identityTerm == null
                            || identityTerm.sort != Sort.REF) {
                        unsupported("ContainerStateIdentity:" + shape);
                        return null;
                    }
                    return stateOfReference(identityTerm.text, shape);
                }

                @Override
                public boolean preserveContainerIdentity(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    return ContainerSmtCodec
                            .evidencedContainerIdentity(expression);
                }

                @Override
                public void noteAbsentKeyDefault(String keyTerm,
                                                 String absentCondition) {
                    recordAbsentKeyDefault(keyTerm, absentCondition);
                }

                @Override
                public ContainerSmtCodec.Term operand(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    Sort expectedSort = expected
                            == ContainerSmtCodec.Sort.ASSOCIATIVE ? Sort.MAP
                            : expected == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE : null;
                    if (ContainerSmtCodec.handles(expression)) {
                        return toContainerTerm(shareLargeTerm(
                                fromContainerTerm(ContainerSmtCodec.term(
                                expression.getAsJsonObject(), this))));
                    }
                    if (ContainerSmtCodec.handlesField(expression)) {
                        return toContainerTerm(shareLargeTerm(
                                fromContainerTerm(ContainerSmtCodec.field(
                                expression.getAsJsonObject(), this))));
                    }
                    return toContainerTerm(term(expression,
                            nativeSortOf(expected)));
                }

                @Override
                public ContainerSmtCodec.Term share(
                        ContainerSmtCodec.Term value) {
                    return toContainerTerm(shareLargeTerm(
                            fromContainerTerm(value)));
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    Term value = term(expression, null);
                    return toContainerTerm(asValue(value,
                            VmTermLowering.expressionJavaType(expression),
                            value.text, ""));
                }

                @Override
                public ContainerSmtCodec.Term element(
                        JsonElement expression, JsonObject mutation) {
                    JsonObject previous = currentElementMutation;
                    currentElementMutation = mutation;
                    try {
                        return box(expression);
                    } finally {
                        currentElementMutation = previous;
                    }
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value,
                        String javaType) {
                    return ContainerSmtCodec.unboxValue(value,
                            javaType, VmTermLowering.unboxedCellSort(sortOfJava(javaType)),
                            this);
                }

                @Override
                public void require(String predicate) {
                    if (currentContainerRequirements != null) {
                        currentContainerRequirements.add(predicate);
                    } else {
                        assertNamed(smtSymbols.mint(
                                "container_value_kind_", predicate, 16),
                                predicate);
                    }
                }

                @Override
                public ContainerSmtCodec.Term field(
                        ContainerSmtCodec.Term owner, String ownerClass,
                        int fieldOffset, String javaType) {
                    Sort result = sortOfJava(javaType);
                    if (owner == null
                            || owner.sort != ContainerSmtCodec.Sort.REF
                            || fieldOffset < 0 || result == Sort.VALUE
                            || result == Sort.MAP
                            || result == Sort.ARRAY_VALUE) {
                        unsupported("FieldAccessExpression:"
                                + ownerClass + "@" + fieldOffset + ":"
                                + javaType);
                        return null;
                    }
                    // A SymbolExpression is already alpha-renamed by replay
                    // scope, and direct propagation preserves that exact
                    // reference across a recorded handoff.  Its field
                    // projection must therefore survive the handoff: scoping
                    // the accessor again would turn field(r) at the producer
                    // and field(r) at the consumer into unrelated functions.
                    // Bare ConSymbolExp heap constants are the exception:
                    // they are not alpha-renamed, so identical spellings from
                    // independent replay JVMs must retain case-local heaps.
                    String projectionScope = owner.text.startsWith("const__")
                            ? currentSymbolScope : "transported";
                    String identity = projectionScope + "\u0000"
                            + ownerClass + "\u0000" + fieldOffset
                            + "\u0000" + javaType;
                    String accessor = "container_field__"
                            + scopeToken(identity);
                    declareFunction(accessor, Collections.singletonList(
                            Term.of("", Sort.REF)), result);
                    return toContainerTerm(Term.of("(" + accessor + " "
                            + owner.text + ")", result,
                            JavaPrimitiveSmtSemantics.widthOfJavaType(javaType)));
                }

                @Override
                public ContainerSmtCodec.Term field(
                        ContainerSmtCodec.Term owner, String ownerClass,
                        int fieldOffset, String javaType,
                        ContainerSmtCodec.Term concreteOwner,
                        ContainerSmtCodec.Term concreteValue) {
                    ContainerSmtCodec.Term projection =
                            field(owner, ownerClass, fieldOffset, javaType);
                    ContainerSmtCodec.Term routed = routedReferenceField(
                            projection, owner, ownerClass, fieldOffset,
                            javaType, concreteOwner, concreteValue);
                    // A shape this emitter cannot route is still a correct
                    // projection; it is only a weaker one, so the observed
                    // pair is dropped rather than the read refused.
                    return routed != null ? routed : projection;
                }

                @Override
                public void unsupported(String reason) {
                    Emitter.this.unsupported.add(
                            "MODEL_SEMANTICS_MISSING:" + reason);
                }
            };
        }

        /**
         * Reads the session owner from the VM's container symbol.
         */

        private ContainerSmtCodec.Term toContainerTerm(Term value) {
            if (value == null) return null;
            retainContainerPrecondition(value);
            ContainerSmtCodec.Sort sort =
                    VmTermLowering.containerSortOf(value.sort);
            if (sort == null) {
                unsupported.add("ContainerOperandSort:" + value.sort);
                return null;
            }
            return new ContainerSmtCodec.Term(value.text, sort,
                    value.integralWidth);
        }

        /** Preserves definedness while crossing the compact codec boundary. */
        private void retainContainerPrecondition(Term value) {
            if (value != null && currentContainerRequirements != null
                    && !"true".equals(value.precondition)) {
                currentContainerRequirements.add(value.precondition);
            }
        }

        private Term fromContainerTerm(ContainerSmtCodec.Term value) {
            if (value == null) return unsupportedTerm(Sort.VALUE);
            Sort sort = VmTermLowering.sortOfContainer(value.sort);
            return Term.of(value.text,
                    sort == Sort.UNKNOWN ? Sort.VALUE : sort,
                    value.integralWidth);
        }

        private Term symbol(JsonObject expression, Sort expected) {
            String raw = optionalString(expression, "_exp");
            if (VmExpressionIr.SYMBOLIC_NULL.equals(raw)) {
                return Term.of("nullRef", Sort.REF);
            }
            if ("V".equals(raw)) return Term.of("true", Sort.BOOL);
            String javaType = optionalString(expression, "_java_type");
            Sort encoded = sortOfJava(javaType);
            // A reference-typed use of an allocated container wants the
            // object, not its state: only that representation can also hold
            // the null the same slot may carry.  Its state stays reachable
            // through the structural witness for a container-typed use.
            Sort sort = expected == Sort.MAP
                    || expected == Sort.ARRAY_VALUE ? expected
                    : expected == Sort.REF && VmExpressionIr
                    .isExecutionLocalStructuralWitness(raw) ? Sort.REF
                    : encoded != Sort.VALUE ? encoded
                    : expected == null ? Sort.REF : expected;
            if ((sort == Sort.REF || sort == Sort.MAP
                    || sort == Sort.ARRAY_VALUE)
                    && VmExpressionIr
                    .isExecutionLocalStructuralWitness(raw)) {
                return structuralWitness(raw, sort);
            }
            if (sort == Sort.REF && currentElementMutation != null
                    && VmExpressionIr.isUntrackedReferencePlaceholder(raw)) {
                return untrackedElementWitness(raw, javaType,
                        currentElementMutation);
            }
            if (!declaredSymbolicRoot(raw)) {
                refuse("SymbolicSourceAuthorityMissing:" + raw,
                        "the VM expression names a root with no manual or "
                                + "configured symbolization event");
                return unsupportedTerm(sort);
            }
            return scopedSymbol(raw, "sym", sort, javaType,
                    "configured_symbol_" + smtName(raw),
                    "ConfiguredSymbol", "configured:");
        }

        /**
         * Lowers a dependent read whose owner is a choice over object
         * identities, or null when this emitter cannot state the choice.
         *
         * <p>An uninterpreted {@code container_field__} projection of such
         * an owner is sound and empty: it says the value is some function of
         * whichever object was installed, and nothing about what that
         * function returns for any of them.  That emptiness is what let a
         * fault-idle candidate hand the wire a key id of zero.  The read is
         * therefore lowered as a declared constant, bound in {@link #finish}
         * to an owner-indexed value: the object this execution actually read
         * from yields what it was observed to hold, an object with a
         * versioned family of its own yields that family's value, and an
         * identity with neither remains the free projection -- a named
         * freedom, never a default.</p>
         */
        private ContainerSmtCodec.Term routedReferenceField(
                ContainerSmtCodec.Term plainProjection,
                ContainerSmtCodec.Term owner, String ownerClass,
                int fieldOffset, String javaType,
                ContainerSmtCodec.Term concreteOwner,
                ContainerSmtCodec.Term concreteValue) {
            Sort result = sortOfJava(javaType);
            if (plainProjection == null || owner == null
                    || concreteOwner == null
                    || concreteValue == null
                    || owner.sort != ContainerSmtCodec.Sort.REF
                    || concreteOwner.sort != ContainerSmtCodec.Sort.REF
                    || fieldOffset < 0 || result == Sort.VALUE
                    || result == Sort.UNKNOWN || result == Sort.MAP
                    || result == Sort.ARRAY_VALUE) {
                return null;
            }
            Term observed = fromContainerTerm(concreteValue);
            if (observed == null || observed.sort != result) return null;
            String executionScope =
                    executionScopesByCase.get(currentSymbolScope);
            if (executionScope == null || executionScope.isEmpty()
                    || CANONICAL_MAP_STATE_SCOPE.equals(executionScope)) {
                return null;
            }
            Term projection = fromContainerTerm(plainProjection);
            if (projection == null || projection.sort != result) return null;
            String identity = executionScope + "\u0000" + ownerClass
                    + "\u0000" + fieldOffset + "\u0000" + javaType
                    + "\u0000" + owner.text + "\u0000" + concreteOwner.text
                    + "\u0000" + observed.text + "\u0000" + currentGuard;
            String name = smtSymbols.mint(REFERENCE_FIELD_PREFIX,
                    identity, 16);
            declare(name, result);
            referenceFieldReads.add(new ReferenceFieldRead(name, result,
                    javaType, fieldOffset, executionScope, owner.text,
                    concreteOwner.text, observed.text, projection.text,
                    currentGuard));
            return toContainerTerm(Term.of(name, result,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType)));
        }

        /**
         * Remembers that one object's own field has a versioned family, so a
         * dependent read that selects that object routes to it instead of to
         * a free projection.
         */
        private void recordGuardedReadFieldFamily(JsonObject node,
                                                  Term value) {
            if (value == null || value.text.isEmpty()) return;
            String location = SharedStateEvidence.locationKey(node);
            if (!"INSTANCE_FIELD".equals(
                    SharedStateEvidence.locationKindOf(location))) return;
            long owner = SharedStateEvidence.locationOwnerOf(location);
            int slot = SharedStateEvidence.locationSlotOf(location);
            if (owner == 0L || slot < 0) return;
            String executionScope =
                    executionScopesByCase.get(currentSymbolScope);
            if (executionScope == null || executionScope.isEmpty()) return;
            guardedReadFieldFamilies.putIfAbsent(
                    fieldFamilyKey(executionScope, "oop:" + owner, slot,
                            guardedReadJavaType(node)),
                    value.text);
        }

        private static String fieldFamilyKey(String executionScope,
                                             String referenceIdentity,
                                             int slot, String javaType) {
            return executionScope + "\u0000" + referenceIdentity
                    + "\u0000" + slot + "\u0000"
                    + JavaPrimitiveSmtSemantics.javaTypeDescriptor(javaType);
        }

        /**
         * Binds every dependent reference-carrier read to its owner.
         *
         * <p>Outermost arm first: the object this execution read from is the
         * one the run has direct evidence about, so it wins over a family
         * that merely describes the same slot of some other identity.</p>
         */
        private void emitReferenceFieldRoutings() {
            for (ReferenceFieldRead read : referenceFieldReads) {
                List<String[]> routes = new ArrayList<>();
                for (Map.Entry<String, Term> entry
                        : structuralWitnesses.entrySet()) {
                    String[] parts = entry.getKey().split("\u0000", -1);
                    if (parts.length != 3
                            || !Sort.REF.name().equals(parts[1])
                            || !read.executionScope.equals(parts[0])) {
                        continue;
                    }
                    String witness = entry.getValue().text;
                    if (witness.equals(read.concreteOwner)) continue;
                    String family = guardedReadFieldFamilies.get(
                            fieldFamilyKey(read.executionScope, parts[2],
                                    read.fieldOffset, read.javaType));
                    if (family == null) continue;
                    routes.add(new String[]{witness, family});
                }
                String body = referenceFieldBinding(read.owner,
                        read.concreteOwner, read.observed, read.projection,
                        routes);
                String previousGuard = enterGuard(read.guard);
                try {
                    assertNamed(smtSymbols.mint(
                                    "reference_field_binding_",
                                    read.name, 16),
                            "(= " + read.name + " " + body + ")");
                } finally {
                    restoreGuard(previousGuard);
                }
            }
        }

        /**
         * A witness for a reference the VM stored into a container without
         * naming it.
         *
         * <p>{@code P_L'<class>'_} is the VM's placeholder for an operand
         * oop no shadow names: the object exists in the recording and is
         * not a root (nothing declared it, nothing the solver may move), so
         * refusing it as a root with no authority refuses the whole
         * composition for an identity the formula only has to keep
         * distinct.  HDFS-17960 met it the moment {@code snapshotCounter}
         * left the carrier set: the {@code Snapshot} inserted into
         * {@code snapshotsByNames} used to be shadowed only because its
         * {@code id} field had received a versioned value.</p>
         *
         * <p>The placeholder carries no oop id, so it cannot be the same
         * witness everywhere it appears -- two distinct objects render the
         * same text.  What is unique is the mutation that stored it: one
         * insertion event, one element.  The witness is therefore an
         * execution-local {@code structural_ref} scoped by the replay scope
         * and the content digest of the mutation node, minted once per
         * insertion and reused wherever that insertion is lowered.  It gets
         * no distinctness constraints (nothing states which placeholders
         * are one object), which over-approximates: a formula that needs
         * two such elements equal or different can choose either.  The
         * placeholder outside a mutation's element position keeps its
         * refusal.</p>
         */
        private Term untrackedElementWitness(String raw, String javaType,
                                             JsonObject mutation) {
            String executionScope = executionScopesByCase.get(
                    currentSymbolScope);
            if (executionScope == null || executionScope.isEmpty()) {
                refuse("StructuralWitnessExecutionScopeMissing:"
                                + currentSymbolScope,
                        "structural witness has no linked replay scope");
                return unsupportedTerm(Sort.REF);
            }
            String digest = mutationDigests.get(mutation);
            if (digest == null) {
                digest = CanonicalJson.sha256(CanonicalJson.render(mutation));
                mutationDigests.put(mutation, digest);
            }
            String key = executionScope + "\u0000untracked-element\u0000"
                    + raw + "\u0000" + digest;
            Term witness = structuralWitnesses.get(key);
            if (witness == null) {
                String name = smtSymbols.mint("structural_ref__"
                        + scopeToken(executionScope) + "__" + smtName(raw)
                        + "__", key, 12);
                witness = Term.of(name, Sort.REF);
                structuralWitnesses.put(key, witness);
                declare(name, Sort.REF);
                JsonObject row = new JsonObject();
                row.addProperty("kind", UNTRACKED_ELEMENT_WITNESS_KIND);
                row.addProperty("placeholder", raw);
                row.addProperty("javaType", javaType);
                row.addProperty("operation",
                        optionalString(mutation, "operation"));
                row.addProperty("shape", optionalString(mutation, "shape"));
                row.addProperty("mutationDigest", digest);
                row.addProperty("executionScope", executionScope);
                row.addProperty("witness", name);
                row.addProperty("uses", 0);
                untrackedElementWitnesses.put(key, row);
            }
            JsonObject row = untrackedElementWitnesses.get(key);
            row.addProperty("uses", row.get("uses").getAsInt() + 1);
            return witness;
        }

        /** Every unnamed element witness, in first-seen order. */
        private JsonArray untrackedElementWitnessLedger() {
            JsonArray result = new JsonArray();
            for (JsonObject row : untrackedElementWitnesses.values()) {
                result.add(row.deepCopy());
            }
            return result;
        }

        /**
         * Lowers a concrete oop/array identity without granting it source
         * authority.  Such terms may state recorded identity and container
         * relations, but are intentionally absent from every materialization
         * ledger and therefore can never become a replay assignment.
         */
        private Term structuralWitness(String raw, Sort sort) {
            // Content-addressed MAP_STATE identities already name the same
            // planned carrier across replay JVMs. Scoping them again by the
            // current boundary session would undo that canonicalization and
            // split symbolic merging back into one map per replay.
            String executionScope = VmExpressionIr
                    .isCanonicalMapStateReference(raw)
                    ? "canonical-map-state"
                    : executionScopesByCase.get(currentSymbolScope);
            if (executionScope == null || executionScope.isEmpty()) {
                refuse("StructuralWitnessExecutionScopeMissing:"
                                + currentSymbolScope,
                        "structural witness has no linked replay scope");
                return unsupportedTerm(sort);
            }
            String referenceIdentity =
                    VmExpressionIr.allocatedReferenceIdentity(raw);
            String semanticIdentity = sort == Sort.REF
                    ? referenceIdentity : raw;
            if (semanticIdentity.isEmpty()) {
                refuse("StructuralWitnessIdentityMissing:" + raw,
                        "allocated VM witness has no decodable object id");
                return unsupportedTerm(sort);
            }
            if (sort == Sort.MAP || sort == Sort.ARRAY_VALUE) {
                String shapeKey = executionScope + "\u0000"
                        + referenceIdentity;
                Sort heldShape = structuralStateSorts.putIfAbsent(
                        shapeKey, sort);
                if (heldShape != null && heldShape != sort) {
                    refuse("StructuralWitnessContainerShapeConflict:" + raw,
                            "one allocated container is used as both "
                                    + heldShape + " and " + sort);
                    return unsupportedTerm(sort);
                }
            }
            String key = executionScope + "\u0000" + sort.name()
                    + "\u0000" + semanticIdentity;
            Term witness = structuralWitnesses.get(key);
            if (witness == null) {
                String prefix = sort == Sort.REF
                        ? "structural_ref" : "structural_state";
                String name = smtSymbols.mint(prefix + "__"
                        + scopeToken(executionScope) + "__"
                        + smtName(raw) + "__", key, 12);
                witness = Term.of(name, sort);
                structuralWitnesses.put(key, witness);
                declare(name, sort);
            }
            if (sort == Sort.REF) {
                constrainAllocatedReference(executionScope,
                        referenceIdentity, witness.text);
            } else if (!VmExpressionIr.isAllocatedArrayReference(raw)) {
                constrainContainerSizeDomain(executionScope,
                        semanticIdentity, witness);
            }
            return witness;
        }

        /**
         * A VM-allocated Java container object holds a Java {@code int}
         * number of elements, so its size is in
         * {@code [0, Integer.MAX_VALUE]} whatever path reached it.
         *
         * <p>The codec already states this fact wherever a {@code size()}
         * relation is lowered, but it states it as a container requirement,
         * which the surrounding case carries as its own path precondition.
         * A case the solver leaves unselected therefore states nothing about
         * the witness, and an index derived from the size -- a binary-search
         * midpoint is {@code (low + high) / 2} -- becomes division by an
         * unbounded integer.  The fact belongs to the allocated container
         * rather than to one path through it, so it is stated once and
         * unguarded, exactly as the same witness's non-nullness is.</p>
         *
         * <p>An allocated array is excluded: the VM records its exact
         * length, and every use of an array state carries that length as
         * the state's own size.  Bounding the bare witness there would name
         * a size term no constraint mentions.</p>
         */
        private void constrainContainerSizeDomain(String executionScope,
                                                  String identity,
                                                  Term witness) {
            String accessor = witness.sort == Sort.ARRAY_VALUE
                    ? "indexed_size" : witness.sort == Sort.MAP
                    ? "assoc_size" : "";
            if (accessor.isEmpty()) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType("I");
            if (domain == null) return;
            String size = "(" + accessor + " " + witness.text + ")";
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                assertNamed(smtSymbols.mint(
                                "container_size_domain_",
                                executionScope + "\u0000" + identity, 16),
                        "(and (<= 0 " + size + ") (<= " + size + " "
                                + domain.upper + "))");
            } finally {
                currentGuard = previousGuard;
            }
        }

        /** A positive VM allocation id denotes a concrete, non-null oop. */
        private void constrainAllocatedReference(String executionScope,
                                                  String identity,
                                                  String reference) {
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                assertNamed(smtSymbols.mint(
                                "allocated_reference_non_null_",
                                executionScope + "\u0000" + identity, 16),
                        "(not (= " + reference + " nullRef))");
            } finally {
                currentGuard = previousGuard;
            }
        }

        private boolean declaredSymbolicRoot(String raw) {
            return manualSourceIdentities.containsKey(raw)
                    || symbolicSourceIdentities.containsKey(raw)
                    || namedSourceIdentities.containsKey(raw)
                    || configuredSourceCanonicalIdentityByObservedRaw
                    .containsKey(raw)
                    || reusedManualAuthorityKey(raw) != null;
        }

        /** Canonical named assertion for the selected fatal path. */
        private Term scopedSymbol(String raw, String prefix, Sort requested,
                                  String javaType, String domainLabel,
                                  String conflictLabel, String sourcePrefix) {
            String manualIdentity = manualSourceIdentities.get(raw);
            String sourceIdentity = symbolicSourceIdentities.get(raw);
            if (sourceIdentity == null) {
                String namedIdentity = namedSourceIdentities.get(raw);
                // A runtime NAMED event attests that this raw expression is
                // the same propagated configured field wherever a selected
                // case consumes it.  Its mint may be outside the selected
                // summaries, but case-local scoping would still manufacture
                // several solver terms for one Java field and then report a
                // false materialization conflict.
                if (namedIdentity != null) sourceIdentity = namedIdentity;
            }
            String reusedManualKey = manualIdentity == null
                    && sourceIdentity == null
                    && !configuredSourceCanonicalIdentityByObservedRaw
                    .containsKey(raw)
                    ? reusedManualAuthorityKey(raw) : null;
            String rootIdentity = manualIdentity == null
                    ? configuredSourceCanonicalIdentityByObservedRaw.get(raw)
                    : manualIdentity;
            if (rootIdentity == null && sourceIdentity != null) {
                rootIdentity = configuredSourceCanonicalIdentityByIdentity
                        .getOrDefault(sourceIdentity, sourceIdentity);
            }
            String sourceRaw = manualIdentity == null
                    ? configuredSourceCanonicalRawByObservedRaw.get(raw)
                    : raw;
            if (sourceRaw == null) {
                sourceRaw = sourceIdentity == null ? raw
                        : configuredSourceRawByIdentity.getOrDefault(
                                sourceIdentity, raw);
            }
            String key = reusedManualKey == null
                    ? symbolScopeKey(sourceRaw, currentSymbolScope,
                    rootIdentity)
                    : "manual-reused\u0000" + reusedManualKey;
            RawSymbol symbol = rawSymbols.get(key);
            if (symbol == null) {
                String name = manualIdentity != null
                        ? recordManualRootName(raw,
                        "manual__" + scopeToken(manualIdentity))
                        : reusedManualKey != null
                        ? "manual_reused__" + scopeToken(reusedManualKey)
                        : rootIdentity == null
                        ? scopedName(prefix, raw)
                        : configuredSourceRootName(sourceRaw,
                        rootIdentity);
                symbol = new RawSymbol(name, requested);
                rawSymbols.put(key, symbol);
                declare(symbol.name, symbol.sort);
                // A configured source denotes one concrete Java field across
                String previousGuard = currentGuard;
                if (rootIdentity != null || reusedManualKey != null) {
                    currentGuard = "";
                }
                try {
                    assertJavaIntegralDomain(symbol.name, symbol.sort,
                            javaType, domainLabel);
                    if (symbol.sort == Sort.REF
                            && VmExpressionIr
                            .isAllocatedInstanceReference(raw)) {
                        assertNamed("allocated_instance_non_null_"
                                        + smtName(symbol.name),
                                "(not (= " + symbol.name + " nullRef))");
                    }
                } finally {
                    currentGuard = previousGuard;
                }
            } else if (symbol.sort != requested) {
                unsupported.add(conflictLabel + "SortConflict:" + raw
                        + ":" + symbol.sort + "->" + requested);
            }
            if (symbol.sort == Sort.STRING) {
                if (symbol.nullness.isEmpty()) {
                    symbol.nullness = scopedName("string_is_null", raw);
                    declare(symbol.nullness, Sort.BOOL);
                }
                recordSourceMaterialization(raw, symbol);
                return Term.nullableString(symbol.name, symbol.nullness,
                        sourcePrefix + key);
            }
            recordSourceMaterialization(raw, symbol);
            return Term.of(symbol.name, symbol.sort,
                    JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
        }

        private void recordSourceMaterialization(String raw,
                                                 RawSymbol symbol) {
            if (manualSourceIdentities.containsKey(raw)) {
                recordManualSourceMaterialization(raw, symbol);
            } else if (reusedManualAuthorityKey(raw) != null
                    && !symbolicSourceIdentities.containsKey(raw)
                    && !namedSourceIdentities.containsKey(raw)
                    && !configuredSourceCanonicalIdentityByObservedRaw
                    .containsKey(raw)) {
                recordReusedManualSourceMaterializations(raw, symbol);
            } else {
                recordConfiguredSourceMaterialization(raw, symbol);
            }
        }

        /** The current case's exact action-bound authority for one VM root. */
        private String reusedManualAuthorityKey(String raw) {
            String executionScope = executionScopesByCase.get(
                    currentSymbolScope);
            if (executionScope == null || executionScope.isEmpty()) {
                return null;
            }
            String key = executionScope + "\u0000" + raw;
            return reusedManualSourceEvents.containsKey(key) ? key : null;
        }

        /**
         * A reused observation makes the existing term replay-addressable at
         * every exact action that observed it.  All aliases receive the same
         * solver term; none is added to the mint registry.
         */
        private void recordReusedManualSourceMaterializations(
                String raw, RawSymbol symbol) {
            String key = reusedManualAuthorityKey(raw);
            if (key == null) return;
            for (JsonObject event : reusedManualSourceEvents.get(key)) {
                String javaType = optionalString(event, "javaType");
                if (sortOfJava(javaType) != symbol.sort) {
                    unsupported.add(
                            "ReusedManualSourceMaterializationSortConflict:"
                                    + optionalString(event, "portId"));
                    continue;
                }
                JsonObject row = new JsonObject();
                row.addProperty("schemaVersion", 1);
                row.addProperty("kind", MANUAL_SOURCE_MATERIALIZATION_KIND);
                row.addProperty("authority",
                        MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
                row.addProperty("portId", optionalString(event, "portId"));
                row.addProperty("occurrenceId",
                        optionalString(event, "plannedOccurrenceId"));
                if (!optionalString(event, "fieldSignature").isEmpty()) {
                    row.addProperty("fieldSignature",
                            optionalString(event, "fieldSignature"));
                }
                row.addProperty("javaTypeDescriptor",
                        javaTypeDescriptor(javaType));
                row.addProperty("sort", symbol.sort.name());
                row.addProperty("smtSort", symbol.sort.smt);
                row.addProperty("solverTerm", symbol.name);
                if (!symbol.nullness.isEmpty()) {
                    row.addProperty("nullnessSolverTerm", symbol.nullness);
                }
                row.addProperty("sourceIdentity",
                        optionalString(event, "sourceIdentity"));
                row.addProperty("sourceIdentityAuthority",
                        ConcolicSummaryImporter
                                .MANUAL_INPUT_OBSERVATION_AUTHORITY);
                row.addProperty("reused", true);
                JsonObject held = manualSourceMaterializations.putIfAbsent(
                        optionalString(event, "sourceIdentity"), row);
                if (held != null && !held.equals(row)) {
                    unsupported.add(
                            "ReusedManualSourceMaterializationConflict:"
                                    + optionalString(event, "portId"));
                }
            }
        }

        private void recordManualSourceMaterialization(
                String raw, RawSymbol symbol) {
            String identity = manualSourceIdentities.get(raw);
            JsonObject event = manualSourceEvents.get(raw);
            if (identity == null || event == null) {
                unsupported.add("ManualSourceMaterializationMissing:" + raw);
                return;
            }
            String javaType = optionalString(event, "javaType");
            if (sortOfJava(javaType) != symbol.sort) {
                unsupported.add("ManualSourceMaterializationSortConflict:"
                        + optionalString(event, "portId"));
                return;
            }
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", MANUAL_SOURCE_MATERIALIZATION_KIND);
            row.addProperty("authority",
                    MANUAL_SOURCE_MATERIALIZATION_AUTHORITY);
            row.addProperty("portId", optionalString(event, "portId"));
            row.addProperty("occurrenceId",
                    optionalString(event, "sourceOccurrenceId"));
            if (!optionalString(event, "fieldSignature").isEmpty()) {
                row.addProperty("fieldSignature",
                        optionalString(event, "fieldSignature"));
            }
            row.addProperty("javaTypeDescriptor",
                    javaTypeDescriptor(javaType));
            row.addProperty("sort", symbol.sort.name());
            row.addProperty("smtSort", symbol.sort.smt);
            row.addProperty("solverTerm", symbol.name);
            if (!symbol.nullness.isEmpty()) {
                row.addProperty("nullnessSolverTerm", symbol.nullness);
            }
            row.addProperty("sourceIdentity", identity);
            row.addProperty("sourceIdentityAuthority",
                    SymbolicSourceEvidence.MANUAL_AUTHORITY);
            JsonObject held = manualSourceMaterializations.putIfAbsent(
                    identity, row);
            if (held != null && !held.equals(row)) {
                unsupported.add("ManualSourceMaterializationConflict:"
                        + optionalString(event, "portId"));
            }
        }

        /**
         * Names the root of one configured-source mint.
         *
         * <p>The producing runtime's own name wins when it published one -
         * {@code sym__<sourceId>__<occurrenceId>__<ordinal>} under wave 3
         * C1 - so the model reports the root the mint site minted.  A row
         * that publishes none is named from its mint identity.  The {@code raw}
         * passed here is already canonical for exact recorded-event projection
         * aliases; collisions between distinct canonical roots are still
         * separated by that raw spelling.</p>
         */
        private String configuredSourceRootName(String raw,
                                                String identity) {
            JsonObject event = symbolicSourceEvents.get(raw);
            String published = event == null ? ""
                    : optionalString(event, SymbolicSourceEvidence.SYMBOL);
            String base = published.isEmpty()
                    ? SymbolicSourceEvidence.isReused(event)
                    ? "sym__propagated__" + smtName(raw)
                    : "source__" + scopeToken(identity)
                    : smtName(published);
            String held = configuredSourceRoots.putIfAbsent(base, raw);
            return held == null || held.equals(raw) ? base
                    : smtSymbols.mint(base + "__", raw, 16);
        }

        /**
         * Publishes the exact writable program source behind one emitted SMT
         */
        private void recordConfiguredSourceMaterialization(
                String raw, RawSymbol symbol) {
            String identity = symbolicSourceIdentities.get(raw);
            if (identity == null) {
                // A root the declared read only NAMED is absent from the
                // root registry, and must stay absent: it was minted
                // elsewhere, so it keeps the name and the guard the mint
                // that made it already gave it.  What the naming adds is
                // this row - the writable program field behind a term the
                // formula already declares.
                identity = namedSourceIdentities.get(raw);
                if (identity == null) return;
            }
            identity = configuredSourceCanonicalIdentityByObservedRaw
                    .getOrDefault(raw,
                            configuredSourceCanonicalIdentityByIdentity
                                    .getOrDefault(identity, identity));
            JsonObject event = configuredSourceEventByIdentity.get(identity);
            if (event == null) event = symbolicSourceEvents.get(raw);
            if (event == null) {
                unsupported.add("ConfiguredSourceMaterializationMissing:"
                        + raw);
                return;
            }
            String javaType = optionalString(event, "javaType");
            String fieldType = fieldSignatureJavaType(
                    optionalString(event, "fieldSignature"));
            Sort declaredSort = sortOfJava(javaType);
            if (declaredSort != symbol.sort
                    || !javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(fieldType))) {
                unsupported.add("ConfiguredSourceMaterializationSortConflict:"
                        + optionalString(event, "sourceId") + ":" + declaredSort
                        + "->" + symbol.sort + ":" + fieldType + "->"
                        + javaType);
                return;
            }
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 3);
            row.addProperty("kind",
                    CONFIGURED_SOURCE_MATERIALIZATION_KIND);
            row.addProperty("authority",
                    CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY);
            String sourceKey = optionalString(event, "sourceKey");
            if (sourceKey.isEmpty()) {
                unsupported.add("ConfiguredSourceMaterializationSourceKeyMissing:"
                        + optionalString(event, "sourceId"));
                return;
            }
            row.addProperty("sourceKey", sourceKey);
            row.addProperty("sourceId", optionalString(event, "sourceId"));
            row.addProperty("sourcePhaseId",
                    optionalString(event, "sourcePhaseId"));
            row.addProperty("sourceOccurrenceId",
                    optionalString(event, "sourceOccurrenceId"));
            row.addProperty("fieldSignature",
                    optionalString(event, "fieldSignature"));
            row.addProperty("javaTypeDescriptor",
                    javaTypeDescriptor(javaType));
            row.addProperty("sort", symbol.sort.name());
            row.addProperty("smtSort", symbol.sort.smt);
            row.addProperty("solverTerm", symbol.name);
            if (!symbol.nullness.isEmpty()) {
                row.addProperty("nullnessSolverTerm", symbol.nullness);
            }
            JsonObject held = configuredSourceMaterializations.putIfAbsent(
                    identity, row);
            // The recorded value is merged onto the stored row rather than
            // compared with it, and the conflict check ignores it: one
            // identity is observed by every replay of the same entry, and
            // only the activations that read the field as the program left
            // it state one.  A row that states none is the same
            // materialization as a row that does.
            if (held != null && !withoutRecordedValue(held).equals(row)) {
                unsupported.add("ConfiguredSourceMaterializationConflict:"
                        + optionalString(event, "sourceId"));
                return;
            }
            mergeRecordedSourceValue(held == null ? row : held,
                    SymbolicSourceEvidence.recordedValueOf(event));
        }

        /** The materialization a row states, with its recording set aside. */
        private JsonObject withoutRecordedValue(JsonObject row) {
            if (!row.has(RECORDED_SOURCE_VALUE)) return row;
            JsonObject copy = row.deepCopy();
            copy.remove(RECORDED_SOURCE_VALUE);
            return copy;
        }

        /**
         * Records what a configured source's field held, or leaves it
         * unstated.
         *
         * <p>Two observations of one entry that disagree are not a value to
         * pick between: the row drops back to stating none, which reads
         * downstream as "unknown" rather than as a recording.</p>
         */
        private void mergeRecordedSourceValue(JsonObject row,
                                              String recordedValue) {
            if (recordedValue == null || recordedValue.isEmpty()) return;
            String held = optionalString(row, RECORDED_SOURCE_VALUE);
            if (held.isEmpty()) {
                row.addProperty(RECORDED_SOURCE_VALUE, recordedValue);
            } else if (!held.equals(recordedValue)) {
                row.remove(RECORDED_SOURCE_VALUE);
            }
        }

        /**
         * Recognizes the sound Java round trip
         */

        private Term lowerSplitElementTerm(JsonObject expression) {
            SplitSegment match = exactSplitSegment(expression);
            if (!match.complete()) {
                return splitElementGap(match.gap);
            }
            List<String> pieces = new ArrayList<>();
            List<String> preconditions = new ArrayList<>();
            for (SplitPiece piece : match.pieces) {
                if (piece.integerSource == null) {
                    pieces.add(quote(piece.text));
                    continue;
                }
                Term integer = integerPieceTerm(piece);
                if (integer.sort != Sort.INT) {
                    return splitElementGap("ROUNDTRIP_SOURCE_NOT_INT");
                }
                assertJavaIntRange(integer);
                Term rendered = VmTermLowering.javaIntString(integer);
                pieces.add(rendered.text);
                preconditions.add(rendered.precondition);
            }
            if (pieces.isEmpty()) {
                return Term.nonNullString(quote(""), "");
            }
            if (pieces.size() == 1) {
                return Term.nonNullString(pieces.get(0),
                        and(preconditions));
            }
            StringBuilder text = new StringBuilder("(str.++");
            for (String piece : pieces) text.append(' ').append(piece);
            return Term.nonNullString(text.append(')').toString(),
                    and(preconditions));
        }

        /**
         * Reads one element out of a concatenation split on a delimiter.
         */
        private SplitSegment exactSplitSegment(JsonElement expression) {
            // A split result reaches its reader through the array the VM
            // filled in, so resolve the select-over-store first: the codec
            JsonElement selected =
                    ContainerSmtCodec.selectedIndexedElement(expression);
            if (selected == null || !selected.isJsonObject()) {
                return SplitSegment.gap("NOT_METHOD_EXPRESSION");
            }
            JsonObject split = selected.getAsJsonObject();
            if (!"MethodExpression".equals(optionalString(split, "_type"))
                    || !isJavaSplitElement(optionalString(split, "_name"))) {
                return SplitSegment.gap("NOT_STRING_SPLIT_ELEMENT");
            }
            JsonArray params = array(split, "_param_list");
            if (params.size() != 3 && params.size() != 4) {
                return SplitSegment.gap("SPLIT_ARITY");
            }

            Integer index = exactIntLiteral(params.get(params.size() - 1));
            if (index == null || index < 0) {
                return SplitSegment.gap("INDEX_NOT_EXACT_LITERAL");
            }
            String delimiter = VmExpressionIr.exactStringLiteral(params.get(1),
                    STRING_TYPED);
            String delimiterGap = delimiterGap(delimiter, false);
            if (!delimiterGap.isEmpty()) {
                return SplitSegment.gap(delimiterGap);
            }
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // A positive limit applies the pattern at most limit-1
                // times, so it has to allow the index splits that reach
                if (limit == null) {
                    return SplitSegment.gap("LIMIT_NOT_LITERAL");
                }
                if (limit > 0 && limit <= index + 1) {
                    return SplitSegment.gap("LIMIT_DOES_NOT_REACH_INDEX");
                }
            }

            ScopedExpression receiver = new ScopedExpression(
                    params.get(0), currentInvocation);
            List<JsonElement> parts = new ArrayList<>();
            if (!flattenConcat(receiver.expression, parts)) {
                return SplitSegment.gap("CONCAT_RECEIVER_REQUIRED");
            }
            return splitConcatElement(parts, receiver.invocation,
                    delimiter.charAt(0), index);
        }

        private SplitSegment splitConcatElement(List<JsonElement> parts,
                                                InvocationKey invocation,
                                                char delimiter, int index) {
            List<SplitPiece> element = new ArrayList<>();
            int segment = 0;
            for (JsonElement part : parts) {
                String literal = VmExpressionIr.exactStringLiteral(part,
                        STRING_TYPED);
                if (literal != null) {
                    int start = 0;
                    while (true) {
                        int at = literal.indexOf(delimiter, start);
                        if (at < 0) break;
                        if (segment == index) {
                            addText(element,
                                    literal.substring(start, at));
                            return SplitSegment.of(element);
                        }
                        segment++;
                        start = at + 1;
                    }
                    if (segment == index) {
                        addText(element, literal.substring(start));
                    }
                    continue;
                }
                JsonElement rendered = javaIntRenderingSource(part);
                if (rendered == null) {
                    return SplitSegment.gap(
                            "PART_NOT_PROVABLY_DELIMITER_FREE");
                }
                if (Character.isDigit(delimiter) || delimiter == '-') {
                    return SplitSegment.gap(
                            "DELIMITER_OCCURS_IN_JAVA_INT_TEXT");
                }
                if (segment == index) {
                    if (!invocation.equals(currentInvocation)
                            && !invocationIndependentInteger(rendered)) {
                        return SplitSegment.gap(
                                "PRODUCER_INT_NOT_PORT_BACKED");
                    }
                    element.add(SplitPiece.integer(rendered, invocation));
                }
            }
            // Java keeps a final element only when it has characters.
            if (segment == index && !element.isEmpty()) {
                return SplitSegment.of(element);
            }
            return SplitSegment.gap(segment < index
                    ? "INDEX_BEYOND_CONCAT_ELEMENTS"
                    : "TRAILING_ELEMENT_MAY_BE_EMPTY");
        }

        /** An empty run between delimiters adds no characters. */
        private static void addText(List<SplitPiece> element, String text) {
            if (!text.isEmpty()) element.add(SplitPiece.text(text));
        }

        /**
         * Whether an int expression means the same thing in every
         */
        private boolean invocationIndependentInteger(
                JsonElement expression) {
            if (exactIntLiteral(expression) != null) return true;
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            return "SymbolExpression".equals(optionalString(object, "_type"))
                    && declaredSymbolicRoot(optionalString(object, "_exp"));
        }

        /** Lowers a split piece's int in the invocation that states it. */
        private Term integerPieceTerm(SplitPiece piece) {
            if (piece.integerInvocation == null
                    || piece.integerInvocation.equals(currentInvocation)) {
                return term(piece.integerSource, Sort.INT);
            }
            InvocationKey previous =
                    enterInvocation(piece.integerInvocation);
            try {
                return term(piece.integerSource, Sort.INT);
            } finally {
                restoreInvocation(previous);
            }
        }

        /** The int a {@code String.valueOf(int)} style part renders. */
        private JsonElement javaIntRenderingSource(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            JsonArray params = array(object, "_param_list");
            if (!"OpStrExpression".equals(optionalString(object, "_type"))
                    || !"toString".equals(optionalString(object, "_name"))
                    || optionalBool(object, "_is_not", false)
                    || params.size() != 1
                    || !isPrimitiveIntExpression(params.get(0))) {
                return null;
            }
            return params.get(0);
        }

        @Override
        public void assertJavaIntRange(Term integer) {
            String key = currentGuard + "\u0000" + integer.text;
            if (!javaIntRangeAssertions.add(key)) return;
            assertNamed("java_int_range_" + javaIntRangeAssertions.size(),
                    VmTermLowering.javaIntRange(integer.text));
        }

        @Override
        void assertJavaIntegralDomain(String term, Sort sort,
                                      String javaType, String identity) {
            if (sort != Sort.INT) return;
            JavaPrimitiveSmtSemantics.IntegralDomain domain =
                    JavaPrimitiveSmtSemantics.domainOfJavaType(javaType);
            if (domain == null || term == null || term.isEmpty()) return;
            String key = currentGuard + "\u0000" + term + "\u0000"
                    + domain.lower + "\u0000" + domain.upper;
            if (!javaIntegralRangeAssertions.add(key)) return;
            assertNamed("java_integral_domain_"
                            + javaIntegralRangeAssertions.size() + "_"
                            + smtName(firstNonBlank(identity, "value")),
                    VmTermLowering.integralRange(domain.lower, term,
                            domain.upper));
        }

        private String methodConstraint(JsonObject expression) {
            String name = optionalString(expression, "_name");
            if (isJavaParseInt(name) || isJavaSplitElement(name)) {
                boolean split = isJavaSplitElement(name);
                Term value = methodTerm(expression, "");
                Term result = term(expression.get("_res_exp"),
                        split ? Sort.STRING : Sort.INT);
                if (!split) {
                    return and(Arrays.asList(result.precondition,
                            value.precondition, "(= " + result.text + " "
                                    + value.text + ")"));
                }
                Term boxedPrefix = asValue(value, "", value.text, "");
                Term boxedResult = asValue(result, "", result.text, "");
                return and(Arrays.asList(boxedPrefix.precondition,
                        boxedResult.precondition, "(= " + boxedResult.text
                                + " " + boxedPrefix.text + ")"));
            }
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(name, "unknown"));
            return "false";
        }

        /** Lower every observed local path; boundary values are already merged. */
        private void regionSummary(RelationSummary selected) {
            lowerRegionCase(selected, selected.pathCaseView(), 0);
        }

        private void lowerRegionCase(RelationSummary summary,
                                     JsonObject item, int index) {
            JsonObject guardIr = object(item, "guard");
            if (!"PATH_CONDITION".equals(optionalString(guardIr, "kind"))) {
                heapGap("UnsupportedRegionGuard@" + summary.regionId()
                        + ":" + index);
                return;
            }
            String occurrence = firstNonBlank(optionalString(item, "occurrenceId"),
                    summary.occurrenceId());
            String owner = firstNonBlank(optionalString(item,
                            LocalCaseIdentity.OWNER),
                    LocalCaseIdentity.owner(
                            summary.immutableJson()));
            String baseSelector = LocalCaseIdentity.selector(owner);
            String observationSelector = optionalString(item,
                    SymbolicPropagationClosure.OBSERVATION_SELECTOR);
            String selector = firstNonBlank(observationSelector,
                    baseSelector);
            String loweredIdentity = firstNonBlank(observationSelector,
                    owner);
            if (!loweredRegionCaseOwners.add(loweredIdentity)) return;
            InvocationKey invocation = new InvocationKey(
                    summary.regionId(), occurrence);
            InvocationKey previousInvocation = enterInvocation(invocation);
            String previousScope = enterSymbolScope(loweredIdentity);
            String previousGuard = enterGuard(selector);
            String previousCaseSelector = currentCaseSelector;
            currentCaseSelector = baseSelector;
            try {
                declare(baseSelector, Sort.BOOL);
                declare(selector, Sort.BOOL);
                List<String> conditions = new ArrayList<>();
                for (JsonElement expression : array(guardIr, "conditions")) {
                    conditions.add(constraint(expression, "region "
                            + summary.regionId() + " case " + index));
                }
                assertNamed("case_selector_definition_"
                                + smtName(loweredIdentity),
                        "(=> " + selector + " " + and(conditions) + ")");
                casePartitions.computeIfAbsent(invocation,
                        ignored -> new LinkedHashSet<>()).add(baseSelector);
                if (!observationSelector.isEmpty()) {
                    observationsByBaseCase.computeIfAbsent(baseSelector,
                            ignored -> new LinkedHashSet<>()).add(
                            observationSelector);
                }
            } finally {
                currentCaseSelector = previousCaseSelector;
                restoreGuard(previousGuard);
                restoreSymbolScope(previousScope);
                restoreInvocation(previousInvocation);
            }
        }

        private void heapGap(String detail) {
            unsupported.add(detail);
        }

        /** Lowers one selected region occurrence's guarded relation. */
        private void lowerRelation(RelationSummary selection) {
            regionSummary(selection);
        }

        private void declare(String name, Sort sort) {
            addDeclaration("const:" + name,
                    "(declare-const " + name + " " + sort.smt + ")");
        }

        private void defineConstant(String name, Sort sort,
                                    String expression) {
            definitions.putIfAbsent(name, Term.of(expression, sort));
        }

        private void declareFunction(String name, List<Term> arguments,
                                     Sort result) {
            StringBuilder declaration = new StringBuilder("(declare-fun ")
                    .append(name).append(" (");
            for (int index = 0; index < arguments.size(); index++) {
                if (index > 0) declaration.append(' ');
                declaration.append(arguments.get(index).sort.smt);
            }
            declaration.append(") ").append(result.smt).append(')');
            addDeclaration("fun:" + name + ":" + declaration,
                    declaration.toString());
        }

        private void addDeclaration(String key, String declaration) {
            declarations.putIfAbsent(key, declaration);
        }

        private String assertNamed(String name, String expression) {
            String asserted = currentGuard.isEmpty() ? expression
                    : "(=> " + currentGuard + " " + expression + ")";
            String existing = assertedFormulas.get(asserted);
            if (existing != null) return existing;
            Integer groupedIndex = currentGuard.isEmpty()
                    || "true".equals(currentGuard) ? null
                    : guardedAssertionIndexes.get(expression);
            if (groupedIndex != null) {
                List<String> guards = guardedAssertionGuards.get(expression);
                guards.add(currentGuard);
                existing = guardedAssertionNames.get(expression);
                assertions.set(groupedIndex, namedAssertion(existing,
                        "(=> " + or(guards) + " " + expression + ")"));
                assertedFormulas.put(asserted, existing);
                return existing;
            }
            String unique = smtName(name);
            if (!assertionNames.add(unique)) {
                int suffix = 2;
                while (!assertionNames.add(unique + "_" + suffix)) {
                    suffix++;
                }
                unique = unique + "_" + suffix;
            }
            assertions.add(namedAssertion(unique, asserted));
            assertedFormulas.put(asserted, unique);
            if (!currentGuard.isEmpty() && !"true".equals(currentGuard)) {
                guardedAssertionIndexes.put(expression,
                        assertions.size() - 1);
                guardedAssertionGuards.put(expression,
                        new ArrayList<>(Collections.singleton(currentGuard)));
                guardedAssertionNames.put(expression, unique);
            }
            return unique;
        }

        /** Emits semantics shared by every activation of one stable term. */
        private String assertWithoutCurrentGuard(String name,
                                                 String expression) {
            String previousGuard = enterGuard("");
            try {
                return assertNamed(name, expression);
            } finally {
                restoreGuard(previousGuard);
            }
        }

        private static String namedAssertion(String name, String expression) {
            return "(assert (! " + expression + " :named " + name + "))";
        }

        private String unknownConstraint(String origin, JsonElement expression) {
            String key = "UnsupportedConstraint:" + origin + ":"
                    + (expression == null ? "null" : GSON.toJson(expression));
            unsupported.add(key);
            return "false";
        }

        private String scopedName(String prefix, String raw) {
            return prefix + "__" + scopeToken(currentSymbolScope) + "__"
                    + smtName(raw);
        }

        /**
         * Unsupported expressions never gain solver freedom.  Their gap is
         */
        private Term unsupportedTerm(Sort sort) {
            if (sort == Sort.BOOL) return Term.of("false", sort);
            if (sort == Sort.INT) return Term.of("0", sort);
            if (sort == Sort.FLOAT32 || sort == Sort.FLOAT64) {
                return Term.of(JavaPrimitiveSmtSemantics.floatingLiteral(
                        "0.0", floatingKind(sort)), sort);
            }
            if (sort == Sort.STRING) {
                return Term.nonNullString("\"\"", "true");
            }
            if (sort == Sort.REF) return Term.of("nullRef", sort);
            String nullValues = "((as const (Array Value Value))"
                    + " (VRef nullRef))";
            if (sort == Sort.MAP) {
                return Term.of("(mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " " + nullValues
                        + " ((as const (Array Int Value))"
                        + " (VRef nullRef))"
                        + " ((as const (Array Value Int)) (- 1)))", sort);
            }
            if (sort == Sort.VALUE) {
                return Term.of("(VRef nullRef)", sort);
            }
            String elements = "((as const (Array Int Value))"
                    + " (VRef nullRef))";
            return Term.of("(mkIndexedState 0 " + elements + ")", sort);
        }

        /** A readable prefix plus a reversible UTF-8 encoding avoids scope
         * collisions introduced by SMT identifier sanitization. */
        private String scopeToken(String scope) {
            String value = firstNonBlank(scope, "global");
            StringBuilder encoded = new StringBuilder();
            for (byte current : value.getBytes(StandardCharsets.UTF_8)) {
                encoded.append(String.format(Locale.ROOT, "%02x",
                        current & 0xff));
            }
            return smtName(value) + "__" + encoded;
        }

        /** One lowered merged consumer boundary and the arms it dispatches. */
        private static final class BoundaryDispatch {
            private final String mergeId;
            private final String familyKey;
            private final String mergedTerm;
            private final String unboundTerm;
            private final List<String> selectors;

            private BoundaryDispatch(String mergeId, String familyKey,
                                     String mergedTerm, String unboundTerm,
                                     List<String> selectors) {
                this.mergeId = mergeId;
                this.familyKey = familyKey;
                this.mergedTerm = mergedTerm;
                this.unboundTerm = unboundTerm;
                this.selectors = new ArrayList<>(selectors);
            }
        }

        /**
         * Records whether each merged consumer boundary dispatches totally.
         *
         * <p>A merge is total when this formula already forbids every arm
         * being false at once.  Two partitions say that unconditionally: a
         * region's case-observation partition, whose observations sum to its
         * base case selector, and a region instance's case-selector
         * partition, which sums to one.  A merge whose arms all sit inside
         * one of those cannot fall through -- the arm the model picks is an
         * arm the recording observed, and the value it carries is the value
         * the wire carried under that observation.</p>
         *
         * <p>A merge whose arms sit in neither may satisfy no arm and read
         * the fall-through term, which nothing pins.  That is the shape, not
         * an exception: since {@code fix/17897-model} most boundaries are
         * lowered as {@code ite(case_selector, rf_value, unbound_boundary)}
         * and are non-total by design -- 12 of 18 on hdfs-17960, both fatal
         * ones included -- because the selector that makes them total is
         * asserted elsewhere.  So this refuses nothing and pins nothing: it
         * publishes one {@link #BOUNDARY_DISPATCH_TOTALITY} row per merge and
         * leaves the reading to the model.  A non-total dispatch becomes a
         * finding only when a model actually falls through it --
         * {@code BooleanReachConditionExtractor.witnessFreedoms} raises
         * {@link WitnessLegitimacy#UNBOUND_WIRE_VALUE_TAKEN} for a model that
         * satisfies no arm while a consumer of the merged term stays
         * active.</p>
         */
        private void requireTotalBoundaryDispatch() {
            List<Set<String>> partitions = new ArrayList<>();
            for (Map.Entry<InvocationKey, Set<String>> entry
                    : casePartitions.entrySet()) {
                if (!entry.getValue().isEmpty()
                        && !faultControlledInstances.contains(
                                entry.getKey())) {
                    partitions.add(entry.getValue());
                }
            }
            for (BoundaryDispatch dispatch : boundaryDispatches) {
                Set<String> arms = new LinkedHashSet<>(dispatch.selectors);
                boolean total = false;
                for (Set<String> partition : partitions) {
                    if (dispatchIsTotalOver(arms, partition)) {
                        total = true;
                        break;
                    }
                }
                boundaryDispatchTotality.add(dispatchRow(dispatch, total));
            }
        }

        /**
         * Whether one case partition forces some arm of this dispatch true.
         *
         * <p>Exactly one case of the partition runs.  For that case the
         * dispatch has to carry an arm: either the case selector itself, or
         * -- when the composition split the case into replay-specific path
         * observations, whose indicators sum to the case selector's -- every
         * one of those observations.  A dispatch that carries only some of a
         * case's observations, or nothing for one case of the partition, is
         * satisfied by no arm whenever that case is the one that ran.</p>
         */
        private boolean dispatchIsTotalOver(Set<String> arms,
                                            Set<String> partition) {
            for (String caseSelector : partition) {
                if (arms.contains(caseSelector)) continue;
                Set<String> observations = observationsByBaseCase.get(
                        caseSelector);
                if (observations == null || observations.isEmpty()
                        || !arms.containsAll(observations)) {
                    return false;
                }
            }
            return !partition.isEmpty();
        }

        /**
         * Names the condition under which one associative read's null is the
         * untouched map's answer for a key nothing put.
         *
         * <p>Published as a Boolean definition so a witness reader asks the
         * solver rather than re-deriving the mutation chain: the solver
         * stage reads the term's value out of the model it already has.</p>
         */
        private void recordAbsentKeyDefault(String keyTerm,
                                            String absentCondition) {
            if (keyTerm == null || keyTerm.isEmpty()
                    || absentCondition == null
                    || absentCondition.isEmpty()) {
                return;
            }
            String identity = keyTerm + "\n" + absentCondition;
            if (!absentKeyDefaultKeys.add(identity)) return;
            String name = smtSymbols.mint(ABSENT_KEY_DEFAULT_PREFIX,
                    identity, 16);
            defineConstant(name, Sort.BOOL, absentCondition);
            JsonObject row = new JsonObject();
            row.addProperty("solverTerm", name);
            row.addProperty("keyTerm", keyTerm);
            // Which read this chain belongs to: a reader of a witness cares
            // about the read the target predicate tests, not about every
            // lookup in the slice that happens to miss.
            row.addProperty("readIdentity", readFromContext.isEmpty() ? ""
                    : readFromContext.peek());
            // The guard this chain was lowered under.  A container read
            // reached through a guarded read's arm is lowered with that arm's
            // selector in the guard, which is how a reader of a witness ties
            // the row to the read the target predicate tests when the read
            // identity itself was not in scope.
            row.addProperty("guard", currentGuard);
            absentKeyDefaults.add(row);
        }

        private JsonObject dispatchRow(BoundaryDispatch dispatch,
                                       boolean total) {
            JsonObject row = new JsonObject();
            row.addProperty("familyKey", dispatch.familyKey);
            row.addProperty("mergeId", dispatch.mergeId);
            row.addProperty("solverTerm", dispatch.mergedTerm);
            row.addProperty("unboundTerm", dispatch.unboundTerm);
            row.addProperty("armCount", dispatch.selectors.size());
            row.addProperty("totalDispatch", total);
            if (!total) {
                // The arms a reader of a witness has to evaluate: a model
                // that satisfies none of them read the unbound term, and
                // that is the wire value nothing bound.
                row.add("armSelectors", GSON.toJsonTree(dispatch.selectors));
            }
            return row;
        }

        private void finish() {
            for (Map.Entry<String, Set<String>> entry
                    : observationsByBaseCase.entrySet()) {
                if (entry.getValue().isEmpty()) continue;
                StringBuilder sum = new StringBuilder("(= (+");
                for (String observation : entry.getValue()) {
                    sum.append(" (ite ").append(observation)
                            .append(" 1 0)");
                }
                sum.append(") (ite ").append(entry.getKey())
                        .append(" 1 0))");
                assertNamed("region_case_observation_partition_"
                                + smtName(entry.getKey()),
                        sum.toString());
            }
            emitReferenceFieldRoutings();
            emitRequestFaultControl();
            requireTotalBoundaryDispatch();
            checkExecutionDivergence();
            checkUnlinkedWriterCases();
            for (Map.Entry<InvocationKey, Set<String>> entry
                    : casePartitions.entrySet()) {
                if (entry.getValue().isEmpty()) continue;
                // A fault-controlled occurrence is partitioned by its
                // predecessor's marker instead: see emitRequestFaultControl.
                if (faultControlledInstances.contains(entry.getKey())) {
                    continue;
                }
                StringBuilder sum = new StringBuilder("(= (+");
                for (String selector : entry.getValue()) {
                    sum.append(" (ite ").append(selector)
                            .append(" 1 0)");
                }
                sum.append(") 1)");
                assertNamed("region_case_selector_partition_"
                                + smtName(entry.getKey().regionId) + "_"
                                + smtName(entry.getKey().instanceId),
                        sum.toString());
            }
            if (!unsupported.isEmpty()) {
                assertions.add("(assert false) ; fail closed: unsupported");
            }
            assertions.add("(check-sat)");
        }

        private String render() {
            StringBuilder result = new StringBuilder();
            appendLines(result, preamble);
            result.append(System.lineSeparator());
            appendLines(result, declarations.values());
            List<String> ordered = orderedDefinitionNames();
            for (String name : ordered) {
                result.append("(declare-const ").append(name).append(' ')
                        .append(definitions.get(name).sort.smt).append(')')
                        .append(System.lineSeparator());
            }
            result.append(System.lineSeparator());
            for (String name : ordered) {
                result.append("(assert (= ").append(name).append(' ')
                        .append(definitions.get(name).text).append("))")
                        .append(System.lineSeparator());
            }
            result.append(System.lineSeparator());
            appendLines(result, assertions);
            return result.toString();
        }

        /**
         * Definitions stay acyclic, but are emitted as constants constrained
         * by exact equalities.  Z3 macro-expands zero-argument define-fun
         * bodies and recreates the exponential expression tree that the DAG
         * names removed.  An unconditional equality is the same definitional
         * extension while preserving sharing in the solver AST.
         */
        private List<String> orderedDefinitionNames() {
            Set<String> pending = new LinkedHashSet<>(definitions.keySet());
            List<String> result = new ArrayList<>();
            while (!pending.isEmpty()) {
                boolean progressed = false;
                for (String name : new ArrayList<>(pending)) {
                    Term definition = definitions.get(name);
                    if (referencesAny(definition.text, pending)) continue;
                    result.add(name);
                    pending.remove(name);
                    progressed = true;
                }
                if (!progressed) {
                    throw new IllegalStateException(
                            "cyclic SMT definitions: " + pending);
                }
            }
            return result;
        }

        private static boolean referencesAny(String expression,
                                             Set<String> symbols) {
            Matcher atoms = SMT_ATOM.matcher(expression);
            while (atoms.find()) {
                if (symbols.contains(atoms.group())) return true;
            }
            return false;
        }

        private static void appendLines(StringBuilder builder,
                                        Iterable<String> lines) {
            for (String line : lines) builder.append(line)
                    .append(System.lineSeparator());
        }
    }

    private static final class RawSymbol {
        private final String name;
        private final Sort sort;
        private String nullness = "";

        private RawSymbol(String name, Sort sort) {
            this.name = name;
            this.sort = sort;
        }
    }

    /** One statically decided piece of a split element. */
    private static final class SplitPiece {
        private final String text;
        private final JsonElement integerSource;
        /**
         * The invocation whose relation states {@link #integerSource}.  A
         */
        private final InvocationKey integerInvocation;

        private SplitPiece(String text, JsonElement integerSource,
                           InvocationKey integerInvocation) {
            this.text = text;
            this.integerSource = integerSource;
            this.integerInvocation = integerInvocation;
        }

        private static SplitPiece text(String text) {
            return new SplitPiece(text, null, null);
        }

        private static SplitPiece integer(JsonElement source,
                                                  InvocationKey invocation) {
            return new SplitPiece("", source, invocation);
        }
    }

    /** One split element decided statically, or the reason it was not. */
    private static final class SplitSegment {
        private final List<SplitPiece> pieces;
        private final String gap;

        private SplitSegment(List<SplitPiece> pieces, String gap) {
            this.pieces = pieces;
            this.gap = firstNonBlank(gap);
        }

        private static SplitSegment of(List<SplitPiece> pieces) {
            return new SplitSegment(
                    Collections.unmodifiableList(
                            new ArrayList<>(pieces)), "");
        }

        private static SplitSegment gap(String gap) {
            return new SplitSegment(null, gap);
        }

        /** An element between two adjacent delimiters is decided and empty. */
        private boolean complete() {
            return pieces != null && gap.isEmpty();
        }

        /** The int this element renders when it renders nothing else. */
        private SplitPiece singleIntegerPiece() {
            return pieces != null && pieces.size() == 1
                    && pieces.get(0).integerSource != null
                    ? pieces.get(0) : null;
        }
    }

    /** An expression together with the invocation whose relation states it. */
    private static final class ScopedExpression {
        private final JsonElement expression;
        private final InvocationKey invocation;

        private ScopedExpression(JsonElement expression,
                                 InvocationKey invocation) {
            this.expression = expression;
            this.invocation = invocation;
        }
    }

    public static final class Result {
        public final String smtLib;
        public final JsonObject manifest;

        private Result(String smtLib, JsonObject manifest) {
            this.smtLib = smtLib;
            this.manifest = manifest;
        }
    }

    public static final class Arguments {
        private Path fatalQueries;
        private final List<Path> summaries = new ArrayList<>();
        private Path output;
        private Path manifest;
        private Path runtimePlan;
        private String fatalRegion = "";
        private String occurrenceId = "";
        private String mappings = "";
        private long clockSkewMillis =
                ClockRootPhysics.DEFAULT_SKEW_MILLIS;
        /** Solver for {@link DeadCaseLemmas}; absent means no probing. */
        private Path z3;
        /** The execution task plan whose carrier declarations the lowered
         *  families are audited against; absent means no ledger. */
        private Path taskPlan;
        private long deadCaseArmRlimit = DeadCaseLemmas.DEFAULT_ARM_RLIMIT;

        public static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length
                        || argv[index + 1].startsWith("--")) {
                    throw new IllegalArgumentException(
                            "Expected --option value at " + argument);
                }
                String value = argv[++index];
                String key = argument.substring(2);
                if ("fatal-query".equals(key)) {
                    result.fatalQueries = Paths.get(value);
                } else if ("summaries".equals(key)) {
                    result.summaries.add(Paths.get(value));
                } else if ("output".equals(key)) {
                    result.output = Paths.get(value);
                } else if ("manifest".equals(key)) {
                    result.manifest = Paths.get(value);
                } else if ("runtime-plan".equals(key)) {
                    result.runtimePlan = Paths.get(value);
                } else if ("fatal-region".equals(key)) {
                    result.fatalRegion = firstNonBlank(value);
                } else if ("occurrence-id".equals(key)) {
                    result.occurrenceId = firstNonBlank(value);
                } else if ("mappings".equals(key)) {
                    result.mappings = firstNonBlank(value);
                } else if ("clock-skew-ms".equals(key)) {
                    result.clockSkewMillis = Long.parseLong(value);
                    if (result.clockSkewMillis < 0L) {
                        throw new IllegalArgumentException(
                                "--clock-skew-ms may not be negative");
                    }
                } else if ("z3".equals(key)) {
                    result.z3 = firstNonBlank(value).isEmpty() ? null
                            : Paths.get(value);
                } else if ("task-plan".equals(key)) {
                    result.taskPlan = firstNonBlank(value).isEmpty() ? null
                            : Paths.get(value);
                } else if ("dead-case-rlimit".equals(key)) {
                    result.deadCaseArmRlimit = Long.parseLong(value);
                    if (result.deadCaseArmRlimit < 0L) {
                        throw new IllegalArgumentException(
                                "--dead-case-rlimit may not be negative");
                    }
                } else {
                    throw new IllegalArgumentException(
                            "Unknown composer option: --" + key);
                }
            }
            if (result.fatalQueries == null || result.runtimePlan == null
                    || result.output == null) {
                throw new IllegalArgumentException(
                        "--fatal-query, --runtime-plan and --output are required");
            }
            if (result.manifest == null) {
                result.manifest = sibling(result.output,
                        "composed_smt_manifest.json");
            }
            return result;
        }
    }

    /** This encoder's own answer to "is this Java type a String?". */
    private static final Predicate<String> STRING_TYPED =
            type -> sortOfJava(type) == Sort.STRING;

    /**
     * Chooses the value sort for one VM guarded read.  The VM's generic
     * reference tag ({@code L}/{@code REF}) loses the declared field type,
     * while the replay metadata retains its JVM descriptor.  An exact
     * String descriptor proves the String refinement before arms are lowered;
     * other reference descriptors retain the REF representation.  Missing
     * metadata remains unsupported rather than being inferred from arms.
     */
    static Sort guardedReadSort(JsonObject node, Sort expected,
                                Collection<Sort> armSorts) {
        // A read whose value IS the container - the cursor a traversal
        // starts from, or a map view - answers the container's own sort.
        // The VM records the erased reference type L for such a read and
        // that erasure resolves to REF, which contradicts every arm: the
        // arms lower to the states they really are and the read was lowered
        // as a reference, so each one read as a sort conflict and the whole
        // traversal of a selected container was refused.
        Sort result = containerValuedReadSort(node);
        if (result == null) {
            result = sortOfJava(guardedReadJavaType(node));
            if (result == Sort.VALUE) result = expected;
        }

        Collection<Sort> candidates = armSorts == null
                ? Collections.emptyList() : armSorts;
        if ((result == null || result == Sort.VALUE)
                && !candidates.isEmpty()) {
            result = candidates.iterator().next();
        }
        for (Sort candidate : candidates) {
            if (candidate == null || candidate != result) return null;
        }
        return result;
    }

    /** The container sort a read of a whole container answers, or null. */
    private static Sort containerValuedReadSort(JsonObject node) {
        String shape = ContainerSmtCodec.containerValuedReadShape(node);
        return "INDEXED".equals(shape) ? Sort.ARRAY_VALUE
                : "ASSOCIATIVE".equals(shape) ? Sort.MAP : null;
    }

    private static String guardedReadJavaType(JsonObject node) {
        String encoded = optionalString(node, "_java_type");
        if (!erasedReferenceType(encoded)) return encoded;
        String descriptor = replayReadDescriptor(node);
        return sortOfJava(descriptor) == Sort.STRING ? descriptor : encoded;
    }

    private static String replayReadDescriptor(JsonObject node) {
        return optionalString(node, "replayReadDescriptor");
    }

    private static boolean erasedReferenceType(String type) {
        String normalized = firstNonBlank(type);
        return "L".equals(normalized)
                || "REF".equalsIgnoreCase(normalized);
    }

    private static Sort sortOfJava(String type) {
        if (type == null) return Sort.VALUE;
        String normalized = type.replace('.', '/');
        Sort container = containerSort(normalized);
        if (container != Sort.VALUE) return container;
        String className = normalized.startsWith("L")
                && normalized.endsWith(";") && normalized.length() > 2
                ? normalized.substring(1, normalized.length() - 1)
                : normalized;
        if ("Z".equals(type) || "boolean".equals(type)) return Sort.BOOL;
        if ("B".equals(type) || "C".equals(type)
                || "S".equals(type) || "I".equals(type)
                || "J".equals(type)
                || "byte".equals(type) || "char".equals(type)
                || "short".equals(type) || "int".equals(type)
                || "long".equals(type)) return Sort.INT;
        if ("F".equals(type) || "float".equals(type)) return Sort.FLOAT32;
        if ("D".equals(type) || "double".equals(type)) return Sort.FLOAT64;
        if ("java/lang/Boolean".equals(className)) return Sort.BOOL;
        if ("java/lang/Byte".equals(className)
                || "java/lang/Character".equals(className)
                || "java/lang/Short".equals(className)
                || "java/lang/Integer".equals(className)
                || "java/lang/Long".equals(className)) return Sort.INT;
        if ("java/lang/Float".equals(className)) return Sort.FLOAT32;
        if ("java/lang/Double".equals(className)) return Sort.FLOAT64;
        if ("String".equals(className)
                || "java/lang/String".equals(className)) return Sort.STRING;
        if (type.isEmpty()) return Sort.VALUE;
        return Sort.REF;
    }

    private static final Pattern FIELD_SIGNATURE = Pattern.compile(
            "^<[^:]+:\\s+([^()<>\\s]+)\\s+[^()<>\\s]+>(?:#.*)?$");

    /** The declared type in a Soot field signature, or an empty string. */
    private static String fieldSignatureJavaType(String signature) {
        Matcher field = FIELD_SIGNATURE.matcher(
                firstNonBlank(signature).trim());
        return field.matches() ? field.group(1) : "";
    }

    private static Sort containerSort(String type) {
        JavaContainerTypes.Shape shape = JavaContainerTypes.shape(type);
        return shape == JavaContainerTypes.Shape.ASSOCIATIVE
                ? Sort.MAP
                : shape == JavaContainerTypes.Shape.INDEXED
                ? Sort.ARRAY_VALUE : Sort.VALUE;
    }

    private static Sort castSort(String descriptor) {
        if ("Z".equals(descriptor) || "B".equals(descriptor)
                || "C".equals(descriptor) || "S".equals(descriptor)
                || "I".equals(descriptor) || "J".equals(descriptor)) {
            return Sort.INT;
        }
        if ("F".equals(descriptor)) return Sort.FLOAT32;
        if ("D".equals(descriptor)) return Sort.FLOAT64;
        if (descriptor.startsWith("L") || descriptor.startsWith("[")) {
            return Sort.REF;
        }
        return Sort.VALUE;
    }

    private static String smtName(String value) {
        String normalized = firstNonBlank(value, "anonymous")
                .replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) normalized = "n_" + normalized;
        return normalized;
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

}
