package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;

import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import edu.uva.liftlab.graphchecker.contract.JavaContainerTypes;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.MaterializationSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.IOException;
import java.math.BigInteger;
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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.IntegralWidth;
import edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.FloatingKind;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
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
 * Composes one selected fatal-region query with concolic summaries of its
 */
public final class ConcolicSmtComposer {
    /** Expression node the VM serializes one guarded read-from arm as. */
    static final String RECORDED_ITE_TYPE = "IteExpression";
    /** Prefix of the one value term of one guarded read. */
    static final String READ_VALUE_PREFIX = "rf_value__";
    static final String RECORDED_MODEL_UNEXPLAINED_READS =
            "RecordedModelUnexplainedReads";
    /** Manifest field of the causal-reach ranking of the fatal disjuncts. */
    static final String CAUSAL_WITNESS_PIN_FIELD = "causalWitnessPin";
    /** Authority of that ranking. */
    static final String CAUSAL_WITNESS_PIN_AUTHORITY =
            "FATAL_DISJUNCT_CROSS_NODE_REACH_V1";
    /** Name of the one assertion the ranking adds. */
    static final String CAUSAL_WITNESS_PIN_ASSERTION = "causal_witness_pin";
    /** One fatal disjunct is the whole query; a ranking over it is a no-op. */
    static final String PIN_SINGLE_DISJUNCT = "SINGLE_FATAL_DISJUNCT";
    /** No candidate read is keyed on a value a recorded handoff carried. */
    static final String PIN_NO_CROSS_NODE_REACH = "NO_CROSS_NODE_CAUSAL_REACH";
    /** Every disjunct ranks alike, so no disjunct is excluded. */
    static final String PIN_NO_DISCRIMINATION = "ALL_DISJUNCTS_RANK_ALIKE";
    /** The pin names the target-path case, which is the honest witness. */
    static final String PIN_KIND_TARGET_PATH_CASE = "TARGET_PATH_CASE";
    /** No case is named, so the pin falls back to the disjunct itself. */
    static final String PIN_KIND_FATAL_DISJUNCT = "FATAL_DISJUNCT_TERM";
    /** A reference to one recorded read value inside a lowered term. */
    private static final Pattern READ_VALUE_REFERENCE = Pattern.compile(
            Pattern.quote(READ_VALUE_PREFIX) + "([0-9]+)");

    /** The three authorities README {@code SMT-1} admits for one input. */
    static final String LOCAL_SYMBOLIC_ROOT = "LOCAL_SYMBOLIC_ROOT";
    static final String COMMUNICATION_LEAF = "COMMUNICATION_LEAF";
    static final String READ_FROM_ARM = "READ_FROM_ARM";
    /**
     * <p>README {@code SMT-1} admits a "known read-from arm" and nothing
     */
    static final String READ_FROM_ARM_UNKNOWN = "READ_FROM_ARM_UNKNOWN";
    /** A selected input several authorities claim; the lineage is not one. */
    static final String INPUT_AUTHORITY_AMBIGUOUS =
            "SelectedInputMultipleAuthorities";
    static final String SELECTED_STATE_READ_WITHOUT_AUTHORITY =
            "SelectedStateReadWithoutAuthority";

    /** A selected input term nothing in the run constrained. */
    static final String INPUT_AUTHORITY_MISSING =
            "SelectedInputWithoutAuthority";
    /** A read the model kept open, so no witness over it is final. */
    static final String SELECTED_READ_FROM_UNKNOWN_ARM =
            "SelectedReadFromUnknownArm";
    /** A selected edge the run only ever proposed. */
    static final String SELECTED_EDGE_CANDIDATE_ONLY =
            "SelectedEdgeCandidateOnly";
    /**
     * authority anyone ever asked for.  README {@code SMT-1} names that a
     */
    static final String UNDECLARED_SELECTED_PORT = "UndeclaredSelectedPort";
    /**
     * traced under - README {@code SMT-1}'s stale generation.
     */
    static final String PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY =
            "PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY";
    static final String UNSAT_CLOSURE_AUTHORITY =
            "SELECTED_CAUSAL_PATH_UNSAT_CLOSURE_V1";
    static final String UNSAT_CLOSURE_COMPLETE =
            "unsatClosureComplete";
    static final String UNSAT_CLOSURE_EVIDENCE =
            "unsatClosureEvidence";
    /** The target published no reach query this composition could start at. */
    static final String TARGET_REACH_QUERY_ABSENT =
            "TARGET_REACH_QUERY_ABSENT";
    /** The order domain holds no VALUE_HANDOFF edge for one export. */
    static final String HANDOFF_ORDER_UNRECORDED =
            "HANDOFF_SEND_BEFORE_RECEIVE_UNRECORDED";
    /** A handoff whose receiving port the region catalog does not declare. */
    static final String HANDOFF_PORT_UNDECLARED =
            VmHandoffEvidence.PORT_UNDECLARED;
    /** Free roots minted where the VM propagated no expression (C2). */
    static final String FREE_SYMBOLS_FIELD = "freeSymbols";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_FIELD =
            "configuredSourceMaterializations";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_KIND =
            "CONFIGURED_SYMBOLIC_SOURCE_MATERIALIZATION";
    static final String CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY =
            "COMPOSER_CONFIGURED_SOURCE_PHASE_TERM_V3";
    private static final String CASE_REGION_ID = "_caseRegionId";
    private static final Set<String> LOOP_AUTHORITY_REFUSALS =
            new LinkedHashSet<>(Arrays.asList(
                    BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES,
                    BoundedLoopComposition.LOOP_CLASSIFICATION_UNDECLARED,
                    BoundedLoopComposition.LOOP_CLASSIFICATION_DISAGREES,
                    LoopBoundPolicy.PATH_LOOP_REACHABILITY_MISSING,
                    LoopBoundPolicy.PATH_ARRAY_CARDINALITY_MISSING,
                    LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND));
    /** Whether this artifact may be accepted as the milestone result. */
    public static final String FINAL_STATUS = "finalStatus";
    /**
     * closed - README {@code GATE-1}'s second acceptance member.
     */
    public static final String PATH_SET_COMPLETE = "pathSetComplete";
    public static final String FINAL_READY = "FINAL_READY";
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
        String manifest = GSON.toJson(result.manifest);
        ArtifactIO.replace(arguments.manifest, manifest
                + System.lineSeparator());
        System.out.println(manifest);
    }

    public static Result compose(Arguments arguments) throws IOException {
        require(arguments.runtimePlan, "runtime plan");
        RuntimePlanArtifact runtimePlan = RuntimePlanArtifact.read(
                arguments.runtimePlan);

        if (arguments.fatalQueries == null
                || !Files.isRegularFile(arguments.fatalQueries)) {
            return refusedComposition(arguments, arguments.fatalQueries
                    + " does not exist: the target task published no reach"
                    + " query at all");
        }
        List<JsonObject> queryRows = ArtifactIO.readJsonl(
                arguments.fatalQueries);
        List<RelationSummary> summaries = new ArrayList<>();
        for (Path summaryFile : arguments.summaries) {
            int row = 0;
            for (JsonObject encoded : ArtifactIO.readJsonl(summaryFile)) {
                try {
                    // Target-reach summaries carry the branch relation and
                    if (ClosureGoalKind.fromTask(encoded)
                            .capturesTargetReach()) {
                        row++;
                        continue;
                    }
                    JsonObject coverage = object(encoded, "pathCoverage");
                    if (coverage.size() > 0) {
                        requireObservedCoverage(encoded, coverage);
                    }
                    RelationSummary summary =
                            RelationSummary.decode(encoded);
                    if (summary.regionId().isEmpty()
                            || summary.summaryId().isEmpty()) {
                        throw new IllegalArgumentException(
                                "summary identity is required");
                    }
                    summaries.add(summary);
                } catch (IllegalArgumentException malformed) {
                    throw new IOException("Malformed relation summary "
                            + summaryFile + " row " + row, malformed);
                }
                row++;
            }
        }
        List<JsonObject> regions = runtimePlan.regions();
        if (regions.isEmpty()) {
            throw new IOException("runtime plan has no region port catalog: "
                    + arguments.runtimePlan);
        }
        JsonObject fatal = selectFatalQuery(queryRows, arguments);
        if (fatal.size() == 0) {
            return refusedComposition(arguments, arguments.fatalQueries
                    + " exists with " + queryRows.size() + " row(s) and holds"
                    + " no ready reach query for region="
                    + arguments.fatalRegion + " occurrence="
                    + arguments.occurrenceId);
        }
        requireCanonicalFatalQuerySchema(fatal);
        String fatalSite = string(fatal, "targetSiteId");

        // Every path in this query is backed by the runtime's exact target
        // event.  The replay seed only fixes the selected branch identity; it
        PortIndex ports = PortIndex.from(regions);
        JsonObject rawContext = object(fatal, "symbolicContext");
        // Runtime-confirmed first-hop demands are authoritative.  CLI bounds
        // describe supplied summaries; they must never erase a demanded edge
        JsonObject resolutionContext = rawContext.deepCopy();
        boolean instanceScopedContext = resolutionContext.size() > 0
                && !string(resolutionContext, "occurrenceId").isEmpty();

        SummaryIndex summaryIndex = SummaryIndex.build(summaries);
        ResolvedSummaryGraph resolved = resolveSummaryGraph(fatal,
                resolutionContext, summaryIndex);
        Map<String, RelationSummary> loweredBySummary = new LinkedHashMap<>();
        for (RelationSummary relation
                : resolved.selectedSummaries.values()) {
            loweredBySummary.put(relation.summaryId(), relation);
        }
        List<RelationSummary> loweredRelations =
                new ArrayList<>(loweredBySummary.values());
        FatalAbsenceMutationWitness failureWitness =
                FatalAbsenceMutationWitness.resolve(fatal, resolved, ports);
        // Runtime identity can expose several aliases for one concrete
        JsonObject context = boundedContext(resolutionContext);
        Emitter emitter = new Emitter(ports,
                new InvocationKey(string(fatal, "regionId"),
                        string(resolutionContext, "occurrenceId")),
                failureWitness);
        emitter.begin(fatal);
        // A configured source may reach a selected downstream relation
        // through VM value handoff without making its own summary a lowered
        List<JsonObject> allCaseEvidenceRows = caseEvidenceRows(
                summaries, fatal);
        emitter.registerSymbolicSources(allCaseEvidenceRows);
        emitter.registerFreeSymbols(allCaseEvidenceRows);
        List<JsonObject> caseEvidenceRows = caseEvidenceRows(
                loweredRelations, fatal);
        emitter.registerExactSharedCarrierPorts(
                resolved.selectedEdges.values());
        if (!instanceScopedContext) {
            // Named against the target the context is missing for, like every
            // other composition gap: the row's kind is not its subject.
            emitter.unsupported.add("MissingTargetInstanceSymbolicContext:"
                    + firstNonBlank(string(fatal, "occurrenceId"), fatalSite,
                    string(fatal, "regionId")));
        }
        // A producer summary that is missing because that producer
        // under-replayed is a hard refusal in general, but off the causal cut
        // of a throw read pinned to its INITIAL map version (which reads no
        // producer output): it is deferred and downgraded to coverage only if
        // such a pin is emitted below.
        for (String gap : resolved.gaps) {
            if (gap.startsWith("MissingExactProducerSummary:")) {
                emitter.deferrableGap(gap, resolved.gapDetails.get(gap));
            } else {
                emitter.unsupported.add(gap);
                String detail = resolved.gapDetails.get(gap);
                if (detail != null) emitter.unsupportedDetail.put(gap, detail);
            }
        }

        // The bounded-loop prefixes of every selected occurrence, built here
        // rather than beside their own emission because the writer universe
        List<JsonObject> selectedSummaryRows = summaryRows(loweredRelations);
        List<JsonObject> selectedEvidenceRows =
                new ArrayList<>(selectedSummaryRows);
        List<JsonObject> scopedPlanRows = targetScopedPlanRows(
                runtimePlan.plans(), fatal,
                bindingRows(resolved.selectedEdges.values()),
                loweredRelations);
        List<JsonObject> loopBoundAuthorities =
                new ArrayList<>(selectedSummaryRows);
        loopBoundAuthorities.add(fatal);
        BoundedLoopComposition loops =
                BoundedLoopComposition.ofPlanRows(scopedPlanRows,
                        loopBoundAuthorities);
        for (RelationSummary relation : loweredRelations) {
            for (JsonElement element : relation.cases()) {
                if (element.isJsonObject()) {
                    loops.observeCase(relation.occurrenceId(),
                            element.getAsJsonObject());
                }
            }
        }
        observeFatalLoopCases(loops, fatal);

        // The recorded session model is lowered first because everything
        // after it may consume it: the target predicate itself can be a
        List<JsonObject> evidenceRows =
                new ArrayList<>(selectedEvidenceRows);
        for (JsonObject row : caseEvidenceRows) {
            if (row.has("_targetPathOrdinal")
                    && (!VmHandoffEvidence.eventsOf(row).isEmpty()
                    || object(row, SharedStateEvidence.RECORDED_FIELD)
                    .size() > 0)) {
                evidenceRows.add(row);
            }
        }
        RecordedSessionModel recorded = RecordedSessionModel.of(
                evidenceRows,
                fatalTargetTerms(fatal), string(fatal, "regionId"));
        emitRecordedSessionModel(emitter, recorded);
        // README SMT-1: a shared-state read the target performs is a
        reportUnauthorizedTargetStateReads(emitter, fatal,
                resolved.staticEdgeIds());
        List<String> fatalTerms = new ArrayList<>();
        List<String> fatalPathSelectors = new ArrayList<>();
        String previousFatalScope = emitter.enterSymbolScope("fatal:"
                + firstNonBlank(string(fatal, "occurrenceId"), fatalSite,
                string(fatal, "regionId"), "selected"));
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
                String pathSelector = RecordedSessionModel.caseSelector(
                        pathOwner);
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
                emitter.bindFatalPath(selectedPathOrdinal, selectedCase,
                        pathTerm);
                fatalPathSelectors.add(selectedCase);
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.bindTargetReachAssertion();
        emitter.bindFatalPathAssertion(or(fatalTerms));
        emitter.bindTargetPathPartition(fatalPathSelectors);

        for (RelationSummary selection : loweredRelations) {
            emitter.lowerRelation(selection);
        }
        emitter.mergeEdgeBindings(resolved.selectedEdges.values());
        emitter.mergeVmHandoffs(caseEvidenceRows, allCaseEvidenceRows,
                loops, recorded);
        emitter.finishRecordedReadExistence();
        emitter.finishFatalAbsenceMutationWitness();
        emitter.finishBindings();
        // Ranked last of the failure-directed passes: it reads the key of
        // every recorded read and every handoff the merge admitted, so it
        // can only be decided once both are in the formula.
        emitter.finishCausalWitnessPin();
        auditDroppedEdgeEvidence(emitter, ports,
                resolved.valueBindingRows());
        // README SMT-1's stale generation, decided before the artifact is
        List<JsonObject> sourceEpochDivergences = sourceEpochDivergences(
                resolved.selectedEdges.values());
        for (JsonObject divergence : sourceEpochDivergences) {
            emitter.unsupported.add(PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY
                    + ":" + string(divergence, "subject"));
        }
        // Resolve the deferred soft gaps BEFORE the formula is finished so
        // that finish() sees them: without an admitted guarded map read they
        // are the hard refusals they always were and must fail the formula
        // closed; with one they are off its causal cut and are downgraded to
        // coverage (below).
        if (!emitter.guardedMapReadAdmitted) {
            emitter.unsupported.addAll(emitter.softGaps);
            emitter.unsupportedDetail.putAll(emitter.softGapDetail);
        }
        emitter.finish();
        String composedSmt = emitter.render();

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", fatalSite);
        manifest.add("resolvedEdgeBindings",
                GSON.toJsonTree(resolved.staticEdgeIds()));
        manifest.add("portOccurrences", emitter.portOccurrences());
        manifest.add("selectedInputLedger", emitter.selectedInputLedger());
        // Present whenever the pass ran, so an empty ledger from a run that
        // checked nothing stays distinguishable from one that found nothing.
        manifest.add("selectedInputLedgerAudit",
                emitter.selectedInputLedgerAudit());
        manifest.add("fatalPathAssertion",
                emitter.fatalPathAssertion());
        manifest.add(CAUSAL_WITNESS_PIN_FIELD,
                emitter.causalWitnessPinLedger());
        manifest.add("targetReachLedger", emitter.targetReachLedger());
        manifest.add(FREE_SYMBOLS_FIELD, emitter.freeSymbolLedger());
        manifest.add(CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                emitter.configuredSourceMaterializationLedger());
        manifest.add("recordedSessionModel", recorded.manifest());
        manifest.add(BoundedLoopComposition.MANIFEST_FIELD,
                loops.manifest());
        manifest.add("recordedValueBindings",
                emitter.recordedValueBindingLedger());
        List<JsonObject> selectedBindings = bindingRows(
                resolved.selectedEdges.values());
        // README's rule for the sibling fact - "an empty selection: nothing
        boolean recordedReadsUnexplained =
                recorded.recordedReadCount() > 0
                        && selectedBindings.isEmpty()
                        && recorded.choiceReadEvents().isEmpty();
        List<JsonObject> coverage = new ArrayList<>(recorded.coverageGaps());
        coverage.addAll(emitter.recordedCoverage);
        coverage.addAll(loops.gaps());
        if (recordedReadsUnexplained) {
            // Named in the coverage channel and not in `unsupported`: that
            // one feeds `state`, and whether the composition is solvable is a
            coverage.add(CoverageDivergence.of(CoverageDivergence.Kind.FLOW,
                    RECORDED_MODEL_UNEXPLAINED_READS,
                    String.valueOf(recorded.recordedReadCount()),
                    "the recorded model holds "
                            + recorded.recordedReadCount()
                            + " read(s) and states no read-from arm or"
                            + " guarded choice for any of them, so its"
                            + " completeness claim examined nothing"));
        }
        // A writer the trace retained as a candidate and nothing resolved is
        // not a recorded read-from relation, and neither is one whose read
        coverage.addAll(RecordedReadFrom.provenanceGaps(
                resolved.valueBindingRows()));
        coverage.addAll(sourceEpochDivergences);
        // Gaps the target query named while being built best effort.  They
        // are coverage facts about the query this composition consumes, so
        for (JsonElement element : array(fatal, "coverageGaps")) {
            if (element.isJsonObject()) {
                coverage.add(element.getAsJsonObject().deepCopy());
            }
        }
        // An admitted guarded map read downgrades its off-cut soft gaps to
        // named coverage gaps (the unsupported/hard decision was already made
        // before finish(), above).
        if (emitter.guardedMapReadAdmitted) {
            for (String subject : emitter.softGaps) {
                coverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        "SAT_WITNESS_OFF_CUT_GAP", subject,
                        firstNonBlank(emitter.softGapDetail.get(subject),
                                "off the admitted throw read's causal cut")));
            }
        }
        JsonArray coverageGaps = new JsonArray();
        for (JsonObject gap : coverage) coverageGaps.add(gap);
        manifest.add("coverageGaps", coverageGaps);
        // The formula is emitted whenever a usable target relation remains;
        // the coverage state says how much of the model the run still
        manifest.add("divergence", CoverageDivergence.summary(coverage,
                emitter.unsupported.isEmpty()));
        JsonArray gaps = new JsonArray();
        appendGaps(gaps, "COMPOSITION_GAP", emitter.unsupported,
                emitter.unsupportedDetail);
        manifest.add("gaps", gaps);
        manifest.addProperty("state", gaps.size() == 0
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        // A recorded model that keeps an unknown-writer arm or an unclosed
        boolean recordedModelComplete = !recordedReadsUnexplained
                && !recorded.partial()
                && emitter.unsupported.isEmpty()
                && !retainsUnknownArm(resolved.valueBindingRows());
        manifest.addProperty("recordedModelComplete",
                recordedModelComplete);
        // README GATE-1's decision, stated as its own member.
        AcceptanceGate gate = new AcceptanceGate();
        for (JsonElement element : gaps) {
            JsonObject gap = element.getAsJsonObject();
            gate.refuse(string(gap, "kind"), string(gap, "subject"),
                    string(gap, "detail"));
        }
        // README SMT-1's stale generation, as an acceptance decision.  A
        // exactly the implicit merge STATE-1 forbids - the NameNode's map
        for (JsonObject divergence : sourceEpochDivergences) {
            gate.refuse(PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY,
                    string(divergence, "subject"),
                    string(divergence, "detail"));
        }
        // Completion criterion 5, and README LOOP-1's "a missing
        Set<String> selectedScopeMethods =
                selectedScopeMethods(loweredRelations, fatal);
        for (JsonObject gap : loops.gaps()) {
            String reason = string(gap, "reason");
            if (!loopAuthorityRefuses(reason,
                    string(gap, "subject"), selectedScopeMethods)) {
                continue;
            }
            // A retained loop outside every selected relation's slice is a
            gate.refuse(reason, string(gap, "subject"),
                    string(gap, "detail"));
        }
        // The read-from half: a selected read whose writer set the trace only
        // ever proposed, and one that kept the arm no writer answers. Both
        for (JsonObject gap : RecordedReadFrom.provenanceGaps(
                resolved.valueBindingRows())) {
            gate.refuse(integer(gap, "statusCode", 0)
                            == SharedStateEvidence.UNKNOWN_WRITER
                            ? SELECTED_READ_FROM_UNKNOWN_ARM
                            : SELECTED_EDGE_CANDIDATE_ONLY,
                    firstNonBlank(string(gap, "locationKey"),
                            string(gap, "edgeId")),
                    string(gap, "detail"));
        }
        // README STATE-1's other half.  The loop above ranges over selected
        for (JsonObject refusal : openGuardedReadRefusals(emitter, recorded)) {
            gate.refuse(SELECTED_READ_FROM_UNKNOWN_ARM,
                    string(refusal, "subject"), string(refusal, "detail"));
        }
        boolean finalReady = gate.size() == 0;
        manifest.addProperty(FINAL_STATUS, finalReady
                ? FINAL_READY : FINAL_REFUSED);
        // README GATE-1's acceptance check reads this member beside the
        // status, so it is published for every composition rather than only
        manifest.addProperty(PATH_SET_COMPLETE,
                pathSetComplete(loweredRelations, fatal));
        manifest.add("finalStatusRefusals", gate.refusals);
        JsonObject unsatClosure = unsatClosureEvidence(
                recordedModelComplete, loweredRelations, fatal, finalReady,
                coverage.size());
        manifest.addProperty(UNSAT_CLOSURE_COMPLETE,
                bool(unsatClosure, UNSAT_CLOSURE_COMPLETE, false));
        manifest.add(UNSAT_CLOSURE_EVIDENCE, unsatClosure);
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                composedSmt.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        // Everything the causal graph needs is now in this manifest, and it
        // is the same everything the formula was lowered from.  Assembling it
        manifest.add(CanonicalSessionModel.MANIFEST_FIELD,
                CanonicalSessionModel.of(manifest,
                        localRelations(loweredRelations),
                        resolvedEdgeEndpoints(resolved.selectedEdges
                                .values()),
                        firstNonBlank(
                                string(resolutionContext, "occurrenceId"),
                                string(fatal, "occurrenceId"))));
        return new Result(composedSmt, manifest);
    }


    /**
     * is published as the Composer's own refusal - the layer README
     * {@code GATE-1} makes the sole owner of that decision - rather than
     */
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
        manifest.addProperty("recordedModelComplete", false);
        // Nothing was lowered, so no path set was ranged over and none can be
        // called complete.  README GATE-1's check reads the member on every
        manifest.addProperty(PATH_SET_COMPLETE, false);
        manifest.add("portOccurrences", new JsonArray());
        manifest.add(CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                new JsonArray());
        // Nothing was lowered, so nothing was read without lineage.
        manifest.add(FREE_SYMBOLS_FIELD, new JsonArray());
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
     * The endpoints of the resolved trace edges.
     */
    private static JsonArray resolvedEdgeEndpoints(
            Collection<ResolvedEdge> edges) {
        JsonArray rows = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        for (ResolvedEdge edge : edges) {
            String edgeId = string(edge.binding, "edgeId");
            if (edgeId.isEmpty() || !seen.add(edgeId)) continue;
            rows.add(CanonicalSessionModel.resolvedEdge(edgeId,
                    bindingSourceInstance(edge.binding),
                    bindingTargetInstance(edge.binding),
                    edge.topologyOnly));
        }
        return rows;
    }

    /**
     * The selected local region relations, as the canonical model holds them.
     */
    private static JsonArray localRelations(
            Collection<RelationSummary> selected) {
        JsonArray relations = new JsonArray();
        for (RelationSummary summary : selected) {
            relations.add(CanonicalSessionModel.relation(
                    summary.occurrenceId(), summary.sourceKey()));
        }
        return relations;
    }

    /**
     * States whether an unsatisfiable selected formula closes every path set
     */
    static JsonObject unsatClosureEvidence(
            boolean recordedModelComplete,
            Collection<RelationSummary> selected,
            JsonObject fatal, boolean finalReady,
            int compositionCoverageGapCount) {
        JsonArray partialRelations = partialProducerSummaryIds(selected);
        int targetCoverageGapCount = array(fatal, "coverageGaps").size();
        boolean producerPathsClosed = partialRelations.size() == 0;
        boolean targetPathsClosed = targetPathsClosed(fatal);
        boolean compositionCoverageClosed = compositionCoverageGapCount == 0;
        boolean complete = recordedModelComplete && producerPathsClosed
                && targetPathsClosed && compositionCoverageClosed
                && finalReady;
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        evidence.addProperty("authority", UNSAT_CLOSURE_AUTHORITY);
        evidence.addProperty("recordedModelComplete",
                recordedModelComplete);
        evidence.addProperty("producerPathsClosed", producerPathsClosed);
        evidence.addProperty("targetPathsClosed", targetPathsClosed);
        evidence.addProperty("compositionCoverageClosed",
                compositionCoverageClosed);
        evidence.addProperty("finalStatusReady", finalReady);
        evidence.addProperty("targetCoverageGapCount",
                targetCoverageGapCount);
        evidence.addProperty("compositionCoverageGapCount",
                compositionCoverageGapCount);
        evidence.add("partialProducerSummaryIds", partialRelations);
        evidence.addProperty(UNSAT_CLOSURE_COMPLETE, complete);
        return evidence;
    }

    /**
     * Both the UNSAT closure claim and README {@code GATE-1}'s published
     */
    private static JsonArray partialProducerSummaryIds(
            Collection<RelationSummary> selected) {
        JsonArray partial = new JsonArray();
        for (RelationSummary summary : selected == null
                ? Collections.<RelationSummary>emptyList() : selected) {
            if (!"CLOSED".equals(summary.pathCoverageState())) {
                partial.add(summary.summaryId());
            }
        }
        return partial;
    }

    /** Whether the target query named no gap in its own path set. */
    private static boolean targetPathsClosed(JsonObject fatal) {
        return array(fatal, "coverageGaps").size() == 0;
    }

    /**
     * README {@code GATE-1}'s {@code pathSetComplete}.
     */
    private static boolean pathSetComplete(
            Collection<RelationSummary> selected, JsonObject fatal) {
        return partialProducerSummaryIds(selected).size() == 0
                && targetPathsClosed(fatal);
    }

    /**
     * Lowers the recorded session model into the formula.
     */
    private static void emitRecordedSessionModel(
            Emitter emitter, RecordedSessionModel recorded) {
        emitter.recorded = recorded;
        emitter.recordedChoiceReads.addAll(recorded.choiceReadEvents());
        for (RecordedSessionModel.OrderVariable position
                : recorded.positions()) {
            emitter.declareBoundedPosition(position.name, position.bound);
        }
        for (String selector : recorded.selectors()) {
            emitter.declare(selector, Sort.BOOL);
        }
        // Case-owned state/order assertions are emitted before relation
        // guards are lowered.  Declare the shared selector names now; the
        for (String selector : recorded.caseSelectors()) {
            emitter.declare(selector, Sort.BOOL);
        }
        // Recorded event existence is declared beside the selectors it is
        // implied by. Target existence is not part of this state model: it
        for (String existence : recorded.existenceSymbols()) {
            emitter.declare(existence, Sort.BOOL);
        }
        for (RecordedSessionModel.OrderAssertion assertion
                : recorded.assertions()) {
            emitter.assertNamed(assertion.name,
                    assertion.caseGuard.isEmpty() ? assertion.term
                            : "(=> " + assertion.caseGuard + " "
                            + assertion.term + ")");
        }
        // A cyclic relation is not a partial order, so no order fact read out
        // of it is sound.  The composition refuses it here, before a solver
        if (!recorded.orderDomainFault().isEmpty()) {
            emitter.unsupported.add("RecordedOrderDomainCycle:"
                    + recorded.orderDomainFault());
        }
        emitter.catalogingRecordedReads = true;
        try {
            for (Map.Entry<Long, JsonObject> entry
                    : recorded.guardedReads().entrySet()) {
                emitter.guardedReadTerm(entry.getValue(), null);
            }
        } finally {
            emitter.catalogingRecordedReads = false;
        }
    }

    /**
     * Names every selected edge whose producer occurrence belongs to a source
     */
    private static List<JsonObject> sourceEpochDivergences(
            Collection<ResolvedEdge> edges) {
        List<JsonObject> divergences = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (ResolvedEdge edge : edges) {
            JsonObject divergence = sourceEpochDivergence(
                    edge.summary.sourceKey(), edge.binding);
            if (divergence.size() == 0
                    || !seen.add(string(divergence, "subject") + "\n"
                    + string(edge.binding, "fromOccurrenceId"))) {
                continue;
            }
            divergences.add(divergence);
        }
        return divergences;
    }

    /** One producer binding's source/epoch check; empty when it agrees. */
    static JsonObject sourceEpochDivergence(String sourceKey,
                                            JsonObject binding) {
        String occurrence = string(binding, "fromOccurrenceId");
        if (sourceKey == null || sourceKey.isEmpty() || occurrence.isEmpty()
                || !occurrence.contains("/region/")
                || occurrence.startsWith(sourceKey + "/region/")) {
            return new JsonObject();
        }
        return CoverageDivergence.of(
                CoverageDivergence.Kind.SOURCE_EPOCH,
                PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY,
                string(binding, "edgeId"),
                "producer occurrence " + occurrence
                        + " is not an occurrence of source " + sourceKey);
    }

    /**
     * The definition methods of every lowered producer plus the fatal target.
     */
    private static Set<String> selectedScopeMethods(
            List<RelationSummary> lowered, JsonObject fatal) {
        Set<String> methods = new LinkedHashSet<>();
        for (RelationSummary relation : lowered) {
            methods.addAll(relation.outputClosure().executionScope().methods());
        }
        return withTargetScopeMethod(methods, fatal);
    }

    /** Adds each fatal replay path's own loop-count vector to the audit. */
    static void observeFatalLoopCases(BoundedLoopComposition loops,
                                      JsonObject fatal) {
        String occurrence = string(fatal, "occurrenceId");
        JsonArray paths = array(fatal, "paths");
        for (int index = 0; index < paths.size(); index++) {
            if (!paths.get(index).isJsonObject()) continue;
            JsonObject path = paths.get(index).getAsJsonObject().deepCopy();
            if (string(path, "caseId").isEmpty()) {
                path.addProperty("caseId", "TARGET_PATH." + index);
            }
            loops.observeCase(occurrence, path);
        }
    }





    static Set<String> withTargetScopeMethod(
            Set<String> producerMethods, JsonObject fatal) {
        Set<String> methods = new LinkedHashSet<>(producerMethods);
        methods.addAll(LoopBoundPolicy.siteMethods(
                string(fatal, "targetSiteId")));
        return methods;
    }

    /**
     * Whether a loop gap's subject names a control site in one of
     */
    static boolean touchesSelectedScope(String subject,
                                        Set<String> scopeMethods) {
        if (scopeMethods.isEmpty()) return true;
        // A gap subject is occurrence + site (+ case), one per line, and each
        // site may be a nest.  Parsed, never scanned: a scan for <...> reads
        // "void <init>(..)" as the method "<init>", which is in no slice, so
        // every loop-authority gap inside a constructor stopped deciding.
        for (String part : subject.split("\\n")) {
            for (String method : LoopBoundPolicy.siteMethods(part)) {
                if (scopeMethods.contains(method)) return true;
            }
        }
        return false;
    }

    /** The exact loop-authority rule the final gate applies. */
    static boolean loopAuthorityRefuses(String reason,
                                                String subject,
                                                Set<String> scopeMethods) {
        return LOOP_AUTHORITY_REFUSALS.contains(reason)
                && touchesSelectedScope(subject, scopeMethods);
    }

    private static final class AcceptanceGate {
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
    }

    /**
     * Whether any composed binding still admits a writer nobody recorded.
     */
    private static boolean retainsUnknownArm(Collection<JsonObject> rows) {
        for (JsonObject binding : rows) {
            if (!string(binding, RecordedReadFrom.EDGE_UNKNOWN_ARM)
                    .isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /**
     * <p>README {@code STATE-1}'s acceptance half is stated over selected
     * never produced - the exact thing {@code SMT-1} forbids in an accepted
     */
    private static List<JsonObject> openGuardedReadRefusals(
            Emitter emitter, RecordedSessionModel recorded) {
        List<JsonObject> refusals = new ArrayList<>();
        Map<Long, BoundedWriterUniverse> universes =
                recorded.boundedWriterUniverses();
        for (Long readEventId : emitter.guardedReadTerms.keySet()) {
            Set<String> cases = emitter.readCaseGuards.get(readEventId);
            if (cases == null || cases.isEmpty()) continue;
            // A read whose fail-open unknown arm was excluded (VM-reported
            // writer set complete) holds no unknown arm in the emitted formula,
            // so the universe's conservative "still admits an unknown writer"
            // no longer describes what was lowered.
            if (emitter.unknownArmExcludedReads.contains(readEventId)) continue;
            BoundedWriterUniverse universe = universes.get(readEventId);
            if (universe == null || !universe.retainsUnknownArm()) continue;
            JsonObject refusal = new JsonObject();
            refusal.addProperty("subject", firstNonBlank(
                    universe.locationKey(), String.valueOf(readEventId)));
            refusal.addProperty("detail", "guarded read " + readEventId
                    + " is consumed by the selected witness and its bounded"
                    + " writer universe still admits an unknown writer");
            refusals.add(refusal);
        }
        return refusals;
    }

    /** The binding rows of the resolved edges. */
    private static List<JsonObject> bindingRows(
            Collection<ResolvedEdge> edges) {
        List<JsonObject> rows = new ArrayList<>();
        for (ResolvedEdge edge : edges) rows.add(edge.binding);
        return rows;
    }

    /**
     * Names every state read the target performs that reached the formula
     */
    private static void reportUnauthorizedTargetStateReads(
            Emitter emitter, JsonObject fatal, Set<String> loweredEdges) {
        for (JsonElement element : array(fatal, "selectedTargetBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (string(binding, RecordedReadFrom.EDGE_FIELD).isEmpty()) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (!edgeId.isEmpty() && loweredEdges.contains(edgeId)) continue;
            String provenance = firstNonBlank(
                    string(binding, RecordedReadFrom.EDGE_PROVENANCE),
                    "NO_RECORDED_EVIDENCE");
            if (RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                    || RecordedReadFrom.PROVENANCE_GUARDED.equals(
                    provenance)) {
                continue;
            }
            // A candidate the recorded session ruled out is not a missing
            // authority when the same session also states what the read did
            // take.  An exact resolution over a writer set the VM reported
            // complete IS the read's authority; this trace edge is then the
            // alternative that resolution excludes, and is reported in the
            // coverage channel exactly as every other excluded writer is.
            if (string(binding, RecordedReadFrom.EDGE_UNKNOWN_ARM).isEmpty()
                    && emitter.recordedReadResolvedExactly(
                            string(binding, "locationKey"),
                            string(binding, "toOccurrenceId"))
                    && emitter.skipExcludedWriter(binding)) {
                continue;
            }
            String gap = string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE_GAP);
            // When the target's map read has been admitted directly as a
            // pinned SAT witness (its removeExpiredKeys REMOVE_IF chain
            // materialized), the separate read-from-edge authority for that
            // same field is off the pinned witness's cut and is deferred to a
            // coverage gap; without a pin it is the hard refusal it always
            // was.
            emitter.deferrableGap(SELECTED_STATE_READ_WITHOUT_AUTHORITY
                    + ":" + firstNonBlank(string(binding, "locationKey"),
                    string(binding, RecordedReadFrom.EDGE_FIELD), edgeId)
                    + ":" + provenance,
                    "the target reads "
                    + firstNonBlank(string(binding,
                            RecordedReadFrom.EDGE_FIELD), edgeId)
                    + " and the trace offers the writer in "
                    + firstNonBlank(string(binding, "fromOccurrenceId"),
                            string(binding, "fromRegion"), "(unnamed)")
                    + " over edge " + edgeId
                    + ", but the recorded session states "
                    + provenance + " for that writer"
                    + (gap.isEmpty() ? "" : " (" + gap + ")")
                    + " on session location "
                    + firstNonBlank(string(binding, "sessionLocationKey"),
                            "(unnamed)")
                    + ", so this read reaches the formula with no read-from"
                    + " arm and no guarded choice");
        }
    }

    /** The selected summaries' rows, as the recorded model reads them. */
    private static List<JsonObject> summaryRows(
            Collection<RelationSummary> selected) {
        List<JsonObject> rows = new ArrayList<>();
        for (RelationSummary summary : selected) {
            JsonObject row = summary.toJson();
            // Normalize already-published merged summaries that predate the
            // explicit regionId field. The output closure is the canonical
            row.addProperty("regionId", summary.regionId());
            rows.add(row);
        }
        return rows;
    }


    private static List<JsonObject> caseEvidenceRows(
            Collection<RelationSummary> relations, JsonObject fatal) {
        List<JsonObject> rows = new ArrayList<>();
        for (RelationSummary relation : relations == null
                ? Collections.<RelationSummary>emptyList() : relations) {
            JsonArray cases = relation.cases();
            for (int index = 0; index < cases.size(); index++) {
                JsonElement element = cases.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject item = element.getAsJsonObject();
                // OCC-1: a case states which occurrence of the relation's
                // address it is.  The receiving occurrence, the case owner and
                // therefore the recorded-event scope, the SMT selector and the
                // VM-handoff producer key are all derived from it, so two
                // activations that both really ran stay two.
                String stated = string(item, "occurrenceId");
                String caseOccurrence = stated.isEmpty()
                        ? relation.occurrenceId() : stated;
                item.addProperty("toOccurrenceId", caseOccurrence);
                item.addProperty(CASE_REGION_ID, relation.regionId());
                item.addProperty("sourceKey", relation.sourceKey());
                String owner = RecordedSessionModel.caseOwner(
                        relation.regionId(), caseOccurrence,
                        string(item, "caseId"), index);
                retainCaseOwner(item, owner);
                rows.add(item);
            }
        }
        if (fatal != null) {
            JsonObject target = fatal.deepCopy();
            target.addProperty("toOccurrenceId",
                    string(fatal, "occurrenceId"));
            rows.add(target);
            JsonArray paths = array(fatal, "paths");
            for (int index = 0; index < paths.size(); index++) {
                if (!paths.get(index).isJsonObject()) continue;
                JsonObject path = paths.get(index).getAsJsonObject()
                        .deepCopy();
                // Wave 3 C2: a path whose only evidence is a free symbol
                // is a case, not an empty row.  Skipping it here dropped it
                // from the lowering AND from the free-symbol census, so the
                // one thing it had to report never reached the manifest.
                if (VmHandoffEvidence.eventsOf(path).isEmpty()
                        && object(path, SharedStateEvidence.RECORDED_FIELD)
                        .size() == 0
                        && SymbolicSourceEvidence.freeSymbolsOf(path)
                        .isEmpty()
                        && array(path, SymbolicSourceEvidence.FIELD)
                        .size() == 0) {
                    continue;
                }
                path.addProperty("toOccurrenceId",
                        string(fatal, "occurrenceId"));
                path.addProperty(CASE_REGION_ID,
                        string(fatal, "regionId"));
                path.addProperty("regionId", string(fatal, "regionId"));
                path.addProperty("occurrenceId",
                        string(fatal, "occurrenceId"));
                path.addProperty("sourceKey", string(fatal, "sourceKey"));
                path.addProperty("_targetPathOrdinal", index);
                retainCaseOwner(path, targetPathCaseOwner(fatal, path,
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
        return RecordedSessionModel.caseOwner(
                string(fatal, "regionId"), string(fatal, "occurrenceId"),
                firstNonBlank(string(path, "caseId"),
                        "TARGET_PATH." + ordinal), ordinal);
    }

    /**
     * Wave 3 C1/C3: one raw VM symbol denotes one SMT root.  A configured
     * source is keyed by the symbol the VM minted, not by the source phase -
     * every entry of a mint site now mints its own symbol, and two entries
     * that share a phase are two roots, not one.
     */
    private static String symbolScopeKey(String raw, String scope,
                                         String sourceIdentity) {
        return sourceIdentity == null
                ? firstNonBlank(scope, "global") + "\u0000" + raw
                : "configured-source\u0000" + raw;
    }


    /** Whether one expression node is an associative container read. */
    private static boolean isAssociativeRead(JsonObject node) {
        return ContainerSmtCodec.EXPRESSION_TYPE.equals(string(node, "_type"))
                && "ASSOCIATIVE".equals(string(node, "shape"))
                && "READ".equals(string(node, "operation"));
    }

    /**
     * The raw VM symbols standing in the <em>key</em> position of one
     * recorded read-from arm.
     *
     * <p>An arm serializes the whole state the reader saw - the container
     * the writer left, every conditional removal above it, and the read
     * itself.  Only the shallowest associative reads are the read the arm
     * <em>is</em>; anything deeper belongs to the state expression that
     * built the container, and its key is a different question.  So the
     * walk stops at the first level that carries one, and answers with the
     * symbols of that level's key arguments alone.</p>
     */
    private static Set<String> associativeReadKeySymbols(JsonElement arm) {
        Set<String> result = new LinkedHashSet<>();
        List<JsonElement> level = new ArrayList<>();
        if (arm != null) level.add(arm);
        while (!level.isEmpty()) {
            List<JsonElement> keys = new ArrayList<>();
            List<JsonElement> next = new ArrayList<>();
            for (JsonElement element : level) {
                if (element == null) continue;
                if (element.isJsonArray()) {
                    for (JsonElement child : element.getAsJsonArray()) {
                        next.add(child);
                    }
                    continue;
                }
                if (!element.isJsonObject()) continue;
                JsonObject object = element.getAsJsonObject();
                if (isAssociativeRead(object)) {
                    JsonArray arguments = array(object, "arguments");
                    if (arguments.size() > 0) keys.add(arguments.get(0));
                    continue;
                }
                for (Map.Entry<String, JsonElement> entry
                        : object.entrySet()) {
                    next.add(entry.getValue());
                }
            }
            if (!keys.isEmpty()) {
                for (JsonElement key : keys) {
                    collectSymbolLeaves(key, result);
                }
                return result;
            }
            level = next;
        }
        return result;
    }

    /** Every raw VM symbol one expression names, in encounter order. */
    private static void collectSymbolLeaves(JsonElement expression,
                                            Set<String> result) {
        if (expression == null) return;
        if (expression.isJsonArray()) {
            for (JsonElement child : expression.getAsJsonArray()) {
                collectSymbolLeaves(child, result);
            }
            return;
        }
        if (!expression.isJsonObject()) return;
        JsonObject object = expression.getAsJsonObject();
        if ("SymbolExpression".equals(string(object, "_type"))) {
            String raw = string(object, "_exp");
            if (!raw.isEmpty()) result.add(raw);
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectSymbolLeaves(entry.getValue(), result);
        }
    }

    /** Stamps every case-local evidence family with its exact owner. */
    private static void retainCaseOwner(JsonObject item, String owner) {
        RecordedSessionModel.writeCaseOwnership(item, owner);
        JsonObject state = object(item, SharedStateEvidence.RECORDED_FIELD);
        if (state.size() > 0) {
            RecordedSessionModel.writeCaseOwnership(state, owner);
        }
        for (JsonElement element : array(item,
                RelationSummary.INTERACTION_EVENTS)) {
            if (element.isJsonObject()) {
                RecordedSessionModel.writeCaseOwnership(
                        element.getAsJsonObject(), owner);
            }
        }
        for (JsonElement element : array(item, VmHandoffEvidence.FIELD)) {
            if (element.isJsonObject()) {
                RecordedSessionModel.writeCaseOwnership(
                        element.getAsJsonObject(), owner);
            }
        }
    }

    /**
     * The plan rows in composition scope: the selected region occurrences.
     */
    static List<JsonObject> targetScopedPlanRows(
            Collection<JsonObject> planRows,
            JsonObject fatal,
            Collection<JsonObject> resolvedBindings,
            Collection<RelationSummary> loweredRelations) {
        Set<String> selected = new LinkedHashSet<>();
        for (RelationSummary relation : loweredRelations == null
                ? Collections.<RelationSummary>emptyList()
                : loweredRelations) {
            String occurrence = relation.occurrenceId();
            if (!occurrence.isEmpty()) selected.add(occurrence);
        }
        // Do not recursively scan the whole target query: it may embed the
        // session event ledger.  Only its explicit target identity members
        addOccurrence(fatal, "occurrenceId", selected);
        collectOccurrences(object(fatal, "selectedTargetOccurrence"),
                selected);
        for (JsonObject binding : resolvedBindings == null
                ? Collections.<JsonObject>emptyList() : resolvedBindings) {
            collectOccurrences(binding, selected);
        }
        List<JsonObject> scoped = new ArrayList<>();
        Set<String> held = new LinkedHashSet<>();
        for (JsonObject row : planRows == null
                ? Collections.<JsonObject>emptyList() : planRows) {
            if (row == null) continue;
            String occurrence = string(row, "occurrenceId");
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
        String occurrence = string(row, field);
        if (!occurrence.isEmpty()) selected.add(occurrence);
    }

    /** Every constraint on every selected fatal path, including state reads. */
    private static JsonArray fatalTargetTerms(JsonObject fatal) {
        JsonArray terms = new JsonArray();
        for (JsonElement element : array(fatal, "paths")) {
            JsonArray constraints = array(element.getAsJsonObject(),
                    "constraints");
            for (JsonElement constraint : constraints) {
                terms.add(constraint.deepCopy());
            }
        }
        return terms;
    }

    /**
     * Names evidence that was proven and then dropped.
     */
    private static void auditDroppedEdgeEvidence(Emitter emitter,
                                                 PortIndex ports,
                                                 List<JsonObject> edges) {
        Set<PortOccurrence> unbound = new LinkedHashSet<>();
        for (PortOccurrence occurrence : emitter.mentionedPorts) {
            if (ports.isInput(occurrence.portId)
                    && !emitter.suppliedInputOccurrences.contains(
                    occurrence)) {
                unbound.add(occurrence);
            }
        }
        if (unbound.isEmpty()) return;
        Set<PortOccurrence> reported = new LinkedHashSet<>();
        for (JsonObject edge : edges) {
            if (!AutomaticRegionEdge
                    .selectedReadFromCompositionBinding(edge)) {
                continue;
            }
            String consumer = bindingTargetInput(edge);
            String instance = bindingTargetInstance(edge);
            String region = firstNonBlank(string(edge, "toRegion"),
                    regionOf(consumer));
            if (consumer.isEmpty() || instance.isEmpty()) continue;
            PortOccurrence occurrence = new PortOccurrence(
                    new InvocationKey(region, instance), consumer);
            if (!unbound.contains(occurrence)
                    || !reported.add(occurrence)) {
                continue;
            }
            emitter.unsupported.add(
                    "DROPPED_CONFIRMED_EDGE_EVIDENCE:"
                            + occurrence + ":"
                            + string(edge, "edgeId"));
        }
    }

    /**
     * <p>There is no second mode to ask for. README's completion criteria say
     */
    static void requireObservedCoverage(JsonObject summary,
                                        JsonObject coverage)
            throws IOException {
        JsonObject relation = object(summary, "regionRelation");
        String coverageState = string(coverage, "coverageState");
        if (integer(coverage, "schemaVersion", -1) != 1
                || !"OBSERVED_PATH_COVERAGE".equals(
                string(coverage, "kind"))
                || !"IMPORTED_VM_PATH_UNDERAPPROX_V1".equals(
                string(coverage, "authority"))
                || bool(coverage, "complete", true)
                // One projection authority remains.  The full-path collision
                // fallback was deleted with README PC-1's ambient path
                || !("SELECTIVE_SYMBOLIC_BRANCH_SLICE".equals(
                string(relation, "guardProjection"))
                && "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1".equals(
                string(coverage, "constraintProjectionAuthority")))
                || integer(coverage, "observedCaseCount", -1)
                != array(relation, "cases").size()
                || integer(coverage, "observedPathCount", -1) < 1
                || integer(coverage, "observedCaseCount", -1)
                < integer(coverage, "observedPathCount", -1)
                || string(coverage, "observedPathSetHash").isEmpty()
                || !("PARTIAL".equals(coverageState)
                || "SEED_ONLY".equals(coverageState))
                || !coverageState.equals(string(summary,
                "pathCoverageState"))) {
            throw new IOException(
                    "Malformed observed-path under-approximation");
        }
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

    /**
     * OCC-1: the planned address behind one occurrence id.
     *
     * <p>A relation summary is closed on the address the campaign scheduled;
     * its cases may be several activations of it, named
     * {@code <address>#a<ordinal>}.  A runtime binding may name either, so
     * every match between the two is made on the address.</p>
     */
    static String plannedOccurrence(String occurrenceId) {
        return edu.uva.liftlab.graphchecker.contract.PathObservation
                .plannedOccurrenceOf(occurrenceId);
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
        if (integer(fatal, "schemaVersion", -1)
                != TargetReachPathQueryBuilder.SCHEMA_VERSION
                || !"TARGET_REACH_PATH_SET_QUERY".equals(
                        string(fatal, "kind"))
                || string(fatal, "queryKey").isEmpty()) {
            throw new IOException("Unsupported canonical fatal query schema");
        }
        if (JsonFields.exactInteger(fatal, "targetOccurrence", -1) < 1) {
            throw new IOException(
                    "Target reach query has no exact branch decision");
        }
        JsonArray paths = array(fatal, "paths");
        if (paths.size() == 0) {
            throw new IOException(
                    "Closed target reach query contains no path");
        }
        for (JsonElement element : paths) {
            if (!element.isJsonObject()
                    || !element.getAsJsonObject().has("constraints")
                    || !element.getAsJsonObject().get("constraints")
                    .isJsonArray()
                    || element.getAsJsonObject().getAsJsonArray(
                    "constraints").size() == 0) {
                throw new IOException(
                        "Malformed target reach path query member");
            }
            if (!element.getAsJsonObject().has(
                    PathObservation.TargetReachEvent.FIELD)) {
                throw new IOException(
                        "Target reach path has no exact attestation "
                                + "authority");
            }
        }
    }

    private static JsonObject selectFatalQuery(List<JsonObject> rows,
                                               Arguments arguments) {
        for (JsonObject row : rows) {
            if (!arguments.fatalRegion.isEmpty()
                    && !arguments.fatalRegion.equals(string(row,
                    "regionId"))) {
                continue;
            }
            if (!arguments.occurrenceId.isEmpty()
                    && !arguments.occurrenceId.equals(string(row,
                    "occurrenceId"))) {
                continue;
            }
            if ("TARGET_REACH_PATH_SET_QUERY".equals(
                    string(row, "kind"))) {
                return row;
            }
        }
        return new JsonObject();
    }

    /**
     * Resolves the instance-scoped producer graph used by composition.
     */
    private static ResolvedSummaryGraph resolveSummaryGraph(
            JsonObject fatal, JsonObject context,
            SummaryIndex summaryIndex) {
        ProducerDemandIndex knownDemands = new ProducerDemandIndex();
        List<JsonObject> targetBindings = relationRows(fatal,
                "selectedTargetBindings");
        while (true) {
            ResolvedSummaryGraph result = resolveSummaryGraphPass(
                    fatal, context, summaryIndex, knownDemands,
                    targetBindings);
            if (!knownDemands.addAll(result.demands)) return result;
        }
    }

    private static ResolvedSummaryGraph resolveSummaryGraphPass(
            JsonObject fatal, JsonObject context, SummaryIndex summaries,
            ProducerDemandIndex knownDemands,
            List<JsonObject> targetBindings) {
        String fatalRegion = string(fatal, "regionId");
        String fatalInstance = string(context, "occurrenceId");
        ResolvedSummaryGraph result = new ResolvedSummaryGraph(fatalRegion,
                fatalInstance, knownDemands);

        registerTargetDemands(result, targetBindings);
        seedTargetBindings(result, summaries, targetBindings);

        while (!result.pending.isEmpty()) {
            ProducerKey consumer = result.pending.removeFirst();
            RelationSummary consumerSelection =
                    result.summaryFor(consumer);
            if (consumerSelection == null) continue;
            Set<String> demandedInputs =
                    consumerSelection.outputClosure().executionScope()
                            .inputPorts();
            if (demandedInputs.isEmpty()) continue;

            // Discover the whole upstream demand for this consumer before
            // selecting any producer summary.  Selecting while scanning one
            List<JsonObject> incoming = summaries.bindingsTargeting(
                    consumer.regionId, consumer.instanceId);
            List<JsonObject> admitted = new ArrayList<>();
            for (JsonObject binding : incoming) {
                if (!bindingTargets(binding, consumer.regionId,
                        consumer.instanceId, demandedInputs)) {
                    continue;
                }
                if (AutomaticRegionEdge.unselectedReadFromBinding(binding)) {
                    continue;
                }
                if (!AutomaticRegionEdge.composerTraversalBinding(binding)) {
                    result.gaps.add("UntrustedRecursiveEdgeBinding:"
                            + string(binding, "edgeId"));
                    continue;
                }
                admitted.add(binding);
                result.registerDemand(bindingSourceRegion(binding),
                        bindingSourceInstance(binding),
                        bindingSourceOutput(binding));
            }
            for (JsonObject binding : admitted) {
                resolveBindingProducer(result, binding, summaries,
                        consumer.regionId, consumer.instanceId);
            }
        }
        if (hasComposerTraversalBinding(targetBindings)
                && result.selectedSummaries.isEmpty()) {
            result.gap("SelectedTargetClosureResolvedNoProducer",
                    "the target's selected bindings name at least one"
                    + " producer the composer may traverse, and resolving"
                    + " every one of them selected no producer summary at"
                    + " all, so the composed formula holds the target's case"
                    + " alone");
        }
        return result;
    }

    private static boolean hasComposerTraversalBinding(
            List<JsonObject> bindings) {
        for (JsonObject binding : bindings) {
            if (AutomaticRegionEdge.composerTraversalBinding(binding)) {
                return true;
            }
        }
        return false;
    }

    private static List<JsonObject> relationRows(JsonObject context,
                                                 String field) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(context, field)) {
            if (element.isJsonObject()) result.add(element.getAsJsonObject());
        }
        return result;
    }

    private static void registerTargetDemands(
            ResolvedSummaryGraph graph, List<JsonObject> bindings) {
        for (JsonObject binding : bindings) {
            if (!AutomaticRegionEdge.composerTraversalBinding(binding)
                    || !bindingTargets(binding, graph.fatalRegion,
                    graph.fatalInstance, bindingTargetInput(binding))) {
                continue;
            }
            String region = bindingSourceRegion(binding);
            String instance = bindingSourceInstance(binding);
            String output = bindingSourceOutput(binding);
            if (!region.isEmpty() && !instance.isEmpty()
                    && !output.isEmpty()) {
                graph.registerDemand(region, instance, output);
            }
        }
    }

    private static void seedTargetBindings(
            ResolvedSummaryGraph graph, SummaryIndex summaries,
            List<JsonObject> bindings) {
        for (JsonObject binding : bindings) {
            String edgeId = string(binding, "edgeId");
            if (!bindingTargets(binding, graph.fatalRegion,
                    graph.fatalInstance, bindingTargetInput(binding))) {
                graph.gaps.add("SelectedTargetBindingScopeMismatch:"
                        + edgeId);
                continue;
            }
            if (!AutomaticRegionEdge.composerTraversalBinding(binding)) {
                if (AutomaticRegionEdge
                        .unselectedReadFromBinding(binding)) {
                    continue;
                }
                graph.gaps.add("SelectedTargetBindingHasNoTraversalAuthority:"
                        + edgeId);
                continue;
            }
            String sourceRegion = bindingSourceRegion(binding);
            String sourceInstance = bindingSourceInstance(binding);
            String output = bindingSourceOutput(binding);
            String input = bindingTargetInput(binding);
            String relationKind = bindingRelationKind(binding);
            if (sourceRegion.isEmpty() || sourceInstance.isEmpty()
                    || output.isEmpty() || input.isEmpty()
                    || relationKind.isEmpty()) {
                graph.gaps.add("MalformedSelectedTargetBinding:"
                        + string(binding, "edgeId"));
                continue;
            }
            ProducerKey key = selectExactProducer(graph, summaries,
                    sourceRegion, sourceInstance, output, binding);
            if (key != null) {
                graph.addDirectBindingIfPresent(key, graph.fatalRegion,
                        graph.fatalInstance, input, binding, binding,
                        relationKind);
                if (!graph.containsExactBinding(binding)) {
                    graph.gaps.add("SelectedTargetBindingUnresolved:"
                            + string(binding, "edgeId"));
                }
            }
        }
    }

    private static void resolveBindingProducer(ResolvedSummaryGraph graph,
                                               JsonObject binding,
                                               SummaryIndex summaries,
                                               String targetRegion,
                                               String targetInstance) {
        if (!AutomaticRegionEdge.composerTraversalBinding(binding)) {
            if (AutomaticRegionEdge.unselectedReadFromBinding(binding)) {
                return;
            }
            graph.gaps.add("UntrustedRecursiveEdgeBinding:"
                    + string(binding, "edgeId"));
            return;
        }
        String sourceRegion = bindingSourceRegion(binding);
        String sourceInstance = bindingSourceInstance(binding);
        String output = bindingSourceOutput(binding);
        String input = bindingTargetInput(binding);
        if (sourceRegion.isEmpty() || output.isEmpty() || input.isEmpty()) {
            graph.gaps.add("MalformedRecursiveEdgeBinding:"
                    + string(binding, "edgeId"));
            return;
        }
        ProducerKey key = selectExactProducer(graph, summaries,
                sourceRegion, sourceInstance, output, binding);
        if (key == null) return;
        if (AutomaticRegionEdge.tracedExchangeCandidate(binding)) {
            graph.addDirectBindingIfPresent(key, targetRegion,
                    targetInstance, input, binding, binding,
                    bindingRelationKind(binding));
            if (!graph.containsExactBinding(binding)) {
                graph.gaps.add("SelectedTopologyBindingUnresolved:"
                        + string(binding, "edgeId"));
            }
            return;
        }
        RelationSummary selected = graph.summaryFor(key);
        // The VM-selected row belongs to the reader, which is the only
        graph.addEdge(new ResolvedEdge(selected, binding.deepCopy()));
    }

    private static ProducerKey selectExactProducer(
            ResolvedSummaryGraph graph, SummaryIndex summaries,
            String region, String requestedInstance,
            String output, JsonObject preferredBinding) {
        graph.registerDemand(region, requestedInstance, output);
        Set<String> demandedOutputs = Collections.singleton(output);
        Map<String, RelationSummary> unique = new LinkedHashMap<>();
        Set<String> fingerprints = new LinkedHashSet<>();
        boolean selectedReadFrom = AutomaticRegionEdge
                .selectedReadFromCompositionBinding(preferredBinding);
        String preferredEdge = string(preferredBinding, "edgeId");
        if (selectedReadFrom && (requestedInstance.isEmpty()
                || output.isEmpty() || preferredEdge.isEmpty())) {
            graph.gaps.add("MalformedSelectedReadFromProducerIdentity:"
                    + preferredEdge);
            return null;
        }
        boolean occurrenceAndPortFound = false;
        for (RelationSummary summary : summaries.covering(region,
                demandedOutputs, requestedInstance)) {
            if (!requestedInstance.isEmpty()
                    && !plannedOccurrence(requestedInstance).equals(
                    plannedOccurrence(summary.occurrenceId()))) {
                continue;
            }
            occurrenceAndPortFound = true;
            if (selectedReadFrom
                    && !producerClosureCarriesEdge(summary, output,
                    preferredEdge)) {
                continue;
            }
            unique.put(summary.summaryId(), summary);
            fingerprints.add(
                    summary.outputClosure().closureFingerprint());
        }
        if (selectedReadFrom && unique.isEmpty()
                && occurrenceAndPortFound) {
            graph.gap("SelectedReadFromMissingProducerCausalEdge:"
                    + preferredEdge + ":"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs),
                    "a summary states region " + region + " at instance "
                    + requestedInstance + " with output port " + output
                    + ", but its output closure does not carry the selected"
                    + " read-from edge " + preferredEdge);
            return null;
        }
        if (!selectedReadFrom && unique.size() > 1
                && !preferredEdge.isEmpty()) {
            // Which summary owns this edge is a question about the whole
            // resolved the edge in one case did produce it.  README CASE-1
            Map<String, RelationSummary> exactEdge = new LinkedHashMap<>();
            for (RelationSummary summary : unique.values()) {
                for (JsonObject edge : summary.edgeBindings()) {
                    if (preferredEdge.equals(string(edge, "edgeId"))
                            && output.equals(bindingSourceOutput(edge))) {
                        exactEdge.put(summary.summaryId(), summary);
                        break;
                    }
                }
            }
            if (exactEdge.size() == 1) {
                unique = exactEdge;
                fingerprints.clear();
                fingerprints.add(unique.values().iterator().next()
                        .outputClosure().closureFingerprint());
            }
        }
        if (unique.isEmpty()) {
            graph.gap("MissingExactProducerSummary:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs),
                    "no summary handed to this composition states region "
                    + region + " at instance "
                    + firstNonBlank(requestedInstance, "(any)")
                    + " with output port " + output
                    + "; the composed set holds "
                    + summaries.summaryCount() + " summary(ies) over region(s)"
                    + " " + summaries.regionIds()
                    + (occurrenceAndPortFound
                    ? ", and the one that names this region and port does not"
                    + " carry the edge " + preferredEdge
                    : ", none of which names that region, instance and port"));
            return null;
        }
        if (fingerprints.size() != 1) {
            graph.gap("AmbiguousProducerClosureFingerprint:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs) + ":fingerprints=" + fingerprints,
                    "the " + unique.size() + " candidate producer summary(ies)"
                    + " for this port state " + fingerprints.size()
                    + " different output closures, so which relation the port"
                    + " is an output of is not stated");
            return null;
        }
        if (unique.size() > 1) {
            graph.gap("AmbiguousExactProducerSummary:"
                    + producerLabel(region, requestedInstance,
                            demandedOutputs),
                    unique.size() + " summaries state this region, instance"
                    + " and output port with the same output closure, so"
                    + " which relation the port is an output of is not"
                    + " stated: " + unique.keySet());
            return null;
        }
        RelationSummary selected = unique.values().iterator().next();
        String instance = firstNonBlank(requestedInstance,
                selected.occurrenceId());
        ProducerKey key = new ProducerKey(region, instance, output,
                selected.summaryId());
        RelationSummary held = graph.selectedProducerSummaries.get(key);
        if (held != null && !held.same(selected)) {
            graph.gap("ConflictingProducerSummarySelection:" + key,
                    "this producer port was already resolved to summary "
                    + held.summaryId() + " and now resolves to "
                    + selected.summaryId());
            return null;
        }
        if (held == null) {
            graph.selectedProducerSummaries.put(key, selected);
            graph.selectedSummaries.put(selected.summaryId(), selected);
            graph.relevantRegions.add(region);
            if (graph.expandedSummaries.add(selected.summaryId())) {
                graph.pending.addLast(key);
            }
        }
        return key;
    }

    private static boolean producerClosureCarriesEdge(
            RelationSummary summary, String output, String edgeId) {
        if (summary == null || output.isEmpty() || edgeId.isEmpty()) {
            return false;
        }
        OutputClosureContract.Member member =
                summary.outputClosure().member(output);
        if (member == null) return false;
        for (JsonElement element : array(member.slice(), "causalEdgeIds")) {
            if (edgeId.equals(element.getAsString())) return true;
        }
        return false;
    }

    private static String producerLabel(String region, String instance,
                                        Set<String> outputs) {
        return region + "[instance="
                + firstNonBlank(instance, "<unique-instance>")
                + ",outputs=" + outputs + "]";
    }

    /**
     * real edge of this relation.  What README CASE-1 requires is that the
     */
    private static List<JsonObject> matchingBindings(
            RelationSummary summary, ProducerKey source, String targetRegion,
            String targetInstance, String targetInput,
            JsonObject expectedRelation, JsonObject expectedBinding,
            String expectedKind) {
        Map<String, JsonObject> matches = new LinkedHashMap<>();
        for (JsonObject binding : summary.edgeBindings()) {
            if (!source.instanceId.equals(bindingSourceInstance(binding))
                    || !source.outputPort.equals(bindingSourceOutput(binding))
                    || !AutomaticRegionEdge
                    .composerTraversalBinding(binding)
                    || !sameCompositionRelation(binding, expectedRelation,
                    expectedKind)
                    || expectedBinding != null
                    && !sameCompositionRelation(binding, expectedBinding,
                    expectedKind)
                    || !bindingTargets(binding, targetRegion,
                    targetInstance, targetInput)) {
                continue;
            }
            String edgeId = string(binding, "edgeId");
            if (!edgeId.isEmpty()) matches.put(edgeId, binding);
        }
        return new ArrayList<>(matches.values());
    }

    /**
     * Keeps a context relation tied to the exact runtime edge that justified
     */
    private static boolean sameCompositionRelation(JsonObject binding,
                                                   JsonObject expected,
                                                   String expectedKind) {
        String kind = firstNonBlank(expectedKind,
                bindingRelationKind(expected));
        if (kind.isEmpty() || !kind.equals(bindingRelationKind(binding))) {
            return false;
        }
        String edgeId = string(expected, "edgeId");
        if (!edgeId.isEmpty() && !edgeId.equals(string(binding, "edgeId"))) {
            return false;
        }
        String fromInstance = bindingSourceInstance(expected);
        String toInstance = bindingTargetInstance(expected);
        if (!fromInstance.isEmpty()
                && !fromInstance.equals(bindingSourceInstance(binding))
                || !toInstance.isEmpty()
                && !toInstance.equals(bindingTargetInstance(binding))) {
            return false;
        }
        if (expected.has("writerEventSeq")) {
            long expectedWriter = longInteger(expected, "writerEventSeq", -1);
            long actualWriter = longInteger(binding, "writerEventSeq", -1);
            if (expectedWriter != actualWriter) return false;
        }
        if (expected.has("readerEventSeq")) {
            long expectedReader = longInteger(expected, "readerEventSeq", -1);
            long actualReader = longInteger(binding, "readerEventSeq", -1);
            if (expectedReader != actualReader) return false;
        }
        return true;
    }

    private static String bindingRelationKind(JsonObject binding) {
        String kind = string(binding, "evidenceKind");
        if (AutomaticRegionEdge.FIELD_ASSIGNMENT_READ_FROM.equals(kind)
                || AutomaticRegionEdge.CONTAINER_MUTATION_READ_FROM
                .equals(kind)) {
            return "READ_FROM";
        }
        if (AutomaticRegionEdge.tracedExchangeCandidate(binding)) {
            return "TOPOLOGY";
        }
        return "";
    }

    private static boolean bindingTargets(JsonObject binding, String region,
                                          String instance, String input) {
        String bindingRegion = string(binding, "toRegion");
        String bindingInstance = bindingTargetInstance(binding);
        return region.equals(bindingRegion)
                && !instance.isEmpty() && instance.equals(bindingInstance)
                && (input.isEmpty() || input.equals(bindingTargetInput(binding)));
    }

    private static boolean bindingTargets(JsonObject binding, String region,
                                          String instance,
                                          Set<String> inputs) {
        return bindingTargets(binding, region, instance,
                bindingTargetInput(binding))
                && inputs.contains(bindingTargetInput(binding));
    }

    private static String bindingSourceRegion(JsonObject binding) {
        return string(binding, "fromRegion");
    }

    private static String bindingSourceInstance(JsonObject binding) {
        return string(binding, "fromOccurrenceId");
    }

    private static String bindingTargetInstance(JsonObject binding) {
        return string(binding, "toOccurrenceId");
    }

    private static String bindingSourceOutput(JsonObject binding) {
        return string(binding, "fromOutputPort");
    }

    private static String bindingTargetInput(JsonObject binding) {
        return string(binding, "toInputPort");
    }

    private static final class SummaryIndex {
        private final Map<String, List<RelationSummary>> byRegion =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> bindingsByTarget =
                new LinkedHashMap<>();
        /** Recorded-value counts per closure, computed once on demand. */
        private final Map<String, Integer> evidenceByClosure =
                new LinkedHashMap<>();

        private static SummaryIndex build(List<RelationSummary> summaries) {
            SummaryIndex result = new SummaryIndex();
            for (RelationSummary decoded : summaries) {
                result.byRegion.computeIfAbsent(decoded.regionId(),
                        ignored -> new ArrayList<>()).add(decoded);
                // README CASE-1: these rows are the reader's case-local
                // resolutions, each already naming the cases that made it.
                for (JsonObject binding : decoded.edgeBindings()) {
                    String targetRegion = string(binding, "toRegion");
                    String targetInstance =
                            bindingTargetInstance(binding);
                    if (targetRegion.isEmpty()
                            || targetInstance.isEmpty()
                            || !readFromArmAuthority(decoded, binding)) {
                        continue;
                    }
                    result.bindingsByTarget.computeIfAbsent(
                            targetRegion + "\n" + targetInstance,
                            ignored -> new ArrayList<>()).add(binding);
                }
            }
            return result;
        }

        /** How many summaries this composition was handed. */
        private int summaryCount() {
            int total = 0;
            for (List<RelationSummary> held : byRegion.values()) {
                total += held.size();
            }
            return total;
        }

        /** The regions those summaries state, for a refusal to name. */
        private Set<String> regionIds() {
            return new LinkedHashSet<>(byRegion.keySet());
        }

        /**
         * Whether this summary is the one that may state a read-from arm.
         */
        private static boolean readFromArmAuthority(RelationSummary summary,
                                                    JsonObject binding) {
            if (string(binding, RecordedReadFrom.EDGE_FIELD).isEmpty()) {
                return true;
            }
            return plannedOccurrence(bindingTargetInstance(binding))
                    .equals(plannedOccurrence(summary.occurrenceId()));
        }

        /**
         * The producers that cover one demand, richest evidence first.
         *
         * <p>One region's occurrences may declare different output closures
         * over the same address: a closure that is exactly the demand and a
         * wider one that also carries the demanded ports' own in-region
         * producers both cover it.  Answering by set equality took the exact
         * one unconditionally, so every value the wider occurrence recorded
         * for the ports feeding the demand was dropped without a word and the
         * demanded port lowered as a local root instead of the handoff it
         * is.  Rank instead: the producer that actually recorded values for
         * more of its own closure wins, and only then the smaller closure --
         * so a demand where neither producer recorded more than the other
         * selects exactly what set equality selected.</p>
         */
        private List<RelationSummary> covering(String region,
                                               Set<String> outputs,
                                               String requestedInstance) {
            // Ranked within the demanded occurrence, never across
            // occurrences: the caller answers one named producer instance,
            // so ranking the region's other occurrences alongside it could
            // drop the very summary the demand names.
            String demanded = plannedOccurrence(requestedInstance);
            Map<String, List<RelationSummary>> candidates =
                    new LinkedHashMap<>();
            for (RelationSummary summary : byRegion.getOrDefault(region,
                    Collections.emptyList())) {
                Set<String> available =
                        summary.outputClosure().outputPorts();
                if (!available.containsAll(outputs)) continue;
                if (!demanded.isEmpty() && !demanded.equals(
                        plannedOccurrence(summary.occurrenceId()))) {
                    continue;
                }
                candidates.computeIfAbsent(closureKey(region, available),
                        ignored -> new ArrayList<>()).add(summary);
            }
            List<RelationSummary> result = new ArrayList<>();
            int richest = -1;
            int smallest = Integer.MAX_VALUE;
            for (Map.Entry<String, List<RelationSummary>> candidate
                    : candidates.entrySet()) {
                List<RelationSummary> group = candidate.getValue();
                int evidence = recordedEvidence(candidate.getKey(), group);
                int size = group.get(0).outputClosure()
                        .outputPorts().size();
                if (evidence > richest
                        || evidence == richest && size < smallest) {
                    result.clear();
                    richest = evidence;
                    smallest = size;
                }
                if (evidence == richest && size == smallest) {
                    result.addAll(group);
                }
            }
            return result;
        }

        /**
         * How many of a closure's own ports these producers recorded a value
         * for.
         *
         * <p>Recorded evidence only: a declared port no case carries an
         * expression for counts for nothing, which is what makes the ranking
         * above fail closed -- an occurrence that produced nothing can never
         * outrank one that produced something.</p>
         */
        private int recordedEvidence(String closure,
                                     List<RelationSummary> group) {
            Integer held = evidenceByClosure.get(closure);
            if (held != null) return held.intValue();
            Set<String> produced = new LinkedHashSet<>();
            for (RelationSummary summary : group) {
                for (JsonElement encoded : summary.cases()) {
                    if (!encoded.isJsonObject()) continue;
                    produced.addAll(object(encoded.getAsJsonObject(),
                            "outputExpressions").keySet());
                }
            }
            produced.retainAll(group.get(0).outputClosure().outputPorts());
            evidenceByClosure.put(closure, Integer.valueOf(produced.size()));
            return produced.size();
        }

        private List<JsonObject> bindingsTargeting(String region,
                                                   String instance) {
            return bindingsByTarget.getOrDefault(region + "\n" + instance,
                    Collections.emptyList());
        }

        private static String closureKey(String region,
                                         Set<String> outputs) {
            return firstNonBlank(region) + "\n"
                    + String.join("\u0000",
                    new TreeSet<>(outputs));
        }
    }

    private static final class ProducerDemandIndex {
        private final Map<String, Set<String>> outputsByInvocation =
                new LinkedHashMap<>();

        private ProducerDemandIndex() {
        }

        private ProducerDemandIndex(ProducerDemandIndex source) {
            addAll(source);
        }

        private void add(String region, String instance, String output) {
            String normalizedRegion = firstNonBlank(region);
            String normalizedOutput = firstNonBlank(output);
            if (normalizedRegion.isEmpty() || normalizedOutput.isEmpty()) {
                return;
            }
            String key = key(normalizedRegion, firstNonBlank(instance));
            outputsByInvocation.computeIfAbsent(key,
                    ignored -> new LinkedHashSet<>()).add(normalizedOutput);
        }

        private boolean addAll(ProducerDemandIndex source) {
            boolean changed = false;
            if (source == null) return false;
            for (Map.Entry<String, Set<String>> entry
                    : source.outputsByInvocation.entrySet()) {
                changed |= outputsByInvocation.computeIfAbsent(
                        entry.getKey(), ignored -> new LinkedHashSet<>())
                        .addAll(entry.getValue());
            }
            return changed;
        }

        private static String key(String region, String instance) {
            return firstNonBlank(region) + "\u0000"
                    + firstNonBlank(instance);
        }
    }

    private static final class ProducerKey {
        private final String regionId;
        private final String instanceId;
        private final String outputPort;
        private final String summaryId;

        private ProducerKey(String regionId, String instanceId,
                            String outputPort, String summaryId) {
            this.regionId = firstNonBlank(regionId);
            this.instanceId = firstNonBlank(instanceId);
            this.outputPort = firstNonBlank(outputPort);
            this.summaryId = firstNonBlank(summaryId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof ProducerKey)) return false;
            ProducerKey value = (ProducerKey) other;
            return regionId.equals(value.regionId)
                    && instanceId.equals(value.instanceId)
                    && outputPort.equals(value.outputPort)
                    && summaryId.equals(value.summaryId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(regionId, instanceId, outputPort, summaryId);
        }

        @Override
        public String toString() {
            return regionId + "[instance=" + instanceId + ",output="
                    + outputPort + ",summary=" + summaryId + "]";
        }
    }

    private static final class InvocationKey {
        private final String regionId;
        private final String instanceId;

        private InvocationKey(String regionId, String instanceId) {
            this.regionId = firstNonBlank(regionId);
            this.instanceId = firstNonBlank(instanceId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof InvocationKey)) return false;
            InvocationKey value = (InvocationKey) other;
            return regionId.equals(value.regionId)
                    && instanceId.equals(value.instanceId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(regionId, instanceId);
        }

        @Override
        public String toString() {
            return regionId + "@" + instanceId;
        }
    }

    private static final class PortOccurrence {
        private final InvocationKey invocation;
        private final String portId;

        private PortOccurrence(InvocationKey invocation, String portId) {
            this.invocation = invocation;
            this.portId = firstNonBlank(portId);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof PortOccurrence)) return false;
            PortOccurrence value = (PortOccurrence) other;
            return invocation.equals(value.invocation)
                    && portId.equals(value.portId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(invocation, portId);
        }

        @Override
        public String toString() {
            return invocation.instanceId + ":" + portId;
        }
    }

    private static final class ResolvedEdge {
        private final RelationSummary summary;
        private final JsonObject binding;
        private final boolean topologyOnly;

        private ResolvedEdge(RelationSummary summary, JsonObject binding) {
            this.summary = summary;
            this.binding = binding;
            String provenance = string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE);
            this.topologyOnly = !AutomaticRegionEdge
                    .trustedRuntimeCompositionBinding(binding)
                    || !provenance.isEmpty()
                    && !RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                    && !RecordedReadFrom.PROVENANCE_GUARDED.equals(provenance);
        }

    }

    /**
     * A failure-directed witness derived only from the selected fatal path,
     */
    private static final class FatalAbsenceMutationWitness {
        private final List<Demand> demands;
        private final Map<PortOccurrence, List<RemovalCaseEffect>> effects =
                new LinkedHashMap<>();
        private final List<String> clauses = new ArrayList<>();

        private FatalAbsenceMutationWitness(List<Demand> demands) {
            this.demands = demands;
        }

        private static FatalAbsenceMutationWitness resolve(
                JsonObject fatal, ResolvedSummaryGraph graph,
                PortIndex ports) {
            List<AbsenceRead> reads = new ArrayList<>();
            int pathOrdinal = 0;
            for (JsonElement pathElement : array(fatal, "paths")) {
                if (!pathElement.isJsonObject()) {
                    pathOrdinal++;
                    continue;
                }
                for (JsonElement constraint : array(
                        pathElement.getAsJsonObject(), "constraints")) {
                    collectAbsenceReads(constraint, pathOrdinal, ports,
                            reads);
                }
                pathOrdinal++;
            }
            String fatalInstance = firstNonBlank(
                    string(fatal, "occurrenceId"),
                    string(object(fatal, "symbolicContext"),
                            "occurrenceId"));
            Map<String, Demand> selected = new LinkedHashMap<>();
            for (AbsenceRead read : reads) {
                PortOccurrence target = new PortOccurrence(
                        new InvocationKey(regionOf(read.inputPort),
                                fatalInstance), read.inputPort);
                for (ResolvedEdge edge : graph.selectedEdges.values()) {
                    JsonObject binding = edge.binding;
                    if (!target.equals(new PortOccurrence(
                            new InvocationKey(string(binding, "toRegion"),
                                    bindingTargetInstance(binding)),
                            bindingTargetInput(binding)))) {
                        continue;
                    }
                    String output = bindingSourceOutput(binding);
                    if (ports.sort(read.inputPort) != Sort.MAP
                            || ports.sort(output) != Sort.MAP
                            || !hasAssociativeRemovalOnSpine(
                            edge.summary.cases(), output)) {
                        continue;
                    }
                    PortOccurrence source = new PortOccurrence(
                            new InvocationKey(bindingSourceRegion(binding),
                                    bindingSourceInstance(binding)), output);
                    Demand demand = new Demand(read.pathOrdinal, target,
                            source, new ResolvedBindingKey(binding),
                            read.keyExpression);
                    selected.putIfAbsent(demand.identity(), demand);
                }
            }
            return new FatalAbsenceMutationWitness(
                    new ArrayList<>(selected.values()));
        }

        private static void collectAbsenceReads(
                JsonElement expression, int pathOrdinal, PortIndex ports,
                List<AbsenceRead> result) {
            if (expression == null || !expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("BinaryExpression".equals(string(object, "_type"))
                    && "==".equals(string(object, "_op"))) {
                JsonElement left = object.get("_left");
                JsonElement right = object.get("_right");
                JsonObject read = associativeReadComparedWithNull(left,
                        right);
                if (read == null) {
                    read = associativeReadComparedWithNull(right, left);
                }
                if (read != null) {
                    String input = portInReceiver(read.get("receiver"),
                            ports);
                    JsonArray arguments = array(read, "arguments");
                    if (!input.isEmpty() && ports.isInput(input)
                            && arguments.size() == 1) {
                        result.add(new AbsenceRead(pathOrdinal, input,
                                arguments.get(0)));
                        return;
                    }
                }
            }
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                collectAbsenceReads(entry.getValue(), pathOrdinal, ports,
                        result);
            }
        }

        private static JsonObject associativeReadComparedWithNull(
                JsonElement candidate, JsonElement other) {
            if (!recordedNull(other) || candidate == null
                    || !candidate.isJsonObject()) return null;
            JsonObject read = candidate.getAsJsonObject();
            return isAssociativeRead(read) ? read : null;
        }

        private static boolean recordedNull(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            return "SymbolExpression".equals(string(object, "_type"))
                    && "N".equals(string(object, "_exp"));
        }

        private static String portInReceiver(JsonElement expression,
                                             PortIndex ports) {
            if (expression == null) return "";
            if (expression.isJsonArray()) {
                for (JsonElement item : expression.getAsJsonArray()) {
                    String found = portInReceiver(item, ports);
                    if (!found.isEmpty()) return found;
                }
                return "";
            }
            if (!expression.isJsonObject()) return "";
            JsonObject object = expression.getAsJsonObject();
            if ("SymbolExpression".equals(string(object, "_type"))) {
                return findPort(string(object, "_exp"), ports);
            }
            JsonElement receiver = object.get("receiver");
            return receiver == null ? ""
                    : portInReceiver(receiver, ports);
        }

        private static boolean hasAssociativeRemovalOnSpine(
                JsonArray cases, String output) {
            for (JsonElement caseElement : cases) {
                if (!caseElement.isJsonObject()) continue;
                JsonElement cursor = object(caseElement.getAsJsonObject(),
                        "outputExpressions").get(output);
                while (cursor != null && cursor.isJsonObject()) {
                    JsonObject relation = cursor.getAsJsonObject();
                    if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                            string(relation, "_type"))
                            || !"ASSOCIATIVE".equals(
                            string(relation, "shape"))) {
                        break;
                    }
                    String operation = string(relation, "operation");
                    if ("REMOVE".equals(operation)
                            || "REMOVE_AT".equals(operation)) {
                        return true;
                    }
                    if (!"PUT".equals(operation)) break;
                    cursor = relation.get("receiver");
                }
            }
            return false;
        }

        private Set<String> outputsFor(InvocationKey invocation) {
            Set<String> result = new LinkedHashSet<>();
            for (Demand demand : demands) {
                if (demand.matchesInvocation(invocation)) {
                    result.add(demand.source.portId);
                }
            }
            return result;
        }

        private void addEffect(PortOccurrence source,
                               RemovalCaseEffect effect) {
            effects.computeIfAbsent(source,
                    ignored -> new ArrayList<>()).add(effect);
        }

        private void connect(JsonObject binding, PortOccurrence source,
                             PortOccurrence target, String writerGuard,
                             String targetState) {
            List<RemovalCaseEffect> candidates = effects.get(source);
            if (candidates == null) return;
            for (Demand demand : demands) {
                if (!demand.target.equals(target)
                        || !demand.binding.equals(
                        new ResolvedBindingKey(binding))
                        || demand.pathTerm.isEmpty()
                        || demand.keyTerm.isEmpty()) {
                    continue;
                }
                for (RemovalCaseEffect effect : candidates) {
                    clauses.add(and(Arrays.asList(demand.pathTerm,
                            writerGuard, effect.selector,
                            demand.keyPrecondition, effect.precondition,
                            "(= " + effect.removedKey + " "
                                    + demand.keyTerm + ")",
                            "(not (assoc_has " + targetState + " "
                                    + demand.keyTerm + "))")));
                }
            }
        }


        private static final class AbsenceRead {
            private final int pathOrdinal;
            private final String inputPort;
            private final JsonElement keyExpression;

            private AbsenceRead(int pathOrdinal, String inputPort,
                                JsonElement keyExpression) {
                this.pathOrdinal = pathOrdinal;
                this.inputPort = inputPort;
                this.keyExpression = keyExpression.deepCopy();
            }
        }

        private static final class Demand {
            private final int pathOrdinal;
            private final PortOccurrence target;
            private final PortOccurrence source;
            private final ResolvedBindingKey binding;
            private final JsonElement keyExpression;
            private String pathTerm = "";
            private String keyTerm = "";
            private String keyPrecondition = "true";

            private Demand(int pathOrdinal, PortOccurrence target,
                           PortOccurrence source,
                           ResolvedBindingKey binding,
                           JsonElement keyExpression) {
                this.pathOrdinal = pathOrdinal;
                this.target = target;
                this.source = source;
                this.binding = binding;
                this.keyExpression = keyExpression.deepCopy();
            }

            private boolean matchesInvocation(InvocationKey invocation) {
                return source.invocation.regionId.equals(invocation.regionId)
                        && (source.invocation.instanceId.equals(
                        invocation.instanceId)
                        || invocation.instanceId.startsWith(
                        source.invocation.instanceId + "#boundedStep"));
            }

            private String identity() {
                return pathOrdinal + "\n" + target + "\n" + source
                        + "\n" + binding.hashCode();
            }
        }

        private static final class RemovalCaseEffect {
            private final String selector;
            private final String removedKey;
            private final String precondition;

            private RemovalCaseEffect(String selector,
                                      String removedKey,
                                      String precondition) {
                this.selector = selector;
                this.removedKey = removedKey;
                this.precondition = precondition;
            }
        }
    }

    private static final class ResolvedBindingKey {
        private final String edgeId;
        private final String evidenceKind;
        private final String fromInstance;
        private final String fromOutput;
        private final String toInstance;
        private final String toInput;
        private final long writerEventSeq;
        private final long readerEventSeq;

        private ResolvedBindingKey(JsonObject binding) {
            this.edgeId = string(binding, "edgeId");
            this.evidenceKind = string(binding, "evidenceKind");
            this.fromInstance = bindingSourceInstance(binding);
            this.fromOutput = bindingSourceOutput(binding);
            this.toInstance = bindingTargetInstance(binding);
            this.toInput = bindingTargetInput(binding);
            this.writerEventSeq = longInteger(binding,
                    "writerEventSeq", -1L);
            this.readerEventSeq = longInteger(binding,
                    "readerEventSeq", -1L);
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof ResolvedBindingKey)) return false;
            ResolvedBindingKey value = (ResolvedBindingKey) other;
            return edgeId.equals(value.edgeId)
                    && evidenceKind.equals(value.evidenceKind)
                    && fromInstance.equals(value.fromInstance)
                    && fromOutput.equals(value.fromOutput)
                    && toInstance.equals(value.toInstance)
                    && toInput.equals(value.toInput)
                    && writerEventSeq == value.writerEventSeq
                    && readerEventSeq == value.readerEventSeq;
        }

        @Override
        public int hashCode() {
            return Objects.hash(edgeId, evidenceKind, fromInstance,
                    fromOutput, toInstance, toInput, writerEventSeq,
                    readerEventSeq);
        }
    }

    private static final class ResolvedSummaryGraph {
        private final String fatalRegion;
        private final String fatalInstance;
        private final ProducerDemandIndex demands;
        private final Map<String, RelationSummary> selectedSummaries =
                new LinkedHashMap<>();
        private final Map<ProducerKey, RelationSummary>
                selectedProducerSummaries = new LinkedHashMap<>();
        private final Set<String> expandedSummaries = new LinkedHashSet<>();
        private final Map<ResolvedBindingKey, ResolvedEdge> selectedEdges =
                new LinkedHashMap<>();
        private final Deque<ProducerKey> pending = new ArrayDeque<>();
        private final Set<String> relevantRegions = new LinkedHashSet<>();
        private final Set<String> gaps = new LinkedHashSet<>();
        /**
         * Why each subject in {@link #gaps} was refused.  A refusal that
         * states only its subject makes the reader re-derive the reason from
         * the artifacts; the reason is what the composition actually found,
         * so it travels with the subject that names it.
         */
        private final Map<String, String> gapDetails = new LinkedHashMap<>();

        /** Records one refusal together with why the composition made it. */
        private void gap(String subject, String detail) {
            gaps.add(subject);
            if (detail != null && !detail.isEmpty()) {
                gapDetails.put(subject, detail);
            }
        }

        private ResolvedSummaryGraph(String fatalRegion,
                                     String fatalInstance,
                                     ProducerDemandIndex knownDemands) {
            this.fatalRegion = firstNonBlank(fatalRegion);
            this.fatalInstance = firstNonBlank(fatalInstance);
            this.demands = new ProducerDemandIndex(knownDemands);
            this.relevantRegions.add(this.fatalRegion);
        }

        private void registerDemand(String region, String instance,
                                    String output) {
            demands.add(region, instance, output);
        }

        private RelationSummary summaryFor(ProducerKey producer) {
            return selectedProducerSummaries.get(producer);
        }

        private void addEdge(ResolvedEdge edge) {
            String edgeId = string(edge.binding, "edgeId");
            if (edgeId.isEmpty()) return;
            ResolvedBindingKey key = new ResolvedBindingKey(edge.binding);
            ResolvedEdge held = selectedEdges.get(key);
            if (held == null) {
                selectedEdges.put(key, edge);
                return;
            }
            // Two rows of one edge that say different things are two answers
            // to one question, and which of them arrived first is not the
            if (!CanonicalJson.render(held.binding).equals(
                    CanonicalJson.render(edge.binding))) {
                gaps.add("AmbiguousRecordedEdgeArm:" + edgeId);
            }
        }

        private void addDirectBindingIfPresent(ProducerKey source,
                                               String targetRegion,
                                               String targetInstance,
                                               String targetInput,
                                               JsonObject expectedRelation,
                                               JsonObject expectedBinding,
                                               String expectedRelationKind) {
            RelationSummary summary = summaryFor(source);
            if (summary == null
                    || !summary.outputClosure().outputPorts().contains(
                    source.outputPort)) {
                return;
            }
            // The producer summary establishes the local transition at this
            if (AutomaticRegionEdge.composerTraversalBinding(
                    expectedBinding)
                    && source.instanceId.equals(
                    bindingSourceInstance(expectedBinding))
                    && source.outputPort.equals(
                    bindingSourceOutput(expectedBinding))
                    && bindingTargets(expectedBinding, targetRegion,
                    targetInstance, targetInput)
                    && sameCompositionRelation(expectedBinding,
                    expectedRelation, expectedRelationKind)) {
                addEdge(new ResolvedEdge(summary,
                        expectedBinding.deepCopy()));
                return;
            }
            List<JsonObject> matches = matchingBindings(summary, source,
                    targetRegion, targetInstance, targetInput,
                    expectedRelation, expectedBinding, expectedRelationKind);
            if (matches.size() == 1) {
                addEdge(new ResolvedEdge(summary, matches.get(0)));
            } else if (matches.size() > 1) {
                gaps.add("AmbiguousDirectEdgeBinding:" + source + "->"
                        + targetRegion + "@" + targetInstance + ":"
                        + targetInput);
            }
        }

        private Set<String> staticEdgeIds() {
            Set<String> result = new LinkedHashSet<>();
            for (ResolvedEdge edge : selectedEdges.values()) {
                String edgeId = string(edge.binding, "edgeId");
                if (!edgeId.isEmpty()) result.add(edgeId);
            }
            return result;
        }

        private List<JsonObject> valueBindingRows() {
            List<JsonObject> result = new ArrayList<>();
            for (ResolvedEdge edge : selectedEdges.values()) {
                if (!edge.topologyOnly) result.add(edge.binding);
            }
            return result;
        }

        private boolean containsExactBinding(JsonObject binding) {
            return selectedEdges.containsKey(new ResolvedBindingKey(binding));
        }

    }

    private static JsonObject boundedContext(JsonObject source) {
        JsonObject result = new JsonObject();
        result.addProperty("occurrenceId", string(source, "occurrenceId"));
        return result;
    }

    /**
     * The region whose name an endpoint id carries, or {@code ""}.
     */
    private static String regionOf(String endpoint) {
        if (endpoint == null) return "";
        int marker = endpoint.indexOf(".in.");
        if (marker < 0) marker = endpoint.indexOf(".out.");
        if (marker > 0) return endpoint.substring(0, marker);
        marker = endpoint.indexOf("::");
        return marker > 0 ? endpoint.substring(0, marker) : "";
    }

    private static String findPort(String rawSymbol, PortIndex ports) {
        for (String port : ports.longestFirst) {
            int index = rawSymbol.indexOf(port);
            while (index >= 0) {
                int end = index + port.length();
                boolean leftBoundary = index == 0
                        || rawSymbol.charAt(index - 1) == '_';
                boolean rightBoundary = end == rawSymbol.length()
                        || rawSymbol.charAt(end) == '_';
                if (leftBoundary && rightBoundary) return port;
                index = rawSymbol.indexOf(port, index + 1);
            }
        }
        return "";
    }

    private static String and(List<String> terms) {
        return booleanNary(terms, true);
    }

    /** One target-local predicate qualified by its exact causal case. */
    static String selectedCasePathTerm(String selectedCase,
                                       String pathTerm) {
        return and(Arrays.asList(selectedCase, pathTerm));
    }

    private static String or(List<String> terms) {
        return booleanNary(terms, false);
    }

    private static String booleanNary(List<String> terms,
                                      boolean conjunction) {
        List<String> filtered = new ArrayList<>();
        for (String term : terms) {
            String value = term == null ? "" : term.trim();
            if (value.isEmpty()
                    || (conjunction ? "true" : "false").equals(value)) continue;
            if ((conjunction ? "false" : "true").equals(value)) return value;
            filtered.add(term);
        }
        if (filtered.isEmpty()) return conjunction ? "true" : "false";
        if (filtered.size() == 1) return filtered.get(0);
        StringBuilder result = new StringBuilder(conjunction
                ? "(and" : "(or");
        for (String term : filtered) result.append(' ').append(term);
        return result.append(')').toString();
    }

    /** Distinct case selectors may coexist; one repeated case may not. */
    static boolean authorityCasesDefinitelyAmbiguous(
            Collection<String> authorityGuards) {
        Set<String> cases = new LinkedHashSet<>();
        for (String guard : authorityGuards) {
            if (!cases.add(guard)) return true;
        }
        return cases.contains("true") && cases.size() > 1;
    }

    static String exactlyOneAuthority(Collection<String> guards) {
        if (guards.isEmpty()) return "false";
        StringBuilder result = new StringBuilder("(= (+");
        for (String guard : guards) {
            result.append(" (ite ").append(guard).append(" 1 0)");
        }
        return result.append(") 1)").toString();
    }

    private static final class Emitter {
        private final PortIndex ports;
        private final FatalAbsenceMutationWitness failureWitness;
        private final List<String> preamble = new ArrayList<>();
        private final List<String> declarations = new ArrayList<>();
        private final List<String> assertions = new ArrayList<>();
        private final Set<String> declarationKeys = new LinkedHashSet<>();
        private final Set<String> assertionNames = new LinkedHashSet<>();
        private final Map<String, RawSymbol> rawSymbols =
                new LinkedHashMap<>();
        /**
         * Java references whose declared type is String need two solver
         */
        private final Map<PortOccurrence, Sort> portSortOverrides =
                new LinkedHashMap<>();
        private final Map<PortOccurrence, Sort> declaredPortSorts =
                new LinkedHashMap<>();
        private final Set<PortOccurrence> boundPorts = new LinkedHashSet<>();
        private final Set<PortOccurrence> mentionedPorts =
                new LinkedHashSet<>();
        /** Case guards under which one declared input is actually consumed. */
        private final Map<PortOccurrence, Set<String>> inputUseGuards =
                new LinkedHashMap<>();
        /** Named exactly-one assertion for each case-local selected-input use. */
        private final Map<PortOccurrence, Map<String, String>>
                inputAuthorityAssertions = new LinkedHashMap<>();
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

        private final Set<String> canonicalPortTermBindings =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> javaIntegralRangeAssertions =
                new LinkedHashSet<>();
        /**
         * Exact target-side whole-map reads, indexed by the VM's session
         */
        private final Map<String, PortOccurrence> recordedMapCarrierPorts =
                new LinkedHashMap<>();
        private final Set<String> ambiguousMapCarrierKeys =
                new LinkedHashSet<>();
        private final List<PortOccurrence[]> portEqualities =
                new ArrayList<>();
        private final Set<String> emittedEdgeBindings =
                new LinkedHashSet<>();
        /** The recorded session model this composition is stated over. */
        private RecordedSessionModel recorded;
        /** Reads whose exactly-one the recorded model already asserted. */
        private final Set<Long> recordedChoiceReads = new LinkedHashSet<>();
        /**
         * README {@code READ-1}'s {@code exists(e) <-> OR(case_k holds e)},
         */
        private final Map<Long, Set<String>> readCaseGuards =
                new LinkedHashMap<>();
        /**
         * {@code READ-1} removes.</p>
         */
        private boolean catalogingRecordedReads;
        /** One value term per lowered guarded read, keyed by read event. */
        private final Map<Long, Term> guardedReadTerms =
                new LinkedHashMap<>();
        /**
         * The read whose arms are currently being lowered.
         */
        private final Deque<Long> readFromContext = new ArrayDeque<>();
        /** One evidence row per recorded value binding, for the manifest. */
        private final JsonArray recordedValueBindings = new JsonArray();
        /** Coverage findings of the recorded value lowering. */
        private final List<JsonObject> recordedCoverage = new ArrayList<>();
        /**
         * Gaps that are hard refusals in general, but sound coverage gaps once
         * the target's throw read has been admitted as a guarded map read whose
         * full recorded writer set (every removeExpiredKeys version across
         * occurrences) is lowered arm for arm: that read then depends only on
         * its own recorded arms and their per-arm key-present floor, so a
         * read-from-edge authority for the same field -- or a side read whose
         * nested map the codec cannot lower -- is off the throw's causal cut
         * and cannot change whether the read returns null.  Deferred so the
         * decision is made once, after the whole formula is lowered and it is
         * known whether such a guarded map read was admitted.
         */
        private final Set<String> softGaps = new LinkedHashSet<>();
        private final Map<String, String> softGapDetail =
                new LinkedHashMap<>();
        /**
         * Whether at least one throw read was admitted as a guarded map read
         * with its full recorded (removeExpiredKeys) writer set lowered arm for
         * arm and floored by a per-arm key-present assertion.
         */
        private boolean guardedMapReadAdmitted;
        /**
         * Reads whose fail-open unknown-writer arm was excluded because the VM
         * reported the recorded writer set complete: the emitted formula holds
         * no unknown arm for these, so a later "still admits an unknown writer"
         * refusal would be reading the writer universe's conservative closure,
         * not the formula that was actually emitted.
         */
        private final Set<Long> unknownArmExcludedReads =
                new LinkedHashSet<>();

        /** Records a gap that a guarded-map-read witness downgrades to coverage. */
        private void deferrableGap(String subject, String detail) {
            softGaps.add(subject);
            if (detail != null && !detail.isEmpty()) {
                softGapDetail.put(subject, detail);
            }
        }
        /**
         * <p>README CASE-1 hands an edge binding the selectors of the cases
         */
        private final Set<String> loweredCaseSelectors =
                new LinkedHashSet<>();
        /** Edges the recorded evidence ruled out, reported once each. */
        private final Set<String> excludedWriters = new LinkedHashSet<>();
        /** Consumer ports already handed a recorded guarded read's value. */
        private final Set<String> recordedReadBoundPorts =
                new LinkedHashSet<>();
        /** Consumer ports whose writer/read choice the VM already decided. */
        private final Set<PortOccurrence> recordedDecidedConsumerPorts =
                new LinkedHashSet<>();
        private final Set<String> declaredOutputVersionChoices =
                new LinkedHashSet<>();
        /**
         * README {@code SMT-1}'s selected-input ledger: which authority
         */
        private final Map<PortOccurrence, Map<String,
                List<InputAuthorityEvidence>>>
                inputAuthorities = new LinkedHashMap<>();

        /** One disjunct of the fatal-path assertion and its lowered term. */
        private static final class FatalDisjunct {
            private final int pathOrdinal;
            private final String caseSelector;
            private final String term;

            private FatalDisjunct(int pathOrdinal, String caseSelector,
                                  String term) {
                this.pathOrdinal = pathOrdinal;
                this.caseSelector = firstNonBlank(caseSelector);
                this.term = firstNonBlank(term);
            }
        }

        private static final class InputAuthorityEvidence {
            private final String evidence;
            private final String caseSelector;

            private InputAuthorityEvidence(String evidence,
                                           String caseSelector) {
                this.evidence = firstNonBlank(evidence);
                this.caseSelector = firstNonBlank(caseSelector);
            }

            private boolean same(String candidate, String selector) {
                return evidence.equals(firstNonBlank(candidate))
                        && caseSelector.equals(firstNonBlank(selector));
            }
        }
        private final Set<PortOccurrence> suppliedInputOccurrences =
                new LinkedHashSet<>();
        private final Map<String, JsonObject> portOccurrences =
                new LinkedHashMap<>();
        private String fatalPathAssertionName = "";
        private String fatalPathAssertionTerm = "";
        /** Every fatal target-path disjunct, in the order it was lowered. */
        private final List<FatalDisjunct> fatalDisjuncts = new ArrayList<>();
        /**
         * Recorded read -> the raw VM symbols its key position names.  A
         * read whose key is a literal contributes an empty set, which is
         * what makes it rank below one keyed on a transported value.
         */
        private final Map<Long, Set<String>> recordedReadKeySymbols =
                new LinkedHashMap<>();
        /**
         * Raw VM symbol -> the recorded cross-node handoff that carried it.
         * A symbol in here reached this node from another one; the VM says
         * so, and nothing here infers it.
         */
        private final Map<String, JsonObject> handoffCarriedSymbols =
                new LinkedHashMap<>();
        /** The causal-reach ranking, present whenever the pass ran. */
        private JsonObject causalWitnessPin = new JsonObject();
        /** Exact runtime target events and the fatal case that owns each. */
        private final JsonArray targetReachEvents = new JsonArray();
        /** Exact producer case and value chosen by each consumer case. */
        /** C2 free roots the replay reported, in mint order. */
        private final Map<String, JsonObject> freeSymbols =
                new LinkedHashMap<>();
        /** SMT root name -> the one raw VM symbol that owns it. */
        private final Map<String, String> configuredSourceRoots =
                new LinkedHashMap<>();
        /** Writable configured roots and their exact emitted SMT terms. */
        private final Map<String, JsonObject>
                configuredSourceMaterializations = new LinkedHashMap<>();
        private final List<String> targetReachCaseTerms = new ArrayList<>();
        /** Definedness facts collected while lowering one container term. */
        private Set<String> currentContainerRequirements;
        private String currentGuard = "";
        private String currentSymbolScope = "global";
        /** Raw VM symbol -> exact configured program-source identity. */
        private Map<String, String> symbolicSourceIdentities =
                Collections.emptyMap();
        /** Raw VM symbol -> exact configured source evidence row. */
        /**
         * VM roots a declared read only NAMED, by the mint identity that
         * named them.  Deliberately separate from the root registry: a named
         * root keeps the SMT name and the domain guard its own mint gave it,
         * and gains only a materialization row.
         */
        private Map<String, String> namedSourceIdentities =
                Collections.emptyMap();
        private Map<String, JsonObject> symbolicSourceEvents =
                Collections.emptyMap();
        private InvocationKey currentInvocation;

        private Emitter(PortIndex ports, InvocationKey fatalInvocation,
                        FatalAbsenceMutationWitness failureWitness) {
            this.ports = ports;
            this.currentInvocation = fatalInvocation;
            this.failureWitness = failureWitness;
        }

        private InvocationKey enterInvocation(InvocationKey invocation) {
            InvocationKey previous = currentInvocation;
            currentInvocation = invocation;
            return previous;
        }

        private void restoreInvocation(InvocationKey invocation) {
            currentInvocation = invocation;
        }

        private PortOccurrence currentOccurrence(String port) {
            return new PortOccurrence(new InvocationKey(regionOf(port),
                    currentInvocation.instanceId), port);
        }

        private PortOccurrence occurrence(String instance, String port) {
            return new PortOccurrence(new InvocationKey(regionOf(port),
                    instance), port);
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
            preamble.add("; fatal region: " + string(fatal, "regionId"));
            preamble.add("(set-logic ALL)");
            preamble.add("(declare-sort Ref 0)");
            preamble.add(ContainerSmtCodec.valueDatatypeDeclaration());
            preamble.add("(declare-const nullRef Ref)");
            preamble.addAll(ContainerSmtCodec.preamble());
            // SMT-LIB's str.from_int is defined only for non-negative
            // integers.  Java's decimal Integer.toString additionally emits
            preamble.add("(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))");
            // Java integral bytecodes wrap in two's-complement arithmetic.
            // Keeping the public scalar carrier as SMT Int is convenient for
            preamble.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            preamble.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        }

        /**
         * Files every C2 free root the replay reported.
         *
         * <p>A free root is a <em>coverage report</em>, never a refusal: the
         * owner's decision is that a composition carrying free symbols is
         * still a composition, and the count is what says how much of it the
         * VM did not propagate.  The root itself is declared only where the
         * expression naming it is lowered, so this census never adds an
         * unreferenced constant to the query.</p>
         */
        private void registerFreeSymbols(List<JsonObject> owners) {
            for (JsonObject owner : owners == null
                    ? Collections.<JsonObject>emptyList() : owners) {
                for (JsonObject row
                        : SymbolicSourceEvidence.freeSymbolsOf(owner)) {
                    JsonObject census = new JsonObject();
                    census.addProperty("symbol", string(row, "symbol"));
                    // The SMT-safe name the VM minted.  Model values are
                    // matched on this; `symbol` is what a reader is shown.
                    census.addProperty("vmSymbol", string(row, "vmSymbol"));
                    census.addProperty("siteId", string(row, "siteId"));
                    census.addProperty("occurrenceId",
                            string(row, "occurrenceId"));
                    census.addProperty("ordinal",
                            integer(row, "ordinal", 0));
                    census.addProperty("javaType", string(row, "javaType"));
                    census.addProperty("reason", string(row, "reason"));
                    freeSymbols.putIfAbsent(string(row, "symbol"), census);
                }
            }
        }

        private void registerSymbolicSources(List<JsonObject> owners) {
            try {
                symbolicSourceIdentities =
                        SymbolicSourceEvidence.rawSymbolIdentities(owners);
                Map<String, JsonObject> events = new LinkedHashMap<>();
                Map<String, String> named = new LinkedHashMap<>();
                for (JsonObject owner : owners == null
                        ? Collections.<JsonObject>emptyList() : owners) {
                    String sourceKey = string(owner, "sourceKey");
                    for (JsonObject event
                            : SymbolicSourceEvidence.eventsOf(owner)) {
                        String raw = string(event, "rawSymbol");
                        JsonObject registered = event.deepCopy();
                        registered.addProperty("sourceKey", sourceKey);
                        JsonObject held = events.putIfAbsent(raw, registered);
                        if (held == null) {
                            if (SymbolicSourceEvidence.isReused(event)) {
                                named.putIfAbsent(raw,
                                        SymbolicSourceEvidence.identity(
                                                event));
                            }
                            continue;
                        }
                        boolean heldNames =
                                SymbolicSourceEvidence.isReused(held);
                        boolean namesRoot =
                                SymbolicSourceEvidence.isReused(registered);
                        if (heldNames != namesRoot) {
                            // The site that MINTED the symbol is its
                            // authority; a read that only named it defers.
                            if (heldNames) events.put(raw, registered);
                            continue;
                        }
                        if (namesRoot) {
                            named.putIfAbsent(raw,
                                    SymbolicSourceEvidence.identity(event));
                            // One propagated root reaching several declared
                            // reads is what propagation IS: the occurrence,
                            // the phase and the producing summary all differ
                            // by construction, and the first read registered
                            // names it for everyone.  Only a different SOURCE
                            // behind one symbol is corruption.
                            if (!string(held, "sourceId").equals(
                                    string(event, "sourceId"))
                                    || !string(held, "fieldSignature").equals(
                                    string(event, "fieldSignature"))
                                    || !string(held, "javaType").equals(
                                    string(event, "javaType"))) {
                                throw new IllegalArgumentException(
                                        "one VM symbol names two configured"
                                                + " sources: " + raw);
                            }
                            continue;
                        }
                        if (!string(held, "sourceId").equals(
                                string(event, "sourceId"))
                                || !string(held, "sourceKey").equals(
                                sourceKey)
                                || !string(held,
                                "sourceOccurrenceId").equals(string(event,
                                "sourceOccurrenceId"))
                                || !string(held, "sourcePhaseId").equals(
                                string(event, "sourcePhaseId"))
                                || !string(held, "fieldSignature").equals(
                                string(event, "fieldSignature"))
                                || !string(held, "javaType").equals(
                                string(event, "javaType"))) {
                            throw new IllegalArgumentException(
                                    "one VM symbol has inconsistent configured"
                                            + " source metadata: " + raw);
                        }
                    }
                }
                symbolicSourceEvents = Collections.unmodifiableMap(events);
                namedSourceIdentities = Collections.unmodifiableMap(named);
            } catch (IllegalArgumentException malformed) {
                symbolicSourceIdentities = Collections.emptyMap();
                symbolicSourceEvents = Collections.emptyMap();
                namedSourceIdentities = Collections.emptyMap();
                unsupported.add("SymbolicSourceEvidenceMalformed:"
                        + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            }
        }

        private void bindFatalPath(int pathOrdinal, String selectedCase,
                                   String pathTerm) {
            fatalDisjuncts.add(new FatalDisjunct(pathOrdinal, selectedCase,
                    pathTerm));
            for (FatalAbsenceMutationWitness.Demand demand
                    : failureWitness.demands) {
                if (demand.pathOrdinal != pathOrdinal) continue;
                Term nativeKey = term(demand.keyExpression, null);
                Term key = asValue(nativeKey,
                        expressionJavaType(demand.keyExpression));
                if (key.sort != Sort.VALUE) {
                    unsupported.add("FatalAbsenceKeySortGap:"
                            + demand.target);
                    continue;
                }
                // Absence/removal evidence belongs to this exact target
                demand.pathTerm = selectedCasePathTerm(selectedCase,
                        pathTerm);
                demand.keyTerm = key.text;
                demand.keyPrecondition = key.precondition;
            }
        }

        private void bindFatalPathAssertion(String pathTerm) {
            fatalPathAssertionTerm = pathTerm;
            fatalPathAssertionName = assertNamed("fatal_path", pathTerm);
        }

        /**
         * Files the key position of one recorded read, arm by arm.
         *
         * <p>Every arm of one read reads the same location with the same
         * key - the arms differ in which writer's state they read, not in
         * what they ask for - so the union over arms is that read's key,
         * and an arm that serializes no associative read contributes
         * nothing.</p>
         */
        private void recordReadKeySymbols(long readEventId,
                                          JsonArray candidates) {
            if (readEventId <= 0L) return;
            Set<String> symbols = recordedReadKeySymbols.computeIfAbsent(
                    readEventId, ignored -> new LinkedHashSet<>());
            for (JsonElement element : candidates) {
                if (!element.isJsonObject()) continue;
                symbols.addAll(associativeReadKeySymbols(
                        element.getAsJsonObject().get("expression")));
            }
        }

        /** Files every raw VM symbol one recorded handoff carried here. */
        private void recordHandoffCarriedSymbols(JsonObject evidence) {
            Set<String> carried = new LinkedHashSet<>();
            collectSymbolLeaves(evidence.get(VmHandoffEvidence.EXPRESSION),
                    carried);
            for (String raw : carried) {
                JsonObject provenance = new JsonObject();
                provenance.addProperty("keySymbol", raw);
                provenance.addProperty("portId", string(evidence, "portId"));
                provenance.addProperty(
                        VmHandoffEvidence.PRODUCER_OCCURRENCE_ID,
                        string(evidence,
                                VmHandoffEvidence.PRODUCER_OCCURRENCE_ID));
                provenance.addProperty(VmHandoffEvidence.EXPORT_EVENT_ID,
                        longInteger(evidence,
                                VmHandoffEvidence.EXPORT_EVENT_ID, 0L));
                provenance.addProperty(VmHandoffEvidence.ATTACH_EVENT_ID,
                        longInteger(evidence,
                                VmHandoffEvidence.ATTACH_EVENT_ID, 0L));
                provenance.addProperty("authority", COMMUNICATION_LEAF);
                handoffCarriedSymbols.putIfAbsent(raw, provenance);
            }
        }

        /**
         * Ranks the fatal disjuncts by causal reach and pins the query to
         * the top rank.
         *
         * <p>A fatal path can be reachable for more than one reason.  When
         * several are, the disjunction the target predicate is asks the
         * weakest of those questions: "can the failure happen at all".  The
         * question worth answering is the causal one - "can it happen
         * <em>through the value another node handed this one</em>" - and
         * that distinction is already recorded: a candidate read is keyed
         * either on a value some cross-node handoff carried, or on
         * something local to this node.  The former outranks the latter.</p>
         *
         * <p>The pin is a <em>strengthening</em>.  It is an extra assertion
         * beside the untouched fatal-path disjunction, so the composed query
         * asks for a model of the top rank rather than of the whole
         * disjunction: {@code sat} for it implies {@code sat} for the
         * disjunction, never the other way round.  Nothing is quietly
         * dropped - the disjunction stays in the formula, and the excluded
         * disjuncts are named in the manifest with the rank that excluded
         * them.</p>
         *
         * <p>What it pins is the top-ranked <em>target-path case</em>, not
         * that path's term.  The term alone is satisfied vacuously: a
         * recorded read that no selected case consumes does not exist, and
         * a value nothing constrains is free to be null, so a solver
         * answers "the read returned null" by never performing the read.
         * The case is the honest question, and it is no weaker - the
         * emitted case definition already states {@code case => term}, and
         * the target-path partition already states that exactly one case
         * holds, so pinning the case implies the term and denies every
         * other path.  A path that somehow names no case falls back to its
         * term, and the manifest says which of the two was pinned.</p>
         *
         * <p>An {@code unsat} under the pin is a result, not a failure: it
         * says the failure cannot happen through the transported value on
         * this path.  The disjunction is still there and the pin is one
         * named assertion, so the weaker question stays one deletion
         * away.</p>
         *
         * <p>It fails closed.  With one disjunct there is nothing to rank;
         * with no disjunct reaching across a node boundary there is no
         * causal question to sharpen; with every disjunct reaching alike
         * there is nothing to exclude.  In all three the formula is exactly
         * the formula it was, which is what keeps a single-read target -
         * every regression row - byte for byte unchanged.</p>
         */
        private void finishCausalWitnessPin() {
            JsonArray ranked = new JsonArray();
            List<FatalDisjunct> top = new ArrayList<>();
            List<JsonObject> excluded = new ArrayList<>();
            int topRank = 0;
            for (FatalDisjunct disjunct : fatalDisjuncts) {
                JsonArray reach = crossNodeReach(disjunct);
                JsonObject row = new JsonObject();
                row.addProperty("pathOrdinal", disjunct.pathOrdinal);
                row.addProperty("caseSelector", disjunct.caseSelector);
                row.addProperty("solverTerm", disjunct.term);
                row.addProperty("rank", reach.size() > 0 ? 1 : 0);
                row.add("crossNodeReach", reach);
                ranked.add(row);
                if (reach.size() > 0) {
                    topRank = 1;
                    top.add(disjunct);
                } else {
                    excluded.add(row);
                }
            }
            causalWitnessPin = new JsonObject();
            causalWitnessPin.addProperty("schemaVersion", 1);
            causalWitnessPin.addProperty("kind", "CAUSAL_WITNESS_PIN");
            causalWitnessPin.addProperty("authority",
                    CAUSAL_WITNESS_PIN_AUTHORITY);
            causalWitnessPin.addProperty("strengthening", true);
            causalWitnessPin.addProperty("disjunctCount",
                    fatalDisjuncts.size());
            causalWitnessPin.add("disjuncts", ranked);
            causalWitnessPin.addProperty("topRank", topRank);
            String refusal = fatalDisjuncts.size() < 2
                    ? PIN_SINGLE_DISJUNCT
                    : topRank == 0 ? PIN_NO_CROSS_NODE_REACH
                    : excluded.isEmpty() ? PIN_NO_DISCRIMINATION : "";
            causalWitnessPin.addProperty("pinned", refusal.isEmpty());
            causalWitnessPin.addProperty("refusal", refusal);
            if (!refusal.isEmpty()) {
                causalWitnessPin.add("excludedDisjuncts", new JsonArray());
                causalWitnessPin.addProperty("assertion", "");
                causalWitnessPin.addProperty("solverTerm", "");
                return;
            }
            boolean byCase = true;
            for (FatalDisjunct disjunct : top) {
                byCase = byCase && !disjunct.caseSelector.isEmpty();
            }
            List<String> terms = new ArrayList<>();
            for (FatalDisjunct disjunct : top) {
                terms.add(byCase ? disjunct.caseSelector : disjunct.term);
            }
            String pinned = or(terms);
            causalWitnessPin.addProperty("pinKind", byCase
                    ? PIN_KIND_TARGET_PATH_CASE : PIN_KIND_FATAL_DISJUNCT);
            JsonArray lost = new JsonArray();
            for (JsonObject row : excluded) {
                JsonObject loser = row.deepCopy();
                loser.addProperty("excludedBecause", PIN_NO_CROSS_NODE_REACH);
                lost.add(loser);
            }
            causalWitnessPin.add("excludedDisjuncts", lost);
            causalWitnessPin.addProperty("solverTerm", pinned);
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                causalWitnessPin.addProperty("assertion", assertNamed(
                        CAUSAL_WITNESS_PIN_ASSERTION, pinned));
            } finally {
                currentGuard = previousGuard;
            }
        }

        /**
         * The recorded cross-node handoffs one disjunct's own reads are
         * keyed on.  A disjunct names the reads it constrains directly; a
         * read reached only through some other equality is not counted,
         * which keeps the rank conservative.
         */
        private JsonArray crossNodeReach(FatalDisjunct disjunct) {
            JsonArray reach = new JsonArray();
            Matcher references = READ_VALUE_REFERENCE.matcher(disjunct.term);
            Set<Long> seen = new LinkedHashSet<>();
            while (references.find()) {
                final long readEventId;
                try {
                    readEventId = Long.parseLong(references.group(1));
                } catch (NumberFormatException notARead) {
                    continue;
                }
                if (!seen.add(readEventId)) continue;
                Set<String> keys = recordedReadKeySymbols.get(readEventId);
                if (keys == null) continue;
                for (String raw : keys) {
                    JsonObject provenance = handoffCarriedSymbols.get(raw);
                    if (provenance == null) continue;
                    JsonObject hit = provenance.deepCopy();
                    hit.addProperty("readEventId", readEventId);
                    reach.add(hit);
                }
            }
            return reach;
        }

        private JsonObject causalWitnessPinLedger() {
            return causalWitnessPin.deepCopy();
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
            String attestationRole = string(path,
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
                expectedPredicate = BranchPredicateAlgebra.complement(
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
                    && event.matches(string(fatal, "targetSiteId"),
                    occurrence, required.getAsBoolean());
            if (!exactRequired || !exactDesired
                    || desired.getAsBoolean() != required.getAsBoolean()
                    || required.getAsBoolean()
                    != replay.requiredTakenOutcome()
                    || !string(fatal, "targetSiteId").equals(
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

        private void bindTargetReachAssertion() {
            if (targetReachCaseTerms.isEmpty()) {
                unsupported.add("SelectedTargetReachEventMissing:selected");
            }
            assertNamed("target_reach_event", or(targetReachCaseTerms));
        }

        private JsonArray targetReachLedger() {
            return targetReachEvents.deepCopy();
        }

        private JsonArray freeSymbolLedger() {
            JsonArray rows = new JsonArray();
            for (JsonObject row : freeSymbols.values()) {
                rows.add(row.deepCopy());
            }
            return rows;
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

        private String bindTargetPathCase(JsonObject fatal, JsonObject path,
                                          int pathOrdinal, String pathTerm) {
            String owner = targetPathCaseOwner(fatal, path, pathOrdinal);
            String selector = RecordedSessionModel.caseSelector(owner);
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

        /**
         * Registers only VM-proven exact whole-map reads.
         */
        private void registerExactSharedCarrierPorts(
                Collection<ResolvedEdge> edges) {
            for (ResolvedEdge edge : edges) {
                registerExactSharedCarrierPort(edge.binding);
            }
        }

        private void registerExactSharedCarrierPort(JsonObject binding) {
            // Deliberately the session-local triple, not the canonical name
            // the rest of the pipeline joins on: the owner recovered here is
            String location = SharedStateEvidence.sessionLocationKey(binding);
            long owner = SharedStateEvidence.locationOwnerOf(location);
            String instance = bindingTargetInstance(binding);
            String input = bindingTargetInput(binding);
            // Exact and guarded VM read-from edges both carry a whole map
            // state.  The guarded edge still has to select one recorded arm;
            String provenance = string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE);
            if (!(RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                    || RecordedReadFrom.PROVENANCE_GUARDED.equals(provenance))
                    || !SharedStateEvidence.isMapState(location)) {
                return;
            }
            // Past that gate the arm *should* substitute the fatal map state
            // unauthorized" the same.  README's fail-closed discipline: name
            String reason = owner <= 0L
                    ? "MAP_OWNER_UNRESOLVED_FROM_LOCATION_KEY:" + location
                    : instance.isEmpty()
                    ? "EXACT_MAP_ARM_NAMES_NO_CONSUMER_OCCURRENCE"
                    : !ports.contains(input)
                    ? "EXACT_MAP_ARM_CONSUMER_PORT_UNDECLARED:" + input
                    : ports.sort(input) != Sort.MAP
                    ? "EXACT_MAP_ARM_CONSUMER_PORT_NOT_MAP_SORTED:"
                            + input + ":expected MAP got "
                            + ports.sort(input)
                    : "";
            if (!reason.isEmpty()) {
                unsupported.add("ExactMapStateArmNotJoined:" + reason);
                return;
            }
            String key = mapCarrierKey(instance, owner);
            PortOccurrence candidate = occurrence(instance, input);
            PortOccurrence previous = recordedMapCarrierPorts.get(key);
            if (previous == null && !ambiguousMapCarrierKeys.contains(key)) {
                recordedMapCarrierPorts.put(key, candidate);
            } else if (previous != null && !previous.equals(candidate)) {
                recordedMapCarrierPorts.remove(key);
                ambiguousMapCarrierKeys.add(key);
                unsupported.add("AmbiguousExactMapCarrier:" + instance
                        + ":" + owner);
            }
        }

        private String mapCarrierKey(String instance, long owner) {
            return firstNonBlank(instance) + "\u0000" + owner;
        }

        private String constraint(JsonElement expression, String origin) {
            if (expression == null || !expression.isJsonObject()) {
                return unknownConstraint(origin, expression);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (BoundedOutputVersions.isVersionSelection(object)) {
                return outputVersionSelection(object, origin);
            }
            if ("MethodExpression".equals(type)) {
                return methodConstraint(object);
            }
            Term term = term(expression, null);
            if (term.sort == Sort.BOOL) return condition(term);
            return unknownConstraint(origin + ": non-boolean " + type,
                    expression);
        }

        /**
         * Binds one relation case to one exported bounded output version.
         */
        private String outputVersionSelection(JsonObject selection,
                                              String origin) {
            String port = string(selection, "outputPort");
            int ordinal = integer(selection, "versionOrdinal", -1);
            int bound = integer(selection, "versionBound", -1);
            if (port.isEmpty() || ordinal < 1 || bound < ordinal
                    || !ports.contains(port)) {
                return unknownConstraint(origin
                        + ": malformed output version selection", selection);
            }
            PortOccurrence occurrence = currentOccurrence(port);
            String choice = "output_version_choice__"
                    + smtName(String.valueOf(occurrence));
            if (declaredOutputVersionChoices.add(choice)) {
                declare(choice, Sort.INT);
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertNamed(choice + "_bounds", "(and (<= 1 " + choice
                            + ") (<= " + choice + " " + bound + "))");
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return "(= " + choice + " " + ordinal + ")";
        }

        /** A term may denote a Java expression that is defined only under a
         * reference guard (for example {@code s.length()} requires
         * cases. */
        private String condition(Term term) {
            return and(Arrays.asList(term.precondition, term.text));
        }

        private Term dependent(Term result, Term... inputs) {
            List<String> values = new ArrayList<>();
            values.add(result.precondition);
            if (inputs != null) {
                for (Term input : inputs) {
                    if (input != null) values.add(input.precondition);
                }
            }
            return result.withPrecondition(and(values));
        }

        private String stringNonNull(Term term) {
            if (term.sort != Sort.STRING) return "false";
            return "false".equals(term.stringNullness) ? "true"
                    : "(not " + term.stringNullness + ")";
        }

        private String stringDereferencePrecondition(Term... strings) {
            List<String> values = new ArrayList<>();
            if (strings != null) {
                for (Term string : strings) {
                    if (string == null || string.sort != Sort.STRING) {
                        values.add("false");
                    } else {
                        values.add(string.precondition);
                        values.add(stringNonNull(string));
                    }
                }
            }
            return and(values);
        }

        /**
         * Lowers one recorded expression.
         */
        private Term term(JsonElement expression, Sort expected) {
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                unsupported.add("ABSENT_EXPRESSION");
                return unsupportedTerm(expected == null
                        ? Sort.REF : expected);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("SymbolExpression".equals(type)) {
                return symbol(object, expected);
            }
            if ("ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConStringSymbolExp".equals(type)) {
                return constant(object, expected);
            }
            if ("BinaryExpression".equals(type)) return binary(object);
            if ("OpStrExpression".equals(type)) {
                return stringOperation(object);
            }
            if ("PlaceholderExpression".equals(type)) {
                String function = string(object, "_place_holder_func");
                int count = integer(object, "_count", -1);
                if (!"currentTimeMills".equals(function) || count < 1) {
                    unsupported.add("PlaceholderExpression:"
                            + firstNonBlank(function, "unknown") + "#"
                            + count);
                    return unsupportedTerm(Sort.INT);
                }
                // The custom VM restarts placeholder ordinals for every
                // replay task.  Therefore #1 identifies an event only inside
                String identity = function + "#" + count;
                String scopedIdentity = currentSymbolScope + "\u0000"
                        + identity;
                String name = scopedName("environment", identity) + "__"
                        + CanonicalJson.sha256(scopedIdentity)
                        .substring(0, 10);
                declare(name, Sort.INT);
                assertJavaIntegralDomain(name, Sort.INT, "J", identity);
                return new Term(name, Sort.INT,
                        IntegralWidth.JAVA_LONG);
            }
            if ("TypeCastExpression".equals(type)) {
                return typeCast(object);
            }
            if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)) {
                return guardedReadTerm(object, expected);
            }
            if (RECORDED_ITE_TYPE.equals(type)) {
                return recordedIteTerm(object, expected);
            }
            if ("MethodExpression".equals(type)) {
                return methodTerm(object);
            }
            if (ContainerSmtCodec.handles(object)) {
                return containerTerm(object);
            }
            if (ContainerSmtCodec.handlesField(object)) {
                return containerFieldTerm(object);
            }
            unsupported.add(type.isEmpty() ? "MISSING_TYPE" : type);
            Sort sort = expected == null ? Sort.VALUE : expected;
            return unsupportedTerm(sort);
        }

        /**
         * Lowers one VM guarded read-from node into the value it denotes.
         */
        /**
         * Whether a guarded read-from candidate is the INITIAL map version:
         * a {@code READ} whose receiver is a bare associative {@code STATE}
         * over a symbol, with no {@code PUT}/{@code REMOVE} chain on top.  Its
         * value is {@code get(key)} on the region-entry map, which lowers to
         * one {@code assoc_read} and carries no truncation.
         */
        /** Whether an arm's state chain carries a conditional removal
         *  ({@code REMOVE_IF}), i.e. a removeExpiredKeys {@code it.remove()}
         *  whose {@code expiry < now} guard z3 can flip to the throw. */
        /** The same associative {@code READ} with every {@code REMOVE_IF}
         *  in its state receiver stripped: {@code get(key)} over the map as
         *  removeExpiredKeys found it, before any expiry-guarded delete. */
        private JsonElement readWithoutConditionalRemovals(
                JsonElement readExpr) {
            if (readExpr == null || !readExpr.isJsonObject()) return null;
            JsonObject read = readExpr.getAsJsonObject();
            if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(read, "_type"))
                    || !"ASSOCIATIVE".equals(string(read, "shape"))
                    || !"READ".equals(string(read, "operation"))
                    || !read.has("receiver")) {
                return null;
            }
            JsonElement stripped = stripConditionalRemovals(
                    read.get("receiver"));
            if (stripped == null) return null;
            JsonObject copy = read.deepCopy();
            copy.add("receiver", stripped);
            return copy;
        }

        /** The state chain with each {@code REMOVE_IF} replaced by its
         *  receiver -- the map without its expiry-guarded deletions. */
        private JsonElement stripConditionalRemovals(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return expression;
            }
            JsonObject object = expression.getAsJsonObject();
            if (ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(object, "_type"))
                    && "REMOVE_IF".equals(string(object, "operation"))) {
                return stripConditionalRemovals(object.get("receiver"));
            }
            JsonObject copy = object.deepCopy();
            if (copy.has("receiver")) {
                JsonElement r = stripConditionalRemovals(copy.get("receiver"));
                if (r != null) copy.add("receiver", r);
            }
            return copy;
        }

        /** The null literal for one sort. */
        private String nullTerm(Sort sort) {
            return sort == Sort.REF ? "nullRef" : "(VRef nullRef)";
        }

        private boolean containsConditionalRemoval(JsonElement expression) {
            if (expression == null || expression.isJsonNull()) return false;
            java.util.Deque<JsonElement> pending =
                    new java.util.ArrayDeque<>();
            pending.push(expression);
            while (!pending.isEmpty()) {
                JsonElement current = pending.pop();
                if (current.isJsonArray()) {
                    for (JsonElement child : current.getAsJsonArray()) {
                        if (child != null) pending.push(child);
                    }
                } else if (current.isJsonObject()) {
                    JsonObject object = current.getAsJsonObject();
                    if ("REMOVE_IF".equals(string(object, "operation"))
                            && "ASSOCIATIVE".equals(string(object, "shape"))) {
                        return true;
                    }
                    for (Map.Entry<String, JsonElement> entry
                            : object.entrySet()) {
                        if (entry.getValue() != null) {
                            pending.push(entry.getValue());
                        }
                    }
                }
            }
            return false;
        }


        private Term guardedReadTerm(JsonObject node, Sort expected) {
            long localReadEventId = longInteger(node, "readEventId", 0L);
            long readEventId = resolveRecordedReadEvent(node,
                    localReadEventId);
            String fault = SharedStateEvidence.guardedReadFault(node);
            // A structurally faulted guarded read (a VM serialization the codec
            // cannot reconstruct arm for arm) has no admissible arm set, so it
            // fails the formula closed rather than being lowered.  A read whose
            // arms serialize intact -- including the removeExpiredKeys map read
            // whose full recorded writer set is lowered below and floored by a
            // per-arm key-present assertion -- is admitted arm for arm.
            if (!fault.isEmpty()) {
                unsupported.add("UnadmittedGuardedRead:" + fault);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            if (localReadEventId > 0L && readEventId <= 0L) {
                unsupported.add("RecordedReadEventScopeAmbiguous:"
                        + currentSymbolScope + ":" + localReadEventId);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            noteReadCase(readEventId);
            Term memoised = guardedReadTerms.get(readEventId);
            if (memoised != null) return memoised;
            if (readFromContext.contains(readEventId)) {
                // A read whose own arm mentions it again is not a value.
                unsupported.add("RecursiveGuardedRead:" + readEventId);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            String javaType = string(node, "_java_type");
            Sort declared = sortOfJava(javaType);
            Sort want = declared != Sort.VALUE ? declared : expected;
            final List<RecordedSessionModel.ReadArm<Term>> arms;
            readFromContext.push(readEventId);
            try {
                arms = recorded.armsOf(readEventId, array(node, "candidates"),
                        candidate -> term(candidate.get("expression"), want));
            } finally {
                readFromContext.pop();
            }
            Sort sort = want != null && want != Sort.VALUE
                    ? want : arms.get(0).term.sort;
            for (RecordedSessionModel.ReadArm<Term> arm : arms) {
                if (arm.term.sort != sort) {
                    deferrableGap("GuardedReadArmSortConflict:"
                            + readEventId + ":" + sort + "!=" + arm.term.sort,
                            "read " + readEventId + " mixes arm sorts the"
                            + " codec cannot join; left opaque");
                    return unsupportedTerm(sort);
                }
            }
            String value = READ_VALUE_PREFIX + readEventId;
            recordReadKeySymbols(readEventId, array(node, "candidates"));
            declare(value, sort);
            Term result = new Term(value, sort,
                    integralWidthOfJava(javaType));
            guardedReadTerms.put(readEventId, result);
            assertJavaIntegralDomain(value, sort, javaType,
                    "recorded read " + readEventId);
            emitGuardedReadArms(node, readEventId, arms, value);
            emitMapReadKeyPresent(node, readEventId, arms, sort);
            emitRecordedSelectionTerm(node, readEventId, sort, value);
            return result;
        }

        /**
         * Forces a guarded map-state read's {@code null} outcome to be a
         * recorded {@code removeExpiredKeys} removal -- a flippable
         * {@code expiry < now} -- and never a trivial key absence.  For each
         * admitted arm, the same read over that arm's state with its
         * conditional removals stripped (the arm's map before any
         * expiry-guarded delete) is asserted non-null <em>when that arm is the
         * one selected</em>, so whichever recorded version z3 reads from, the
         * read can still reach {@code null} only by a {@code REMOVE_IF} firing.
         * Emitted only for a map read whose recorded arms carry a conditional
         * removal (the removeExpiredKeys shape); a read with no removal arm has
         * no absence floor to establish, which keeps the guard inert for
         * single-occurrence reads that carry no removal chain.  This is the
         * soundness floor the pinned witness carried for its one arm, now
         * carried per arm by the full-arm lowering so the emitted formula stays
         * "the removeExpiredKeys mechanism, not trivial keyId-absence".
         */
        /**
         * Whether a guarded read is the removeExpiredKeys shape: a map-state
         * read at least one of whose recorded arms carries a conditional
         * removal.  The soundness floor and the unknown-arm exclusion apply
         * only to this shape, which keeps both inert for scalar shared-state
         * reads that carry no removal chain.
         */
        private boolean isMapRemovalRead(JsonObject node) {
            if (!SharedStateEvidence.LOCATION_KIND_MAP_STATE.equals(
                    SharedStateEvidence.locationKindOf(
                            SharedStateEvidence.locationKey(node)))) {
                return false;
            }
            for (JsonElement element : array(node, "candidates")) {
                if (element.isJsonObject() && containsConditionalRemoval(
                        element.getAsJsonObject().get("expression"))) {
                    return true;
                }
            }
            return false;
        }

        private void emitMapReadKeyPresent(JsonObject node, long readEventId,
                List<RecordedSessionModel.ReadArm<Term>> arms, Sort sort) {
            if (!isMapRemovalRead(node)) return;
            guardedMapReadAdmitted = true;
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                for (RecordedSessionModel.ReadArm<Term> arm : arms) {
                    if (arm.unknown) continue;
                    JsonElement withoutRemovals =
                            readWithoutConditionalRemovals(
                                    arm.candidate.get("expression"));
                    if (withoutRemovals == null) continue;
                    readFromContext.push(readEventId);
                    try {
                        Term present = term(withoutRemovals, sort);
                        if (present.sort != sort) continue;
                        assertNamed("recorded_map_read_key_present__"
                                        + readEventId + "__" + arm.arm,
                                "(=> " + arm.selector + " "
                                + and(Arrays.asList(present.precondition,
                                        "(not (= " + present.text + " "
                                        + nullTerm(sort) + "))")) + ")");
                    } finally {
                        readFromContext.pop();
                    }
                }
            } finally {
                currentGuard = previousGuard;
            }
        }

        /** Maps a replay-local VM id into this case's collision-free domain. */
        private long resolveRecordedReadEvent(JsonObject node, long eventId) {
            if (eventId <= 0L) return eventId;
            String scope = firstNonBlank(string(node, "recordedEventScope"),
                    currentSymbolScope);
            return recorded.resolveEventId(scope, eventId);
        }

        private String recordedReadExistsName(long readEventId) {
            return recorded.scopedReadExistsName(readEventId);
        }

        private String recordedSelectorName(long readEventId, String arm) {
            return recorded.scopedSelectorName(readEventId, arm);
        }

        /**
         * Lowers the node's own serialized selection term.
         */
        private void emitRecordedSelectionTerm(JsonObject node,
                                               long readEventId, Sort sort,
                                               String value) {
            String previousGuard = currentGuard;
            currentGuard = "";
            readFromContext.push(readEventId);
            try {
                Term chain = term(node.get("ite"), sort);
                if (chain.sort != sort) {
                    unsupported.add("RecordedSelectionTermSortConflict:"
                            + readEventId + ":" + sort + "!=" + chain.sort);
                    return;
                }
                assertNamed("recorded_read_term__" + readEventId,
                        and(Arrays.asList(chain.precondition, "(= " + value
                                + " " + chain.text + ")")));
            } finally {
                readFromContext.pop();
                currentGuard = previousGuard;
            }
        }

        /** Records the case guard one consumption of a read happened under. */
        private void noteReadCase(long readEventId) {
            if (catalogingRecordedReads || readEventId <= 0L) return;
            readCaseGuards.computeIfAbsent(readEventId,
                            ignored -> new LinkedHashSet<>())
                    .add(currentGuard.isEmpty() ? "true" : currentGuard);
        }

        /**
         * Defines {@code exists(read)} for every recorded read this formula
         */
        private void finishRecordedReadExistence() {
            Set<Long> reads = new LinkedHashSet<>(guardedReadTerms.keySet());
            reads.addAll(recordedChoiceReads);
            for (Long readEventId : reads) {
                String symbol = recordedReadExistsName(readEventId);
                declare(symbol, Sort.BOOL);
                Set<String> guards = readCaseGuards.get(readEventId);
                if (guards == null || guards.isEmpty()) {
                    assertNamed("recorded_read_absent__" + readEventId,
                            "(not " + symbol + ")");
                    recordedCoverage.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW,
                            "RECORDED_READ_OUTSIDE_SELECTED_CASES",
                            String.valueOf(readEventId),
                            "no selected case or binding consumes recorded"
                                    + " read " + readEventId + ", so it"
                                    + " selects no writer arm"));
                    continue;
                }
                assertNamed("recorded_read_exists__" + readEventId,
                        "(= " + symbol + " "
                                + or(new ArrayList<>(guards)) + ")");
            }
        }

        /**
         * Emits the value equality and the writer path guard of every arm.
         */
        private void emitGuardedReadArms(
                JsonObject node, long readEventId,
                List<RecordedSessionModel.ReadArm<Term>> arms, String value) {
            String previousGuard = currentGuard;
            currentGuard = "";
            // The fail-open unknown arm is excluded only for the guarded map
            // read whose full removeExpiredKeys writer set is lowered and
            // floored by a per-arm key-present assertion: there the unknown arm
            // is both spurious (the VM reports the set complete) and unsound (it
            // would let the throw read null from an unrecorded writer instead of
            // a recorded removal).  A scalar shared-state read keeps its
            // fail-open arm exactly as before, so this stays inert for the
            // single-occurrence workloads the matrix covers.
            boolean closeUnknownArm = bool(node, "writerSetComplete", false)
                    && isMapRemovalRead(node);
            List<String> selectors = new ArrayList<>();
            try {
                for (RecordedSessionModel.ReadArm<Term> readArm : arms) {
                    declare(readArm.selector, Sort.BOOL);
                    selectors.add(readArm.selector);
                    Term armTerm = readArm.term;
                    String equality = assertNamed(
                            "recorded_read_value__" + readEventId + "__"
                                    + readArm.arm,
                            "(=> " + readArm.selector + " "
                                    + and(Arrays.asList(armTerm.precondition,
                                    "(= " + value + " " + armTerm.text + ")"))
                                    + ")");
                    String guardAssertion = emitRecordedWriterGuard(
                            readEventId, readArm, closeUnknownArm);
                    recordedValueBindings.add(recordedValueBinding(node,
                            readArm.candidate, readEventId, readArm.selector,
                            equality, guardAssertion));
                }
                if (!recordedChoiceReads.contains(readEventId)) {
                    // The recorded model states the choice for every read it
                    String exists = recordedReadExistsName(readEventId);
                    declare(exists, Sort.BOOL);
                    StringBuilder exactlyOne = new StringBuilder("(= (+");
                    for (int index = 0; index < selectors.size(); index++) {
                        exactlyOne.append(" (ite ")
                                .append(selectors.get(index)).append(" 1 0)");
                        assertNamed("recorded_read_arm_exists__"
                                        + readEventId + "__" + index,
                                "(=> " + selectors.get(index) + " " + exists
                                        + ")");
                    }
                    assertNamed("recorded_read_choice__" + readEventId,
                            "(=> " + exists + " "
                                    + exactlyOne.append(") 1)") + ")");
                    recordedChoiceReads.add(readEventId);
                    recordedCoverage.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW,
                            "RECORDED_READ_CHOICE_WITHOUT_ORDER",
                            SharedStateEvidence.locationKey(node),
                            "read " + readEventId + " chooses a writer with no"
                                    + " position in the recorded order"
                                    + " domain"));
                }
            } finally {
                currentGuard = previousGuard;
            }
        }

        /** Emits the VM-selected arm's own writer path guard. */
        private String emitRecordedWriterGuard(
                long readEventId,
                RecordedSessionModel.ReadArm<Term> arm,
                boolean closeUnknownArm) {
            if (arm.unknown) {
                if (!closeUnknownArm) return "";
                // The read's recorded writer set is complete and this is the
                // removeExpiredKeys map read, so the fail-open unknown-writer
                // arm is spurious: exclude it, leaving the read to select one
                // of its recorded writers.  (README STATE-1: a closed writer
                // set needs no unknown arm; retaining it would let the throw
                // read take null from an unrecorded writer -- the trivial
                // absence the recorded removal must not be replaced by.)
                unknownArmExcludedReads.add(readEventId);
                return assertNamed("recorded_write_guard__" + readEventId
                                + "__" + arm.arm,
                        "(=> " + arm.selector + " false)");
            }
            boolean crossOccurrenceArm = false;
            JsonObject version = recorded.writerVersionForRead(
                    readEventId, arm.writerEventId);
            if (version.size() == 0) {
                // No version-store metadata was admitted for this writer.  That
                // is only a real gap when the write has no place in the shared
                // order domain: a write the recorded happens-before already
                // orders before this read is a genuine read-from arm even when
                // its writer lives in a different bounded occurrence than the
                // reader (README STATE-1: allKeys is declared symbolic-input,
                // so every recorded writer of it is admitted, not only the
                // reader's own occurrence).  The order domain's
                // recorded_read_cut / recorded_write_exists pair already
                // carries that writer's happens-before, so the arm needs only
                // its own recorded reachability below; the version-store
                // snapshot is confirmation, never the authority.
                long writerEvent = recorded.resolveEventForRead(
                        readEventId, arm.writerEventId);
                if (writerEvent <= 0L || !recorded.ordersEvent(writerEvent)) {
                    // A candidate write no recorded order can place is a write
                    // this model cannot admit at all: fail the arm closed.
                    deferrableGap("RecordedWriterVersionMissing:"
                            + readEventId + ":" + arm.arm + ":"
                            + arm.writerEventId,
                            "writer " + arm.writerEventId + " of read "
                            + readEventId + " has no position in the recorded"
                            + " order domain, so no read-from arm can carry it");
                    return assertNamed("recorded_write_guard__" + readEventId
                                    + "__" + arm.arm,
                            "(=> " + arm.selector + " false)");
                }
                // fall through: admit the cross-occurrence arm on its own
                // recorded writer path guard.
                crossOccurrenceArm = true;
            }
            // The guarded-read candidate is the reader-side VM answer.  A
            // version-store snapshot can confirm that its writer exists, but
            JsonElement pathGuard = arm.candidate.get("pathGuard");
            // A cross-occurrence writer's candidate carries no local path guard
            // (its reachability is the loop iteration that produced it, already
            // held by the recorded_read_cut / recorded_write_exists ordering);
            // an absent guard there is not an unsupported constraint but an arm
            // gated solely by the recorded happens-before.
            if (crossOccurrenceArm && pathGuard == null) return "";
            if (SharedStateEvidence.unguarded(pathGuard)) return "";
            String guard = constraint(pathGuard,
                    "recorded writer guard " + arm.arm + " of read "
                            + readEventId);
            return assertNamed("recorded_write_guard__" + readEventId + "__"
                    + arm.arm, "(=> " + arm.selector + " " + guard + ")");
        }

        /** One machine-checkable evidence row for one lowered arm. */
        private JsonObject recordedValueBinding(JsonObject node,
                                                JsonObject candidate,
                                                long readEventId,
                                                String selector,
                                                String valueAssertion,
                                                String guardAssertion) {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "RECORDED_READ_FROM_VALUE_BINDING");
            row.addProperty("authority",
                    SharedStateEvidence.GUARDED_READ_AUTHORITY);
            row.addProperty("readEventId", readEventId);
            String locationKey = SharedStateEvidence.locationKey(node);
            row.addProperty("locationKey", locationKey);
            // A map-state read is lowered by the same arms as a scalar one -
            // the arm expression is the only thing that differs - so the kind
            row.addProperty("locationKind",
                    SharedStateEvidence.locationKindOf(locationKey));
            row.addProperty("selector", selector);
            row.addProperty("arm", string(candidate, "selector"));
            row.addProperty("unknown", bool(candidate, "unknown", false));
            long localVersion = longInteger(candidate, "fieldVersionId", 0L);
            long fieldVersion = recorded.resolveEventForRead(
                    readEventId, localVersion);
            row.addProperty("fieldVersionId", fieldVersion);
            row.addProperty("writerRegionId", string(candidate, "regionId"));
            row.addProperty("valueAssertion", valueAssertion);
            row.addProperty("writerGuardAssertion", guardAssertion);
            row.addProperty("writerExists",
                    recorded.ordersEvent(fieldVersion));
            return row;
        }

        /**
         * Lowers one arm of the VM's own serialized selection term.
         */
        private Term recordedIteTerm(JsonObject node, Sort expected) {
            String arm = string(node, "selector");
            if (readFromContext.isEmpty() || arm.isEmpty()) {
                unsupported.add("RecordedIteOutsideGuardedRead:"
                        + firstNonBlank(arm, "unnamed"));
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            String selector = recordedSelectorName(readFromContext.peek(), arm);
            declare(selector, Sort.BOOL);
            Term then = term(node.get("then"), expected);
            Term otherwise = term(node.get("else"), expected);
            if (then.sort != otherwise.sort) {
                unsupported.add("RecordedIteArmSortConflict:" + arm + ":"
                        + then.sort + "!=" + otherwise.sort);
                return unsupportedTerm(then.sort);
            }
            return dependent(new Term("(ite " + selector + " " + then.text
                    + " " + otherwise.text + ")", then.sort,
                    then.integralWidth), then, otherwise);
        }

        /** The recorded value bindings, as one manifest member. */
        private JsonArray recordedValueBindingLedger() {
            return recordedValueBindings.deepCopy();
        }

        private Term containerTerm(JsonObject expression) {
            return lowerContainerTerm(exactMapReadState(expression), false);
        }

        /**
         * An exact whole-map input already denotes the selected VM version.
         */
        private JsonObject exactMapReadState(JsonObject expression) {
            if (!"ASSOCIATIVE".equals(string(expression, "shape"))) {
                return expression;
            }
            String operation = string(expression, "operation");
            if (!("READ".equals(operation) || "CONTAINS".equals(operation)
                    || "SIZE".equals(operation)
                    || "IS_EMPTY".equals(operation)
                    || "ITERATOR".equals(operation))) {
                return expression;
            }
            JsonObject state = containerState(expression.get("receiver"));
            if (state == null) return expression;
            JsonObject identity = object(state, "receiver");
            if (!"SymbolExpression".equals(string(identity, "_type"))) {
                return expression;
            }
            long owner = symbolicContainerOwner(string(identity, "_exp"));
            if (owner <= 0L || !recordedMapCarrierPorts.containsKey(
                    mapCarrierKey(currentInvocation.instanceId, owner))) {
                return expression;
            }
            JsonObject projected = expression.deepCopy();
            projected.add("receiver", state.deepCopy());
            return projected;
        }

        private JsonObject containerState(JsonElement expression) {
            JsonElement cursor = expression;
            while (cursor != null && cursor.isJsonObject()) {
                JsonObject object = cursor.getAsJsonObject();
                if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                        string(object, "_type"))) {
                    return null;
                }
                if ("STATE".equals(string(object, "operation"))) {
                    return object;
                }
                cursor = object.get("receiver");
            }
            return null;
        }

        private Term containerFieldTerm(JsonObject expression) {
            return lowerContainerTerm(expression, true);
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
                    if (identity != null && identity.isJsonObject()
                            && "SymbolExpression".equals(string(
                            identity.getAsJsonObject(), "_type"))) {
                        if (shape == ContainerSmtCodec.Sort.ASSOCIATIVE) {
                            long owner = symbolicContainerOwner(string(
                                    identity.getAsJsonObject(), "_exp"));
                            PortOccurrence exact = owner <= 0L ? null
                                    : recordedMapCarrierPorts.get(mapCarrierKey(
                                    currentInvocation.instanceId, owner));
                            if (exact != null) {
                                declarePort(exact, Sort.MAP);
                                mentionPort(exact);
                                return new ContainerSmtCodec.Term(
                                        portName(exact), shape);
                            }
                        }
                        String port = findPort(string(
                                identity.getAsJsonObject(), "_exp"));
                        Sort required = shape
                                == ContainerSmtCodec.Sort.INDEXED
                                ? Sort.ARRAY_VALUE : Sort.MAP;
                        if (!port.isEmpty()) {
                            promotePort(port, required);
                        }
                        if (!port.isEmpty() && portSort(port) == required) {
                            ContainerSmtCodec.Term encoded = toContainerTerm(
                                    term(identity, required));
                            if (encoded != null && encoded.sort == shape) {
                                return encoded;
                            }
                        }
                        if (port.isEmpty()) {
                            // VM-local collection identities need not be
                            // canonical region ports.  Preserve them as
                            ContainerSmtCodec.Term encoded = toContainerTerm(
                                    term(identity, required));
                            if (encoded != null && encoded.sort == shape) {
                                return encoded;
                            }
                        }
                    }
                    Term reference = term(identity, Sort.REF);
                    if (reference == null || reference.sort != Sort.REF) {
                        unsupported("ContainerStateIdentity:" + shape);
                        return null;
                    }
                    return new ContainerSmtCodec.Term(
                            (shape == ContainerSmtCodec.Sort.INDEXED
                                    ? "(indexed_state_of "
                                    : "(assoc_state_of ")
                                    + reference.text + ")",
                            shape);
                }

                @Override
                public ContainerSmtCodec.Term operand(
                        JsonElement expression,
                        ContainerSmtCodec.Sort expected) {
                    if (ContainerSmtCodec.handles(expression)) {
                        return ContainerSmtCodec.term(
                                expression.getAsJsonObject(), this);
                    }
                    if (ContainerSmtCodec.handlesField(expression)) {
                        return ContainerSmtCodec.field(
                                expression.getAsJsonObject(), this);
                    }
                    Sort nativeExpected = expected == ContainerSmtCodec.Sort.INT
                            ? Sort.INT
                            : expected == ContainerSmtCodec.Sort.BOOL
                            ? Sort.BOOL
                            : expected == ContainerSmtCodec.Sort.REF
                            ? Sort.REF
                            : expected == ContainerSmtCodec.Sort.INDEXED
                            ? Sort.ARRAY_VALUE
                            : expected
                            == ContainerSmtCodec.Sort.ASSOCIATIVE
                            ? Sort.MAP : null;
                    return toContainerTerm(term(expression, nativeExpected));
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    return toContainerTerm(asValue(term(expression, null),
                            expressionJavaType(expression)));
                }

                @Override
                public ContainerSmtCodec.Term unbox(
                        ContainerSmtCodec.Term value,
                        String javaType) {
                    return ContainerSmtCodec.unboxValue(value,
                            javaType, unboxedCellSort(javaType),
                            this);
                }

                @Override
                public void require(String predicate) {
                    if (currentContainerRequirements != null) {
                        currentContainerRequirements.add(predicate);
                    } else {
                        assertNamed("container_value_kind_"
                                + CanonicalJson.sha256(predicate)
                                .substring(0, 16), predicate);
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
                    // A raw heap reference is meaningful only inside the
                    String identity = currentSymbolScope + "\u0000"
                            + ownerClass + "\u0000" + fieldOffset
                            + "\u0000" + javaType;
                    String accessor = "container_field__"
                            + scopeToken(identity);
                    declareFunction(accessor, Collections.singletonList(
                            new Term("", Sort.REF)), result);
                    return toContainerTerm(new Term("(" + accessor + " "
                            + owner.text + ")", result,
                            integralWidthOfJava(javaType)));
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
        private long symbolicContainerOwner(String raw) {
            if (raw == null) return 0L;
            int marker = raw.lastIndexOf("__M_");
            if (marker < 0 && raw.startsWith("M_")) marker = 0;
            int separator = raw.lastIndexOf("__");
            int width = 2;
            if (separator <= marker + 2
                    || separator + width >= raw.length()) {
                separator = raw.lastIndexOf('_');
                width = 1;
            }
            if (marker < 0 || separator <= marker + 2
                    || separator + width >= raw.length()) {
                return 0L;
            }
            try {
                long owner = Long.parseLong(raw.substring(separator + width));
                return owner > 0L ? owner : 0L;
            } catch (NumberFormatException invalid) {
                return 0L;
            }
        }

        private ContainerSmtCodec.Term toContainerTerm(Term value) {
            if (value == null) return null;
            ContainerSmtCodec.Sort sort = value.sort == Sort.BOOL
                    ? ContainerSmtCodec.Sort.BOOL
                    : value.sort == Sort.INT
                    ? ContainerSmtCodec.Sort.INT
                    : value.sort == Sort.REF
                    ? ContainerSmtCodec.Sort.REF
                    : value.sort == Sort.VALUE
                    ? ContainerSmtCodec.Sort.VALUE : null;
            if (value.sort == Sort.ARRAY_VALUE) {
                sort = ContainerSmtCodec.Sort.INDEXED;
            } else if (value.sort == Sort.MAP) {
                sort = ContainerSmtCodec.Sort.ASSOCIATIVE;
            } else if (value.sort == Sort.FLOAT32) {
                sort = ContainerSmtCodec.Sort.FLOAT32;
            } else if (value.sort == Sort.FLOAT64) {
                sort = ContainerSmtCodec.Sort.FLOAT64;
            } else if (value.sort == Sort.STRING) {
                sort = ContainerSmtCodec.Sort.STRING;
            }
            if (sort == null) {
                unsupported.add("ContainerOperandSort:" + value.sort);
                return null;
            }
            return new ContainerSmtCodec.Term(value.text, sort,
                    value.integralWidth);
        }

        private Term fromContainerTerm(ContainerSmtCodec.Term value) {
            if (value == null) return unsupportedTerm(Sort.VALUE);
            Sort sort = value.sort == ContainerSmtCodec.Sort.BOOL
                    ? Sort.BOOL
                    : value.sort == ContainerSmtCodec.Sort.INT
                    ? Sort.INT
                    : value.sort == ContainerSmtCodec.Sort.REF
                    ? Sort.REF
                    : value.sort == ContainerSmtCodec.Sort.FLOAT32
                    ? Sort.FLOAT32
                    : value.sort == ContainerSmtCodec.Sort.FLOAT64
                    ? Sort.FLOAT64
                    : value.sort == ContainerSmtCodec.Sort.STRING
                    ? Sort.STRING
                    : value.sort == ContainerSmtCodec.Sort.INDEXED
                    ? Sort.ARRAY_VALUE
                    : value.sort == ContainerSmtCodec.Sort.ASSOCIATIVE
                    ? Sort.MAP : Sort.VALUE;
            return new Term(value.text, sort, value.integralWidth);
        }

        private Term symbol(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            if ("N".equals(raw)) {
                return new Term("nullRef", Sort.REF);
            }
            if ("V".equals(raw)) {
                return new Term("true", Sort.BOOL);
            }

            String port = findPort(raw);
            if (!port.isEmpty()) {
                mentionPort(currentOccurrence(port));
                if (expected == Sort.MAP) {
                    promotePort(port, Sort.MAP);
                    declarePort(port, Sort.MAP);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.MAP);
                }
                if (expected == Sort.ARRAY_VALUE) {
                    if (portSort(port) != Sort.ARRAY_VALUE) {
                        unsupported.add("ArraySymbolPortSortConflict:" + port
                                + ":" + portSort(port));
                    } else {
                        declarePort(port, Sort.ARRAY_VALUE);
                        boundPorts.add(currentOccurrence(port));
                        return new Term(portName(port), Sort.ARRAY_VALUE);
                    }
                }
                Port schema = ports.get(port);
                if (expected == Sort.REF && schema != null
                        && (portSort(port) == Sort.MAP
                        || portSort(port) == Sort.ARRAY_VALUE)) {
                    return canonicalPortTerm(port, Sort.REF,
                            string(expression, "_java_type"));
                }
                if (schema != null && portSort(port) == Sort.MAP) {
                    declarePort(port, Sort.MAP);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.MAP);
                }
                if (schema != null && portSort(port) == Sort.ARRAY_VALUE) {
                    declarePort(port, Sort.ARRAY_VALUE);
                    boundPorts.add(currentOccurrence(port));
                    return new Term(portName(port), Sort.ARRAY_VALUE);
                }
                if (schema != null
                        && JavaPrimitiveBoxing.wrapperType(
                        schema.javaType)) {
                    if (expected == Sort.REF) {
                        return canonicalBoxedPrimitiveReferenceTerm(port);
                    }
                    return canonicalPortTerm(port,
                            sortOfJava(schema.javaType), schema.javaType);
                }
            }

            String expressionJavaType = string(expression, "_java_type");
            Sort expressionSort = sortOfJava(expressionJavaType);
            Sort sort = expressionSort != Sort.VALUE ? expressionSort
                    : expected == null ? Sort.VALUE : expected;
            if (sort == Sort.VALUE || sort == Sort.MAP) {
                sort = sortOfJava(string(expression, "_java_type"));
                if (sort == Sort.VALUE || sort == Sort.MAP) sort = Sort.REF;
            }
            if (!port.isEmpty()) {
                return canonicalPortTerm(port, sort, expressionJavaType);
            }

            return scopedSymbol(raw, "sym", sort,
                    expressionJavaType, "scoped_symbol_" + smtName(raw),
                    "ScopedSymbol", "scoped:");
        }


        private Term canonicalPortTerm(String port, Sort sort,
                                       String expressionJavaType) {
            Port schema = ports.get(port);
            String schemaJavaType = schema == null ? "" : schema.javaType;
            String integralJavaType = canonicalIntegralJavaType(
                    schemaJavaType, expressionJavaType);
            if (sort == Sort.REF
                    && sortOfJava(schemaJavaType) == Sort.STRING) {
                return canonicalNullableStringReferenceTerm(port,
                        schemaJavaType);
            }
            PortOccurrence occurrence = currentOccurrence(port);
            String bindingKey = occurrence + "\u0000" + sort.name();
            String name = "sym__port__" + smtName(occurrence.toString()) + "__"
                    + sort.name().toLowerCase(Locale.ROOT);
            IntegralWidth schemaWidth = integralWidthOfJava(schemaJavaType);
            IntegralWidth expressionWidth = integralWidthOfJava(
                    expressionJavaType);
            if (schemaWidth != IntegralWidth.NONE
                    && expressionWidth != IntegralWidth.NONE
                    && schemaWidth != expressionWidth) {
                unsupported.add("CanonicalPortIntegralWidthConflict:" + port
                        + ":" + schemaWidth + "!=" + expressionWidth);
            }
            FloatingKind schemaFloating = JavaPrimitiveSmtSemantics
                    .floatingKindOfJavaType(schemaJavaType);
            FloatingKind expressionFloating = JavaPrimitiveSmtSemantics
                    .floatingKindOfJavaType(expressionJavaType);
            FloatingKind requestedFloating = floatingKind(sort);
            if (schemaFloating != FloatingKind.NONE
                    && requestedFloating != schemaFloating) {
                unsupported.add("CanonicalPortFloatingSortConflict:" + port
                        + ":schema=" + schemaFloating + ":requested="
                        + requestedFloating);
            }
            if (expressionFloating != FloatingKind.NONE
                    && requestedFloating != expressionFloating) {
                unsupported.add("CanonicalPortExpressionFloatingSortConflict:"
                        + port + ":expression=" + expressionFloating
                        + ":requested=" + requestedFloating);
            }
            if (schemaFloating != FloatingKind.NONE
                    && expressionFloating != FloatingKind.NONE
                    && schemaFloating != expressionFloating) {
                unsupported.add("CanonicalPortFloatingTypeConflict:" + port
                        + ":" + schemaFloating + "!="
                        + expressionFloating);
            }
            declare(name, sort);
            Term term;
            if (sort == Sort.STRING) {
                String nullness = "sym__port__"
                        + smtName(occurrence.toString())
                        + "__string_is_null";
                declare(nullness, Sort.BOOL);
                term = Term.nullableString(name, nullness,
                        "canonical-port:" + port);
            } else {
                term = new Term(name, sort,
                        integralWidthOfJava(integralJavaType));
            }
            if (canonicalPortTermBindings.add(bindingKey)) {
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertJavaIntegralDomain(name, sort, integralJavaType,
                            "canonical_port_"
                                    + smtName(occurrence.toString()));
                    if (emitPortBinding(port, term)) {
                        boundPorts.add(occurrence);
                        recordCanonicalPortOccurrence(occurrence, sort, name,
                                term.stringNullness);
                    }
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return term;
        }

        private void recordCanonicalPortOccurrence(
                PortOccurrence occurrence, Sort sort, String solverTerm,
                String nullnessSolverTerm) {
            JsonObject row = new JsonObject();
            row.addProperty("portId", occurrence.portId);
            row.addProperty("occurrenceId",
                    occurrence.invocation.instanceId);
            row.addProperty("sort", sort.name());
            row.addProperty("portTerm", portName(occurrence));
            row.addProperty("solverTerm", solverTerm);
            if (!firstNonBlank(nullnessSolverTerm).isEmpty()
                    && !"false".equals(nullnessSolverTerm)) {
                row.addProperty("nullnessSolverTerm", nullnessSolverTerm);
            }
            portOccurrences.put(occurrence + "\u0000" + sort.name(),
                    row);
        }

        private JsonArray portOccurrences() {
            List<Map.Entry<String, JsonObject>> rows = new ArrayList<>(
                    portOccurrences.entrySet());
            rows.sort(Map.Entry.comparingByKey());
            JsonArray result = new JsonArray();
            for (Map.Entry<String, JsonObject> row : rows) {
                JsonObject encoded = row.getValue().deepCopy();
                String portId = string(encoded, "portId");
                String occurrenceId = string(encoded, "occurrenceId");
                boolean supplied = false;
                for (PortOccurrence occurrence : suppliedInputOccurrences) {
                    if (occurrence.portId.equals(portId)
                            && occurrence.invocation.instanceId.equals(
                            occurrenceId)) {
                        supplied = true;
                        break;
                    }
                }
                encoded.addProperty("supplied", supplied);
                result.add(encoded);
            }
            return result;
        }

        /** Canonical named assertion for the selected fatal path. */
        private JsonObject fatalPathAssertion() {
            JsonObject result = new JsonObject();
            result.addProperty("name", fatalPathAssertionName);
            result.addProperty("solverTerm", fatalPathAssertionTerm);
            return result;
        }

        /**
         * Models an erased JVM reference view of a statically-known String
         */
        private Term canonicalNullableStringReferenceTerm(
                String port, String schemaJavaType) {
            Term stringTerm = canonicalPortTerm(port, Sort.STRING,
                    schemaJavaType);
            PortOccurrence occurrence = currentOccurrence(port);
            String name = "sym__port__" + smtName(occurrence.toString())
                    + "__ref";
            declare(name, Sort.REF);
            String bindingKey = occurrence
                    + "\u0000NULLABLE_STRING_REFERENCE_VIEW";
            if (canonicalPortTermBindings.add(bindingKey)) {
                String formula = "(= (= " + name + " nullRef) "
                        + stringTerm.stringNullness + ")";
                String previousGuard = currentGuard;
                currentGuard = "";
                try {
                    assertNamed("nullable_string_reference_view_" + port,
                            formula);
                } finally {
                    currentGuard = previousGuard;
                }
            }
            return new Term(name, Sort.REF);
        }

        /**
         * Keeps Java wrapper identity separate from the wrapper's logical
         */
        private Term canonicalBoxedPrimitiveReferenceTerm(String port) {
            PortOccurrence occurrence = currentOccurrence(port);
            String name = "sym__port__"
                    + smtName(occurrence.toString()) + "__boxed_ref";
            declare(name, Sort.REF);
            return new Term(name, Sort.REF);
        }

        private Term scopedSymbol(String raw, String prefix, Sort requested,
                                  String javaType, String domainLabel,
                                  String conflictLabel, String sourcePrefix) {
            String sourceIdentity = symbolicSourceIdentities.get(raw);
            String key = symbolScopeKey(raw, currentSymbolScope,
                    sourceIdentity);
            RawSymbol symbol = rawSymbols.get(key);
            if (symbol == null) {
                String name = sourceIdentity == null
                        ? scopedName(prefix, raw)
                        : configuredSourceRootName(raw, sourceIdentity);
                symbol = new RawSymbol(name, requested);
                rawSymbols.put(key, symbol);
                declare(symbol.name, symbol.sort);
                // A configured source denotes one concrete Java field across
                String previousGuard = currentGuard;
                if (sourceIdentity != null) currentGuard = "";
                try {
                    assertJavaIntegralDomain(symbol.name, symbol.sort,
                            javaType, domainLabel);
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
                recordConfiguredSourceMaterialization(raw, symbol);
                return Term.nullableString(symbol.name, symbol.nullness,
                        sourcePrefix + key);
            }
            recordConfiguredSourceMaterialization(raw, symbol);
            return new Term(symbol.name, symbol.sort,
                    integralWidthOfJava(javaType));
        }

        /**
         * Names the root of one configured-source mint.
         *
         * <p>The producing runtime's own name wins when it published one -
         * {@code sym__<sourceId>__<occurrenceId>__<ordinal>} under wave 3
         * C1 - so the model reports the root the mint site minted.  A row
         * that publishes none is named from its mint identity.  Two raw
         * symbols that would land on one name are separated by the symbol
         * itself, so the map from VM symbol to root stays injective.</p>
         */
        private String configuredSourceRootName(String raw,
                                                String identity) {
            JsonObject event = symbolicSourceEvents.get(raw);
            String published = event == null ? ""
                    : string(event, SymbolicSourceEvidence.SYMBOL);
            String base = published.isEmpty()
                    ? "source__" + scopeToken(identity)
                    : smtName(published);
            String held = configuredSourceRoots.putIfAbsent(base, raw);
            return held == null || held.equals(raw) ? base
                    : base + "__" + sha256(raw).substring(0, 16);
        }

        /**
         * Publishes the exact writable program source behind one emitted SMT
         */
        private void recordConfiguredSourceMaterialization(
                String raw, RawSymbol symbol) {
            String identity = symbolicSourceIdentities.get(raw);
            JsonObject event = symbolicSourceEvents.get(raw);
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
            if (event == null) {
                unsupported.add("ConfiguredSourceMaterializationMissing:"
                        + raw);
                return;
            }
            String javaType = string(event, "javaType");
            String fieldType = fieldSignatureJavaType(
                    string(event, "fieldSignature"));
            Sort declaredSort = sortOfJava(javaType);
            if (declaredSort != symbol.sort
                    || !javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(fieldType))) {
                unsupported.add("ConfiguredSourceMaterializationSortConflict:"
                        + string(event, "sourceId") + ":" + declaredSort
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
            String sourceKey = string(event, "sourceKey");
            if (sourceKey.isEmpty()) {
                unsupported.add("ConfiguredSourceMaterializationSourceKeyMissing:"
                        + string(event, "sourceId"));
                return;
            }
            row.addProperty("sourceKey", sourceKey);
            row.addProperty("sourceId", string(event, "sourceId"));
            row.addProperty("sourcePhaseId",
                    string(event, "sourcePhaseId"));
            row.addProperty("sourceOccurrenceId",
                    string(event, "sourceOccurrenceId"));
            row.addProperty("fieldSignature",
                    string(event, "fieldSignature"));
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
            if (held != null && !held.equals(row)) {
                unsupported.add("ConfiguredSourceMaterializationConflict:"
                        + string(event, "sourceId"));
            }
        }

        private Term constant(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            String javaType = string(expression, "_java_type");
            String value = constantPayload(raw);
            Sort sort = sortOfJava(javaType);
            Term result;
            // The JVM has no boolean comparison instruction, so a boolean
            if (expected == Sort.BOOL
                    && (sort == Sort.BOOL || sort == Sort.INT)) {
                if (!"0".equals(value) && !"1".equals(value)) {
                    unsupported.add("InvalidJavaBooleanLiteral:"
                            + firstNonBlank(raw, "MISSING"));
                    result = unsupportedTerm(Sort.BOOL);
                } else {
                    result = new Term("1".equals(value)
                            ? "true" : "false", Sort.BOOL);
                }
            } else if (expected == Sort.REF && ("0".equals(value)
                    || "N".equals(raw))) {
                result = new Term("nullRef", Sort.REF);
            } else if (sort.floating()) {
                String literal = JavaPrimitiveSmtSemantics.floatingLiteral(
                        value, floatingKind(sort));
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : new Term(literal, sort);
            } else if (sort == Sort.INT) {
                String literal = integerLiteral(value);
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : new Term(literal, Sort.INT,
                        integralWidthOfJava(javaType));
            } else if (sort == Sort.STRING) {
                result = Term.nonNullString(quote(value), "true");
            } else {
                String name = "const__" + smtName(raw);
                declare(name, sort == Sort.VALUE ? Sort.REF : sort);
                result = new Term(name,
                        sort == Sort.VALUE ? Sort.REF : sort);
            }
            return result;
        }

        private Term invalidNumericLiteral(String raw, Sort sort) {
            unsupported.add("InvalidNumericLiteral:" + sort + ":"
                    + firstNonBlank(raw, "MISSING"));
            return unsupportedTerm(sort);
        }

        private Term typeCast(JsonObject expression) {
            JsonElement sourceExpression = expression.get("_exp");
            Term source = term(sourceExpression, null);
            String sourceType = castDescriptor(
                    firstNonBlank(string(expression, "sourceJavaType"),
                            expressionJavaType(sourceExpression)));
            String targetType = castDescriptor(firstNonBlank(
                    string(expression, "targetJavaType"),
                    string(expression, "_java_type")));
            Sort sourceSort = castSort(sourceType);
            Sort targetSort = castSort(targetType);
            boolean primitivePair = JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(sourceType)
                    && JavaPrimitiveSmtSemantics
                    .primitiveNumericDescriptor(targetType);
            if (primitivePair && source.sort == sourceSort) {
                String conversion = JavaPrimitiveSmtSemantics.primitiveCast(
                        source.text, sourceType, targetType);
                if (conversion != null) {
                    return dependent(new Term(conversion, targetSort,
                            integralWidthOfJava(targetType)), source);
                }
            } else if (primitivePair) {
                unsupported.add("JavaCastSourceSortConflict:"
                        + firstNonBlank(sourceType, "UNKNOWN") + ":"
                        + source.sort + "!=" + sourceSort);
                Sort diagnosticSort = targetSort == Sort.VALUE
                        ? Sort.REF : targetSort;
                return unsupportedTerm(diagnosticSort);
            }
            unsupported.add("MODEL_SEMANTICS_MISSING:TypeCastExpression:"
                    + firstNonBlank(sourceType, "UNKNOWN") + "->"
                    + firstNonBlank(targetType, "UNKNOWN"));
            Sort diagnosticSort = targetSort == Sort.VALUE
                    ? Sort.REF : targetSort;
            return unsupportedTerm(diagnosticSort);
        }

        private Term binary(JsonObject expression) {
            String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                    string(expression, "_op"));
            JsonElement leftExpression = expression.get("_left");
            if (leftExpression == null || leftExpression.isJsonNull()) {
                Term operand = term(expression.get("_right"), null);
                if ("-".equals(operator) && numeric(operand.sort)) {
                    if (operand.sort.floating()) {
                        return dependent(new Term(JavaPrimitiveSmtSemantics
                                .floatingNegate(operand.text), operand.sort),
                                operand);
                    }
                    if (operand.integralWidth != IntegralWidth.NONE) {
                        return dependent(new Term(wrapIntegral("(- " + operand.text
                                + ")", operand.integralWidth), Sort.INT,
                                operand.integralWidth), operand);
                    }
                    unsupported.add("AmbiguousJavaIntegralUnaryWidth:"
                            + firstNonBlank(operator, "MISSING"));
                    return unsupportedTerm(Sort.INT);
                }
                if ("~".equals(operator) && operand.sort == Sort.INT
                        && operand.integralWidth != IntegralWidth.NONE) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .complement(operand.text, operand.integralWidth),
                            Sort.INT, operand.integralWidth), operand);
                }
                unsupported.add("NonNumericOrUnknownUnary:"
                        + firstNonBlank(operator, "MISSING") + ":"
                        + operand.sort);
                return unsupportedTerm(operand.sort);
            }
            Sort identitySort = boxedPrimitiveReferenceEquality(expression)
                    ? Sort.REF : null;
            Term left = term(expression.get("_left"), identitySort);
            Term right = term(expression.get("_right"),
                    identitySort == null ? left.sort : identitySort);
            if (left.sort != right.sort && right.isZero()
                    && left.sort == Sort.REF) {
                right = new Term("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = new Term("nullRef", Sort.REF);
            }
            if ("--".equals(operator)) {
                if (left.sort == Sort.INT && right.sort == Sort.INT
                        && left.integralWidth == IntegralWidth.JAVA_LONG
                        && right.integralWidth == IntegralWidth.JAVA_LONG) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .integralCompareResult(left.text, right.text),
                            Sort.INT, IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmLcmpOperands:"
                        + left.sort + ":" + left.integralWidth + ":"
                        + right.sort + ":" + right.integralWidth);
                return new Term("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if ("--l".equals(operator) || "--g".equals(operator)) {
                if (left.sort == right.sort && left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingCompareResult(left.text, right.text,
                                    "--g".equals(operator)), Sort.INT,
                            IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmFloatingCompareOperands:"
                        + operator + ":" + left.sort + ":" + right.sort);
                return new Term("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if (left.sort != right.sort && numeric(left.sort)
                    && numeric(right.sort)
                    && (left.sort.floating() || right.sort.floating())) {
                Sort promoted = left.sort == Sort.FLOAT64
                        || right.sort == Sort.FLOAT64
                        ? Sort.FLOAT64 : Sort.FLOAT32;
                left = floatingPromotion(left, promoted, "left");
                right = floatingPromotion(right, promoted, "right");
            }
            if (("==".equals(operator) || "!=".equals(operator))
                    && (left.sort == Sort.STRING && isNull(right)
                    || right.sort == Sort.STRING && isNull(left))) {
                Term string = left.sort == Sort.STRING ? left : right;
                String equality = string.stringNullness;
                return dependent(new Term("!=".equals(operator)
                        ? "(not " + equality + ")" : equality,
                        Sort.BOOL), left, right);
            }
            if (left.sort != right.sort
                    && (("==".equals(operator) || "!=".equals(operator))
                    && (isNull(left) || isNull(right)))) {
                // Java primitives are never null.  This is the one mixed-sort
                // binary relation whose semantics can be closed without an
                return dependent(new Term("!=".equals(operator)
                        ? "true" : "false", Sort.BOOL), left, right);
            }
            if ("&&".equals(operator) || "||".equals(operator)) {
                if (left.sort != Sort.BOOL || right.sort != Sort.BOOL) {
                    unsupported.add("NonBooleanLogic:" + operator + ":"
                            + left.sort + ":" + right.sort);
                    return unsupportedTerm(Sort.BOOL);
                }
                boolean conjunction = "&&".equals(operator);
                String rightEvaluated = conjunction ? left.text
                        : "(not " + left.text + ")";
                String defined = and(Arrays.asList(left.precondition,
                        "(=> " + rightEvaluated + " "
                                + right.precondition + ")"));
                return new Term("(" + (conjunction ? "and" : "or")
                        + " " + left.text + " " + right.text + ")",
                        Sort.BOOL).withPrecondition(defined);
            }
            if (left.sort != right.sort) {
                unsupported.add("BinarySortConflict:" + operator + ":"
                        + left.sort + "!=" + right.sort);
                Sort resultSort = "==".equals(operator)
                        || "!=".equals(operator)
                        || !comparison(operator).isEmpty()
                        ? Sort.BOOL : left.sort;
                return unsupportedTerm(resultSort);
            }
            if ("==".equals(operator) || "!=".equals(operator)) {
                if (left.sort == Sort.STRING) {
                    if (ContainerSmtCodec.handlesFieldBinding(expression)) {
                        Term symbol = ContainerSmtCodec.handlesField(
                                expression.get("_left")) ? right : left;
                        String materialization = ContainerSmtCodec
                                .materializedStringEquality(left.text,
                                right.text, symbol.stringNullness);
                        return dependent(new Term(materialization,
                                Sort.BOOL), left, right);
                    }
                    if (!left.stringReferenceOrigin.isEmpty()
                            && left.stringReferenceOrigin.equals(
                            right.stringReferenceOrigin)) {
                        return dependent(new Term("!=".equals(operator)
                                ? "false" : "true", Sort.BOOL),
                                left, right);
                    }
                    unsupported.add("MODEL_SEMANTICS_MISSING:"
                            + "JAVA_STRING_REFERENCE_IDENTITY:"
                            + operator);
                    return dependent(unsupportedTerm(Sort.BOOL),
                            left, right);
                }
                if (left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                String equality = "(= " + left.text + " " + right.text + ")";
                return dependent(new Term("!=".equals(operator)
                        ? "(not " + equality + ")" : equality, Sort.BOOL),
                        left, right);
            }
            String smt = comparison(operator);
            if (!smt.isEmpty()) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add("NonNumericComparison:" + operator + ":"
                            + left.sort);
                    return unsupportedTerm(Sort.BOOL);
                }
                if (left.sort.floating()) {
                    return dependent(new Term(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                return dependent(new Term("(" + smt + " " + left.text + " "
                        + right.text + ")", Sort.BOOL), left, right);
            }
            if (bitwiseOperator(operator)) {
                IntegralWidth width = promotedIntegralWidth(left, right);
                if (width == IntegralWidth.NONE) {
                    unsupported.add("AmbiguousJavaIntegralBitwiseWidth:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return unsupportedTerm(Sort.INT);
                }
                return dependent(new Term(JavaPrimitiveSmtSemantics.bitwise(
                        operator, left.text, right.text, width), Sort.INT,
                        width), left, right);
            }
            if (shiftOperator(operator)) {
                if (left.sort != Sort.INT || right.sort != Sort.INT
                        || left.integralWidth == IntegralWidth.NONE) {
                    unsupported.add("AmbiguousJavaIntegralShift:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return unsupportedTerm(Sort.INT);
                }
                return dependent(new Term(JavaPrimitiveSmtSemantics.shift(
                        operator, left.text, right.text,
                        left.integralWidth), Sort.INT,
                        left.integralWidth), left, right);
            }
            if (arithmeticOperator(operator)) {
                if (!numeric(left.sort) || !numeric(right.sort)) {
                    unsupported.add("NonNumericArithmetic:" + operator + ":"
                            + left.sort);
                    return unsupportedTerm(left.sort);
                }
                Sort resultSort = left.sort;
                if ("%".equals(operator) && resultSort.floating()) {
                    // SMT's fp.rem is the IEEE remainder, which rounds the
                    // quotient to even where Java's % truncates it.
                    unsupported.add("JavaFloatingRemainderUnmodeled");
                    return unsupportedTerm(resultSort);
                }
                if (resultSort.floating()) {
                    String floating = JavaPrimitiveSmtSemantics
                            .floatingArithmetic(operator, left.text,
                                    right.text);
                    if (floating != null) return dependent(new Term(floating,
                            resultSort), left, right);
                    unsupported.add("JavaFloatingOperatorUnmodeled:"
                            + operator);
                    return unsupportedTerm(resultSort);
                }
                if ("@".equals(operator) || "/".equals(operator)
                        || "%".equals(operator)) {
                    IntegralWidth quotientWidth = promotedIntegralWidth(left,
                            right);
                    if (quotientWidth == IntegralWidth.NONE) {
                        unsupported.add("AmbiguousJavaIntegralBinaryWidth:"
                                + operator + ":" + left.integralWidth + ":"
                                + right.integralWidth);
                        return unsupportedTerm(Sort.INT);
                    }
                    // Java truncates toward zero and takes the dividend's
                    // sign; a zero divisor throws rather than producing a
                    // value, so it is stated as the operation's definedness
                    // instead of being left to the solver's choice.
                    String quotient = "%".equals(operator)
                            ? JavaPrimitiveSmtSemantics.integralRemainder(
                            left.text, right.text, quotientWidth)
                            : JavaPrimitiveSmtSemantics.integralDivision(
                            left.text, right.text, quotientWidth);
                    return dependent(new Term(quotient, Sort.INT,
                            quotientWidth).withPrecondition(
                            JavaPrimitiveSmtSemantics.integralDivisorDefined(
                                    right.text)), left, right);
                }
                smt = arithmetic(operator);
                String arithmeticExpression = "(" + smt + " "
                        + left.text + " " + right.text + ")";
                IntegralWidth resultWidth = promotedIntegralWidth(left,
                        right);
                if (resultWidth == IntegralWidth.NONE) {
                    unsupported.add("AmbiguousJavaIntegralBinaryWidth:"
                            + operator + ":" + left.integralWidth + ":"
                            + right.integralWidth);
                    return unsupportedTerm(Sort.INT);
                }
                return dependent(new Term(wrapIntegral(arithmeticExpression,
                        resultWidth), Sort.INT, resultWidth), left, right);
            }
            unsupported.add("BinaryOperator:" + operator);
            return unsupportedTerm(Sort.BOOL);
        }

        private boolean boxedPrimitiveReferenceEquality(
                JsonObject expression) {
            String operator = string(expression, "_op");
            if (!"==".equals(operator) && !"!=".equals(operator)) {
                return false;
            }
            return boxedPrimitiveReferenceOperand(expression.get("_left"))
                    || boxedPrimitiveReferenceOperand(
                    expression.get("_right"));
        }

        private boolean boxedPrimitiveReferenceOperand(
                JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"SymbolExpression".equals(string(object, "_type"))
                    || sortOfJava(string(object, "_java_type"))
                    != Sort.REF) {
                return false;
            }
            String port = findPort(string(object, "_exp"));
            Port schema = ports.get(port);
            return schema != null
                    && JavaPrimitiveBoxing.wrapperType(schema.javaType);
        }

        private Term floatingPromotion(Term term, Sort target,
                                       String origin) {
            FloatingKind targetKind = floatingKind(target);
            if (term.sort == target) return term;
            if (term.sort.floating()) {
                String converted = JavaPrimitiveSmtSemantics
                        .floatingConversion(term.text,
                                floatingKind(term.sort), targetKind);
                if (converted != null) return dependent(new Term(converted,
                        target), term);
            } else if (term.sort == Sort.INT
                    && term.integralWidth != IntegralWidth.NONE) {
                String converted = JavaPrimitiveSmtSemantics
                        .integralToFloating(term.text, targetKind);
                if (converted != null) return dependent(new Term(converted,
                        target), term);
            }
            unsupported.add("UnsupportedJavaNumericPromotion:" + origin
                    + ":" + term.sort + "->" + target);
            return unsupportedTerm(target);
        }

        /** Emits exact core Java String predicates/value operations plus the
         * materially different Java/SMT semantics remain fail-closed. */
        private Term stringOperation(JsonObject expression) {
            String operation = string(expression, "_name");
            boolean negated = bool(expression, "_is_not", false);
            JsonArray params = array(expression, "_param_list");
            if ("isEmpty".equals(operation)) {
                List<Term> strings = exactStringParameters(params, 1);
                if (strings == null) {
                    return codecGap("OpStrExpression." + operation,
                            params.size() == 1 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.BOOL);
                }
                Term receiver = strings.get(0);
                return booleanStringResult("(= (str.len " + receiver.text
                        + ") 0)", negated,
                        stringDereferencePrecondition(receiver));
            }
            if ("length".equals(operation)) {
                if (negated) {
                    return codecGap("OpStrExpression.length",
                            "NEGATED_VALUE_OPERATION", Sort.INT);
                }
                List<Term> strings = exactStringParameters(params, 1);
                if (strings == null) {
                    return codecGap("OpStrExpression.length",
                            params.size() == 1 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.INT);
                }
                Term receiver = strings.get(0);
                Term length = new Term("(str.len " + receiver.text + ")",
                        Sort.INT, IntegralWidth.JAVA_INT).withPrecondition(
                        stringDereferencePrecondition(receiver));
                assertJavaIntegralDomain(length.text, length.sort, "I",
                        "java_string_length");
                return length;
            }
            if ("equals".equals(operation)) {
                if (params.size() != 2) {
                    return codecGap("OpStrExpression.equals", "ARITY",
                            Sort.BOOL);
                }
                Term receiver = term(params.get(0), null);
                Term argument = term(params.get(1), null);
                if (receiver.sort != Sort.STRING) {
                    return codecGap("OpStrExpression.equals",
                            "NON_STRING_PARAMETER", Sort.BOOL);
                }
                String predicate;
                if (isNull(argument)) {
                    predicate = "false";
                } else if (argument.sort == Sort.STRING) {
                    predicate = and(Arrays.asList(
                            stringNonNull(argument),
                            "(= " + receiver.text + " "
                                    + argument.text + ")"));
                } else {
                    return codecGap("OpStrExpression.equals",
                            "ARGUMENT_DYNAMIC_TYPE_UNMODELED", Sort.BOOL);
                }
                String defined = and(Arrays.asList(receiver.precondition,
                        stringNonNull(receiver), argument.precondition));
                return booleanStringResult(predicate, negated, defined);
            }
            if ("contains".equals(operation)
                    || "startsWith".equals(operation)
                    || "endsWith".equals(operation)) {
                List<Term> strings = exactStringParameters(params, 2);
                if (strings == null) {
                    return codecGap("OpStrExpression." + operation,
                            params.size() == 2 ? "NON_STRING_PARAMETER"
                                    : "ARITY", Sort.BOOL);
                }
                Term receiver = strings.get(0);
                Term argument = strings.get(1);
                String predicate;
                if ("contains".equals(operation)) {
                    predicate = "(str.contains " + receiver.text + " "
                            + argument.text + ")";
                } else if ("startsWith".equals(operation)) {
                    predicate = "(str.prefixof " + argument.text + " "
                            + receiver.text + ")";
                } else {
                    predicate = "(str.suffixof " + argument.text + " "
                            + receiver.text + ")";
                }
                return booleanStringResult(predicate, negated,
                        stringDereferencePrecondition(receiver, argument));
            }
            if (negated) {
                return codecGap("OpStrExpression." + operation,
                        "NEGATED_VALUE_OPERATION", Sort.STRING);
            }
            if ("concat".equals(operation)) {
                if (params.size() == 0) {
                    return codecGap("OpStrExpression.concat", "EMPTY",
                            Sort.STRING);
                }
                List<Term> strings = exactStringParameters(params,
                        params.size());
                if (strings == null) return codecGap(
                        "OpStrExpression.concat", "NON_STRING_PARAMETER",
                        Sort.STRING);
                String defined = stringDereferencePrecondition(
                        strings.toArray(new Term[strings.size()]));
                if (strings.size() == 1) {
                    return Term.nonNullString(strings.get(0).text, defined);
                }
                StringBuilder result = new StringBuilder("(str.++");
                for (Term value : strings) {
                    result.append(' ').append(value.text);
                }
                return Term.nonNullString(result.append(')').toString(),
                        defined);
            }
            if ("toString".equals(operation)) {
                if (params.size() != 1
                        || !isPrimitiveIntExpression(params.get(0))) {
                    return codecGap("OpStrExpression.toString",
                            "REQUIRES_ONE_PRIMITIVE_INT", Sort.STRING);
                }
                Term integer = term(params.get(0), Sort.INT);
                if (integer.sort != Sort.INT) {
                    return codecGap("OpStrExpression.toString",
                            "NON_INT_TERM", Sort.STRING);
                }
                assertJavaIntRange(integer);
                return javaIntString(integer);
            }
            return codecGap("OpStrExpression." + firstNonBlank(operation,
                    "unknown"), "UNSUPPORTED_OPERATION", Sort.STRING);
        }

        private List<Term> exactStringParameters(JsonArray params,
                                                 int expectedArity) {
            if (params.size() != expectedArity) return null;
            List<Term> result = new ArrayList<>();
            for (JsonElement parameter : params) {
                // Passing STRING as an expected sort would let a malformed
                // primitive SymbolExpression be declared as String. Derive
                Term value = term(parameter, null);
                if (value.sort != Sort.STRING) return null;
                result.add(value);
            }
            return result;
        }

        private Term booleanStringResult(String predicate,
                                         boolean negated,
                                         String precondition) {
            return new Term(negated ? "(not " + predicate + ")"
                    : predicate, Sort.BOOL).withPrecondition(precondition);
        }

        /**
         * Recognizes the sound Java round trip
         */
        private Term parseIntTerm(JsonObject expression) {
            JsonArray params = array(expression, "_param_list");
            if (params.size() != 1 && params.size() != 2) {
                return codecGap("java/lang/Integer.parseInt", "ARITY",
                        Sort.INT);
            }
            if (params.size() == 2) {
                Integer radix = exactIntLiteral(params.get(1));
                if (radix == null || radix != 10) {
                    return codecGap("java/lang/Integer.parseInt",
                            "RADIX_NOT_LITERAL_10", Sort.INT);
                }
            }
            SplitSegment match = exactSplitSegment(params.get(0));
            if (!match.complete()) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_NOT_PROVED_" + match.gap, Sort.INT);
            }
            // parseInt inverts Integer.toString only when the element is
            // that rendering and nothing else; any surrounding text would
            SplitPiece source = match.singleIntegerPiece();
            if (source == null) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_ELEMENT_NOT_ONE_INT_RENDERING", Sort.INT);
            }
            Term integer = integerPieceTerm(source);
            if (integer.sort != Sort.INT) {
                return codecGap("java/lang/Integer.parseInt",
                        "ROUNDTRIP_SOURCE_NOT_INT", Sort.INT);
            }
            assertJavaIntRange(integer);
            return integer;
        }

        private Term splitElementTerm(JsonObject expression) {
            SplitSegment match = exactSplitSegment(expression);
            if (!match.complete()) {
                return codecGap("java/lang/String.splitElement", match.gap,
                        Sort.STRING);
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
                    return codecGap("java/lang/String.splitElement",
                            "ROUNDTRIP_SOURCE_NOT_INT", Sort.STRING);
                }
                assertJavaIntRange(integer);
                Term rendered = javaIntString(integer);
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
            if (!"MethodExpression".equals(string(split, "_type"))
                    || !isJavaSplitElement(string(split, "_name"))) {
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
            String delimiterGap = literalDelimiterGap(delimiter);
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
            return "SymbolExpression".equals(string(object, "_type"))
                    && !findPort(string(object, "_exp")).isEmpty();
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
            if (!"OpStrExpression".equals(string(object, "_type"))
                    || !"toString".equals(string(object, "_name"))
                    || bool(object, "_is_not", false)
                    || params.size() != 1
                    || !isPrimitiveIntExpression(params.get(0))) {
                return null;
            }
            return params.get(0);
        }

        private Term javaIntString(Term integer) {
            return Term.nonNullString("(java_int_to_string "
                    + integer.text + ")", integer.precondition);
        }

        private void assertJavaIntRange(Term integer) {
            String key = currentGuard + "\u0000" + integer.text;
            if (!javaIntRangeAssertions.add(key)) return;
            assertNamed("java_int_range_" + javaIntRangeAssertions.size(),
                    "(and (<= (- 2147483648) " + integer.text + ")"
                            + " (<= " + integer.text + " 2147483647))");
        }

        private void assertJavaIntegralDomain(String term, Sort sort,
                                              String javaType,
                                              String identity) {
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
                    "(and (<= " + domain.lower + " " + term + ")"
                            + " (<= " + term + " " + domain.upper + "))");
        }

        private Term codecGap(String operation, String gap, Sort sort) {
            unsupported.add("MODEL_SEMANTICS_MISSING:" + operation + ":"
                    + gap);
            return unsupportedTerm(sort);
        }

        /**
         * Admits only a delimiter that is one ordinary literal character.
         */
        private String literalDelimiterGap(String value) {
            if (value == null || value.length() != 1) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            char delimiter = value.charAt(0);
            if (Character.isISOControl(delimiter)) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            if ("\\.^$|?*+()[]{}".indexOf(delimiter) >= 0) {
                return "REGEX_NOT_SAFE_SINGLE_LITERAL";
            }
            return "";
        }

        private String methodConstraint(JsonObject expression) {
            String name = string(expression, "_name");
            if (isJavaParseInt(name) || isJavaSplitElement(name)) {
                boolean split = isJavaSplitElement(name);
                Term value = methodTerm(expression);
                Term result = term(expression.get("_res_exp"),
                        split ? Sort.STRING : Sort.INT);
                if (!split) {
                    return and(Arrays.asList(result.precondition,
                            value.precondition, "(= " + result.text + " "
                                    + value.text + ")"));
                }
                Term boxedPrefix = asValue(value, "");
                Term boxedResult = asValue(result, "");
                return and(Arrays.asList(boxedPrefix.precondition,
                        boxedResult.precondition, "(= " + boxedResult.text
                                + " " + boxedPrefix.text + ")"));
            }
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(name, "unknown"));
            return "false";
        }

        private Term methodTerm(JsonObject expression) {
            String method = string(expression, "_name");
            if (isJavaParseInt(method)) {
                return parseIntTerm(expression);
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression);
            }
            Term result = term(expression.get("_res_exp"), null);
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(method, "unknown"));
            return unsupportedTerm(result.sort);
        }

        private void regionSummary(RelationSummary selected) {
            regionSummary(selected, new InvocationKey(selected.regionId(),
                    selected.occurrenceId()), "selected");
        }

        private void regionSummary(RelationSummary selected,
                                   InvocationKey invocation,
                                   String scopeSuffix) {
            JsonObject summary = selected.toJson();
            // Null for README section 3's T_C1.  Everything below that reads
            // it is a question about a demanded output, and a consumer has
            OutputClosureContract outputClosure =
                    selected.outputClosure();
            String region = selected.regionId();
            if (!bool(summary, "relationallyComplete", false)) {
                heapGap("IncompleteRegionSummary@" + region);
                return;
            }
            JsonObject relation = object(summary, "regionRelation");
            if (!"GUARDED_PATH_MERGE".equals(string(relation, "kind"))) {
                heapGap("UnsupportedRegionRelation@" + region);
                return;
            }
            String previousScope = enterSymbolScope("summary:"
                    + firstNonBlank(string(summary, "summaryId"),
                    region, "selected") + ":" + scopeSuffix + ":"
                    + invocation.instanceId);
            InvocationKey previousInvocation = enterInvocation(invocation);
            try {
                guardedRegionRelation(invocation, relation, outputClosure);
            } finally {
                restoreInvocation(previousInvocation);
                restoreSymbolScope(previousScope);
            }
        }

        private void guardedRegionRelation(InvocationKey invocation,
                                           JsonObject relation,
                                           OutputClosureContract outputClosure) {
            String region = invocation.regionId;
            JsonArray cases = array(relation, "cases");
            if (cases.size() == 0) {
                heapGap("GuardedPathCaseCountGap@" + region);
                return;
            }
            // OCC-1: the cases of one relation may be several activations
            // of one planned address.  They are not alternatives -- all of
            // them ran -- so each is lowered as its own occurrence and the
            // exactly-one partition is drawn inside an occurrence, never
            // across them.
            Map<String, List<String>> selectorsByOccurrence =
                    new LinkedHashMap<>();
            List<String> selectors = new ArrayList<>();
            Set<String> selectorSymbols = new LinkedHashSet<>();
            String previousGuard = currentGuard;
            for (int index = 0; index < cases.size(); index++) {
                // Guard construction belongs to the outer relation.  Leaving
                // case N's implication active here would bind case N+1 inputs
                currentGuard = previousGuard;
                if (!cases.get(index).isJsonObject()) {
                    heapGap("MalformedGuardedPathCase@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject item = cases.get(index).getAsJsonObject();
                if (string(item, "sourceTaskId").isEmpty()) {
                    heapGap("MissingRegionCaseSourceTask@" + region
                            + ":" + index);
                    continue;
                }
                Set<String> casePorts = new LinkedHashSet<>(
                        object(item, "outputExpressions").keySet());
                for (JsonElement event : array(item,
                        RelationSummary.INTERACTION_EVENTS)) {
                    if (!event.isJsonObject()) continue;
                    String port = string(event.getAsJsonObject(), "portId");
                    if (!port.isEmpty()) casePorts.add(port);
                }
                // OCC-1: an activation the importer marked partial carries
                // only the members it captured, so it publishes a subset of
                // the joint demand by construction.  It stays a case -- the
                // mark travels into the manifest's case evidence -- and a
                // consumer that demands a port this occurrence never produced
                // is still refused by name where the producer is selected.
                boolean partialActivation = item.has("relationallyComplete")
                        && !bool(item, "relationallyComplete", true);
                // Once-only-root rule: a complete occurrence owes no port
                // whose only writers are instance-scoped once-only heap
                // writes it never sampled, so the ports it did not produce
                // being exactly those is not a joint-set mismatch.  Asked of
                // the one authority every owner of this rule asks, which is
                // fail-closed on a writer set that will not decode and on a
                // flag stated on any capture kind but an exact heap write.
                // Inert for every closure with no such port (all matrix
                // closures).
                boolean onlyInstanceScopedMissing = false;
                if (outputClosure != null) {
                    Set<String> missing = new LinkedHashSet<>(
                            outputClosure.outputPorts());
                    missing.removeAll(casePorts);
                    onlyInstanceScopedMissing = !missing.isEmpty()
                            && outputClosure.onceOnlyInstanceScopedPorts()
                                    .containsAll(missing)
                            && outputClosure.outputPorts()
                                    .containsAll(casePorts);
                }
                if (outputClosure != null
                        && outputClosure.outputPorts().size() > 1
                        && !casePorts.equals(outputClosure.outputPorts())
                        && !(partialActivation && outputClosure.outputPorts()
                                .containsAll(casePorts))
                        && !onlyInstanceScopedMissing) {
                    heapGap("JointOutputExpressionSetMismatch@" + region
                            + ":" + index);
                    continue;
                }
                JsonObject guardIr = object(item, "guard");
                if (!"PATH_CONDITION".equals(string(guardIr, "kind"))) {
                    heapGap("UnsupportedRegionGuard@" + region
                            + ":" + index);
                    continue;
                }
                String stated = string(item, "occurrenceId");
                String caseOccurrence = stated.isEmpty()
                        ? invocation.instanceId : stated;
                // One occurrence per case: this is what keeps two activations
                // off one `port__X__instance__Y` constant, off one symbol
                // scope, and off one recorded-event scope.
                InvocationKey caseInvocation =
                        caseOccurrence.equals(invocation.instanceId)
                        ? invocation
                        : new InvocationKey(region, caseOccurrence);
                String caseIdentity = RecordedSessionModel.caseOwner(region,
                        caseOccurrence, string(item, "caseId"), index);
                InvocationKey previousInvocation =
                        enterInvocation(caseInvocation);
                String previousScope = enterSymbolScope(caseIdentity);
                try {
                    List<String> conditionTerms = new ArrayList<>();
                    for (JsonElement expression : array(guardIr,
                            "conditions")) {
                        conditionTerms.add(constraint(expression,
                                "region " + region + " case " + index));
                    }
                    String guard = and(conditionTerms);
                    String selector = RecordedSessionModel.caseSelector(
                            caseIdentity);
                    if (!selectorSymbols.add(selector)) {
                        heapGap("DuplicateCaseSelector@" + region + ":"
                                + index);
                    }
                    selectors.add(selector);
                    declare(selector, Sort.BOOL);
                    // README CASE-1: the case's own edge bindings are guarded
                    // by this same constant, so record it as defined here
                    loweredCaseSelectors.add(selector);
                    // A selector identifies one complete producer causal
                    selectorsByOccurrence.computeIfAbsent(caseOccurrence,
                            ignored -> new ArrayList<>()).add(selector);
                    assertNamed("case_selector_definition_" + region + "_"
                                    + index,
                            "(=> " + selector + " " + guard + ")");
                    currentGuard = selector;
                    recordFatalAbsenceRemovalEffects(caseInvocation, item,
                            selector);
                    bindOutputExpressions(region, item, outputClosure);
                } finally {
                    currentGuard = previousGuard;
                    restoreSymbolScope(previousScope);
                    enterInvocation(previousInvocation);
                }
            }
            currentGuard = previousGuard;
            if (selectors.size() == cases.size() && !selectors.isEmpty()) {
                // One occurrence follows exactly one of its own recorded
                // cases.  Several occurrences of one address each follow one
                // of theirs, and they all happened: summing across them would
                // say that only one activation ever ran.
                for (Map.Entry<String, List<String>> entry
                        : selectorsByOccurrence.entrySet()) {
                    StringBuilder partition = new StringBuilder("(= (+");
                    for (String selector : entry.getValue()) {
                        partition.append(" (ite ").append(selector)
                                .append(" 1 0)");
                    }
                    // A relation with one occurrence keeps the name it always
                    // had; only a relation that really holds several needs
                    // them told apart.
                    assertNamed(selectorsByOccurrence.size() == 1
                            ? "region_case_selector_partition_" + region
                            : "region_case_selector_partition_" + region + "_"
                                    + smtName(entry.getKey()),
                            partition.append(") 1)").toString());
                }
            } else {
                heapGap("CaseSelectorPartitionGap@" + region);
            }
        }

        private void recordFatalAbsenceRemovalEffects(
                InvocationKey invocation, JsonObject pathCase,
                String selector) {
            for (String output : failureWitness.outputsFor(invocation)) {
                JsonElement expression = object(pathCase,
                        "outputExpressions").get(output);
                if (expression == null) continue;
                Set<String> previousRequirements =
                        currentContainerRequirements;
                Set<String> requirements = new LinkedHashSet<>();
                currentContainerRequirements = requirements;
                List<ContainerSmtCodec.AssociativeRemovalEffect> effects;
                try {
                    effects = ContainerSmtCodec
                            .associativeRemovalEffects(expression,
                                    containerHost());
                } finally {
                    currentContainerRequirements = previousRequirements;
                }
                PortOccurrence source = new PortOccurrence(invocation,
                        output);
                for (ContainerSmtCodec.AssociativeRemovalEffect effect
                        : effects) {
                    List<String> preconditions = new ArrayList<>(requirements);
                    preconditions.add(effect.precondition);
                    failureWitness.addEffect(source,
                            new FatalAbsenceMutationWitness.RemovalCaseEffect(
                                    selector, effect.removedKey.text,
                                    and(preconditions)));
                }
            }
        }

        private void bindOutputExpressions(String region,
                                           JsonObject summary,
                                           OutputClosureContract closure) {
            JsonObject outputs = object(summary, "outputExpressions");
            for (Map.Entry<String, JsonElement> entry
                    : outputs.entrySet()) {
                String port = entry.getKey();
                if (!ports.contains(port)
                        || !entry.getValue().isJsonObject()) {
                    heapGap("OutputExpressionEndpoint@" + region + ":"
                            + port);
                    continue;
                }
                requireExactRuntimePutReferenceValue(port,
                        entry.getValue(), closure);
                requireObservedSnapshotReferenceMembers(entry.getValue());
                Term value = term(entry.getValue(), portSort(port));
                if (value.sort == Sort.MAP
                        || value.sort == Sort.ARRAY_VALUE) {
                    promotePort(port, value.sort);
                }
                bindPort(port, value);
            }
        }

        /**
         * Preserves the non-null identity of the reference value observed by
         */
        private void requireExactRuntimePutReferenceValue(
                String port, JsonElement expression,
                OutputClosureContract closure) {
            if (closure == null) return;
            OutputClosureContract.Member member = closure.member(port);
            Port schema = ports.get(port);
            if (member == null || schema == null
                    || expression == null || !expression.isJsonObject()) {
                return;
            }
            long selectedEvent = longInteger(member.slice(),
                    "selectedRuntimeEventSeq", -1L);
            if (selectedEvent < 0L) return;

            JsonObject selectedAccess = null;
            int selectedAccessCount = 0;
            for (JsonElement element : array(schema.metadata,
                    "runtimeAccesses")) {
                if (!element.isJsonObject()) continue;
                JsonObject access = element.getAsJsonObject();
                if (longInteger(access, "eventSeq", -1L)
                        != selectedEvent) {
                    continue;
                }
                selectedAccess = access;
                selectedAccessCount++;
            }
            if (selectedAccessCount != 1
                    || !"EXACT_RUNTIME_ASSOCIATIVE_PUT_PROVENANCE_V1"
                    .equals(string(selectedAccess,
                            "containerMemberIdentityAuthority"))
                    || longInteger(selectedAccess,
                            "containerValueObjectId", 0L) <= 0L) {
                return;
            }

            JsonObject relation = expression.getAsJsonObject();
            JsonArray arguments = array(relation, "arguments");
            if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(relation, "_type"))
                    || !"ASSOCIATIVE".equals(string(relation, "shape"))
                    || !"PUT".equals(string(relation, "operation"))
                    || arguments.size() != 2) {
                return;
            }
            JsonElement valueExpression = arguments.get(1);
            Term value = term(valueExpression, null);
            if (value.sort != Sort.REF || isNull(value)) return;
            String identity = currentSymbolScope + "\u0000" + port
                    + "\u0000" + selectedEvent + "\u0000"
                    + longInteger(selectedAccess,
                    "containerValueObjectId", 0L) + "\u0000"
                    + CanonicalJson.render(valueExpression);
            assertNamed("exact_runtime_put_reference_non_null_"
                            + CanonicalJson.sha256(identity)
                            .substring(0, 16),
                    "(distinct " + value.text + " nullRef)");
        }

        /**
         * Normal-exit container outputs are rebuilt by the runtime from the
         */
        private void requireObservedSnapshotReferenceMembers(
                JsonElement expression) {
            List<JsonElement> members = new ArrayList<>();
            JsonElement cursor = expression;
            boolean exactSnapshot = false;
            while (cursor != null && cursor.isJsonObject()) {
                JsonObject relation = cursor.getAsJsonObject();
                if (!ContainerSmtCodec.EXPRESSION_TYPE.equals(
                        string(relation, "_type"))) {
                    break;
                }
                String operation = string(relation, "operation");
                if (ContainerSmtCodec.emptiesState(operation)) {
                    exactSnapshot = true;
                    break;
                }
                String shape = string(relation, "shape");
                JsonArray arguments = array(relation, "arguments");
                if ("ASSOCIATIVE".equals(shape)
                        && "PUT".equals(operation)
                        && arguments.size() == 2) {
                    members.add(arguments.get(0));
                    members.add(arguments.get(1));
                } else if ("INDEXED".equals(shape)
                        && "APPEND".equals(operation)
                        && arguments.size() == 1) {
                    members.add(arguments.get(0));
                } else {
                    break;
                }
                cursor = relation.get("receiver");
            }
            if (!exactSnapshot) return;

            for (JsonElement member : members) {
                Term value = term(member, null);
                if (value.sort != Sort.REF || isNull(value)) continue;
                String identity = currentSymbolScope + "\u0000"
                        + CanonicalJson.render(member);
                assertNamed("observed_snapshot_reference_non_null_"
                                + CanonicalJson.sha256(identity)
                                .substring(0, 16),
                        "(distinct " + value.text + " nullRef)");
            }
        }

        private void heapGap(String detail) {
            unsupported.add(detail);
        }

        private void declareBoundedPosition(String position, int bound) {
            declare(position, Sort.INT);
            assertNamed(position + "_bounds", "(and (<= 0 " + position
                    + ") (< " + position + " " + bound + "))");
        }

        private void mergeEdgeBindings(Collection<ResolvedEdge> edges) {
            // Decide this from the whole selected set before lowering it.
            // Edge order is not evidence: a diagnostic candidate may sort
            for (ResolvedEdge edge : edges) {
                if (edge.topologyOnly) continue;
                JsonObject binding = edge.binding;
                String provenance = string(binding,
                        RecordedReadFrom.EDGE_PROVENANCE);
                if (RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                        || RecordedReadFrom.PROVENANCE_GUARDED.equals(
                        provenance)) {
                    recordedDecidedConsumerPorts.add(occurrence(
                            bindingTargetInstance(binding),
                            bindingTargetInput(binding)));
                }
            }
            int edgeIndex = 0;
            for (ResolvedEdge edge : edges) {
                if (edge.topologyOnly) continue;
                // README CASE-1.  The binding names the cases whose execution
                String previousGuard = currentGuard;
                currentGuard = conjunction(previousGuard,
                        bindingCaseGuard(edge.binding));
                try {
                    mergeEdgeBinding(edge.binding, edgeIndex++);
                } finally {
                    currentGuard = previousGuard;
                }
            }
        }

        /**
         * The guard under which one edge binding's evidence was observed.
         */
        private String bindingCaseGuard(JsonObject binding) {
            JsonArray owners = array(binding,
                    RelationSummary.CASE_SELECTORS);
            if (owners.size() == 0) return "";
            List<String> defined = new ArrayList<>();
            for (JsonElement element : owners) {
                String selector = element.isJsonPrimitive()
                        ? element.getAsString() : "";
                if (loweredCaseSelectors.contains(selector)) {
                    defined.add(selector);
                }
            }
            if (defined.isEmpty()) {
                // Named, not asserted: guarding this arm would reference a
                // enablement CASE-1 forbids.
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        "EDGE_BINDING_CASE_NOT_LOWERED",
                        string(binding, "edgeId"),
                        "the relation case that resolved this edge is not"
                                + " lowered in this composition"));
                return "";
            }
            return or(defined);
        }

        /** Lowers one selected edge under its own case guard. */
        private void mergeEdgeBinding(JsonObject binding, int edgeIndex) {
            String region = bindingSourceRegion(binding);
            String targetRegion = string(binding, "toRegion");
            String output = bindingSourceOutput(binding);
            String input = bindingTargetInput(binding);
            PortOccurrence outputOccurrence = occurrence(
                    bindingSourceInstance(binding), output);
            PortOccurrence inputOccurrence = occurrence(
                    bindingTargetInstance(binding), input);
            String label = "edge_binding_" + region + "_to_"
                    + targetRegion + "_" + edgeIndex;
            if (!ports.contains(output) || !ports.contains(input)) {
                heapGap("EdgeBindingPortGap@" + region
                        + ":" + output + "->" + input);
                return;
            }
            if (skipExcludedWriter(binding)) return;
            String provenance = string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE);
            if (recordedDecidedConsumerPorts.contains(inputOccurrence)
                    && !RecordedReadFrom.PROVENANCE_EXACT.equals(
                    provenance)
                    && !RecordedReadFrom.PROVENANCE_GUARDED.equals(
                    provenance)) {
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        "RECORDED_EVIDENCE_DECIDED_CONSUMER_PORT",
                        string(binding, "edgeId"),
                        "consumer port " + inputOccurrence + " was"
                                + " already decided by VM read-from"
                                + " evidence; this diagnostic candidate"
                                + " is retained for audit and not"
                                + " composed"));
                return;
            }
            if (emittedEdgeBindings.contains(edgeBindingKey(binding))) {
                return;
            }
            // An exact read-from is an equality, not a choice: the VM
            // proved which write the read took, so a selector over one
            if (RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)) {
                if (bindRecordedExactWriter(binding, outputOccurrence,
                        inputOccurrence, label)) {
                } else {
                    heapGap("UnresolvedRecordedExactBinding:"
                            + string(binding, "edgeId"));
                }
                return;
            }
            if ("EQUALITY".equals(bindingRelationKind(binding))) {
                String equalityAssertion = assertPortBindingEqualityNamed(
                        outputOccurrence, inputOccurrence, label);
                if (!equalityAssertion.isEmpty()) {
                    emitRecordedBindingOrder(binding, label,
                            equalityAssertion);
                    emittedEdgeBindings.add(edgeBindingKey(binding));
                    failureWitness.connect(binding, outputOccurrence,
                            inputOccurrence, "true",
                            portName(inputOccurrence));
                } else {
                    heapGap("EdgeBindingEqualityGap@" + region
                            + ":" + output + "->" + input);
                }
                return;
            }
            if (bindRecordedGuardedRead(binding, outputOccurrence,
                    inputOccurrence, label)) {
                emittedEdgeBindings.add(edgeBindingKey(binding));
            } else {
                heapGap("UnresolvedRecordedEdgeBinding:"
                        + string(binding, "edgeId"));
            }
        }


        /** Lowers one selected region occurrence's guarded relation. */
        private void lowerRelation(RelationSummary selection) {
            regionSummary(selection);
        }

        /**
         * Lowers the case-local VM handoffs of the selected occurrences.
         *
         * <p>Wave 3 C3: a handoff row's {@code expression} is the sender's
         * expression, read back from the receiving storage after attach.  It
         * is therefore bound at the receiver directly, from the recorded
         * lineage the row already carries.  No producer case is looked up:
         * the row states {@code producerTaskId}/{@code producerOccurrenceId}
         * as provenance for the ledger, and the producer's own path
         * conditions are lowered once by its relation summary.  What stays
         * is the ORDER evidence README {@code RPC-1}/{@code EVENT-1} require
         * - both endpoints of the exact {@code VALUE_HANDOFF} edge and the
         * per-receiver send-before-receive assertion.</p>
         */
        private void mergeVmHandoffs(List<JsonObject> caseRows,
                                     List<JsonObject> producerCaseRows,
                                     BoundedLoopComposition model,
                                     RecordedSessionModel recorded) {
            Map<String, List<String>> producerSelectors =
                    producerCaseSelectors(producerCaseRows);
            for (JsonObject owner : caseRows) {
                String occurrence = string(owner, "toOccurrenceId");
                String caseOwner = string(owner,
                        RecordedSessionModel.CASE_OWNER);
                String selector = string(owner,
                        RecordedSessionModel.CASE_SELECTOR);
                List<JsonObject> events = VmHandoffEvidence.eventsOf(owner);
                if (events.isEmpty()) continue;
                if (occurrence.isEmpty()) {
                    model.gap("HANDOFF_CASE_OCCURRENCE_MISSING", "",
                            "a VM handoff case names no receiving occurrence");
                    continue;
                }
                if (caseOwner.isEmpty()) {
                    model.gap("HANDOFF_CASE_SCOPE_MISSING", occurrence,
                            "a VM handoff is not owned by one exact producer"
                                    + " or target path case");
                    unsupported.add("HANDOFF_CASE_SCOPE_MISSING:"
                            + occurrence);
                    continue;
                } else if (selector.isEmpty()
                        || !selector.equals(RecordedSessionModel.caseSelector(
                        caseOwner))) {
                    model.gap("HANDOFF_CASE_SCOPE_MISSING", caseOwner,
                            "a guarded VM handoff has no exact case selector");
                    unsupported.add("HANDOFF_CASE_SCOPE_MISSING:"
                            + caseOwner);
                    continue;
                }
                Map<String, List<JsonObject>> byPort = new LinkedHashMap<>();
                for (JsonObject event : events) {
                    byPort.computeIfAbsent(string(event, "portId"),
                            ignored -> new ArrayList<>()).add(event);
                }
                for (Map.Entry<String, List<JsonObject>> entry
                        : byPort.entrySet()) {
                    if (entry.getValue().size() != 1) {
                        model.gap("HANDOFF_CASE_VALUE_AMBIGUOUS",
                                occurrence + ":" + entry.getKey(),
                                "one case attached more than one value to the"
                                        + " same unversioned receiving port");
                        continue;
                    }
                    emitVmHandoff(entry.getValue().get(0), occurrence,
                            caseOwner, selector, producerSelectors, model,
                            recorded);
                }
            }
        }

        /**
         * Indexes the imported cases by the execution that produced them.
         *
         * <p>This is a lookup, not a search: the key is exactly the pair a
         * VM handoff row already states, and every case that ran under that
         * pair is kept.  Nothing is narrowed by port, event or ordinal, so
         * there is no tie for a heuristic to break and no refusal to raise.
         * </p>
         */
        private Map<String, List<String>> producerCaseSelectors(
                List<JsonObject> producerCaseRows) {
            Map<String, List<String>> result = new LinkedHashMap<>();
            for (JsonObject candidate : producerCaseRows == null
                    ? Collections.<JsonObject>emptyList()
                    : producerCaseRows) {
                String owner = string(candidate,
                        RecordedSessionModel.CASE_OWNER);
                if (owner.isEmpty()) continue;
                String key = string(candidate, "sourceTaskId") + "\n"
                        + string(candidate, "toOccurrenceId");
                List<String> selectors = result.get(key);
                if (selectors == null) {
                    selectors = new ArrayList<>();
                    result.put(key, selectors);
                }
                String selector = RecordedSessionModel.caseSelector(owner);
                if (!selectors.contains(selector)) selectors.add(selector);
            }
            return result;
        }

        private void emitVmHandoff(JsonObject event, String occurrenceId,
                                   String caseOwner, String caseSelector,
                                   Map<String, List<String>> producerSelectors,
                                   BoundedLoopComposition model,
                                   RecordedSessionModel recorded) {
            long localExportEvent = longInteger(event, "exportEventId", 0L);
            long exportEvent = recorded.resolveEventId(caseOwner,
                    localExportEvent);
            String consumerPort = string(event, "portId");
            JsonObject evidence = event.deepCopy();
            // The receiving occurrence is the case's, not the event's: a VM
            // handoff reference states which export it attached, and the case
            evidence.addProperty("toOccurrenceId", occurrenceId);
            evidence.addProperty("kind", VmHandoffEvidence.BINDING_KIND);
            if (!caseOwner.isEmpty()) {
                evidence.addProperty(RecordedSessionModel.CASE_OWNER,
                        caseOwner);
                evidence.addProperty(RecordedSessionModel.CASE_SELECTOR,
                        caseSelector);
            }
            if (exportEvent <= 0L) {
                String subject = occurrenceId + ":" + consumerPort + ":"
                        + localExportEvent + ":" + caseOwner;
                unsupported.add(HANDOFF_ORDER_UNRECORDED + ":" + subject);
                model.gap(HANDOFF_ORDER_UNRECORDED, subject,
                        "the RPC export id cannot be resolved inside the"
                                + " receiving replay case");
                return;
            }
            evidence.addProperty("localExportEventId", localExportEvent);
            evidence.addProperty("exportEventId", exportEvent);
            // README RPC-1: the send-before-receive edge names both of its
            // endpoints.  One export may be attached at several receivers, so
            long localAttachEvent = VmHandoffEvidence.attachEventOf(event);
            long attachEvent = recorded.resolveEventId(caseOwner,
                    localAttachEvent);
            evidence.addProperty("localAttachEventId", localAttachEvent);
            evidence.addProperty(VmHandoffEvidence.ATTACH_EVENT_ID,
                    attachEvent);
            String order = recorded.handoffOrderAssertion(
                    localExportEvent, localAttachEvent, caseSelector);
            if (order.isEmpty() && model != null) {
                String subject = occurrenceId + ":" + consumerPort + ":"
                        + exportEvent;
                unsupported.add(HANDOFF_ORDER_UNRECORDED + ":" + subject);
                model.gap(HANDOFF_ORDER_UNRECORDED,
                        subject,
                        "the recorded order domain holds no VALUE_HANDOFF"
                                + " edge for this export event, so"
                                + " send < receive is not asserted");
                return;
            }
            evidence.addProperty("orderAssertion", order);
            PortOccurrence consumer = occurrence(
                    string(evidence, "toOccurrenceId"), consumerPort);
            if (!ports.contains(consumerPort)) {
                if (model != null) {
                    model.gap(HANDOFF_PORT_UNDECLARED, consumerPort,
                            "the runtime region port catalog declares no such"
                                    + " port, so this handoff is a model row"
                                    + " and no SMT term");
                }
                return;
            }

            // Wave 3 C3.  The receiver's storage already denotes the
            // sender's expression, so no producer case is searched to lower
            // it.  What the row does state is which producer sent it, and
            // that is the scope the expression is lowered in: a raw VM symbol
            // is unique only inside one replay execution, so two independent
            // producers whose locals happen to share a spelling must not
            // collapse onto one SMT root.  Configured-source roots are named
            // by the VM symbol itself and stay shared across scopes, which is
            // how the sender's and the receiver's view of one propagated
            // value remain the same term.
            String producerTask = string(event,
                    VmHandoffEvidence.PRODUCER_TASK_ID);
            String producerOccurrence = string(event,
                    VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);

            // The stated producer ran, because this receive happened.  That
            // implication is lineage the row carries, so it is restated here
            // as one assertion over the cases the same (task, occurrence)
            // imported: one case is an equality, several are the disjunction
            // of the valuations that execution took, and none imported says
            // nothing.  The producer's own path conditions are lowered once,
            // by its relation summary, and are not repeated here.
            List<String> statedProducers = producerSelectors.get(
                    producerTask + "\n" + producerOccurrence);
            if (statedProducers != null && !statedProducers.isEmpty()) {
                String priorLinkGuard = currentGuard;
                currentGuard = firstNonBlank(caseSelector);
                try {
                    for (String selector : statedProducers) {
                        declare(selector, Sort.BOOL);
                    }
                    assertNamed("vm_handoff_producer_guard_"
                                    + sha256(producerTask + "\n"
                                    + producerOccurrence + "\n"
                                    + consumerPort).substring(0, 16),
                            statedProducers.size() == 1
                                    ? statedProducers.get(0)
                                    : or(statedProducers));
                } finally {
                    currentGuard = priorLinkGuard;
                }
                JsonArray statedRow = new JsonArray();
                for (String selector : statedProducers) {
                    statedRow.add(selector);
                }
                evidence.add("producerCaseSelectors", statedRow);
            }
            InvocationKey priorProducerInvocation = enterInvocation(
                    new InvocationKey("", producerOccurrence));
            String priorProducerScope = enterSymbolScope("producer:"
                    + producerTask + "/" + producerOccurrence);
            String priorProducerGuard = currentGuard;
            final Term attached;
            try {
                currentGuard = firstNonBlank(caseSelector);
                int unsupportedBefore = unsupported.size();
                attached = term(event.get(VmHandoffEvidence.EXPRESSION),
                        portSort(consumer));
                if (unsupported.size() != unsupportedBefore) {
                    model.gap("HANDOFF_EXPRESSION_UNSUPPORTED",
                            occurrenceId + ":" + consumerPort,
                            "the exact attached VM expression cannot be"
                                    + " lowered at the receiving port sort");
                    return;
                }
            } finally {
                currentGuard = priorProducerGuard;
                restoreSymbolScope(priorProducerScope);
                restoreInvocation(priorProducerInvocation);
            }
            InvocationKey previousInvocation = enterInvocation(
                    consumer.invocation);
            String scope = caseOwner.isEmpty()
                    ? "fatal:" + occurrenceId : caseOwner;
            String previousScope = enterSymbolScope(scope);
            String previousGuard = currentGuard;
            currentGuard = firstNonBlank(caseSelector);
            try {
                if (attached.sort == Sort.MAP
                        || attached.sort == Sort.ARRAY_VALUE) {
                    promotePort(consumerPort, attached.sort);
                }
                String valueAssertion = emitPortBindingAssertion(
                        consumerPort, attached);
                if (valueAssertion.isEmpty()) {
                    model.gap("HANDOFF_EXPRESSION_BINDING_FAILED",
                            occurrenceId + ":" + consumerPort,
                            "the exact attached expression did not produce a"
                                    + " receiving-port assertion");
                    return;
                }
                boundPorts.add(consumer);
                if (ports.isInput(consumerPort)) {
                    markSuppliedInput(consumer);
                }
                recordInputAuthority(consumer, COMMUNICATION_LEAF,
                        valueAssertion);
                evidence.addProperty("valueAssertion", valueAssertion);
                recordHandoffCarriedSymbols(evidence);
                recordValueBinding(evidence,
                        VmHandoffEvidence.BINDING_KIND + "\n" + exportEvent
                                + "\n" + consumerPort + "\n" + caseOwner,
                        "VMH.");
            } finally {
                currentGuard = previousGuard;
                restoreSymbolScope(previousScope);
                restoreInvocation(previousInvocation);
            }
        }

        /**
         * Files one lowered value binding in the ledger both artifacts
         */
        private void recordValueBinding(JsonObject evidence,
                                        String bindingKey, String prefix) {
            if (string(evidence, "valueAssertion").isEmpty()) return;
            evidence.addProperty("bindingKey", bindingKey);
            evidence.addProperty("edgeId", prefix
                    + sha256(bindingKey).substring(0, 16));
            recordedValueBindings.add(evidence);
        }

        /**
         * States one exact binding's recorded order in the one order domain.
         */
        private void emitRecordedBindingOrder(JsonObject binding,
                                              String label,
                                              String equalityAssertion) {
            JsonObject evidence = exactValueBinding(binding,
                    equalityAssertion);
            for (String member : new String[]{
                    RecordedReadFrom.EDGE_PROVENANCE,
                    RecordedReadFrom.EDGE_FIELD, "locationKey"}) {
                if (binding.has(member)) {
                    evidence.addProperty(member, string(binding, member));
                }
            }
            long version = longInteger(binding, "fieldVersionId", 0L);
            long read = longInteger(binding, "readEventId", 0L);
            evidence.addProperty("fieldVersionId", version);
            evidence.addProperty("readEventId", read);
            recordedValueBindings.add(evidence);
        }

        /**
         * The endpoint members every exact value binding states, in the one
         * order both the manifest ledger and its census read them in.
         */
        private static JsonObject exactValueBinding(
                JsonObject binding, String equalityAssertion) {
            JsonObject evidence = new JsonObject();
            evidence.addProperty("kind", "RECORDED_EXACT_VALUE_BINDING");
            evidence.addProperty("edgeId", string(binding, "edgeId"));
            evidence.addProperty("valueAssertion", equalityAssertion);
            for (String member : new String[]{"fromOccurrenceId",
                    "toOccurrenceId", "fromOutputPort", "toInputPort"}) {
                evidence.addProperty(member, string(binding, member));
            }
            return evidence;
        }

        /** One exact VM read and writer after replay-local id resolution. */
        private static final class RecordedBindingCase {
            private final long versionEventId;
            private final long readEventId;
            private final String guard;

            private RecordedBindingCase(long versionEventId,
                                        long readEventId, String guard) {
                this.versionEventId = versionEventId;
                this.readEventId = readEventId;
                this.guard = firstNonBlank(guard);
            }
        }

        /** Resolves an exact binding independently in every reader replay. */
        private List<RecordedBindingCase> recordedBindingCases(
                JsonObject binding) {
            long localVersion = longInteger(binding, "fieldVersionId", 0L);
            long localRead = longInteger(binding, "readEventId", 0L);
            if (localVersion <= 0L || localRead <= 0L) {
                return Collections.emptyList();
            }
            String producer = string(binding, "fromOccurrenceId");
            List<RecordedBindingCase> result = new ArrayList<>();
            List<RecordedSessionModel.ReadCase> reads = recorded.readCasesOf(
                    string(binding, "locationKey"),
                    RecordedEvidenceIdentity.siteKey(string(binding,
                            "toOccurrenceId")));
            for (RecordedSessionModel.ReadCase readCase : reads) {
                long read = recorded.resolveEventForRead(readCase.readEventId,
                        localRead);
                if (read != readCase.readEventId) continue;
                long version = recorded.resolveEventForRead(read,
                        localVersion);
                JsonObject writer = recorded.writerVersion(version);
                if (version <= 0L || !recorded.exactReadSelects(read, version)
                        || writer.size() == 0
                        || !producer.isEmpty() && !producer.equals(
                        SharedStateEvidence.writerSite(writer))) {
                    continue;
                }
                result.add(new RecordedBindingCase(version, read,
                        readCase.caseGuard));
            }
            return result;
        }

        private void emitRecordedBindingOrderCase(
                JsonObject binding, String label, String equalityAssertion,
                RecordedBindingCase recordedCase) {
            JsonObject evidence = exactValueBinding(binding,
                    equalityAssertion);
            evidence.addProperty("fieldVersionId",
                    recordedCase.versionEventId);
            evidence.addProperty("readEventId", recordedCase.readEventId);
            evidence.addProperty("caseGuard",
                    firstNonBlank(recordedCase.guard, "true"));
            String previousGuard = currentGuard;
            currentGuard = conjunction(previousGuard, recordedCase.guard);
            try {
                evidence.addProperty("orderAssertion", emitRecordedOrder(
                        recordedCase.versionEventId,
                        recordedCase.readEventId, label));
            } finally {
                currentGuard = previousGuard;
            }
            recordedValueBindings.add(evidence);
        }

        /**
         * Asserts {@code before < after} in the shared position domain, after
         */
        private String emitRecordedOrder(long before, long after,
                                         String label) {
            if (!recorded.ordersEvent(before)
                    || !recorded.ordersEvent(after)) {
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        RecordedSessionModel.UNORDERED_READ_CUT, label,
                        "events " + before + " and " + after + " are not both"
                                + " in the recorded order domain"));
                return "";
            }
            int status = recorded.propose(before, after);
            if (status != SessionOrderDomain.ORDER_OK) {
                unsupported.add("RecordedOrderRefused:"
                        + SessionOrderDomain.statusName(status) + ":"
                        + before + "->" + after);
                return "";
            }
            return assertNamed("recorded_exact_order__" + before + "__"
                            + after,
                    "(< " + recorded.scopedPositionName(before) + " "
                            + recorded.scopedPositionName(after) + ")");
        }

        /**
         * Whether the recorded session resolved every replay case of one
         * state read to one exact version.  Such a read carries the session's
         * own read-from authority, whatever the trace additionally proposed.
         */
        private boolean recordedReadResolvedExactly(String locationKey,
                                                    String readerOccurrence) {
            if (recorded == null) return false;
            List<RecordedSessionModel.ReadCase> cases =
                    recorded.readCasesOf(locationKey,
                            RecordedEvidenceIdentity.siteKey(
                                    readerOccurrence));
            if (cases.isEmpty()) return false;
            for (RecordedSessionModel.ReadCase readCase : cases) {
                if (!SharedStateEvidence.RESOLUTION_EXACT.equals(
                        readCase.resolution)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Whether the recorded evidence ruled this candidate writer out.
         */
        private boolean skipExcludedWriter(JsonObject binding) {
            if (!RecordedReadFrom.PROVENANCE_EXCLUDED.equals(string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE))) {
                return false;
            }
            if (excludedWriters.add(string(binding, "edgeId"))) {
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        RecordedReadFrom.PROVENANCE_EXCLUDED,
                        string(binding, "edgeId"),
                        "the recorded read-from evidence names another writer"
                                + " for " + bindingTargetInput(binding)
                                + "; this candidate is not composed"));
            }
            return true;
        }

        /**
         * Lowers one proven read-from as the equality it is.
         */
        private boolean bindRecordedExactWriter(JsonObject binding,
                                                PortOccurrence source,
                                                PortOccurrence target,
                                                String label) {
            if (!RecordedReadFrom.PROVENANCE_EXACT.equals(string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE))) {
                return false;
            }
            List<RecordedBindingCase> cases = recordedBindingCases(binding);
            if (cases.isEmpty()) {
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        RecordedSessionModel.UNORDERED_READ_CUT,
                        string(binding, "edgeId"),
                        "exact VM binding cannot be addressed in one replay"
                                + " case"));
                return false;
            }
            boolean emitted = false;
            for (RecordedBindingCase recordedCase : cases) {
                String previousGuard = currentGuard;
                currentGuard = conjunction(previousGuard, recordedCase.guard);
                try {
                    String equality = assertPortBindingEqualityNamed(source,
                            target, label + "_" + recordedCase.readEventId);
                    if (equality.isEmpty()) continue;
                    JsonObject scopedBinding = binding.deepCopy();
                    scopedBinding.addProperty("fieldVersionId",
                            recordedCase.versionEventId);
                    scopedBinding.addProperty("readEventId",
                            recordedCase.readEventId);
                    emitRecordedBindingOrderCase(scopedBinding, label,
                            equality, recordedCase);
                    boundPorts.add(target);
                    recordInputAuthority(target, READ_FROM_ARM,
                            string(binding, "edgeId") + ":"
                                    + recordedCase.readEventId);
                    if (ports.isInput(target.portId)) {
                        markSuppliedInput(target);
                    }
                    failureWitness.connect(scopedBinding, source, target,
                            firstNonBlank(recordedCase.guard, "true"),
                            portName(target));
                    emitted = true;
                } finally {
                    currentGuard = previousGuard;
                }
            }
            if (!emitted) {
                heapGap("RecordedExactReadFromGap@" + target);
                return false;
            }
            emittedEdgeBindings.add(edgeBindingKey(binding));
            return true;
        }

        /**
         * Hands one consumer port the value the read-from selectors choose.
         */
        private boolean bindRecordedGuardedRead(JsonObject binding,
                                                PortOccurrence producer,
                                                PortOccurrence consumer,
                                                String label) {
            if (!RecordedReadFrom.PROVENANCE_GUARDED
                    .equals(string(binding,
                            RecordedReadFrom.EDGE_PROVENANCE))) {
                return false;
            }
            List<RecordedSessionModel.ReadCase> readCases =
                    recorded.guardedReadCasesOf(
                            string(binding, "locationKey"),
                            RecordedEvidenceIdentity.siteKey(string(binding,
                                    "toOccurrenceId")));
            if (readCases.isEmpty()) {
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        SharedStateEvidence.reason(
                                SharedStateEvidence.NOT_SELECTED),
                        string(binding, "edgeId"),
                        "no recorded guarded read of "
                                + string(binding, "locationKey")
                                + " addresses consumer "
                                + string(binding, "toOccurrenceId")));
                return false;
            }
            boolean boundAny = false;
            boolean complete = true;
            for (RecordedSessionModel.ReadCase readCase : readCases) {
                long read = readCase.readEventId;
                Term value = guardedReadTerms.get(read);
                if (value == null) {
                    complete = false;
                    recordedCoverage.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW,
                            "RECORDED_GUARDED_READ_VALUE_MISSING",
                            string(binding, "edgeId") + ":" + read,
                            "case-local guarded read has no lowered value term"));
                    continue;
                }
                String bindingKey = consumer + "\u0000" + read;
                if (!recordedReadBoundPorts.add(bindingKey)) {
                    boundAny = true;
                    recordedCoverage.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW,
                            "RECORDED_GUARDED_READ_ALREADY_BOUND",
                            string(binding, "edgeId") + ":" + read,
                            "consumer port " + consumer + " already holds"
                                    + " this replay case's guarded read value"));
                    continue;
                }

                String previousGuard = currentGuard;
                currentGuard = conjunction(previousGuard, readCase.caseGuard);
                try {
                    noteReadCase(read);
                    Sort portSort = portSort(consumer);
                    if (portSort == Sort.MAP && value.sort != Sort.MAP) {
                        boolean stateBound = bindRecordedGuardedState(binding,
                                producer, consumer, read, label + "_" + read);
                        boundAny |= stateBound;
                        complete &= stateBound;
                        continue;
                    }
                    Term bound = portSort == Sort.VALUE
                            ? asValue(value, ports.get(consumer.portId) == null
                            ? "" : ports.get(consumer.portId).javaType) : value;
                    if (bound.sort != portSort) {
                        unsupported.add("RecordedReadPortSortConflict:"
                                + consumer + ":" + portSort + "!="
                                + bound.sort);
                        complete = false;
                        continue;
                    }
                    declarePort(consumer, portSort);
                    String assertion = assertNamed(label + "_recorded_read_"
                                    + read,
                            and(Arrays.asList(bound.precondition, "(= "
                                    + portName(consumer) + " " + bound.text
                                    + ")")));
                    boundPorts.add(consumer);
                    // README SMT-1 admits a *known* read-from arm.  This
                    boolean unknownArm = !string(binding,
                            RecordedReadFrom.EDGE_UNKNOWN_ARM).isEmpty();
                    recordInputAuthority(consumer, unknownArm
                                    ? READ_FROM_ARM_UNKNOWN : READ_FROM_ARM,
                            string(binding, "edgeId") + ":" + read);
                    // Deliberately not added to `unsupported`.  An unknown arm
                    // reading README forbids of an under-approximation.  The
                    if (ports.isInput(consumer.portId)) {
                        markSuppliedInput(consumer);
                    }
                    JsonObject evidence = new JsonObject();
                    evidence.addProperty("kind",
                            "RECORDED_GUARDED_READ_PORT_BINDING");
                    evidence.addProperty("edgeId", string(binding, "edgeId"));
                    evidence.addProperty("locationKey",
                            string(binding, "locationKey"));
                    evidence.addProperty(RecordedReadFrom.EDGE_FIELD,
                            string(binding, RecordedReadFrom.EDGE_FIELD));
                    evidence.addProperty("toOccurrenceId",
                            string(binding, "toOccurrenceId"));
                    evidence.addProperty("toInputPort", consumer.portId);
                    evidence.addProperty("readEventId", read);
                    evidence.addProperty("caseGuard",
                            firstNonBlank(readCase.caseGuard, "true"));
                    evidence.addProperty("valueTerm", value.text);
                    evidence.addProperty("valueAssertion", assertion);
                    evidence.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                            string(binding, RecordedReadFrom.EDGE_UNKNOWN_ARM));
                    recordedValueBindings.add(evidence);
                    failureWitness.connect(binding, producer, consumer,
                            firstNonBlank(readCase.caseGuard, "true"),
                            portName(consumer));
                    boundAny = true;
                } finally {
                    currentGuard = previousGuard;
                }
            }
            if (boundAny) emittedEdgeBindings.add(edgeBindingKey(binding));
            return boundAny && complete;
        }

        private String conjunction(String left, String right) {
            if (left == null || left.isEmpty()) return firstNonBlank(right);
            if (right == null || right.isEmpty()) return firstNonBlank(left);
            if (left.equals(right)) return left;
            return "(and " + left + " " + right + ")";
        }

        /**
         * Binds a container-state edge to the VM versions selected by its
         */
        private boolean bindRecordedGuardedState(JsonObject binding,
                                                 PortOccurrence producerPort,
                                                 PortOccurrence consumer,
                                                 long readEventId,
                                                 String label) {
            JsonObject guarded = recorded.guardedReads().get(readEventId);
            if (guarded == null) return false;
            String producer = string(binding, "fromOccurrenceId");
            List<String> selectors = new ArrayList<>();
            for (RecordedSessionModel.ReadArm<Object> arm : recorded.armsOf(
                    readEventId, array(guarded, "candidates"), null)) {
                if (arm.unknown) continue;
                JsonObject version = recorded.writerVersionForRead(
                        readEventId, arm.writerEventId);
                if (version.size() == 0
                        || "INITIAL".equals(string(version, "versionKind"))
                        || !producer.equals(
                        SharedStateEvidence.writerSite(version))) {
                    continue;
                }
                selectors.add(arm.selector);
            }
            if (selectors.isEmpty()) {
                unsupported.add("RecordedWriterOccurrenceHasNoStateArm:"
                        + string(binding, "edgeId") + ":" + producer);
                return false;
            }
            String stateBinding = assertPortBindingEqualityNamed(producerPort,
                    consumer, label + "_state");
            if (stateBinding.isEmpty()) return false;
            String selection = assertNamed(label + "_selected_writer",
                    or(selectors));
            boundPorts.add(consumer);
            recordInputAuthority(consumer, READ_FROM_ARM,
                    string(binding, "edgeId"));
            if (ports.isInput(consumer.portId)) markSuppliedInput(consumer);
            JsonObject evidence = new JsonObject();
            evidence.addProperty("kind",
                    "RECORDED_GUARDED_STATE_PORT_BINDING");
            evidence.addProperty("edgeId", string(binding, "edgeId"));
            evidence.addProperty("locationKey",
                    string(binding, "locationKey"));
            evidence.addProperty("toOccurrenceId",
                    string(binding, "toOccurrenceId"));
            evidence.addProperty("toInputPort", consumer.portId);
            evidence.addProperty("readEventId", readEventId);
            evidence.addProperty("selectedWriterAssertion", selection);
            evidence.addProperty("valueAssertion", stateBinding);
            recordedValueBindings.add(evidence);
            emittedEdgeBindings.add(edgeBindingKey(binding));
            failureWitness.connect(binding, producerPort, consumer,
                    selection, portName(consumer));
            return true;
        }

        private String edgeBindingKey(JsonObject binding) {
            return string(binding, "edgeId") + "\n"
                    + bindingSourceInstance(binding) + "\n"
                    + bindingSourceOutput(binding) + "\n"
                    + bindingTargetInstance(binding) + "\n"
                    + bindingTargetInput(binding) + "\n"
                    + longInteger(binding, "writerEventSeq", -1L) + "\n"
                    + longInteger(binding, "readerEventSeq", -1L);
        }

        private void finishBindings() {
            Map<PortOccurrence, Set<PortOccurrence>> equalPorts =
                    new LinkedHashMap<>();
            for (PortOccurrence[] equality : portEqualities) {
                equalPorts.computeIfAbsent(equality[0],
                        ignored -> new LinkedHashSet<>()).add(equality[1]);
                equalPorts.computeIfAbsent(equality[1],
                        ignored -> new LinkedHashSet<>()).add(equality[0]);
            }
            Deque<PortOccurrence> pending = new ArrayDeque<>(boundPorts);
            while (!pending.isEmpty()) {
                for (PortOccurrence port : equalPorts.getOrDefault(
                        pending.removeFirst(), Collections.emptySet())) {
                    if (boundPorts.add(port)) {
                        pending.addLast(port);
                    }
                }
            }
            for (PortOccurrence port : mentionedPorts) {
                if (!boundPorts.contains(port) && ports.isInput(port.portId)) {
                    unsupported.add("UnboundPort:" + port);
                }
            }
            // README SMT-1's free selected port.  The two sweeps above and
            for (PortOccurrence port : undeclaredSelectedPorts()) {
                unsupported.add(UNDECLARED_SELECTED_PORT + ":" + port);
            }
            // README SMT-1 is case-local: a selected input may legitimately
            String previousGuard = currentGuard;
            currentGuard = "";
            try {
                for (Map.Entry<PortOccurrence, Set<String>> useEntry
                        : inputUseGuards.entrySet()) {
                    PortOccurrence port = useEntry.getKey();
                    Map<String, List<InputAuthorityEvidence>> authorities =
                            authoritiesOf(port);
                    List<String> activeGuards = authorityGuards(authorities);
                    if (activeGuards.isEmpty()) {
                        unsupported.add(INPUT_AUTHORITY_MISSING + ":" + port);
                    }
                    if (authorityCasesDefinitelyAmbiguous(activeGuards)) {
                        unsupported.add(INPUT_AUTHORITY_AMBIGUOUS + ":" + port);
                    }
                    int ordinal = 0;
                    for (String useGuard : useEntry.getValue()) {
                        String obligation = exactlyOneAuthority(activeGuards);
                        if (!"true".equals(useGuard)) {
                            obligation = "(=> " + useGuard + " "
                                    + obligation + ")";
                        }
                        String assertion = assertNamed(
                                "selected_input_authority_" + portName(port)
                                        + "_" + ordinal++, obligation);
                        inputAuthorityAssertions.computeIfAbsent(port,
                                ignored -> new LinkedHashMap<>())
                                .put(useGuard, assertion);
                    }
                }
            } finally {
                currentGuard = previousGuard;
            }
        }

        /**
         * The mentioned port occurrences no region row declares.
         */
        private List<PortOccurrence> undeclaredSelectedPorts() {
            List<PortOccurrence> undeclared = new ArrayList<>();
            for (PortOccurrence port : mentionedPorts) {
                if (port.portId.isEmpty()
                        || ports.get(port.portId) != null) {
                    continue;
                }
                undeclared.add(port);
            }
            return undeclared;
        }

        private static List<String> authorityGuards(
                Map<String, List<InputAuthorityEvidence>> authorities) {
            List<String> result = new ArrayList<>();
            for (List<InputAuthorityEvidence> evidence
                    : authorities.values()) {
                for (InputAuthorityEvidence fact : evidence) {
                    result.add(firstNonBlank(fact.caseSelector, "true"));
                }
            }
            return result;
        }

        private JsonArray selectedInputLedger() {
            List<PortOccurrence> ordered = new ArrayList<>();
            for (PortOccurrence port : mentionedPorts) {
                if (ports.isInput(port.portId)) ordered.add(port);
            }
            ordered.sort(Comparator.comparing(PortOccurrence::toString));
            JsonArray result = new JsonArray();
            for (PortOccurrence port : ordered) {
                Map<String, List<InputAuthorityEvidence>> authorities =
                        authoritiesOf(port);
                JsonObject row = new JsonObject();
                row.addProperty("portId", port.portId);
                row.addProperty("occurrenceId", port.invocation.instanceId);
                List<String> activeGuards = authorityGuards(authorities);
                row.addProperty("authority", activeGuards.isEmpty()
                        ? INPUT_AUTHORITY_MISSING
                        : authorityCasesDefinitelyAmbiguous(activeGuards)
                        ? INPUT_AUTHORITY_AMBIGUOUS
                        : activeGuards.size() == 1
                        ? authorities.keySet().iterator().next()
                        : "CASE_LOCAL_EXACTLY_ONE");
                JsonArray uses = new JsonArray();
                Map<String, String> assertions = inputAuthorityAssertions
                        .getOrDefault(port, Collections.emptyMap());
                for (String guard : inputUseGuards.getOrDefault(port,
                        Collections.emptySet())) {
                    JsonObject use = new JsonObject();
                    use.addProperty("caseGuard", guard);
                    String assertion = assertions.get(guard);
                    if (assertion != null) {
                        use.addProperty("authorityAssertion", assertion);
                    }
                    uses.add(use);
                }
                row.add("uses", uses);
                JsonArray evidence = new JsonArray();
                for (Map.Entry<String, List<InputAuthorityEvidence>> entry
                        : authorities.entrySet()) {
                    for (InputAuthorityEvidence fact : entry.getValue()) {
                        JsonObject named = new JsonObject();
                        named.addProperty("authority", entry.getKey());
                        named.addProperty("evidence", fact.evidence);
                        if (!fact.caseSelector.isEmpty()) {
                            named.addProperty(
                                    RecordedSessionModel.CASE_SELECTOR,
                                    fact.caseSelector);
                        }
                        evidence.add(named);
                    }
                }
                row.add("evidence", evidence);
                result.add(row);
            }
            return result;
        }

        /** One row stating that the case-local selected-input pass ran. */
        private JsonObject selectedInputLedgerAudit() {
            int ports = 0;
            int uses = 0;
            int facts = 0;
            int missing = 0;
            int ambiguous = 0;
            int unknownArmAuthorities = 0;
            for (Map.Entry<PortOccurrence, Set<String>> entry
                    : inputUseGuards.entrySet()) {
                ports++;
                uses += entry.getValue().size();
                Map<String, List<InputAuthorityEvidence>> authorities =
                        authoritiesOf(entry.getKey());
                List<String> guards = authorityGuards(authorities);
                facts += guards.size();
                if (guards.isEmpty()) missing++;
                else if (authorityCasesDefinitelyAmbiguous(guards)) ambiguous++;
                unknownArmAuthorities += authorities.getOrDefault(
                        READ_FROM_ARM_UNKNOWN,
                        Collections.<InputAuthorityEvidence>emptyList()).size();
            }
            JsonObject audit = new JsonObject();
            audit.addProperty("schemaVersion", 4);
            audit.addProperty("kind", "SELECTED_INPUT_LEDGER_AUDIT");
            audit.addProperty("authority", "SELECTED_INPUT_LEDGER_V4");
            audit.addProperty("inputOccurrencesChecked", ports);
            audit.addProperty("inputUsesChecked", uses);
            audit.addProperty("authorityEvidenceChecked", facts);
            audit.addProperty("missingOccurrences", missing);
            audit.addProperty("ambiguousOccurrences", ambiguous);
            // The ports the three counts above could not range over, because
            // no region row declares them.  Reported beside them so that
            audit.addProperty("undeclaredPortOccurrences",
                    undeclaredSelectedPorts().size());
            // The read-from authorities the recorded model left open, kept
            // apart from the proven ones the same way the ledger keeps them.
            audit.addProperty("unknownArmAuthorities", unknownArmAuthorities);
            return audit;
        }




        /** A value supply is not itself a consumer use of the input. */
        private String assertPortBindingEqualityNamed(PortOccurrence left,
                                                      PortOccurrence right,
                                                      String label) {
            if (!preparePortEquality(left, right)) return "";
            String formula = "(= " + portName(left) + " "
                    + portName(right) + ")";
            String assertionName = assertNamed(label, formula);
            recordSuppliedInput(left, right);
            portEqualities.add(new PortOccurrence[]{left, right});
            return assertionName;
        }


        private boolean preparePortEquality(PortOccurrence left,
                                            PortOccurrence right) {
            if (left.portId.isEmpty() || right.portId.isEmpty()) return false;
            Sort leftSort = portSort(left);
            Sort rightSort = portSort(right);
            if (leftSort != rightSort
                    && refineNeutralPortSort(left, right, leftSort,
                    rightSort)) {
                leftSort = portSort(left);
                rightSort = portSort(right);
            }
            if (leftSort != rightSort) {
                unsupported.add("PortSortMismatch:" + left + ":" + leftSort
                        + "!=" + right + ":" + rightSort);
                return false;
            }
            if (!compatibleArrayPortTypes(left.portId, right.portId,
                    leftSort)) {
                return false;
            }
            declarePort(left, leftSort);
            declarePort(right, rightSort);
            return true;
        }

        /**
         * the container sort its counterpart already proved.
         */
        private boolean refineNeutralPortSort(PortOccurrence left,
                                              PortOccurrence right,
                                              Sort leftSort, Sort rightSort) {
            PortOccurrence neutral = leftSort == Sort.VALUE ? left
                    : rightSort == Sort.VALUE ? right : null;
            Sort container = leftSort == Sort.VALUE ? rightSort : leftSort;
            if (neutral == null || container != Sort.MAP
                    && container != Sort.ARRAY_VALUE
                    || declaredPortSorts.containsKey(neutral)) {
                return false;
            }
            String leftType = declaredPortJavaType(left.portId);
            if (leftType.isEmpty()
                    || !leftType.equals(declaredPortJavaType(right.portId))) {
                return false;
            }
            portSortOverrides.put(neutral, container);
            return true;
        }

        private String declaredPortJavaType(String port) {
            Port schema = ports.get(port);
            return schema == null ? "" : schema.declaredJavaType();
        }

        private boolean compatibleArrayPortTypes(String left, String right,
                                                 Sort sort) {
            if (sort != Sort.ARRAY_VALUE) return true;
            String leftType = javaTypeDescriptor(
                    declaredPortJavaType(left));
            String rightType = javaTypeDescriptor(
                    declaredPortJavaType(right));
            if (!leftType.isEmpty() && leftType.equals(rightType)) {
                return true;
            }
            unsupported.add("ArrayPortJavaTypeMismatch:" + left + ":"
                    + firstNonBlank(leftType, "<unknown>") + "!=" + right
                    + ":" + firstNonBlank(rightType, "<unknown>"));
            return false;
        }

        private void recordSuppliedInput(PortOccurrence left,
                                         PortOccurrence right) {
            Port leftPort = ports.get(left.portId);
            Port rightPort = ports.get(right.portId);
            if (leftPort != null && leftPort.input
                    && rightPort != null && !rightPort.input) {
                markSuppliedInput(left);
            }
            if (rightPort != null && rightPort.input
                    && leftPort != null && !leftPort.input) {
                markSuppliedInput(right);
            }
        }

        /**
         * provenance the README forbids.</p>
         */
        private void recordInputAuthority(PortOccurrence occurrence,
                                          String authority, String evidence) {
            // Filed for whatever the value arrived at.  Requiring the catalog
            // to declare that port an input first would drop the authority of
            if (occurrence == null) return;
            List<InputAuthorityEvidence> facts = inputAuthorities
                    .computeIfAbsent(occurrence,
                            ignored -> new LinkedHashMap<>())
                    .computeIfAbsent(authority,
                            ignored -> new ArrayList<>());
            for (InputAuthorityEvidence fact : facts) {
                if (fact.same(evidence, currentGuard)) return;
            }
            facts.add(new InputAuthorityEvidence(evidence, currentGuard));
        }

        /**
         * The authorities that constrain one selected input port.
         */
        private Map<String, List<InputAuthorityEvidence>> authoritiesOf(
                PortOccurrence port) {
            Map<String, List<InputAuthorityEvidence>> bound =
                    inputAuthorities.get(port);
            Map<String, List<InputAuthorityEvidence>> result =
                    new LinkedHashMap<>();
            if (bound != null) {
                for (Map.Entry<String, List<InputAuthorityEvidence>> entry
                        : bound.entrySet()) {
                    result.put(entry.getKey(), new ArrayList<>(entry.getValue()));
                }
            }
            Port schema = ports.get(port.portId);
            // VALUE_FRONTIER permits an otherwise-unbound selected input to
            // be a local symbolic root.  It is not a second value source once
            if (result.isEmpty() && schema != null
                    && DependencyRole.VALUE_FRONTIER.equals(
                    string(schema.metadata, "dependencyRole"))) {
                result.computeIfAbsent(LOCAL_SYMBOLIC_ROOT,
                                ignored -> new ArrayList<>())
                        .add(new InputAuthorityEvidence(
                                DependencyRole.VALUE_FRONTIER, ""));
            }
            return result;
        }

        /** Records the exact case in which a selected input term is read. */
        private void mentionPort(PortOccurrence occurrence) {
            mentionedPorts.add(occurrence);
            if (!ports.isInput(occurrence.portId)) return;
            String useGuard = firstNonBlank(currentGuard, "true");
            inputUseGuards.computeIfAbsent(occurrence,
                    ignored -> new LinkedHashSet<>()).add(useGuard);
        }

        private void markSuppliedInput(PortOccurrence occurrence) {
            suppliedInputOccurrences.add(occurrence);
        }


        private Term asValue(Term term, String javaType) {
            if (term.sort == Sort.VALUE) return term;
            if (term.sort == Sort.INT) {
                String boxed = ContainerSmtCodec.boxIntegral(
                        term.text, javaType);
                return dependent(new Term(firstNonBlank(boxed,
                        "(VInt " + term.text + ")"), Sort.VALUE), term);
            }
            if (term.sort == Sort.FLOAT32) return dependent(new Term(
                    "(VFloat " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.FLOAT64) return dependent(new Term(
                    "(VDouble " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.BOOL) return dependent(new Term("(VBool "
                    + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.STRING) {
                String boxed = "false".equals(term.stringNullness)
                        ? "(VString " + term.text + ")"
                        : "(ite " + term.stringNullness
                                + " (VRef nullRef) (VString "
                                + term.text + "))";
                return dependent(new Term(boxed, Sort.VALUE), term);
            }
            if (term.sort == Sort.REF) return dependent(new Term("(VRef "
                    + term.text + ")", Sort.VALUE), term);
            unsupported.add("CannotBox:" + term.sort);
            return unsupportedTerm(Sort.VALUE);
        }

        private void bindPort(String port, Term value) {
            PortOccurrence occurrence = currentOccurrence(port);
            if (currentGuard.isEmpty() && boundPorts.contains(occurrence)) {
                return;
            }
            if (emitPortBinding(port, value)) {
                boundPorts.add(occurrence);
            }
        }

        private boolean emitPortBinding(String port, Term value) {
            return !emitPortBindingAssertion(port, value).isEmpty();
        }

        /** Emits and returns the exact named receiving-port assertion. */
        private String emitPortBindingAssertion(String port, Term value) {
            PortOccurrence occurrence = currentOccurrence(port);
            Port schema = ports.get(port);
            Sort portSort = schema == null ? Sort.VALUE : portSort(port);
            declarePort(occurrence, portSort);
            mentionPort(occurrence);
            if (portSort == Sort.MAP) {
                Term state = value.sort == Sort.MAP ? value
                        : value.sort == Sort.REF
                        ? new Term("(assoc_state_of " + value.text + ")",
                        Sort.MAP)
                        : null;
                if (state == null) {
                    unsupported.add("MapPortBinding:" + port + ":" + value.sort);
                    return "";
                }
                String formula = and(Arrays.asList(state.precondition,
                        "(= " + portName(occurrence) + " " + state.text
                                + ")"));
                return assertNamed("bind_" + port, formula);
            } else if (portSort == Sort.ARRAY_VALUE) {
                Term state = value.sort == Sort.ARRAY_VALUE ? value
                        : value.sort == Sort.REF
                        ? new Term("(indexed_state_of " + value.text + ")",
                        Sort.ARRAY_VALUE)
                        : null;
                if (state == null) {
                    unsupported.add("ArrayValuePortBinding:" + port + ":"
                            + value.sort);
                    return "";
                }
                String formula = and(Arrays.asList(state.precondition,
                        "(= " + portName(occurrence) + " " + state.text
                                + ")"));
                return assertNamed("bind_" + port, formula);
            } else {
                if (value.sort == Sort.ARRAY_VALUE) {
                    unsupported.add("UnsupportedArrayToScalarBinding:" + port
                            + ":" + value.sort);
                    return "";
                }
                Term boxed = asValue(value,
                        schema == null ? "" : schema.javaType);
                String formula = and(Arrays.asList(boxed.precondition,
                        "(= " + portName(occurrence) + " " + boxed.text
                                + ")"));
                return assertNamed("bind_" + port, formula);
            }
        }

        private void declarePort(String port, Sort requested) {
            declarePort(currentOccurrence(port), requested);
        }

        private void declarePort(PortOccurrence occurrence, Sort requested) {
            String port = occurrence.portId;
            Sort canonical = portSort(occurrence);
            Sort sort = requested == null ? canonical : requested;
            if (ports.contains(port) && sort != canonical) {
                unsupported.add("PortDeclarationSortConflict:" + port + ":"
                        + canonical + "->" + sort);
                sort = canonical;
            }
            Sort declared = declaredPortSorts.get(occurrence);
            if (declared != null && declared != sort) {
                unsupported.add("PortRedeclarationSortConflict:" + port
                        + ":" + declared + "->" + sort);
                return;
            }
            declaredPortSorts.put(occurrence, sort);
            addDeclaration("port:" + occurrence,
                    "(declare-const " + portName(occurrence) + " "
                            + sort.smt + ")");
        }

        private Sort portSort(String port) {
            return portSort(currentOccurrence(port));
        }

        private Sort portSort(PortOccurrence occurrence) {
            Sort declared = declaredPortSorts.get(occurrence);
            if (declared != null) return declared;
            Sort override = portSortOverrides.get(occurrence);
            return override == null ? ports.sort(occurrence.portId) : override;
        }

        private void promotePort(String port, Sort sort) {
            PortOccurrence occurrence = currentOccurrence(port);
            Sort current = portSort(port);
            boolean referenceToContainer = current == Sort.REF
                    && (sort == Sort.MAP || sort == Sort.ARRAY_VALUE);
            if (current != sort && current != Sort.VALUE
                    && !referenceToContainer) {
                unsupported.add("PortSortPromotionConflict:" + port + ":"
                        + current + "->" + sort);
                return;
            }
            portSortOverrides.put(occurrence, sort);
        }

        private String portName(String port) {
            return portName(currentOccurrence(port));
        }

        private String portName(PortOccurrence occurrence) {
            return "port__" + smtName(occurrence.portId)
                    + "__instance__"
                    + smtName(occurrence.invocation.instanceId);
        }

        private void declare(String name, Sort sort) {
            addDeclaration("const:" + name,
                    "(declare-const " + name + " " + sort.smt + ")");
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
            if (declarationKeys.add(key)) declarations.add(declaration);
        }

        private String assertNamed(String name, String expression) {
            String unique = smtName(name);
            if (!assertionNames.add(unique)) {
                int suffix = 2;
                while (!assertionNames.add(unique + "_" + suffix)) {
                    suffix++;
                }
                unique = unique + "_" + suffix;
            }
            String asserted = currentGuard.isEmpty() ? expression
                    : "(=> " + currentGuard + " " + expression + ")";
            assertions.add("(assert (! " + asserted + " :named "
                    + unique + "))");
            return unique;
        }

        private boolean isNull(Term term) {
            return term.sort == Sort.REF && "nullRef".equals(term.text);
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
            if (sort == Sort.BOOL) return new Term("false", sort);
            if (sort == Sort.INT) return new Term("0", sort);
            if (sort == Sort.FLOAT32 || sort == Sort.FLOAT64) {
                return new Term(JavaPrimitiveSmtSemantics.floatingLiteral(
                        "0.0", floatingKind(sort)), sort);
            }
            if (sort == Sort.STRING) {
                return Term.nonNullString("\"\"", "true");
            }
            if (sort == Sort.REF) return new Term("nullRef", sort);
            String nullValues = "((as const (Array Value Value))"
                    + " (VRef nullRef))";
            if (sort == Sort.MAP) {
                return new Term("(mkAssocState 0"
                        + " ((as const (Array Value Bool)) false)"
                        + " " + nullValues
                        + " ((as const (Array Int Value))"
                        + " (VRef nullRef))"
                        + " ((as const (Array Value Int)) (- 1)))", sort);
            }
            if (sort == Sort.VALUE) {
                return new Term("(VRef nullRef)", sort);
            }
            String elements = "((as const (Array Int Value))"
                    + " (VRef nullRef))";
            return new Term("(mkIndexedState 0 " + elements + ")", sort);
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

        private String findPort(String rawSymbol) {
            for (String port : ports.longestFirst) {
                int index = rawSymbol.indexOf(port);
                while (index >= 0) {
                    int end = index + port.length();
                    // Runtime field symbols wrap the exact activation token as
                    // ..._<port>_<owner>.  Do not accept arbitrary substrings
                    boolean leftBoundary = index == 0
                            || rawSymbol.charAt(index - 1) == '_';
                    boolean rightBoundary = end == rawSymbol.length()
                            || rawSymbol.charAt(end) == '_';
                    if (leftBoundary && rightBoundary) return port;
                    index = rawSymbol.indexOf(port, index + 1);
                }
            }
            return "";
        }

        private void finish() {
            if (!unsupported.isEmpty()) {
                assertions.add("(assert false) ; fail closed: unsupported");
            }
            assertions.add("(check-sat)");
        }

        private void finishFatalAbsenceMutationWitness() {
            if (failureWitness.demands.isEmpty()) return;
            if (failureWitness.clauses.isEmpty()) {
                unsupported.add("FatalAbsenceMutationWitnessGap");
                return;
            }
            assertNamed("fatal_absence_mutation_witness",
                    or(failureWitness.clauses));
        }

        private String render() {
            StringBuilder result = new StringBuilder();
            appendLines(result, preamble);
            result.append(System.lineSeparator());
            appendLines(result, declarations);
            result.append(System.lineSeparator());
            appendLines(result, assertions);
            return result.toString();
        }

        private static void appendLines(StringBuilder builder,
                                        List<String> lines) {
            for (String line : lines) builder.append(line)
                    .append(System.lineSeparator());
        }
    }



    static String materializedPortJavaType(JsonObject port) {
        return MaterializationSpec.logicalJavaType(port);
    }

    private static final class PortIndex {
        private final Map<String, Port> ports = new LinkedHashMap<>();
        private final List<String> longestFirst = new ArrayList<>();

        private static PortIndex from(List<JsonObject> regions) {
            PortIndex result = new PortIndex();
            for (JsonObject region : regions) {
                for (JsonElement element : array(region, "symbolicInputs")) {
                    if (element.isJsonObject()) result.add(
                            element.getAsJsonObject(), true);
                }
                for (JsonElement element : array(region, "outputs")) {
                    if (element.isJsonObject()) result.add(
                            element.getAsJsonObject(), false);
                }
            }
            result.longestFirst.addAll(result.ports.keySet());
            Collections.sort(result.longestFirst,
                    new Comparator<String>() {
                        @Override
                        public int compare(String left, String right) {
                            return Integer.compare(right.length(), left.length());
                        }
                    });
            return result;
        }

        private void add(JsonObject json, boolean input) {
            String id = string(json, "portId");
            if (id.isEmpty()) return;
            String cell = string(json, "cell");
            String javaType = materializedPortJavaType(json);
            Sort sort = containerSort(javaType);
            if (sort == Sort.VALUE) {
                sort = containerCellSort(cell);
            }
            ports.put(id, new Port(javaType,
                    firstNonBlank(declaredFieldJavaType(json),
                            declaredCellJavaType(cell)), sort, input, json));
        }

        /**
         * The declared Java type of the field a port's access path ends at.
         */
        private static String declaredFieldJavaType(JsonObject json) {
            JsonArray declarations = array(json, "fieldPathDeclarations");
            if (declarations.size() == 0) return "";
            JsonElement last = declarations.get(declarations.size() - 1);
            return last.isJsonPrimitive()
                    ? fieldSignatureJavaType(last.getAsString()) : "";
        }

        private Port get(String id) {
            return ports.get(id);
        }

        private boolean contains(String id) {
            return ports.containsKey(id);
        }

        private Sort sort(String id) {
            Port port = ports.get(id);
            return port == null ? Sort.VALUE : port.sort;
        }

        private boolean isInput(String id) {
            Port port = ports.get(id);
            return port != null && port.input;
        }

    }

    private static final class Port {
        private final String javaType;
        private final String declaredFieldJavaType;
        private final Sort sort;
        private final boolean input;
        private final JsonObject metadata;

        private Port(String javaType, String declaredFieldJavaType,
                     Sort sort, boolean input, JsonObject metadata) {
            this.javaType = javaType;
            this.declaredFieldJavaType = declaredFieldJavaType;
            this.sort = sort;
            this.input = input;
            this.metadata = metadata == null
                    ? new JsonObject() : metadata.deepCopy();
        }

        /** The type Java declares for this port's value, when it is known. */
        private String declaredJavaType() {
            return firstNonBlank(javaType, declaredFieldJavaType);
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

    private enum Sort {
        BOOL("Bool"), INT("Int"),
        FLOAT32("(_ FloatingPoint 8 24)"),
        FLOAT64("(_ FloatingPoint 11 53)"), STRING("String"),
        REF("Ref"), MAP("AssocState"), VALUE("Value"),
        ARRAY_VALUE("IndexedState");

        private final String smt;

        Sort(String smt) {
            this.smt = smt;
        }

        private boolean floating() {
            return this == FLOAT32 || this == FLOAT64;
        }
    }

    private static final class Term {
        private final String text;
        private final Sort sort;
        private final IntegralWidth integralWidth;
        /** Empty only for non-String terms.  "false" means a known non-null
         * String; any other value is the nullable reference companion Bool. */
        private final String stringNullness;
        /** Stable provenance used only for Java reference identity. */
        private final String stringReferenceOrigin;
        /** Java evaluation definedness (notably String dereference guards). */
        private final String precondition;

        private Term(String text, Sort sort) {
            this(text, sort, IntegralWidth.NONE);
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth) {
            this(text, sort, integralWidth,
                    sort == Sort.STRING ? "false" : "", "", "true");
        }

        private Term(String text, Sort sort,
                     IntegralWidth integralWidth,
                     String stringNullness,
                     String stringReferenceOrigin,
                     String precondition) {
            this.text = text;
            this.sort = sort;
            this.integralWidth = sort == Sort.INT && integralWidth != null
                    ? integralWidth : IntegralWidth.NONE;
            this.stringNullness = sort == Sort.STRING
                    ? firstNonBlank(stringNullness, "false") : "";
            this.stringReferenceOrigin = sort == Sort.STRING
                    ? firstNonBlank(stringReferenceOrigin) : "";
            this.precondition = firstNonBlank(precondition, "true");
        }

        private static Term nullableString(String text, String nullness,
                                           String referenceOrigin) {
            return new Term(text, Sort.STRING, IntegralWidth.NONE,
                    nullness, referenceOrigin, "true");
        }

        private static Term nonNullString(String text,
                                          String precondition) {
            return new Term(text, Sort.STRING, IntegralWidth.NONE,
                    "false", "", precondition);
        }

        private Term withPrecondition(String value) {
            return new Term(text, sort, integralWidth, stringNullness,
                    stringReferenceOrigin, value);
        }

        private boolean isZero() {
            return "0".equals(text) || "(- 0)".equals(text);
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

    /** The Java sort one boxed container cell unboxes to. */
    private static ContainerSmtCodec.Sort unboxedCellSort(String javaType) {
        Sort sort = sortOfJava(javaType);
        return sort == Sort.BOOL ? ContainerSmtCodec.Sort.BOOL
                : sort == Sort.REF ? ContainerSmtCodec.Sort.REF
                : sort == Sort.FLOAT32 ? ContainerSmtCodec.Sort.FLOAT32
                : sort == Sort.FLOAT64 ? ContainerSmtCodec.Sort.FLOAT64
                : sort == Sort.STRING ? ContainerSmtCodec.Sort.STRING
                : ContainerSmtCodec.Sort.VALUE;
    }

    private static Sort containerCellSort(String cell) {
        return containerSort(declaredCellJavaType(cell));
    }

    private static final Pattern CELL_PARAMETER = Pattern.compile(
            ">\\.param[0-9]+:([^#]+)(?:#.*)?$");
    private static final Pattern CELL_RETURN = Pattern.compile(
            "^<[^:]+:\\s+([^<>\\s]+)\\s+[^<>\\s(]+\\([^>]*\\)>"
                    + "\\.return(?:#.*)?$");

    /**
     * The Java type a port's cell declares, or an empty string.
     */
    private static String declaredCellJavaType(String cell) {
        String value = firstNonBlank(cell).trim();
        Matcher parameter = CELL_PARAMETER.matcher(value);
        if (parameter.find()) return parameter.group(1).trim();
        String field = fieldSignatureJavaType(value);
        if (!field.isEmpty()) return field;
        Matcher returned = CELL_RETURN.matcher(value);
        return returned.matches() ? returned.group(1) : "";
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

    private static boolean numeric(Sort sort) {
        return sort == Sort.INT || sort.floating();
    }

    private static IntegralWidth integralWidthOfJava(String javaType) {
        return JavaPrimitiveSmtSemantics.widthOfJavaType(javaType);
    }

    static String canonicalIntegralJavaType(String schemaJavaType,
                                            String expressionJavaType) {
        return integralWidthOfJava(schemaJavaType) == IntegralWidth.NONE
                ? expressionJavaType : schemaJavaType;
    }

    private static FloatingKind floatingKind(Sort sort) {
        if (sort == Sort.FLOAT32) return FloatingKind.JAVA_FLOAT;
        if (sort == Sort.FLOAT64) return FloatingKind.JAVA_DOUBLE;
        return FloatingKind.NONE;
    }

    /** Java binary numeric promotion for the two integral JVM widths. */
    private static IntegralWidth promotedIntegralWidth(Term left,
                                                        Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
    }

    private static String wrapIntegral(String expression,
                                       IntegralWidth width) {
        return JavaPrimitiveSmtSemantics.wrap(expression, width);
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

    private static String castDescriptor(String javaType) {
        return JavaPrimitiveSmtSemantics.primitiveDescriptor(javaType);
    }

    private static String expressionJavaType(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return "";
        JsonObject object = expression.getAsJsonObject();
        String type = string(object, "_type");
        if ("TypeCastExpression".equals(type)) {
            return string(object, "_java_type");
        }
        if ("MethodExpression".equals(type)) {
            return string(object(object, "_res_exp"), "_java_type");
        }
        return string(object, "_java_type");
    }

    private static String integerLiteral(String value) {
        String raw = firstNonBlank(value).trim();
        if (raw.isEmpty() || raw.length() > 1024) return null;
        try {
            BigInteger parsed = new BigInteger(raw);
            return parsed.signum() < 0
                    ? "(- " + parsed.negate().toString() + ")"
                    : parsed.toString();
        } catch (NumberFormatException ignored) {
            return null;
        }
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
