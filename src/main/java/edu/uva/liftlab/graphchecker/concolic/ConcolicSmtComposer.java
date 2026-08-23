package edu.uva.liftlab.graphchecker.concolic;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.artifact;
import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sibling;

import edu.uva.liftlab.graphchecker.contract.BoundedOutputVersions;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
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

/**
 * Composes one selected fatal-region query with concolic summaries of its
 * upstream regions and runtime-validated equality/read-from edges.  The
 * resulting SMT is a structurally checked candidate formula used to obtain a
 * candidate model. Promoting it with an unforced natural target replay is
 * deliberately outside this component and remains the documented TODO.
 *
 * <p>This class is intentionally project independent. It consumes only common
 * region, summary, branch-contract, solver-context, and runtime-edge schemas;
 * no adapter can inject an arbitrary case formula. Missing upstream summaries
 * are reported as gaps and make the query unsatisfiable, so a syntactically
 * valid SMT query is never mistaken for a complete model.</p>
 */
public final class ConcolicSmtComposer {
    /** Expression node the VM serializes one guarded read-from arm as. */
    static final String RECORDED_ITE_TYPE = "IteExpression";
    /** Prefix of the one value term of one guarded read. */
    static final String READ_VALUE_PREFIX = "rf_value__";
    /**
     * A declared cut port on a relation that names no region for it.
     *
     * <p>A refusal and not a gap: the port is declared, the relation is real,
     * and the one thing needed to place it - which activation's region the
     * port belongs to - is stated by nobody. Answering {@code ""} dropped the
     * relation out of the resolved summary graph in silence.</p>
     */
    static final String CUT_PORT_REGION_UNRESOLVED =
            "CUT_PORT_REGION_UNRESOLVED";
    static final String LIVE_HANDOFF_PRODUCER_RELATION_MISSING =
            "LIVE_HANDOFF_PRODUCER_RELATION_MISSING";
    static final String LIVE_HANDOFF_PRODUCER_RELATION_AMBIGUOUS =
            "LIVE_HANDOFF_PRODUCER_RELATION_AMBIGUOUS";

    /** The three authorities README {@code SMT-1} admits for one input. */
    /**
     * The recorded model holds reads that no arm and no guarded choice
     * explains, so its completeness claim examined nothing.
     */
    static final String RECORDED_MODEL_UNEXPLAINED_READS =
            "RecordedModelUnexplainedReads";

    static final String LOCAL_SYMBOLIC_ROOT = "LOCAL_SYMBOLIC_ROOT";
    static final String COMMUNICATION_LEAF = "COMMUNICATION_LEAF";
    static final String READ_FROM_ARM = "READ_FROM_ARM";
    /** A selected input several authorities claim; the lineage is not one. */
    static final String INPUT_AUTHORITY_AMBIGUOUS =
            "SelectedInputMultipleAuthorities";
    /** A selected input term nothing in the run constrained. */
    /**
     * A state read the target performs whose recorded arm no authority
     * admitted, while the container it reads is still asserted over.
     */
    static final String SELECTED_STATE_READ_WITHOUT_AUTHORITY =
            "SelectedStateReadWithoutAuthority";

    static final String INPUT_AUTHORITY_MISSING =
            "SelectedInputWithoutAuthority";
    /** A read the model kept open, so no witness over it is final. */
    static final String SELECTED_READ_FROM_UNKNOWN_ARM =
            "SelectedReadFromUnknownArm";
    /** A selected edge the run only ever proposed. */
    static final String SELECTED_EDGE_CANDIDATE_ONLY =
            "SelectedEdgeCandidateOnly";
    /** Names the gate that produced finalStatus and its refusal rows. */
    static final String ACCEPTANCE_GATE_AUTHORITY =
            "COMPOSER_ACCEPTANCE_GATE_V1";
    /** The target published no reach query this composition could start at. */
    static final String TARGET_REACH_QUERY_ABSENT =
            "TARGET_REACH_QUERY_ABSENT";
    /** The order domain holds no VALUE_HANDOFF edge for one export. */
    static final String HANDOFF_ORDER_UNRECORDED =
            "HANDOFF_SEND_BEFORE_RECEIVE_UNRECORDED";
    /** A handoff whose receiving port the region catalog does not declare. */
    static final String HANDOFF_PORT_UNDECLARED =
            VmHandoffEvidence.PORT_UNDECLARED;
    static final String HANDOFF_PRODUCER_CASE_MISSING =
            "HANDOFF_PRODUCER_CASE_MISSING";
    static final String HANDOFF_PRODUCER_CASE_AMBIGUOUS =
            "HANDOFF_PRODUCER_CASE_AMBIGUOUS";
    static final String HANDOFF_PRODUCER_GUARD_MALFORMED =
            "HANDOFF_PRODUCER_GUARD_MALFORMED";
    private static final String CASE_REGION_ID = "_caseRegionId";
    /**
     * Declaration conflicts and a selected count beyond K_L refuse final
     * acceptance. Missing path-local count/cardinality evidence remains a
     * coverage gap and does not rewrite or discard the guarded case.
     */
    private static final Set<String> LOOP_AUTHORITY_REFUSALS =
            new LinkedHashSet<>(Arrays.asList(
                    BoundedLoopComposition.LOOP_BODY_BOUND_UNDECLARED,
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES,
                    BoundedLoopComposition.LOOP_CLASSIFICATION_UNDECLARED,
                    BoundedLoopComposition.LOOP_CLASSIFICATION_DISAGREES,
                    LoopBoundPolicy.PATH_LOOP_COUNT_OUT_OF_BOUND));
    /** Whether this artifact may be accepted as the milestone result. */
    public static final String FINAL_STATUS = "finalStatus";
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
                    // VM evidence that the fatal query already embeds.  They
                    // deliberately have no outputClosure and are therefore
                    // not upstream RelationSummary inputs.  A campaign file
                    // may contain both roles; accepting it directly keeps the
                    // production pipeline from needing a second filtering
                    // artifact.
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
        // is never promoted into target-reach evidence by composition.
        PortIndex ports = PortIndex.from(regions);
        JsonObject rawContext = object(fatal, "symbolicContext");
        // Runtime-confirmed first-hop demands are authoritative.  CLI bounds
        // describe supplied summaries; they must never erase a demanded edge
        // and turn its consumer input into an unconstrained existential.
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
        // writer/read event. Resolution deliberately admits only aliases
        // backed by an exact producer summary.  Re-scope the context to that
        // resolved graph before emission: one surviving alternative becomes
        // an ordinary versioned merge, while an entirely concrete alias
        // group disappears without creating symbolic ports.
        JsonObject context = boundedContext(resolutionContext,
                resolved);
        Emitter emitter = new Emitter(ports,
                new InvocationKey(string(fatal, "regionId"),
                        string(resolutionContext, "occurrenceId")),
                failureWitness);
        emitter.begin(fatal);
        // A configured source may reach a selected downstream relation
        // through VM value handoff without making its own summary a lowered
        // relation.  All summaries passed to this composition are already the
        // selected campaign scope, so source identity must be registered from
        // that complete evidence set before case-local alpha-renaming.
        List<JsonObject> allCaseEvidenceRows = caseEvidenceRows(
                summaries, fatal);
        emitter.registerSymbolicSources(allCaseEvidenceRows);
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
        emitter.unsupported.addAll(resolved.gaps);

        // The bounded-loop prefixes of every selected occurrence, built here
        // rather than beside their own emission because the writer universe
        // places a writer at the loop slots of the loop it sits in.
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
            for (JsonElement element : array(object(relation.toJson(),
                    "regionRelation"), "cases")) {
                if (element.isJsonObject()) {
                    loops.observeCase(relation.occurrenceId(),
                            element.getAsJsonObject());
                }
            }
        }

        // The recorded session model is lowered first because everything
        // after it may consume it: the target predicate itself can be a
        // guarded read, an exact binding orders its two events in this
        // model's one position domain, and a guarded binding hands its
        // consumer port the very value term these selectors choose.
        List<JsonObject> evidenceRows =
                new ArrayList<>(selectedEvidenceRows);
        if (object(fatal, SharedStateEvidence.RECORDED_FIELD).size() > 0
                || !VmHandoffEvidence.eventsOf(fatal).isEmpty()) {
            evidenceRows.add(fatal);
        }
        RecordedSessionModel recorded = RecordedSessionModel.of(
                evidenceRows,
                fatalTargetTerms(fatal), string(fatal, "regionId"));
        emitRecordedSessionModel(emitter, recorded);
        // README SMT-1: a shared-state read the target performs is a
        // selected input and must name exactly one authority.  The
        // selected-input ledger below covers declared ports; a container
        // read does not travel on a port, so a map whose only recorded arm
        // the session excluded reached the formula with no authority and no
        // refusal - the query then states a membership question about a
        // container nothing constrains, which solves trivially and reads as
        // success.  The exclusion is decided at import and was previously
        // reported only while lowering a selected relation's edges, so a
        // target whose producer relation was refused lost the finding
        // altogether.  It is named here from the target's own bindings.
        reportUnauthorizedTargetStateReads(emitter, fatal,
                resolved.staticEdgeIds());
        List<String> fatalTerms = new ArrayList<>();
        List<String> fatalPrefixTerms = new ArrayList<>();
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
                List<String> prefixTerms = new ArrayList<>();
                JsonArray constraints = array(path, "constraints");
                for (int constraintIndex = 0;
                     constraintIndex < constraints.size();
                     constraintIndex++) {
                    boolean fatalCondition = constraintIndex
                            == constraints.size() - 1;
                    if (fatalCondition) {
                        emitter.beginFatalOperandCapture(
                                selectedPathOrdinal);
                    }
                    try {
                        String constraintTerm = emitter.constraint(
                                constraints.get(constraintIndex), label);
                        pathTerms.add(constraintTerm);
                        if (!fatalCondition) {
                            prefixTerms.add(constraintTerm);
                            emitter.recordFatalPrefixEquality(
                                    selectedPathOrdinal,
                                    constraints.get(constraintIndex));
                        }
                    } finally {
                        if (fatalCondition) {
                            emitter.endFatalOperandCapture();
                        }
                    }
                }
                String pathTerm = and(pathTerms);
                String prefixTerm = and(prefixTerms);
                fatalTerms.add(pathTerm);
                fatalPrefixTerms.add(prefixTerm);
                emitter.recordTargetReach(selectedPathOrdinal, path,
                        pathTerm, fatal);
                emitter.bindFatalPathPrefix(selectedPathOrdinal,
                        prefixTerm);
                emitter.bindFatalPath(selectedPathOrdinal, pathTerm);
            }
        } finally {
            emitter.restoreSymbolScope(previousFatalScope);
        }
        emitter.bindTargetReachAssertion();
        emitter.bindFatalPrefixAssertion(or(fatalPrefixTerms));
        emitter.bindFatalPathAssertion(or(fatalTerms));

        for (RelationSummary selection : loweredRelations) {
            emitter.lowerRelation(selection);
        }
        emitter.merge(context);
        emitter.mergeEdgeBindings(resolved.selectedEdges.values());
        emitter.mergeVmHandoffs(caseEvidenceRows, allCaseEvidenceRows,
                loops, recorded);
        emitter.finishRecordedReadExistence();
        emitter.finishFatalAbsenceMutationWitness();
        emitter.finishBindings();
        boolean auditedEdgeEvidence = true;
        auditDroppedEdgeEvidence(emitter, ports,
                resolved.valueBindingRows());
        emitter.finish();
        String composedSmt = emitter.render();

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("fatalSite", fatalSite);
        manifest.add("resolvedEdgeBindings",
                GSON.toJsonTree(resolved.staticEdgeIds()));
        manifest.add("fatalAbsenceMutationWitness",
                failureWitness.manifest());
        manifest.add("portOccurrences", emitter.portOccurrences());
        manifest.add("selectedInputLedger", emitter.selectedInputLedger());
        // Present whenever the pass ran, so an empty ledger from a run that
        // checked nothing stays distinguishable from one that found nothing.
        manifest.add("selectedInputLedgerAudit",
                emitter.selectedInputLedgerAudit());
        manifest.add("operandBindingLedger",
                emitter.operandBindingLedger());
        manifest.add("targetReachLedger", emitter.targetReachLedger());
        manifest.addProperty("droppedEdgeEvidenceAudit",
                auditedEdgeEvidence ? "AUDITED"
                        : "EDGE_VALIDATIONS_NOT_SUPPLIED");
        manifest.add("recordedSessionModel", recorded.manifest());
        manifest.add(BoundedLoopComposition.MANIFEST_FIELD,
                loops.manifest());
        manifest.add("recordedValueBindings",
                emitter.recordedValueBindingLedger());
        List<JsonObject> selectedBindings = bindingRows(
                resolved.selectedEdges.values());
        // README's rule for the sibling fact - "an empty selection: nothing
        // was lowered, so nothing said anything, is not complete either" -
        // stated for this one.  Both conjuncts of recordedModelComplete are
        // vacuous on an empty model: retainsUnknownArm iterates nothing, and
        // partial() is false precisely when there are no guarded reads.  A
        // model that explained none of the reads it holds therefore asserted
        // completeness *because* it contained nothing, and the guard that
        // forbids reading UNSAT as unreachability was left with one working
        // term.  A model holding no recorded read at all is deliberately not
        // caught: there is nothing there to be incomplete about.
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
            // separate question from how much of the run it still covers.
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
        // kept an unknown-writer arm.  Both stay in the model - the candidate
        // set is what the run observed - and both are reported here, so a
        // reader can tell either from a proven binding.
        coverage.addAll(RecordedReadFrom.provenanceGaps(
                resolved.valueBindingRows()));
        coverage.addAll(sourceEpochDivergences(
                resolved.selectedEdges.values()));
        // Gaps the target query named while being built best effort.  They
        // are coverage facts about the query this composition consumes, so
        // they belong in the same stream rather than only in its artifact.
        for (JsonElement element : array(fatal, "coverageGaps")) {
            if (element.isJsonObject()) {
                coverage.add(element.getAsJsonObject().deepCopy());
            }
        }
        JsonArray coverageGaps = new JsonArray();
        for (JsonObject gap : coverage) coverageGaps.add(gap);
        manifest.add("coverageGaps", coverageGaps);
        // The formula is emitted whenever a usable target relation remains;
        // the coverage state says how much of the model the run still
        // supports, so an UNSAT from a partial model is never read as a
        // conclusion about the program.
        manifest.add("divergence", CoverageDivergence.summary(coverage,
                emitter.unsupported.isEmpty()));
        JsonArray gaps = new JsonArray();
        appendGaps(gaps, "COMPOSITION_GAP", emitter.unsupported);
        manifest.add("gaps", gaps);
        manifest.addProperty("state", gaps.size() == 0
                ? "CANDIDATE_READY" : "CANDIDATE_WITH_GAPS");
        // A recorded model that keeps an unknown-writer arm or an unclosed
        // candidate set is an under-approximation of the run, so an
        // unsatisfiable answer over it is inconclusive.  It does not reject a
        // satisfying witnessed path: branch replay is best effort and later
        // cases extend the causal supergraph instead of invalidating an
        // already authoritative case.
        manifest.addProperty("recordedModelComplete",
                !recordedReadsUnexplained
                        && !recorded.partial()
                        && !retainsUnknownArm(resolved.valueBindingRows()));
        // README GATE-1's decision, stated as its own member.
        //
        // It is deliberately not folded into "state": that member says the
        // composition produced a usable model, and the diagnostic reach
        // projection consumes it as such - a partial recorded model is still
        // the run's own evidence and is still worth solving.  Whether the
        // result may be accepted as the milestone artifact is a stricter and
        // separate question, and an open arm or a candidate-only edge answers
        // it no.
        //
        // Every blocker is one named row - code, subject, detail - so a later
        // layer reports it instead of parsing it back out of a sentence, and
        // so an empty list is readable beside finalStatusEvidence, which says
        // what this gate ranged over to produce it.
        AcceptanceGate gate = new AcceptanceGate();
        for (JsonElement element : gaps) {
            JsonObject gap = element.getAsJsonObject();
            gate.refuse(string(gap, "kind"), string(gap, "subject"), "");
        }
        // Completion criterion 5, and README LOOP-1's "a missing
        // classification, guard, slot, state version, cardinality, or bound is
        // a gap".  An accepted witness may not consume a value whose loop
        // prefix ran to the bound and was still continuing, and it may not be
        // built over a loop whose kind, K_L or N no plan row states.  The
        // composition already names each of those as coverage; here they also
        // decide acceptance.  A slot with no relation is deliberately not in
        // this set: a condition-bounded replay materializes only the slots it
        // ran, and the fixed-count case where every slot is required is
        // refused by the emitter instead.
        Set<String> selectedScopeMethods =
                selectedScopeMethods(loweredRelations);
        for (JsonObject gap : loops.gaps()) {
            String reason = string(gap, "reason");
            if (!LOOP_AUTHORITY_REFUSALS.contains(reason)) continue;
            // A retained loop outside every selected relation's slice is a
            // loop this composition never had to model: the run walked it,
            // nothing the witness rests on came out of it, and the coverage
            // row above already says so.  Refusing on it would make an
            // acceptance decision about startup, configuration parsing,
            // metrics registration or protobuf validation.  The scope is the
            // relation's own definition methods, so the rule follows the
            // slice and needs no list of names to keep current.
            if (!touchesSelectedScope(string(gap, "subject"),
                    selectedScopeMethods)) {
                continue;
            }
            gate.refuse(reason, string(gap, "subject"),
                    string(gap, "detail"));
        }
        // The read-from half: a selected read whose writer set the trace only
        // ever proposed, and one that kept the arm no writer answers. Both
        // are already coverage; the location each one is about is the subject
        // rather than the shape of the row it came in.
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
        manifest.addProperty(FINAL_STATUS, gate.size() == 0
                ? FINAL_READY : FINAL_REFUSED);
        manifest.add("finalStatusRefusals", gate.refusals);
        // What the gate ranged over, so that an empty refusal list is the
        // answer of a gate that ran and not the silence of one that did not.
        manifest.add("finalStatusEvidence", gateEvidence(
                loweredRelations.size(),
                emitter.selectedInputLedger().size(),
                selectedBindings.size(), gaps.size(),
                loops.boundedLoops().size()));
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                composedSmt.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        // Everything the causal graph needs is now in this manifest, and it
        // is the same everything the formula was lowered from.  Assembling it
        // once, here, is what stops the visualization from building a second
        // reading of the run out of the runtime plan's edge catalog.
        manifest.add(CanonicalSessionModel.MANIFEST_FIELD,
                CanonicalSessionModel.of(manifest,
                        localRelations(loweredRelations),
                        resolvedEdgeEndpoints(resolved.selectedEdges
                                .values()),
                        string(fatal, "regionId"),
                        firstNonBlank(
                                string(resolutionContext, "occurrenceId"),
                                string(fatal, "occurrenceId"))));
        return new Result(composedSmt, manifest);
    }

    /**
     * What the acceptance gate ranged over, in the shape every composition
     * publishes it in.
     *
     * <p>A composition that weighed nothing says so with zero counts.
     * Omitting the member instead would make "the gate ran and found nothing
     * to weigh" read exactly like "the gate never ran", and telling those two
     * apart is the whole reason this member exists.</p>
     */
    private static JsonObject gateEvidence(int selectedRelations,
                                           int selectedInputs,
                                           int selectedEdgeBindings,
                                           int compositionGaps,
                                           int boundedLoops) {
        JsonObject evidence = new JsonObject();
        evidence.addProperty("authority", ACCEPTANCE_GATE_AUTHORITY);
        evidence.addProperty("selectedRelations", selectedRelations);
        evidence.addProperty("selectedInputs", selectedInputs);
        evidence.addProperty("selectedEdgeBindings", selectedEdgeBindings);
        evidence.addProperty("compositionGaps", compositionGaps);
        evidence.addProperty("boundedLoops", boundedLoops);
        return evidence;
    }

    /**
     * The composition of a target whose reach query never arrived.
     *
     * <p>The query is the one input this component starts at, and a task that
     * failed closed leaves it absent or holding no ready row.  That is a
     * selected blocker of this run and not an infrastructure failure, so it
     * is published as the Composer's own refusal - the layer README
     * {@code GATE-1} makes the sole owner of that decision - rather than
     * thrown, which left the failure to be inferred from gap rows written by
     * other stages.</p>
     *
     * <p>The artifact is a header-only query with no assertion: there is
     * nothing recorded to assert.  It carries the same closure members every
     * composition does, all stating the same thing - that this one closed
     * nothing.</p>
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
        manifest.add("portOccurrences", new JsonArray());
        // No port was occupied and no model was produced, so this artifact
        // is not a candidate model a later stage may conclude from.
        manifest.addProperty("state", "CANDIDATE_WITH_GAPS");
        manifest.addProperty(FINAL_STATUS, FINAL_REFUSED);
        manifest.add("finalStatusRefusals", gate.refusals);
        manifest.add("finalStatusEvidence", gateEvidence(0, 0, 0, 0, 0));
        manifest.add("composedSmtArtifact", artifact(arguments.output,
                smtLib.getBytes(StandardCharsets.UTF_8)));
        manifest.add("runtimePlanArtifact", artifact(arguments.runtimePlan));
        return new Result(smtLib, manifest);
    }

    /**
     * The endpoints of the resolved trace edges.
     *
     * <p>{@code resolvedEdgeBindings} names them by id alone, which is enough
     * for an audit and not enough to draw one. An edge that never became a
     * value binding is still part of what the composition selected, so the
     * canonical model needs the pair it ran between.</p>
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
                    bindingSourceOutput(edge.binding),
                    bindingTargetInput(edge.binding)));
        }
        return rows;
    }

    /**
     * The selected local region relations, as the canonical model holds them.
     *
     * <p>The formula keeps only their effects - assertion names, port terms -
     * so the identity of the relation each one came from would otherwise reach
     * no artifact at all, and the graph would have to rediscover it from the
     * runtime plan.</p>
     */
    private static JsonArray localRelations(
            Collection<RelationSummary> selected) {
        JsonArray relations = new JsonArray();
        for (RelationSummary summary : selected) {
            JsonObject row = summary.toJson();
            relations.add(CanonicalSessionModel.relation(
                    summary.summaryId(), summary.relationKey(),
                    summary.regionId(),
                    summary.occurrenceId(), summary.sourceKey(),
                    array(object(row, "regionRelation"), "cases").size(),
                    string(row, "pathCoverageState")));
        }
        return relations;
    }

    /**
     * Lowers the recorded session model into the formula.
     *
     * <p>Six things reach the SMT here, and every one of them is stated over
     * the same two variable families - one {@code event_position__} per
     * recorded event and one {@code rf_selector__} per candidate arm:</p>
     *
     * <ul>
     *   <li>the shared order domain, one bounded position per recorded event,
     *   related exactly where the ledger related them;</li>
     *   <li>exactly-one selection per guarded read;</li>
     *   <li>{@code write < read} and the latest-visible cut against the
     *   competing writers, per selected arm;</li>
     *   <li>writer existence: an arm whose write the domain does not hold is
     *   asserted infeasible;</li>
     *   <li>the reader-value equality, which is where the choice stops being
     *   metadata and starts deciding the target's value;</li>
     *   <li>the writer's own recorded path guard, which is what makes an arm
     *   whose writer never took its branch infeasible.</li>
     * </ul>
     *
     * <p>The first four are the recorded model's own terms. The last two need
     * the expression emitter, so they are lowered here, against the same
     * selector names, and never against a second selector family.</p>
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
        // guarded relation defines the same constants later.
        for (String selector : recorded.caseSelectors()) {
            emitter.declare(selector, Sort.BOOL);
        }
        // Recorded event existence is declared beside the selectors it is
        // implied by. Target existence is not part of this state model: it
        // comes only from the exact target event carried by a fatal case.
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
        // ever sees the query, rather than emitting a formula over it.
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
     * or epoch other than the producing summary's own.
     *
     * <p>Different nodes and different epochs never merge implicitly. A
     * binding whose producer occurrence is not inside the producer's source
     * key would do exactly that, so it is reported as a source/epoch
     * divergence. The check is made only for occurrence ids in the canonical
     * {@code <sourceKey>/region/<region>#<n>} form: claiming a divergence
     * from an id this layer cannot parse would be inventing one.</p>
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
                "PRODUCER_OCCURRENCE_OUTSIDE_SOURCE_KEY",
                string(binding, "edgeId"),
                "producer occurrence " + occurrence
                        + " is not an occurrence of source " + sourceKey);
    }

    /**
     * The refusal rows one acceptance gate collected.
     *
     * <p>One named row per code and subject, in the order the blockers were
     * found. A row is never dropped for having a blank subject: a blocker
     * nobody could name is still a blocker, and the shape that hides it is
     * exactly the silence this gate exists to prevent.</p>
     */
    /**
     * The definition methods of every relation this composition lowered.
     *
     * <p>This is the slice the witness is built out of.  A loop whose control
     * sites all lie outside it was walked by the run but contributed nothing
     * the model rests on.
     */
    private static Set<String> selectedScopeMethods(
            List<RelationSummary> lowered) {
        Set<String> methods = new LinkedHashSet<>();
        for (RelationSummary relation : lowered) {
            methods.addAll(relation.outputClosure().executionScope().methods());
        }
        return methods;
    }

    /**
     * Whether a loop gap's subject names a control site in one of
     * {@code scopeMethods}.  The subject carries the loop site id, which is a
     * method signature plus a unit index, or an {@code L(a+b+...)} nest of
     * them; a nest counts when any member does.
     */
    static boolean touchesSelectedScope(String subject,
                                        Set<String> scopeMethods) {
        if (scopeMethods.isEmpty()) return true;
        for (Matcher matcher = LOOP_SITE_METHOD.matcher(subject);
             matcher.find(); ) {
            if (scopeMethods.contains(matcher.group())) return true;
        }
        return false;
    }

    /** The method-signature half of a loop site id. */
    private static final Pattern LOOP_SITE_METHOD =
            Pattern.compile("<[^<>]+>");

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

        /**
         * Copies {@code other}'s refusals except those whose code is in
         * {@code coverageOnly}, which are appended to {@code coverage} as
         * named partial-coverage rows instead.  A code that describes how much
         * of the run the model covers belongs there; only a code that forbids
         * acceptance belongs in the gate.
         */
        void refuseAllExcept(AcceptanceGate other, Set<String> coverageOnly,
                             List<JsonObject> coverage) {
            for (JsonElement element : other.refusals) {
                JsonObject row = element.getAsJsonObject();
                String code = string(row, "code");
                if (coverageOnly.contains(code)) {
                    coverage.add(CoverageDivergence.of(
                            CoverageDivergence.Kind.FLOW, code,
                            string(row, "subject"), string(row, "detail")));
                    continue;
                }
                refuse(code, string(row, "subject"), string(row, "detail"));
            }
        }

        void refuseAll(AcceptanceGate other) {
            for (JsonElement element : other.refusals) {
                JsonObject row = element.getAsJsonObject();
                refuse(string(row, "code"), string(row, "subject"),
                        string(row, "detail"));
            }
        }

        int size() {
            return refusals.size();
        }
    }

    /**
     * Whether any composed binding still admits a writer nobody recorded.
     *
     * <p>A read can keep its unknown arm without the slice holding a guarded
     * term for it: an exact read of a location whose writer set is already
     * incomplete is decided and still under-approximate, because an untracked
     * write could have produced the same value.</p>
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

    /** The binding rows of the resolved edges. */
    private static List<JsonObject> bindingRows(
            Collection<ResolvedEdge> edges) {
        List<JsonObject> rows = new ArrayList<>();
        for (ResolvedEdge edge : edges) rows.add(edge.binding);
        return rows;
    }

    /**
     * Names every state read the target performs that reached the formula
     * with no admitted read-from arm.
     *
     * <p>An excluded arm is not an absent one: the session decided that this
     * read took a write other than the candidate the trace offered, which is
     * exactly what {@link RecordedReadFrom}'s per-location index exists to
     * establish when one declared field names several objects.  What must not
     * happen is for that decision to leave no trace in the composed artifact
     * while the container it concerns is still asserted over.</p>
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
            emitter.unsupported.add(SELECTED_STATE_READ_WITHOUT_AUTHORITY
                    + ":" + firstNonBlank(string(binding, "locationKey"),
                    string(binding, RecordedReadFrom.EDGE_FIELD), edgeId)
                    + ":" + provenance);
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
            // owner; no heuristic reconstruction is involved.
            row.addProperty("regionId", summary.regionId());
            rows.add(row);
        }
        return rows;
    }


    /**
     * Every row that may carry case-local VM handoff references: each
     * selected relation's guarded cases and the target-reach query itself.
     */
    private static List<JsonObject> caseEvidenceRows(
            Collection<RelationSummary> relations, JsonObject fatal) {
        List<JsonObject> rows = new ArrayList<>();
        for (RelationSummary relation : relations == null
                ? Collections.<RelationSummary>emptyList() : relations) {
            JsonObject row = relation.toJson();
            JsonArray cases = array(object(row, "regionRelation"), "cases");
            for (int index = 0; index < cases.size(); index++) {
                JsonElement element = cases.get(index);
                if (!element.isJsonObject()) continue;
                JsonObject item = element.getAsJsonObject();
                item.addProperty("toOccurrenceId", relation.occurrenceId());
                item.addProperty(CASE_REGION_ID, relation.regionId());
                String owner = RecordedSessionModel.caseOwner(
                        relation.regionId(), relation.occurrenceId(),
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
        }
        return rows;
    }

    private static String symbolScopeKey(String raw, String scope,
                                         String sourceIdentity) {
        return sourceIdentity == null
                ? firstNonBlank(scope, "global") + "\u0000" + raw
                : "configured-source\u0000" + sourceIdentity;
    }

    /** Focused seam for the source/case alpha-renaming invariant. */
    static String symbolScopeKeyForTests(List<JsonObject> owners, String raw,
                                         String scope) {
        String identity = SymbolicSourceEvidence.rawSymbolIdentities(owners)
                .get(raw);
        return symbolScopeKey(raw, scope, identity);
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
     *
     * <p>The runtime plan is a workload-wide discovery catalog.  Relevance is
     * admitted only by a lowered relation, an endpoint of a resolved edge, or
     * the fatal target occurrence itself. Nothing is admitted by unresolved
     * context, exchange identity, payload equality or catalog adjacency.</p>
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
        // are selection authorities.
        addOccurrence(fatal, "occurrenceId", selected);
        collectOccurrences(object(fatal, "selectedTargetOccurrence"),
                selected);
        for (JsonObject binding : resolvedBindings == null
                ? Collections.<JsonObject>emptyList() : resolvedBindings) {
            collectOccurrences(binding, selected);
        }
        addOccurrence(fatal, "occurrenceId", selected);

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
     *
     * <p>An input the query presents without a producer is a freedom: the
     * model lets it take any value of its type, so a condition that turns on
     * it asserts almost nothing.  That freedom is honest only while no
     * producer for it was ever proven.  When the validated runtime edges
     * already carry an admissible write/read pair naming that exact consumer
     * port, the composition dropped a relation it was entitled to use, and
     * reporting no gap over it is a false report - worse than never having
     * found the evidence, because silence cannot be told from a genuine
     * absence.</p>
     *
     * <p>The admission gate is the shared one.  An edge counts only where
     * {@link AutomaticRegionEdge#selectedReadFromCompositionBinding} admits
     * it and the resolved summary graph actually selected it. Concrete,
     * candidate and excluded trace rows are scheduling/audit evidence, not a
     * value relation the composer dropped. One gap per unbound consumer port
     * keeps the report proportional to the freedoms, not to the trace.</p>
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
     * Checks that an observed-path relation states its under-approximation.
     *
     * <p>There is no second mode to ask for. README's completion criteria say
     * the observed concolic cases <em>are</em> an existential
     * under-approximation, so every relation this composer reads is one, and
     * a flag naming the only mode it is ever in could refuse a campaign but
     * never make one more honest. What the run has to state is how far its
     * coverage got, and it does: each relation carries its own
     * {@code pathCoverageState}. That state guides further best-effort replay;
     * it does not reject a satisfying path whose selected causal chain has
     * complete value authority.</p>
     */
    private static void requireObservedCoverage(JsonObject summary,
                                                JsonObject coverage)
            throws IOException {
        JsonObject relation = object(summary, "regionRelation");
        if (integer(coverage, "schemaVersion", -1) != 1
                || !"OBSERVED_PATH_COVERAGE".equals(
                string(coverage, "kind"))
                || !"IMPORTED_VM_PATH_UNDERAPPROX_V1".equals(
                string(coverage, "authority"))
                || bool(coverage, "complete", true)
                // One projection authority remains.  The full-path collision
                // fallback was deleted with README PC-1's ambient path
                // condition, so the disjunct admitting a relation whose guard
                // and constraint authority were both that fallback could no
                // longer be satisfied by anything the merge can emit.
                || !("SELECTIVE_SYMBOLIC_BRANCH_SLICE".equals(
                string(relation, "guardProjection"))
                && "SELECTIVE_SYMBOLIC_INPUT_SLICE_V1".equals(
                string(coverage, "constraintProjectionAuthority")))
                || integer(coverage, "observedCaseCount", -1)
                != array(relation, "cases").size()
                || integer(coverage, "observedPathCount", -1) < 1
                || integer(coverage, "observedCaseCount", -1)
                < integer(coverage, "observedPathCount", -1)
                || string(coverage, "observedPathSetHash").isEmpty()) {
            throw new IOException(
                    "Malformed observed-path under-approximation");
        }
    }

    private static void appendGaps(JsonArray target, String kind,
                                   Set<String> subjects) {
        for (String subject : subjects) {
            JsonObject gap = new JsonObject();
            gap.addProperty("kind", kind);
            gap.addProperty("subject", subject);
            target.add(gap);
        }
    }

    private static void requireCanonicalFatalQuerySchema(JsonObject fatal)
            throws IOException {
        String kind = string(fatal, "kind");
        if (integer(fatal, "schemaVersion", -1) != 1
                || !"TARGET_REACH_PATH_SET_QUERY".equals(kind)) {
            throw new IOException("Unsupported canonical fatal query schema");
        }
        if (!"RECORDED_TARGET_PREFIX_V1".equals(
                string(fatal, "constraintAuthority"))
                || string(fatal, "targetSiteId").isEmpty()) {
            throw new IOException(
                    "Incomplete closed target reach path query");
        }
        for (JsonElement element : array(fatal, "paths")) {
            if (!element.isJsonObject()
                    || !element.getAsJsonObject().has("constraints")
                    || !element.getAsJsonObject().get("constraints")
                    .isJsonArray()) {
                throw new IOException(
                        "Malformed target reach path query member");
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
     *
     * <p>The fatal symbolic context is the only authority for the first hop.
     * Once an exact producer summary has been selected, its requested-output
     * slice declares the downstream input ports that may recursively admit an
     * upstream edge binding.  This keeps global plans and unrelated summary
     * bindings out of the automatic SMT relation.</p>
     */
    private static ResolvedSummaryGraph resolveSummaryGraph(
            JsonObject fatal, JsonObject context,
            SummaryIndex summaryIndex) {
        ProducerDemandIndex knownDemands = new ProducerDemandIndex();
        List<JsonObject> equalities = relationRows(context,
                "equalityRelations");
        List<JsonObject> targetBindings = relationRows(fatal,
                "selectedTargetBindings");
        while (true) {
            ResolvedSummaryGraph result = resolveSummaryGraphPass(
                    fatal, context, summaryIndex, knownDemands, equalities,
                    targetBindings);
            if (!knownDemands.addAll(result.demands)) return result;
        }
    }

    private static ResolvedSummaryGraph resolveSummaryGraphPass(
            JsonObject fatal, JsonObject context, SummaryIndex summaries,
            ProducerDemandIndex knownDemands,
            List<JsonObject> equalities,
            List<JsonObject> targetBindings) {
        String fatalRegion = string(fatal, "regionId");
        String fatalInstance = string(context, "occurrenceId");
        ResolvedSummaryGraph result = new ResolvedSummaryGraph(fatalRegion,
                fatalInstance, knownDemands);

        registerContextDemands(result, equalities);
        registerTargetDemands(result, targetBindings);
        seedContextRelations(result, summaries, equalities, "EQUALITY");
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
            // edge at a time lets two singleton summaries stand in for one
            // atomic multi-output invocation.
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
            result.gaps.add("SelectedTargetClosureResolvedNoProducer");
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

    @SafeVarargs
    private static void registerContextDemands(
            ResolvedSummaryGraph graph, List<JsonObject>... groups) {
        for (List<JsonObject> relations : groups) {
            for (JsonObject relation : relations) {
                registerContextDemand(graph, relation);
            }
        }
    }

    private static void registerContextDemand(ResolvedSummaryGraph graph,
                                              JsonObject relation) {
        String output = string(relation, "fromEndpoint");
        String sourceRegion = relationRegion(relation, "fromRegion", output);
        if (!graph.fatalRegion.equals(relationRegion(relation, "toRegion",
                string(relation, "toEndpoint")))
                || sourceRegion.isEmpty()) return;
        for (JsonElement element : selectedBindings(relation)) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!AutomaticRegionEdge.composerTraversalBinding(binding)) {
                continue;
            }
            String targetInstance = bindingTargetInstance(binding);
            if (!targetInstance.isEmpty()
                    && !graph.fatalInstance.equals(targetInstance)) {
                continue;
            }
            String sourceInstance = bindingSourceInstance(binding);
            if (!sourceInstance.isEmpty()) {
                graph.registerDemand(sourceRegion, sourceInstance, output);
            }
        }
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

    private static void seedContextRelations(
            ResolvedSummaryGraph graph, SummaryIndex summaries,
            List<JsonObject> relations, String expectedKind) {
        for (JsonObject relation : relations) {
            seedContextRelation(graph, relation, summaries, expectedKind);
        }
    }

    private static void seedContextRelation(ResolvedSummaryGraph graph,
                                            JsonObject relation,
                                            SummaryIndex summaries,
                                            String expectedRelationKind) {
        String output = string(relation, "fromEndpoint");
        String input = string(relation, "toEndpoint");
        String sourceRegion = relationRegion(relation, "fromRegion", output);
        if (!graph.fatalRegion.equals(
                relationRegion(relation, "toRegion", input))
                || sourceRegion.isEmpty()) {
            return;
        }
        JsonArray bindings = selectedBindings(relation);
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!AutomaticRegionEdge.composerTraversalBinding(binding)) {
                graph.gaps.add("UntrustedContextEdgeBinding:"
                        + string(binding, "edgeId"));
                continue;
            }
            String targetInstance = bindingTargetInstance(binding);
            if (!targetInstance.isEmpty()
                    && !graph.fatalInstance.equals(targetInstance)) {
                continue;
            }
            String sourceInstance = bindingSourceInstance(binding);
            if (sourceInstance.isEmpty()) continue;
            ProducerKey key = selectExactProducer(graph, summaries,
                    sourceRegion, sourceInstance, output, binding);
            if (key != null) {
                graph.addDirectBindingIfPresent(key, graph.fatalRegion,
                        graph.fatalInstance, input, relation,
                        binding, expectedRelationKind);
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
        // occurrence that can know which earlier write it consumed.  The
        // producer summary was already complete when that read happened, so
        // its diagnostic edge copy can only remain TRACE_CANDIDATE_WRITER.
        // selectExactProducer has instead checked the producer occurrence,
        // output port, and this edge id in that output member's causal slice.
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
                demandedOutputs)) {
            if (!requestedInstance.isEmpty()
                    && !requestedInstance.equals(
                    summary.occurrenceId())) {
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
            graph.gaps.add("SelectedReadFromMissingProducerCausalEdge:"
                    + preferredEdge + ":"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs));
            return null;
        }
        if (!selectedReadFrom && unique.size() > 1
                && !preferredEdge.isEmpty()) {
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
            graph.gaps.add("MissingExactProducerSummary:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs));
            return null;
        }
        if (fingerprints.size() != 1) {
            graph.gaps.add("AmbiguousProducerClosureFingerprint:"
                    + producerLabel(region, requestedInstance,
                    demandedOutputs) + ":fingerprints=" + fingerprints);
            return null;
        }
        if (unique.size() > 1) {
            graph.gaps.add("AmbiguousExactProducerSummary:"
                    + producerLabel(region, requestedInstance,
                            demandedOutputs));
            return null;
        }
        RelationSummary selected = unique.values().iterator().next();
        String instance = firstNonBlank(requestedInstance,
                selected.occurrenceId());
        ProducerKey key = new ProducerKey(region, instance, output,
                selected.summaryId());
        RelationSummary held = graph.selectedProducerSummaries.get(key);
        if (held != null && !held.same(selected)) {
            graph.gaps.add("ConflictingProducerSummarySelection:" + key);
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

    private static JsonArray selectedBindings(JsonObject relation) {
        JsonArray admitted = new JsonArray();
        for (JsonElement element : array(relation, "selectedBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            // Runtime refinement keeps a ruled-out trace candidate in the
            // artifact for auditability.  It is not a selected read-from arm
            // and therefore must neither demand a producer relation nor emit
            // a value/order constraint.
            if (AutomaticRegionEdge.unselectedReadFromBinding(binding)) {
                continue;
            }
            admitted.add(binding);
        }
        return admitted;
    }

    /**
     * Keeps a context relation tied to the exact runtime edge that justified
     * it.  Matching ports and instances are not enough: an RPC equality and a
     * heap READ_FROM can legitimately name the same canonical cells while
     * carrying different identity semantics.
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

    /**
     * The supplied relations, indexed by the demanded outputs each closure
     * declares, because that is what a demand is resolved against.
     */
    private static final class SummaryIndex {
        private final Map<String, List<RelationSummary>> byClosure =
                new LinkedHashMap<>();
        private final Map<String, List<RelationSummary>> byRegion =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> bindingsByTarget =
                new LinkedHashMap<>();

        private static SummaryIndex build(List<RelationSummary> summaries) {
            SummaryIndex result = new SummaryIndex();
            for (RelationSummary decoded : summaries) {
                result.byRegion.computeIfAbsent(decoded.regionId(),
                        ignored -> new ArrayList<>()).add(decoded);
                result.byClosure.computeIfAbsent(closureKey(
                                decoded.regionId(),
                                decoded.outputClosure().outputPorts()),
                        ignored -> new ArrayList<>()).add(decoded);
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

        /**
         * Whether this summary is the one that may state a read-from arm.
         *
         * <p>The scheduler declares one read-from binding on <em>both</em>
         * endpoints, and correctly: both the writer and the reader have to
         * select the carrier.  Only the reader can attest the arm.  Its
         * read-out of the session store names the read as its own
         * activation's and resolves the writer; the writer's read-out of
         * that same store sees a read of an activation it is not, cannot
         * name the reader, and so its copy stays a trace candidate no matter
         * what the run proved.  Both copies used to be indexed under the
         * same target, so one edge id resolved twice and the copy that
         * happened to arrive first became the arm - which is not an
         * authority in either direction.  A binding that is not a read-from
         * is not addressed by this rule and is indexed as before.</p>
         */
        private static boolean readFromArmAuthority(RelationSummary summary,
                                                    JsonObject binding) {
            if (string(binding, RecordedReadFrom.EDGE_FIELD).isEmpty()) {
                return true;
            }
            return bindingTargetInstance(binding)
                    .equals(summary.occurrenceId());
        }

        /** The producers that cover one demand. */
        private List<RelationSummary> covering(String region,
                                               Set<String> outputs) {
            List<RelationSummary> exact = byClosure.get(
                    closureKey(region, outputs));
            if (exact != null) return exact;
            int smallest = Integer.MAX_VALUE;
            List<RelationSummary> result = new ArrayList<>();
            for (RelationSummary summary : byRegion.getOrDefault(region,
                    Collections.emptyList())) {
                Set<String> available =
                        summary.outputClosure().outputPorts();
                if (!available.containsAll(outputs)) continue;
                if (available.size() < smallest) {
                    result.clear();
                    smallest = available.size();
                }
                if (available.size() == smallest) result.add(summary);
            }
            return result;
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

        private Set<String> outputs(String region, String instance) {
            Set<String> result = new TreeSet<>();
            Set<String> exact = outputsByInvocation.get(
                    key(region, instance));
            if (exact != null) result.addAll(exact);
            return result;
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
     * its exact runtime state edge, and real VM output relations.  It is used
     * when a fatal associative lookup returns null and the supplying region
     * has a path that actually removes a member from that same state.
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
                            edge.summary.toJson(), output)) {
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
            return ContainerSmtCodec.EXPRESSION_TYPE.equals(
                    string(read, "_type"))
                    && "ASSOCIATIVE".equals(string(read, "shape"))
                    && "READ".equals(string(read, "operation"))
                    ? read : null;
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
                JsonObject summary, String output) {
            for (JsonElement caseElement : array(
                    object(summary, "regionRelation"), "cases")) {
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

        private JsonObject manifest() {
            JsonObject result = new JsonObject();
            result.addProperty("authority",
                    "EXACT_FATAL_ABSENCE_MUTATION_WITNESS_V1");
            result.addProperty("state", demands.isEmpty()
                    ? "NOT_APPLICABLE" : clauses.isEmpty()
                    ? "GAP" : "PINNED");
            result.addProperty("clauseCount", clauses.size());
            return result;
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
            // authority that settles it.  Equal rows are the same evidence
            // offered twice and are simply kept once.
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
            // exact producer occurrence.  The target query establishes the
            // cross-region edge at this exact consumer occurrence.  Requiring
            // the local summary to repeat the consumer edge would make one
            // observed producer output unusable by a second recorded read of
            // that same version.  Admit the query edge directly only when its
            // VM/runtime authority and both endpoints agree with the selected
            // local relation; no concrete value participates in this join.
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

        private boolean containsBinding(JsonObject relation,
                                        JsonObject binding) {
            String from = string(relation, "fromEndpoint");
            String to = string(relation, "toEndpoint");
            for (ResolvedEdge selected : selectedEdges.values()) {
                JsonObject candidate = selected.binding;
                String kind = bindingRelationKind(candidate);
                if (from.equals(bindingSourceOutput(candidate))
                        && to.equals(bindingTargetInput(candidate))
                        && bindingSourceInstance(binding).equals(
                        bindingSourceInstance(candidate))
                        && bindingTargetInstance(binding).equals(
                        bindingTargetInstance(candidate))
                        && sameCompositionRelation(candidate, relation, kind)
                        && sameCompositionRelation(candidate, binding, kind)) {
                    return true;
                }
            }
            return false;
        }

    }

    private static JsonObject boundedContext(JsonObject source,
                                             ResolvedSummaryGraph graph) {
        JsonObject result = new JsonObject();
        result.addProperty("occurrenceId", string(source, "occurrenceId"));
        result.add("equalityClasses",
                array(source, "equalityClasses").deepCopy());
        JsonArray selected = new JsonArray();
        for (JsonElement element : array(source, "equalityRelations")) {
            if (!element.isJsonObject()) {
                continue;
            }
            JsonObject relation = element.getAsJsonObject();
            JsonObject exact = selectedContextRelation(relation, graph);
            if (exact.size() > 0) selected.add(exact);
        }
        result.add("equalityRelations", selected);
        return result;
    }

    private static JsonObject selectedContextRelation(
            JsonObject relation, ResolvedSummaryGraph graph) {
        JsonArray bindings = new JsonArray();
        for (JsonElement element : selectedBindings(relation)) {
            if (element.isJsonObject()
                    && graph.containsBinding(relation,
                    element.getAsJsonObject())) {
                bindings.add(element.deepCopy());
            }
        }
        if (bindings.size() == 0) return new JsonObject();
        JsonObject result = relation.deepCopy();
        result.add("selectedBindings", bindings);
        return result;
    }

    /**
     * The region whose name an endpoint id carries, or {@code ""}.
     *
     * <p>A region mints its own ports as {@code <regionId>.in./.out.}, so for
     * those the id is the answer. A <em>declared cut port</em> is not one of
     * those and never will be: {@code CommunicationCatalogContract} names it
     * after the exchange <em>site</em> - {@code <exchangeSiteKey>.req.<name>}
     * or {@code .resp} - because the port belongs to a call site two
     * occurrences meet at, and the site has no region. So
     * {@code ""} is the right answer for one, and the wrong thing to do with
     * that answer is to treat it as "give up": use {@link #relationRegion},
     * which asks the relation itself, wherever an empty answer would drop the
     * row.</p>
     */
    private static String regionOf(String endpoint) {
        if (endpoint == null) return "";
        int marker = endpoint.indexOf(".in.");
        if (marker < 0) marker = endpoint.indexOf(".out.");
        if (marker > 0) return endpoint.substring(0, marker);
        marker = endpoint.indexOf("::");
        return marker > 0 ? endpoint.substring(0, marker) : "";
    }

    /**
     * The region one endpoint of a relation belongs to.
     *
     * <p>The relation states it, and the endpoint's own name is only the
     * fallback for the rows that state nothing. That order matters now that a
     * region can close on a declared cut port: parsing the id first answered
     * {@code ""} for every such producer, and an empty source region is what
     * {@link #seedContextRelation} returns on - so a client prefix whose
     * output really is a cut port was dropped out of the resolved summary
     * graph without a gap, a producer and its edge simply absent from the
     * composition.</p>
     *
     * @throws IllegalStateException naming {@link #CUT_PORT_REGION_UNRESOLVED}
     *         when the endpoint is a declared cut port and the relation names
     *         no region for it. That row cannot be placed and cannot be
     *         parsed either; dropping it is the loss above, and answering
     *         with the fatal region would attribute one activation's port to
     *         another.
     */
    static String relationRegion(JsonObject relation, String member,
                                 String endpoint) {
        String stated = string(relation, member);
        if (!stated.isEmpty()) return stated;
        String parsed = regionOf(endpoint);
        if (!parsed.isEmpty()) return parsed;
        if (CommunicationCatalogContract.declaredPortId(endpoint)) {
            throw new IllegalStateException(CUT_PORT_REGION_UNRESOLVED
                    + ": endpoint=" + endpoint + " member=" + member
                    + " edge=" + string(relation, "edgeId")
                    + " reason=A_DECLARED_CUT_PORT_CARRIES_NO_REGION_AND_THE"
                    + "_RELATION_NAMES_NONE");
        }
        return "";
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
         * views.  The String-sorted term carries the characters while this
         * companion Bool carries reference nullness.  Keeping the companion
         * keyed by the same case-scoped raw identity prevents one guarded
         * path from constraining another path's engine-local symbol.
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
        private final Set<String> canonicalPortTermBindings =
                new LinkedHashSet<>();
        private final Set<String> javaIntRangeAssertions =
                new LinkedHashSet<>();
        private final Set<String> javaIntegralRangeAssertions =
                new LinkedHashSet<>();
        /**
         * Exact target-side whole-map reads, indexed by the VM's session
         * owner.  The fatal expression still names the concrete map object
         * it queried; this table is the recorded proof that that object state
         * is the consumer port already bound to its selected writer.
         */
        private final Map<String, PortOccurrence> recordedMapCarrierPorts =
                new LinkedHashMap<>();
        private final Set<String> ambiguousMapCarrierKeys =
                new LinkedHashSet<>();
        private final Map<PortOccurrence, Sort>
                validatedIncomingEdgeInputSorts =
                new LinkedHashMap<>();
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
         * collected as the guards under which each recorded read's value was
         * actually consumed. A case selector means the load happens only in
         * that case; {@code "true"} means it happens in the fatal path or in
         * a selected edge binding, both of which the composition asserts
         * outright.
         */
        private final Map<Long, Set<String>> readCaseGuards =
                new LinkedHashMap<>();
        /**
         * Whether the emitter is walking the recorded read catalog.
         *
         * <p>That pass lowers every guarded read the slice holds so its arms
         * and value symbol exist; it is not a case that contains them.
         * Counting it as one would make every read exist unconditionally,
         * which is exactly the one-unconditional-choice-per-task shape
         * {@code READ-1} removes.</p>
         */
        private boolean catalogingRecordedReads;
        /** One value term per lowered guarded read, keyed by read event. */
        private final Map<Long, Term> guardedReadTerms =
                new LinkedHashMap<>();
        /**
         * The read whose arms are currently being lowered.
         *
         * <p>A serialized {@code IteExpression} names its arm by the bare
         * selector the read declared, so the read it belongs to is context.
         * The stack, rather than a field, is what keeps a guarded read nested
         * inside another guarded read's arm from stealing the outer read's
         * selectors.</p>
         */
        private final Deque<Long> readFromContext = new ArrayDeque<>();
        /** One evidence row per recorded value binding, for the manifest. */
        private final JsonArray recordedValueBindings = new JsonArray();
        /** Coverage findings of the recorded value lowering. */
        private final List<JsonObject> recordedCoverage = new ArrayList<>();
        /** Edges the recorded evidence ruled out, reported once each. */
        private final Set<String> excludedWriters = new LinkedHashSet<>();
        /** Consumer ports already handed a recorded guarded read's value. */
        private final Set<PortOccurrence> recordedReadBoundPorts =
                new LinkedHashSet<>();
        /** Consumer ports whose writer/read choice the VM already decided. */
        private final Set<PortOccurrence> recordedDecidedConsumerPorts =
                new LinkedHashSet<>();
        private final Set<String> declaredOutputVersionChoices =
                new LinkedHashSet<>();
        /**
         * README {@code SMT-1}'s selected-input ledger: which authority
         * constrained each selected input port occurrence.
         *
         * <p>Exactly one is required.  Zero authorities is a free SMT
         * variable wearing a port name, and several is an ambiguous lineage;
         * both refuse the composed artifact instead of being averaged into
         * one binding, because either would let a satisfying model reach the
         * target through a value nothing in the run produced.</p>
         */
        private final Map<PortOccurrence, Map<String,
                List<InputAuthorityEvidence>>>
                inputAuthorities = new LinkedHashMap<>();

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
        /**
         * Solver terms read by the final branch condition of each fatal
         * path.  These are captured while lowering the real expression, so
         * the audit consumes the exact terms and sorts emitted to SMT rather
         * than reconstructing them from source names.
         */
        private final Map<String, FatalOperand> fatalOperands =
                new LinkedHashMap<>();
        /**
         * Exact, top-level equalities asserted by each selected fatal path
         * prefix.  They let the audit follow an engine-local temporary back
         * to a dynamic input port without guessing from names or values.
         */
        private final Map<Integer, List<FatalPrefixEquality>>
                fatalPrefixEqualities = new LinkedHashMap<>();
        /** Exact value-carrying named assertions, indexed by runtime edge. */
        private final List<ProducerVersionBinding> producerVersionBindings =
                new ArrayList<>();
        private boolean capturingFatalOperands;
        private int capturedFatalPathOrdinal = -1;
        private int nextFatalOperandOrdinal;
        private String fatalPrefixAssertionName = "";
        private String fatalPrefixAssertionTerm = "";
        private String fatalPathAssertionName = "";
        private String fatalPathAssertionTerm = "";
        private final Map<Integer, String> fatalPathPrefixes =
                new LinkedHashMap<>();
        /** Exact runtime target events and the fatal case that owns each. */
        private final JsonArray targetReachEvents = new JsonArray();
        private final List<String> targetReachCaseTerms = new ArrayList<>();
        private final Set<String> fatalDependentAssertionNames =
                new LinkedHashSet<>();
        /** Definedness facts collected while lowering one container term. */
        private Set<String> currentContainerRequirements;
        private String currentGuard = "";
        private String currentSymbolScope = "global";
        /** Raw VM symbol -> exact configured program-source identity. */
        private Map<String, String> symbolicSourceIdentities =
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

        private void beginFatalOperandCapture(int pathOrdinal) {
            capturingFatalOperands = true;
            capturedFatalPathOrdinal = pathOrdinal;
        }

        private void endFatalOperandCapture() {
            capturingFatalOperands = false;
            capturedFatalPathOrdinal = -1;
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
            // a leading '-' for negative values.  Keeping this definition in
            // the common emitter lets the codec proof below remain ordinary,
            // solver-visible string semantics instead of an unconstrained UF.
            preamble.add("(define-fun java_int_to_string ((i Int)) String"
                    + " (ite (< i 0)"
                    + " (str.++ \"-\" (str.from_int (- i)))"
                    + " (str.from_int i)))");
            // Java integral bytecodes wrap in two's-complement arithmetic.
            // Keeping the public scalar carrier as SMT Int is convenient for
            // ports and model materialization, but raw SMT +, -, and * would
            // otherwise silently use unbounded mathematical integers.
            preamble.add(JavaPrimitiveSmtSemantics.INT_WRAP_DEFINITION);
            preamble.add(JavaPrimitiveSmtSemantics.LONG_WRAP_DEFINITION);
        }

        private void registerSymbolicSources(List<JsonObject> owners) {
            try {
                symbolicSourceIdentities =
                        SymbolicSourceEvidence.rawSymbolIdentities(owners);
            } catch (IllegalArgumentException malformed) {
                symbolicSourceIdentities = Collections.emptyMap();
                unsupported.add("SymbolicSourceEvidenceMalformed:"
                        + firstNonBlank(malformed.getMessage(), "UNKNOWN"));
            }
        }

        private void bindFatalPath(int pathOrdinal, String pathTerm) {
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
                demand.pathTerm = pathTerm;
                demand.keyTerm = key.text;
                demand.keyPrecondition = key.precondition;
            }
        }

        private void bindFatalPathAssertion(String pathTerm) {
            fatalPathAssertionTerm = pathTerm;
            fatalPathAssertionName = assertNamed("fatal_path", pathTerm);
            fatalDependentAssertionNames.add(fatalPathAssertionName);
        }

        /**
         * Files one case-local source attestation after checking it against
         * the selected query's replay witness. The case guard expresses the
         * desired opposite outcome; the runtime event is never rewritten to
         * claim that outcome was observed. A missing or mismatched event is
         * an acceptance refusal, never a reason to synthesize target
         * existence from state reads in the target region.
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
            String attestationRole = firstNonBlank(string(path,
                    TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE),
                    TargetReachPathQueryBuilder.SOURCE_TARGET_REACH_EVENT);
            boolean sourceAttestation = TargetReachPathQueryBuilder
                    .SOURCE_TARGET_REACH_EVENT.equals(attestationRole);
            boolean requiredAttestation = TargetReachPathQueryBuilder
                    .REQUIRED_TARGET_REACH_EVENT.equals(attestationRole);
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
            fatalDependentAssertionNames.add(assertNamed(
                    "target_reach_event", or(targetReachCaseTerms)));
        }

        private JsonArray targetReachLedger() {
            return targetReachEvents.deepCopy();
        }

        private void bindFatalPathPrefix(int pathOrdinal,
                                         String prefixTerm) {
            fatalPathPrefixes.put(pathOrdinal,
                    firstNonBlank(prefixTerm, "true"));
        }

        private void bindFatalPrefixAssertion(String prefixTerm) {
            fatalPrefixAssertionTerm = prefixTerm;
            fatalPrefixAssertionName = assertNamed(
                    "fatal_path_prefix", prefixTerm);
        }

        private void captureFatalOperand(JsonObject expression, Term term) {
            if (!capturingFatalOperands || term == null) return;
            String raw = string(expression, "_exp");
            // These are fixed engine literals, not solver operands.
            if ("N".equals(raw) || "V".equals(raw)) return;
            String port = findPort(raw);
            PortOccurrence occurrence = port.isEmpty() ? null
                    : currentOccurrence(port);
            String javaType = string(expression, "_java_type");
            Term pin = term.sort == Sort.VALUE || term.sort == Sort.MAP
                    || term.sort == Sort.ARRAY_VALUE
                    ? term : asValue(term, javaType);
            String key = capturedFatalPathOrdinal + "\u0000" + term.text
                    + "\u0000" + term.sort.name();
            if (fatalOperands.containsKey(key)) return;
            String operandId = "fatal_operand_" + capturedFatalPathOrdinal
                    + "_" + nextFatalOperandOrdinal++;
            fatalOperands.put(key, new FatalOperand(operandId,
                    capturedFatalPathOrdinal,
                    term.text, term.sort, pin.text, pin.sort, occurrence));
        }

        private void recordFatalPrefixEquality(
                int pathOrdinal, JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return;
            JsonObject object = expression.getAsJsonObject();
            if ("MethodExpression".equals(string(object, "_type"))
                    && isJavaParseInt(string(object, "_name"))) {
                SplitPiece source = exactParseIntIntegerSource(object);
                PortOccurrence sourceOccurrence =
                        exactIntegerPieceOccurrence(source);
                if (sourceOccurrence == null) return;
                Term result = term(object.get("_res_exp"), Sort.INT);
                Term value = integerPieceTerm(source);
                if (result.sort != value.sort) return;
                fatalPrefixEqualities.computeIfAbsent(pathOrdinal,
                        ignored -> new ArrayList<>()).add(
                        new FatalPrefixEquality(result.text, result.sort,
                                null, value.text, value.sort,
                                sourceOccurrence));
                return;
            }
            if (!"BinaryExpression".equals(string(object, "_type"))
                    || !"==".equals(string(object, "_op"))) {
                return;
            }
            JsonElement leftExpression = object.get("_left");
            JsonElement rightExpression = object.get("_right");
            PortOccurrence leftOccurrence = directPortOccurrence(
                    leftExpression);
            PortOccurrence rightOccurrence = directPortOccurrence(
                    rightExpression);
            if (leftOccurrence == null && rightOccurrence == null) return;

            Term left = term(leftExpression, null);
            Term right = term(rightExpression, left.sort);
            if (left.sort != right.sort) return;
            fatalPrefixEqualities.computeIfAbsent(pathOrdinal,
                    ignored -> new ArrayList<>()).add(
                    new FatalPrefixEquality(left.text, left.sort,
                            leftOccurrence, right.text, right.sort,
                            rightOccurrence));
        }

        /**
         * Returns the exact integer witness recognized by the parse/split
         * codec.  This is the same structural proof used to lower parseInt;
         * it does not infer lineage from a concrete value or a symbol name.
         */
        private SplitPiece exactParseIntIntegerSource(JsonObject expression) {
            JsonArray params = array(expression, "_param_list");
            if (params.size() != 1 && params.size() != 2) return null;
            if (params.size() == 2) {
                Integer radix = exactIntLiteral(params.get(1));
                if (radix == null || radix != 10) return null;
            }
            SplitSegment segment = exactSplitSegment(params.get(0));
            return segment.complete() ? segment.singleIntegerPiece() : null;
        }

        private PortOccurrence exactIntegerPieceOccurrence(
                SplitPiece piece) {
            if (piece == null || piece.integerSource == null
                    || !piece.integerSource.isJsonObject()) {
                return null;
            }
            JsonObject source = piece.integerSource.getAsJsonObject();
            if (!"SymbolExpression".equals(string(source, "_type"))) {
                return null;
            }
            String port = findPort(string(source, "_exp"));
            if (port.isEmpty()) return null;
            InvocationKey invocation = piece.integerInvocation == null
                    ? currentInvocation : piece.integerInvocation;
            return occurrence(invocation.instanceId, port);
        }

        private PortOccurrence directPortOccurrence(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            if (!"SymbolExpression".equals(string(object, "_type"))) {
                return null;
            }
            String port = findPort(string(object, "_exp"));
            return port.isEmpty() ? null : currentOccurrence(port);
        }

        private PortOccurrence exactFatalOperandOccurrence(
                FatalOperand operand) {
            if (operand.occurrence != null) return operand.occurrence;
            List<FatalPrefixEquality> equalities = fatalPrefixEqualities.get(
                    operand.pathOrdinal);
            if (equalities == null || equalities.isEmpty()) return null;

            Set<String> pending = new LinkedHashSet<>();
            Set<String> visited = new LinkedHashSet<>();
            Set<PortOccurrence> occurrences = new LinkedHashSet<>();
            pending.add(fatalEqualityTerm(operand.solverTerm,
                    operand.solverSort));
            while (!pending.isEmpty()) {
                String current = pending.iterator().next();
                pending.remove(current);
                if (!visited.add(current)) continue;
                for (FatalPrefixEquality equality : equalities) {
                    String left = fatalEqualityTerm(equality.leftTerm,
                            equality.leftSort);
                    String right = fatalEqualityTerm(equality.rightTerm,
                            equality.rightSort);
                    if (current.equals(left)) {
                        if (equality.leftOccurrence != null) {
                            occurrences.add(equality.leftOccurrence);
                        }
                        if (equality.rightOccurrence != null) {
                            occurrences.add(equality.rightOccurrence);
                        }
                        pending.add(right);
                    } else if (current.equals(right)) {
                        if (equality.leftOccurrence != null) {
                            occurrences.add(equality.leftOccurrence);
                        }
                        if (equality.rightOccurrence != null) {
                            occurrences.add(equality.rightOccurrence);
                        }
                        pending.add(left);
                    }
                }
            }
            return occurrences.size() == 1
                    ? occurrences.iterator().next() : null;
        }

        private String fatalEqualityTerm(String term, Sort sort) {
            return sort.name() + "\u0000" + term;
        }

        /**
         * Registers only VM-proven exact whole-map reads.
         *
         * <p>This is not field matching.  The VM location key supplies the
         * session-stable map owner, and the exact read-from edge supplies the
         * consumer occurrence and input port.  A conflicting port for the
         * same owner/occurrence is refused instead of guessed.</p>
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
            // matched against a rid parsed out of this session's own symbol
            // names, so both sides must speak the same session's numbering.
            String location = SharedStateEvidence.sessionLocationKey(binding);
            long owner = SharedStateEvidence.locationOwnerOf(location);
            String instance = bindingTargetInstance(binding);
            String input = bindingTargetInput(binding);
            // Exact and guarded VM read-from edges both carry a whole map
            // state.  The guarded edge still has to select one recorded arm;
            // this registration only makes that state available at the
            // consumer port instead of replaying a serialized seed history
            // beside it.
            String provenance = string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE);
            if (!(RecordedReadFrom.PROVENANCE_EXACT.equals(provenance)
                    || RecordedReadFrom.PROVENANCE_GUARDED.equals(provenance))
                    || !SharedStateEvidence.isMapState(location)) {
                return;
            }
            // Past that gate the arm *should* substitute the fatal map state
            // for this consumer's port, and each remaining precondition is a
            // way that substitution silently did not happen - the container
            // join then falls back to a free `sym__fatal_...` map root and
            // the paired signal reads "root vanished" and "root left
            // unauthorized" the same.  README's fail-closed discipline: name
            // the reason rather than let absence look like nothing wrong.
            // The sort check is the one most likely to bite, so it reports
            // the sort it actually found.
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
         *
         * <p>The version choice is a solver variable per port occurrence,
         * bounded by the site-local export.  Each expanded case's guard says
         * {@code choice == ordinal}; with the ordinary exactly-one selector
         * partition this makes the solver pick exactly one exported version
         * per producer occurrence, and different alpha-renamed occurrences
         * choose independently.</p>
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
         * {@code s != null}).  Keep that guard inside the expression so a
         * guarded-case selector owns it; emitting a top-level assertion while
         * constructing the selector would incorrectly constrain sibling
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
         *
         * <p>An operand slot the recording left out is not the Java null
         * reference: a recorded null is its own null symbol, and the two
         * appear side by side in the same relation.  Reading the omission
         * as null would state the one fact the record does not carry - and
         * it is the strongest fact available, because it decides every
         * later read of the value.  An absent operand is therefore a named
         * gap like any other unproven thing.</p>
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
                Term result = symbol(object, expected);
                captureFatalOperand(object, result);
                return result;
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
                // the currently imported path case; treating it as a global
                // identity accidentally equates (for example) one source's
                // clock read with a later read on a different source.
                String identity = function + "#" + count;
                String scopedIdentity = currentSymbolScope + "\u0000"
                        + identity;
                String name = scopedName("environment", identity) + "__"
                        + CanonicalJson.sha256(scopedIdentity)
                        .substring(0, 10);
                declare(name, Sort.INT);
                assertJavaIntegralDomain(name, Sort.INT, "J", identity);
                Term result = new Term(name, Sort.INT,
                        IntegralWidth.JAVA_LONG);
                captureFatalOperand(object, result);
                return result;
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
         *
         * <p>The node is the whole answer to "which write did this read
         * take": an exactly-one selection over the recorded candidate arms
         * plus an unconditional unknown-writer arm. The value it denotes is
         * one fresh constant, and each arm says what that constant equals
         * when its selector holds:</p>
         *
         * <pre>
         * rf_k -&gt; (v = expr_k AND guard(W_k))
         * </pre>
         *
         * <p>{@code write &lt; read}, the latest-visible cut and writer
         * existence are stated by the recorded model over the same selector
         * names, so nothing here needs to restate them and nothing here may
         * contradict them. The unknown arm deliberately constrains nothing
         * but the value - it is a fresh VM symbol - which is what keeps the
         * choice satisfiable when the recorded order rules every observed
         * writer out.</p>
         *
         * <p>The term is memoised per read event. Two mentions of one read
         * are one read, and giving them two constants would let a model take
         * two different writers for a single Java load.</p>
         */
        private Term guardedReadTerm(JsonObject node, Sort expected) {
            String fault = SharedStateEvidence.guardedReadFault(node);
            if (!fault.isEmpty()) {
                unsupported.add("UnadmittedGuardedRead:" + fault);
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            long readEventId = longInteger(node, "readEventId", 0L);
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
            JsonArray candidates = array(node, "candidates");
            List<Term> arms = new ArrayList<>();
            readFromContext.push(readEventId);
            try {
                for (JsonElement element : candidates) {
                    arms.add(term(element.getAsJsonObject().get("expression"),
                            want));
                }
            } finally {
                readFromContext.pop();
            }
            Sort sort = want != null && want != Sort.VALUE
                    ? want : arms.get(0).sort;
            for (Term arm : arms) {
                if (arm.sort != sort) {
                    unsupported.add("GuardedReadArmSortConflict:"
                            + readEventId + ":" + sort + "!=" + arm.sort);
                    return unsupportedTerm(sort);
                }
            }
            String value = READ_VALUE_PREFIX + readEventId;
            declare(value, sort);
            Term result = new Term(value, sort,
                    integralWidthOfJava(javaType));
            guardedReadTerms.put(readEventId, result);
            assertJavaIntegralDomain(value, sort, javaType,
                    "recorded read " + readEventId);
            emitGuardedReadArms(node, readEventId, candidates, arms, value);
            emitRecordedSelectionTerm(node, readEventId, sort, value);
            return result;
        }

        /**
         * Lowers the node's own serialized selection term.
         *
         * <p>The VM writes the choice twice: once as the candidate array the
         * arms above are stated over, and once as a nested
         * {@code IteExpression} chain over the same selectors. Admission
         * already requires both, so both are lowered - a chain this emitter
         * cannot render is a gap and not a detail, and finding that out here
         * is the difference between a named refusal and a formula quietly
         * built from half of an admitted node.</p>
         *
         * <p>Given the exactly-one selection the two are the same statement,
         * so asserting the chain cannot remove a model the arms admitted. It
         * can only conflict where the VM's two halves conflict, and a node
         * whose selection term contradicts its own candidates supports
         * nothing.</p>
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
         * states a choice over.
         *
         * <p>The recorded model gates each read's exactly-one on this Boolean
         * and every arm implies it; here it is bound to the cases that
         * actually consume the load. A read no selected case and no selected
         * binding consumes is bound false - it has no arm, and it imposes no
         * write/read order - and named, because "this run watched a load the
         * composed witness does not contain" is a coverage finding and not a
         * silent omission.</p>
         */
        private void finishRecordedReadExistence() {
            Set<Long> reads = new LinkedHashSet<>(guardedReadTerms.keySet());
            reads.addAll(recordedChoiceReads);
            for (Long readEventId : reads) {
                String symbol = RecordedSessionModel.readExistsName(
                        readEventId);
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
         *
         * <p>Both are stated unconditionally with respect to the region case
         * currently being lowered. A writer's path guard is a fact about the
         * writer's own execution, and the selector is the read's own choice;
         * neither becomes true only because some consumer case was taken, and
         * nesting them under {@code currentGuard} would let an unselected
         * consumer case silently license any writer.</p>
         */
        private void emitGuardedReadArms(JsonObject node, long readEventId,
                                         JsonArray candidates,
                                         List<Term> arms, String value) {
            String previousGuard = currentGuard;
            currentGuard = "";
            List<String> selectors = new ArrayList<>();
            try {
                for (int index = 0; index < candidates.size(); index++) {
                    JsonObject candidate = candidates.get(index)
                            .getAsJsonObject();
                    String arm = string(candidate, "selector");
                    String selector = RecordedSessionModel.selectorName(
                            readEventId, arm);
                    declare(selector, Sort.BOOL);
                    selectors.add(selector);
                    Term armTerm = arms.get(index);
                    String equality = assertNamed(
                            "recorded_read_value__" + readEventId + "__" + arm,
                            "(=> " + selector + " " + and(Arrays.asList(
                                    armTerm.precondition, "(= " + value + " "
                                            + armTerm.text + ")")) + ")");
                    String guardAssertion = emitRecordedWriterGuard(
                            readEventId, arm, selector, candidate);
                    recordedValueBindings.add(recordedValueBinding(node,
                            candidate, selector, equality, guardAssertion));
                }
                if (!recordedChoiceReads.contains(readEventId)) {
                    // The recorded model states the choice for every read it
                    // could place in the order domain.  A read it could not -
                    // an unwatched location, a session with no ledger - still
                    // denotes one value, so the choice is stated here, gated
                    // on the same read-existence Boolean, and the missing
                    // order stays a named coverage finding.
                    String exists = RecordedSessionModel.readExistsName(
                            readEventId);
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
        private String emitRecordedWriterGuard(long readEventId, String arm,
                                               String selector,
                                               JsonObject candidate) {
            if (bool(candidate, "unknown", false)) return "";
            long fieldVersionId = longInteger(candidate, "fieldVersionId", 0L);
            JsonObject version = recorded == null
                    ? new JsonObject()
                    : recorded.writerVersion(fieldVersionId);
            if (version.size() == 0) {
                unsupported.add("RecordedWriterVersionMissing:"
                        + readEventId + ":" + arm + ":" + fieldVersionId);
                return assertNamed("recorded_write_guard__" + readEventId
                                + "__" + arm,
                        "(=> " + selector + " false)");
            }
            // The guarded-read candidate is the reader-side VM answer.  A
            // version-store snapshot can confirm that its writer exists, but
            // cannot replace the path guard serialized on the selected arm:
            // doing so can make an infeasible reader choice satisfiable when
            // the two snapshots were captured at different points.
            JsonElement pathGuard = candidate.get("pathGuard");
            if (SharedStateEvidence.unguarded(pathGuard)) return "";
            String guard = constraint(pathGuard,
                    "recorded writer guard " + arm + " of read "
                            + readEventId);
            return assertNamed("recorded_write_guard__" + readEventId + "__"
                    + arm, "(=> " + selector + " " + guard + ")");
        }

        /** One machine-checkable evidence row for one lowered arm. */
        private JsonObject recordedValueBinding(JsonObject node,
                                                JsonObject candidate,
                                                String selector,
                                                String valueAssertion,
                                                String guardAssertion) {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "RECORDED_READ_FROM_VALUE_BINDING");
            row.addProperty("authority",
                    SharedStateEvidence.GUARDED_READ_AUTHORITY);
            row.addProperty("readEventId",
                    longInteger(node, "readEventId", 0L));
            String locationKey = SharedStateEvidence.locationKey(node);
            row.addProperty("locationKey", locationKey);
            // A map-state read is lowered by the same arms as a scalar one -
            // the arm expression is the only thing that differs - so the kind
            // travels as a property of the row rather than as a second row
            // shape the model and the drawing would each have to know.
            row.addProperty("locationKind",
                    SharedStateEvidence.locationKindOf(locationKey));
            row.addProperty("selector", selector);
            row.addProperty("arm", string(candidate, "selector"));
            row.addProperty("unknown", bool(candidate, "unknown", false));
            row.addProperty("fieldVersionId",
                    longInteger(candidate, "fieldVersionId", 0L));
            row.addProperty("writerRegionId", string(candidate, "regionId"));
            row.addProperty("valueAssertion", valueAssertion);
            row.addProperty("writerGuardAssertion", guardAssertion);
            row.addProperty("writerExists", recorded != null
                    && recorded.ordersEvent(longInteger(candidate,
                    "fieldVersionId", 0L)));
            return row;
        }

        /**
         * Lowers one arm of the VM's own serialized selection term.
         *
         * <p>The node names its arm by the bare selector the enclosing read
         * declared, so it is only meaningful inside that read. Outside one it
         * is refused rather than resolved against whichever read happens to
         * be in scope.</p>
         */
        private Term recordedIteTerm(JsonObject node, Sort expected) {
            String arm = string(node, "selector");
            if (readFromContext.isEmpty() || arm.isEmpty()) {
                unsupported.add("RecordedIteOutsideGuardedRead:"
                        + firstNonBlank(arm, "unnamed"));
                return unsupportedTerm(expected == null
                        ? Sort.VALUE : expected);
            }
            String selector = RecordedSessionModel.selectorName(
                    readFromContext.peek(), arm);
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
         * A serialized read also contains that version's historic PUT/REMOVE
         * chain; replaying the chain on top of the input duplicates the state
         * and turns its stored values into unrelated fatal-scope roots.  For
         * an observational operation, replace that receiver by the same
         * STATE identity whose exact carrier resolves to the input port.
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
                            // typed, unconstrained container state instead
                            // of rejecting every size/read derived from the
                            // collection.
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
                        ContainerSmtCodec.Term value, String javaType) {
                    if (value == null
                            || value.sort != ContainerSmtCodec.Sort.VALUE) {
                        return value;
                    }
                    String kind = ContainerSmtCodec.valueKind(javaType);
                    if (!kind.isEmpty()) {
                        require("((_ is " + kind + ") "
                                + value.text + ")");
                    }
                    String integralValue =
                            ContainerSmtCodec.unboxIntegral(
                                    value.text, javaType);
                    if (!integralValue.isEmpty()) {
                        return new ContainerSmtCodec.Term(
                                integralValue, ContainerSmtCodec.Sort.INT,
                                JavaPrimitiveSmtSemantics.widthOfJavaType(
                                        javaType));
                    }
                    Sort sort = sortOfJava(javaType);
                    if (sort == Sort.BOOL) {
                        return new ContainerSmtCodec.Term(
                                "(valueBool " + value.text + ")",
                                ContainerSmtCodec.Sort.BOOL);
                    }
                    if (sort == Sort.REF) {
                        return new ContainerSmtCodec.Term(
                                "(valueRef " + value.text + ")",
                                ContainerSmtCodec.Sort.REF);
                    }
                    if (sort == Sort.FLOAT32) {
                        return new ContainerSmtCodec.Term(
                                "(valueFloat " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT32);
                    }
                    if (sort == Sort.FLOAT64) {
                        return new ContainerSmtCodec.Term(
                                "(valueDouble " + value.text + ")",
                                ContainerSmtCodec.Sort.FLOAT64);
                    }
                    if (sort == Sort.STRING) {
                        return new ContainerSmtCodec.Term(
                                "(valueString " + value.text + ")",
                                ContainerSmtCodec.Sort.STRING);
                    }
                    return value;
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
                    // replay case that produced it.  Two producer summaries
                    // may come from separate JVM executions, where the same
                    // class/offset denotes two unrelated heaps.  Sharing one
                    // accessor across those cases accidentally couples their
                    // path guards.  Explicit composed edges and VM handoffs
                    // carry cross-case value identity; raw heap projection
                    // deliberately does not.
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
         *
         * <p>Older fixtures used {@code M_<type>__<rid>}; the Zero VM emits
         * {@code M_L'<type>'_<rid>}.  The type spelling is deliberately not
         * interpreted here: the final positive decimal component is the
         * session identity shared with {@code MAP_STATE/<rid>#-3}.</p>
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

        /**
         * A canonical port is a formal relation variable, not an engine-local
         * counter.  Give each scalar view of it one global typed witness and
         * connect that witness to the Value-typed schema port unconditionally.
         */
        private Term canonicalPortTerm(String port, Sort sort) {
            return canonicalPortTerm(port, sort, "");
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

        /**
         * Emits the minimum solver-native evidence required by a generic
         * pin/ablation audit.  The ledger deliberately contains no source
         * method, application field, or expected value: it names only terms,
         * sorts, dynamic ports, runtime edge ids, and the exact assertions
         * already present in the generated SMT.
         */
        private JsonObject operandBindingLedger() {
            JsonObject result = new JsonObject();
            result.addProperty("schemaVersion", 2);
            result.addProperty("kind", "FATAL_OPERAND_BINDING_LEDGER");
            JsonObject fatalAssertion = new JsonObject();
            fatalAssertion.addProperty("name", fatalPathAssertionName);
            fatalAssertion.addProperty("solverTerm",
                    fatalPathAssertionTerm);
            result.add("fatalPathAssertion", fatalAssertion);
            result.add("fatalDependentAssertionNames", GSON.toJsonTree(
                    fatalDependentAssertionNames));
            JsonObject retainedPrefix = new JsonObject();
            retainedPrefix.addProperty("name", fatalPrefixAssertionName);
            retainedPrefix.addProperty("solverTerm",
                    fatalPrefixAssertionTerm);
            result.add("retainedPathPrefixAssertion", retainedPrefix);

            JsonArray paths = new JsonArray();
            for (Map.Entry<Integer, String> entry
                    : fatalPathPrefixes.entrySet()) {
                int operandCount = 0;
                for (FatalOperand operand : fatalOperands.values()) {
                    if (operand.pathOrdinal == entry.getKey()) {
                        operandCount++;
                    }
                }
                JsonObject path = new JsonObject();
                path.addProperty("pathOrdinal", entry.getKey());
                path.addProperty("pathPrefixTerm", entry.getValue());
                path.addProperty("operandCount", operandCount);
                paths.add(path);
            }
            result.add("paths", paths);

            JsonArray operands = new JsonArray();
            for (FatalOperand operand : fatalOperands.values()) {
                JsonObject row = new JsonObject();
                row.addProperty("operandId", operand.operandId);
                row.addProperty("pathOrdinal", operand.pathOrdinal);
                PortOccurrence exactLineage =
                        exactFatalOperandOccurrence(operand);
                boolean exactOccurrence = exactLineage != null;
                Term exactLedgerTerm = exactOccurrence
                        ? exactFatalLedgerTerm(operand, exactLineage)
                        : null;
                row.addProperty("solverTerm", exactOccurrence
                        ? exactLedgerTerm.text : operand.solverTerm);
                row.addProperty("solverSort", exactOccurrence
                        ? exactLedgerTerm.sort.smt
                        : operand.solverSort.smt);
                row.addProperty("pinTerm", exactOccurrence
                        ? exactLedgerTerm.text : operand.pinTerm);
                row.addProperty("pinSort", exactOccurrence
                        ? exactLedgerTerm.sort.smt : operand.pinSort.smt);
                row.addProperty("pathPrefixTerm",
                        fatalPathPrefixes.getOrDefault(
                                operand.pathOrdinal, "true"));
                if (exactOccurrence) {
                    row.addProperty("portId", exactLineage.portId);
                    row.addProperty("occurrenceId",
                            exactLineage.invocation.instanceId);
                    row.addProperty("producerLineageStatus",
                            "EXACT_TARGET_PORT_OCCURRENCE");
                    row.addProperty("producerLineageAuthority",
                            operand.occurrence != null
                                    ? "DIRECT_FATAL_PORT_REFERENCE_V1"
                                    : "EXACT_FATAL_PREFIX_EQUALITY_ALIAS_V1");
                } else {
                    row.addProperty("producerLineageStatus",
                            "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE");
                }
                JsonArray versions = new JsonArray();
                Set<String> emitted = new LinkedHashSet<>();
                for (ProducerVersionBinding binding
                        : producerVersionBindings) {
                    // Producer-version evidence belongs only to the exact
                    // dynamic consumer port occurrence named by this fatal
                    // operand.  A same-sort producer elsewhere in the composed
                    // workflow is not lineage evidence for an engine-local
                    // temporary, even when both happen to take the same value.
                    if (!exactOccurrence
                            || !exactLineage.equals(binding.target)
                            || exactLedgerTerm.sort != binding.solverSort) {
                        continue;
                    }
                    String key = binding.edgeId + "\u0000"
                            + binding.assertionName + "\u0000"
                            + binding.solverTerm;
                    if (!emitted.add(key)) continue;
                    versions.add(binding.toJson());
                }
                row.add("producerVersions", versions);
                operands.add(row);
            }
            result.add("operands", operands);

            Map<String, Set<String>> assertionsByEdge =
                    new LinkedHashMap<>();
            for (ProducerVersionBinding binding : producerVersionBindings) {
                assertionsByEdge.computeIfAbsent(binding.edgeId,
                        ignored -> new LinkedHashSet<>()).add(
                        binding.assertionName);
            }
            JsonArray edges = new JsonArray();
            for (Map.Entry<String, Set<String>> entry
                    : assertionsByEdge.entrySet()) {
                JsonObject edge = new JsonObject();
                edge.addProperty("edgeId", entry.getKey());
                edge.add("assertionNames", GSON.toJsonTree(
                        entry.getValue()));
                edges.add(edge);
            }
            result.add("edgeAssertions", edges);
            return result;
        }

        /**
         * Uses the operand's native sort when the incoming edge carries it
         * directly.  State edges carry primitive fields through the ordinary
         * {@code Value} port, so in that one case the audit term is merely
         * the corresponding JVM box (for example {@code VInt(temp)}).  The
         * path prefix and the canonical port binding already assert the two
         * representations equal; no new program constraint is introduced.
         */
        private Term exactFatalLedgerTerm(FatalOperand operand,
                                          PortOccurrence occurrence) {
            boolean nativeSort = false;
            boolean valueSort = false;
            for (ProducerVersionBinding binding : producerVersionBindings) {
                if (!occurrence.equals(binding.target)) continue;
                nativeSort |= binding.solverSort == operand.solverSort;
                valueSort |= binding.solverSort == Sort.VALUE;
            }
            Term nativeTerm = new Term(operand.solverTerm,
                    operand.solverSort);
            if (nativeSort || !valueSort) return nativeTerm;
            Term boxed = asValue(nativeTerm);
            return boxed.sort == Sort.VALUE ? boxed : nativeTerm;
        }

        /**
         * Models an erased JVM reference view of a statically-known String
         * input without inventing a second Value binding for the same port.
         * The reference token is used only for identity/null comparisons;
         * its nullness is exactly the canonical nullable-String companion.
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
         * primitive value.  Field materialization and {@code ==}/{@code !=}
         * use this reference witness, while value/unboxing flow binds the
         * canonical Value port through {@link #canonicalPortTerm}.
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
                        : "source__" + scopeToken(sourceIdentity);
                symbol = new RawSymbol(name, requested);
                rawSymbols.put(key, symbol);
                declare(symbol.name, symbol.sort);
                assertJavaIntegralDomain(symbol.name, symbol.sort, javaType,
                        domainLabel);
            } else if (symbol.sort != requested) {
                unsupported.add(conflictLabel + "SortConflict:" + raw
                        + ":" + symbol.sort + "->" + requested);
            }
            if (symbol.sort == Sort.STRING) {
                if (symbol.nullness.isEmpty()) {
                    symbol.nullness = scopedName("string_is_null", raw);
                    declare(symbol.nullness, Sort.BOOL);
                }
                return Term.nullableString(symbol.name, symbol.nullness,
                        sourcePrefix + key);
            }
            return new Term(symbol.name, symbol.sort,
                    integralWidthOfJava(javaType));
        }

        private Term constant(JsonObject expression, Sort expected) {
            String raw = string(expression, "_exp");
            String javaType = string(expression, "_java_type");
            String value = constantPayload(raw);
            Sort sort = sortOfJava(javaType);
            Term result;
            // The JVM has no boolean comparison instruction, so a boolean
            // test compiles to a comparison against the int literal 0:
            // `if (!it.hasNext())` reaches here as BOOL against an int 0.
            // Reading that as a sort conflict drops the guard and forces
            // its case false, so an integral 0/1 in a boolean position is
            // Java's own encoding of false/true, exactly as the path
            // solver already reads it.
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

        /**
         * Admits only conversions that are the identity in this encoder's
         * mathematical primitive model.  The source is lowered with its own
         * declared type first; a target sort is never allowed to redeclare it.
         */
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
            String operator = string(expression, "_op");
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
                // ill-sorted SMT application.
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
                if ("%".equals(operator)) {
                    unsupported.add(resultSort.floating()
                            ? "JavaFloatingRemainderUnmodeled"
                            : "JavaIntegralRemainderUnmodeled");
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
                if ("@".equals(operator) || "/".equals(operator)) {
                    unsupported.add("JavaIntegralDivisionUnmodeled");
                    return unsupportedTerm(Sort.INT);
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
         * decimal conversion used by the generic Java codec. Operations with
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
                // every operand's sort first, then accept only real strings.
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
         *
         * <pre>
         * parseInt(splitElement(concat(toString(i), d, suffix),
         *                       d, [limit], 0)[, 10]) == i
         * </pre>
         *
         * and returns {@code i} itself.  Structural recognition is important:
         * a free parse/split UF would permit models that Java cannot execute.
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
            // make Java throw rather than return this integer.
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
         *
         * <p>Java's split takes a regex, so only a delimiter that is one
         * ordinary literal character is admitted.  The concatenation is then
         * ordinary text that can be segmented statically: an exact literal
         * part contributes its own characters, and every delimiter inside it
         * ends an element.  A {@code toString(int)} part renders only digits
         * and a leading minus - exactly what {@code java_int_to_string}
         * states - so for a delimiter outside that set it provably contains
         * none.  Any other part might contain a delimiter and decides
         * nothing.</p>
         *
         * <p>The walk must reach the delimiter that closes the requested
         * element, because a later part could otherwise still extend it.  An
         * element that runs to the end of the concatenation is admitted only
         * when it is provably non-empty, since Java drops trailing empty
         * elements.</p>
         */
        private SplitSegment exactSplitSegment(JsonElement expression) {
            // A split result reaches its reader through the array the VM
            // filled in, so resolve the select-over-store first: the codec
            // lowers the same selection, and this proof inspects syntax.
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
            String delimiter = exactStringLiteral(params.get(1));
            String delimiterGap = literalDelimiterGap(delimiter);
            if (!delimiterGap.isEmpty()) {
                return SplitSegment.gap(delimiterGap);
            }
            if (params.size() == 4) {
                Integer limit = exactIntLiteral(params.get(2));
                // A positive limit applies the pattern at most limit-1
                // times, so it has to allow the index splits that reach
                // this element plus the one that closes it.  Zero and
                // negative limits always split as far as the text goes.
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
                String literal = exactStringLiteral(part);
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
         * invocation.  A literal always does, and a port names one formal
         * relation variable whose witness {@link #integerPieceTerm} selects
         * by entering the stating invocation.  Anything else - a region
         * local symbol above all - is named only inside the invocation that
         * stated it, and lowering it elsewhere would invent a free value.
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

        private boolean flattenConcat(JsonElement expression,
                                      List<JsonElement> result) {
            if (expression == null || !expression.isJsonObject()) {
                return false;
            }
            JsonObject object = expression.getAsJsonObject();
            if (!"OpStrExpression".equals(string(object, "_type"))
                    || !"concat".equals(string(object, "_name"))
                    || bool(object, "_is_not", false)) {
                return false;
            }
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (parameter != null && parameter.isJsonObject()
                        && "OpStrExpression".equals(string(
                        parameter.getAsJsonObject(), "_type"))
                        && "concat".equals(string(
                        parameter.getAsJsonObject(), "_name"))) {
                    if (!flattenConcat(parameter, result)) return false;
                } else {
                    result.add(parameter);
                }
            }
            return true;
        }

        private boolean provablyStringValued(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if ("ConStringSymbolExp".equals(type)) return true;
            if ("SymbolExpression".equals(type)
                    || "ConSymbolExp".equals(type)
                    || "ConstExpr".equals(type)) {
                return sortOfJava(string(object, "_java_type"))
                        == Sort.STRING;
            }
            if (!"OpStrExpression".equals(type)
                    || bool(object, "_is_not", false)) return false;
            String operation = string(object, "_name");
            if ("toString".equals(operation)) {
                JsonArray params = array(object, "_param_list");
                return params.size() == 1
                        && isPrimitiveIntExpression(params.get(0));
            }
            if (!"concat".equals(operation)) return false;
            JsonArray params = array(object, "_param_list");
            if (params.size() == 0) return false;
            for (JsonElement parameter : params) {
                if (!provablyStringValued(parameter)) return false;
            }
            return true;
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

        private boolean isPrimitiveIntExpression(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return false;
            JsonObject object = expression.getAsJsonObject();
            String javaType = string(object, "_java_type");
            return "I".equals(javaType) || "int".equals(javaType);
        }

        private Integer exactIntLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConstExpr".equals(type) || "ConSymbolExp".equals(type))) {
                return null;
            }
            String javaType = string(object, "_java_type");
            if (!("I".equals(javaType) || "int".equals(javaType))) {
                return null;
            }
            String value = constantPayload(string(object, "_exp"));
            if (!value.matches("-?[0-9]+")) return null;
            try {
                return Integer.valueOf(value);
            } catch (NumberFormatException ignored) {
                return null;
            }
        }

        private String exactStringLiteral(JsonElement expression) {
            if (expression == null || !expression.isJsonObject()) return null;
            JsonObject object = expression.getAsJsonObject();
            String type = string(object, "_type");
            if (!("ConStringSymbolExp".equals(type)
                    || "ConstExpr".equals(type)
                    || "ConSymbolExp".equals(type))) return null;
            if (sortOfJava(string(object, "_java_type")) != Sort.STRING) {
                return null;
            }
            return constantPayload(string(object, "_exp"));
        }

        /**
         * Admits only a delimiter that is one ordinary literal character.
         *
         * <p>Java splits on a regex, so a metacharacter would match text
         * this segmentation never sees.  A delimiter made only of digits or
         * a minus is still admitted here and refused later, but only if an
         * integer rendering actually takes part.</p>
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
                Term boxedPrefix = asValue(value);
                Term boxedResult = asValue(result);
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
            // none; its cases are lowered exactly as a producer's are.
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
            List<String> selectors = new ArrayList<>();
            Set<String> selectorSymbols = new LinkedHashSet<>();
            String previousGuard = currentGuard;
            for (int index = 0; index < cases.size(); index++) {
                // Guard construction belongs to the outer relation.  Leaving
                // case N's implication active here would bind case N+1 inputs
                // under the wrong path.
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
                if (outputClosure != null
                        && outputClosure.outputPorts().size() > 1
                        && !casePorts.equals(outputClosure.outputPorts())) {
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
                String caseIdentity = RecordedSessionModel.caseOwner(region,
                        invocation.instanceId, string(item, "caseId"), index);
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
                    assertNamed("case_selector_definition_" + region + "_"
                                    + index,
                            "(= " + selector + " " + guard + ")");
                    currentGuard = selector;
                    recordFatalAbsenceRemovalEffects(invocation, item,
                            selector);
                    bindOutputExpressions(region, item, outputClosure);
                } finally {
                    currentGuard = previousGuard;
                    restoreSymbolScope(previousScope);
                }
            }
            currentGuard = previousGuard;
            if (selectors.size() == cases.size() && !selectors.isEmpty()) {
                StringBuilder partition = new StringBuilder("(= (+");
                for (String selector : selectors) {
                    partition.append(" (ite ").append(selector)
                            .append(" 1 0)");
                }
                assertNamed("region_case_selector_partition_" + region,
                        partition.append(") 1)").toString());
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
         * one exact runtime {@code Map.put} completion.
         *
         * <p>The selected output event is the join key between the imported
         * output closure and the static port's runtime-access ledger.  A
         * constraint is emitted only when that join selects exactly one
         * access in the same root invocation, the access carries the exact
         * associative-put provenance authority, and its recorded value object
         * id is non-zero.  Consequently no Java type, symbol spelling, or
         * application-specific name is used to infer nullness.</p>
         *
         * <p>That runtime event completes the outermost mutation represented
         * by the selected output expression.  Earlier {@code PUT}s on the
         * receiver spine are not constrained by this evidence.</p>
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
         * members that Java actually observed: {@code SNAPSHOT_BASE} followed
         * by {@code PUT}/{@code APPEND} (recordings taken before the base got
         * its own op name write {@code CLEAR} there).  A non-null member is
         * represented by a
         * VM reference symbol, while an observed null is the dedicated
         * {@code N} expression.  Preserve that distinction in the selected
         * path case; otherwise SMT may alias a concrete object identity with
         * {@code nullRef} and manufacture a missing map value.
         *
         * <p>This deliberately applies only to the snapshot suffix of a
         * captured output. Ordinary symbolic reference inputs, including
         * nullable map values, remain nullable.</p>
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

        private void merge(JsonObject context) {
            for (JsonElement element : array(context, "equalityClasses")) {
                if (!element.isJsonObject()) continue;
                JsonArray members = array(element.getAsJsonObject(), "members");
                List<String> selected = new ArrayList<>();
                for (JsonElement member : members) {
                    if (!member.isJsonPrimitive()) continue;
                    String endpoint = member.getAsString();
                    if (currentInvocation.regionId.equals(
                            regionOf(endpoint))) {
                        selected.add(endpoint);
                    }
                }
                if (selected.size() < 2) continue;
                String first = selected.get(0);
                for (int index = 1; index < selected.size(); index++) {
                    assertPortEquality(first, selected.get(index), "alias");
                }
            }
        }

        private void declareBoundedPosition(String position, int bound) {
            declare(position, Sort.INT);
            assertNamed(position + "_bounds", "(and (<= 0 " + position
                    + ") (< " + position + " " + bound + "))");
        }

        private void mergeEdgeBindings(Collection<ResolvedEdge> edges) {
            // Decide this from the whole selected set before lowering it.
            // Edge order is not evidence: a diagnostic candidate may sort
            // before the exact/guarded row that rules out a second binding of
            // the same consumer port.
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
                JsonObject binding = edge.binding;
                String region = bindingSourceRegion(binding);
                String targetRegion = string(binding, "toRegion");
                String output = bindingSourceOutput(binding);
                String input = bindingTargetInput(binding);
                PortOccurrence outputOccurrence = occurrence(
                        bindingSourceInstance(binding), output);
                PortOccurrence inputOccurrence = occurrence(
                        bindingTargetInstance(binding), input);
                String label = "edge_binding_" + region + "_to_"
                        + targetRegion + "_" + edgeIndex++;
                if (!ports.contains(output) || !ports.contains(input)) {
                    heapGap("EdgeBindingPortGap@" + region
                            + ":" + output + "->" + input);
                    continue;
                }
                if (skipExcludedWriter(binding)) continue;
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
                    continue;
                }
                if (emittedEdgeBindings.contains(
                        edgeBindingKey(binding))) {
                    validateIncomingEdgeInput(inputOccurrence, input);
                    continue;
                }
                // An exact read-from is an equality, not a choice: the VM
                // proved which write the read took, so a selector over one
                // arm would only restate it with a free Boolean in the way.
                if (bindRecordedExactWriter(binding, outputOccurrence,
                        inputOccurrence, label)) {
                    validateIncomingEdgeInput(inputOccurrence, input);
                    continue;
                }
                if ("EQUALITY".equals(bindingRelationKind(binding))) {
                    String equalityAssertion = assertPortEqualityNamed(
                            outputOccurrence,
                            inputOccurrence, label);
                    if (!equalityAssertion.isEmpty()) {
                        recordProducerVersionBinding(binding,
                                outputOccurrence, inputOccurrence,
                                equalityAssertion);
                        emitRecordedBindingOrder(binding, label,
                                equalityAssertion, false);
                        validateIncomingEdgeInput(inputOccurrence, input);
                        emittedEdgeBindings.add(edgeBindingKey(binding));
                        failureWitness.connect(binding, outputOccurrence,
                                inputOccurrence, "true",
                                portName(inputOccurrence));
                    } else {
                        heapGap("EdgeBindingEqualityGap@" + region
                                + ":" + output + "->" + input);
                    }
                    continue;
                }
                if (bindRecordedGuardedRead(binding, outputOccurrence,
                        inputOccurrence, label)) {
                    validateIncomingEdgeInput(inputOccurrence, input);
                    emittedEdgeBindings.add(edgeBindingKey(binding));
                } else {
                    heapGap("UnresolvedRecordedEdgeBinding:"
                            + string(binding, "edgeId"));
                }
            }
        }


        /** Lowers one selected region occurrence's guarded relation. */
        private void lowerRelation(RelationSummary selection) {
            regionSummary(selection);
        }

        /**
         * Lowers the case-local VM handoffs of the selected occurrences.
         *
         * <p>A successful attach means the receiver's location already
         * denotes the sender's expression, so no value equality is
         * manufactured here: what the formula needs is the ledger's own
         * {@code send < receive} order and one recorded authority for the
         * receiving port.  Both come from the {@code VALUE_HANDOFF} edge the
         * VM wrote, addressed by the exact export event the case references.
         * A reference the order domain does not hold is a named gap, never a
         * proposed order.</p>
         */
        private void mergeVmHandoffs(List<JsonObject> caseRows,
                                     List<JsonObject> producerCaseRows,
                                     BoundedLoopComposition model,
                                     RecordedSessionModel recorded) {
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
                    // Target handoffs are currently carried at query level.
                    // That is exact only for a single selected target path;
                    // multiple path selectors need path-local ownership.
                    if (array(owner, "paths").size() != 1) {
                        model.gap("HANDOFF_CASE_SCOPE_MISSING", occurrence,
                                "a target query with multiple paths carries"
                                        + " an unowned VM handoff");
                        continue;
                    }
                } else if (selector.isEmpty()
                        || !selector.equals(RecordedSessionModel.caseSelector(
                        caseOwner))) {
                    model.gap("HANDOFF_CASE_SCOPE_MISSING", caseOwner,
                            "a guarded VM handoff has no exact case selector");
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
                    JsonObject producerCase = exactHandoffProducerCase(
                            entry.getValue().get(0), producerCaseRows,
                            occurrence, entry.getKey(), model);
                    if (producerCase == null) continue;
                    emitVmHandoff(entry.getValue().get(0), occurrence,
                            caseOwner, selector, producerCase, model,
                            recorded);
                }
            }
        }

        /**
         * Resolves header provenance to one imported producer case that
         * actually observed the exact exported port.  VM event ids and equal
         * payloads are deliberately not match keys: both repeat across
         * independent replay sessions.
         */
        private JsonObject exactHandoffProducerCase(
                JsonObject event, List<JsonObject> producerCaseRows,
                String consumerOccurrence, String port,
                BoundedLoopComposition model) {
            String taskId = string(event,
                    VmHandoffEvidence.PRODUCER_TASK_ID);
            String occurrenceId = string(event,
                    VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
            List<JsonObject> matches = new ArrayList<>();
            for (JsonObject candidate : producerCaseRows == null
                    ? Collections.<JsonObject>emptyList()
                    : producerCaseRows) {
                if (!taskId.equals(string(candidate, "sourceTaskId"))
                        || !occurrenceId.equals(string(candidate,
                        "toOccurrenceId"))) {
                    continue;
                }
                int observed = 0;
                for (JsonElement raw : array(candidate,
                        RelationSummary.INTERACTION_EVENTS)) {
                    if (raw.isJsonObject() && port.equals(
                            string(raw.getAsJsonObject(), "portId"))) {
                        observed++;
                    }
                }
                if (observed == 1) matches.add(candidate);
            }
            String subject = consumerOccurrence + ":" + port + ":"
                    + taskId;
            if (matches.isEmpty()) {
                unsupported.add(HANDOFF_PRODUCER_CASE_MISSING + ":"
                        + subject);
                model.gap(HANDOFF_PRODUCER_CASE_MISSING, subject,
                        "the RPC header names no imported producer case "
                                + "that observed this exact output port");
                return null;
            }
            if (matches.size() != 1) {
                unsupported.add(HANDOFF_PRODUCER_CASE_AMBIGUOUS + ":"
                        + subject);
                model.gap(HANDOFF_PRODUCER_CASE_AMBIGUOUS, subject,
                        "the RPC header names more than one imported "
                                + "producer case for this output port");
                return null;
            }
            return matches.get(0);
        }

        private void emitVmHandoff(JsonObject event, String occurrenceId,
                                   String caseOwner, String caseSelector,
                                   JsonObject producerCase,
                                   BoundedLoopComposition model,
                                   RecordedSessionModel recorded) {
            long exportEvent = longInteger(event, "exportEventId", 0L);
            String consumerPort = string(event, "portId");
            JsonObject evidence = event.deepCopy();
            // The receiving occurrence is the case's, not the event's: a VM
            // handoff reference states which export it attached, and the case
            // it is local to states where that attach happened.
            evidence.addProperty("toOccurrenceId", occurrenceId);
            evidence.addProperty("kind", VmHandoffEvidence.BINDING_KIND);
            if (!caseOwner.isEmpty()) {
                evidence.addProperty(RecordedSessionModel.CASE_OWNER,
                        caseOwner);
                evidence.addProperty(RecordedSessionModel.CASE_SELECTOR,
                        caseSelector);
            }
            String order = recorded == null ? ""
                    : recorded.handoffOrderAssertion(exportEvent,
                    caseSelector);
            if (order.isEmpty() && model != null) {
                model.gap(HANDOFF_ORDER_UNRECORDED,
                        String.valueOf(exportEvent),
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

            JsonObject producerGuardIr = object(producerCase, "guard");
            String producerRegion = string(producerCase, CASE_REGION_ID);
            String producerOccurrence = string(event,
                    VmHandoffEvidence.PRODUCER_OCCURRENCE_ID);
            String producerCaseOwner = string(producerCase,
                    RecordedSessionModel.CASE_OWNER);
            if (!"PATH_CONDITION".equals(string(producerGuardIr, "kind"))
                    || producerRegion.isEmpty()
                    || producerOccurrence.isEmpty()
                    || producerCaseOwner.isEmpty()) {
                unsupported.add(HANDOFF_PRODUCER_GUARD_MALFORMED + ":"
                        + producerOccurrence + ":" + consumerPort);
                model.gap(HANDOFF_PRODUCER_GUARD_MALFORMED,
                        producerOccurrence + ":" + consumerPort,
                        "the exact producer case has no bounded Java path "
                                + "guard or case scope");
                return;
            }

            // The receiver now holds the producer's Expression*. Lower its
            // raw locals and the Java path that selected it in the exact
            // producer case scope. The path guard is asserted outright: an
            // implication alone would leave the receiving port unconstrained
            // whenever the producer took a different Java path.
            InvocationKey priorProducerInvocation = enterInvocation(
                    new InvocationKey(producerRegion,
                            producerOccurrence));
            String priorProducerScope = enterSymbolScope(producerCaseOwner);
            String priorProducerGuard = currentGuard;
            Term attached;
            String producerGuardAssertion;
            try {
                currentGuard = "";
                List<String> conditions = new ArrayList<>();
                for (JsonElement condition : array(producerGuardIr,
                        "conditions")) {
                    conditions.add(constraint(condition,
                            "VM handoff producer " + string(event,
                                    VmHandoffEvidence.PRODUCER_TASK_ID)));
                }
                producerGuardAssertion = assertNamed(
                        "vm_handoff_producer_guard_"
                                + sha256(string(event,
                                VmHandoffEvidence.PRODUCER_TASK_ID) + "\n"
                                + producerOccurrence + "\n" + consumerPort)
                                .substring(0, 16), and(conditions));
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
            evidence.addProperty("producerCaseOwner", producerCaseOwner);
            evidence.addProperty("producerGuardAssertion",
                    producerGuardAssertion);
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
                validateIncomingEdgeInput(consumer, consumerPort);
                evidence.addProperty("valueAssertion", valueAssertion);
                recordValueBinding(evidence,
                        VmHandoffEvidence.BINDING_KIND + "\n" + exportEvent
                                + "\n" + consumerPort, "VMH.");
            } finally {
                currentGuard = previousGuard;
                restoreSymbolScope(previousScope);
                restoreInvocation(previousInvocation);
            }
        }

        /**
         * Files one lowered value binding in the ledger both artifacts
         * project.
         *
         * <p>Only an equality that reached the formula is filed. The ledger
         * is "one row per lowered SMT value binding" and the parity audit
         * reads it as exactly that, so a row with no assertion would make the
         * drawing claim a constraint the query does not contain. The equality
         * itself is not lost: it stays in the composition member beside the
         * named gap that says why nothing was lowered.</p>
         */
        private void recordValueBinding(JsonObject evidence,
                                        String bindingKey, String prefix) {
            if (string(evidence, "valueAssertion").isEmpty()) return;
            evidence.addProperty("bindingKey", bindingKey);
            evidence.addProperty("edgeId", prefix
                    + sha256(bindingKey).substring(0, 16));
            recordedValueBindings.add(evidence);
        }

        private void validateIncomingEdgeInput(PortOccurrence occurrence,
                                               String input) {
            Sort incomingSort = ports.get(input) == null ? null
                    : sortOfJava(ports.get(input).javaType);
            Sort previous = validatedIncomingEdgeInputSorts.get(occurrence);
            if (incomingSort != null
                    && (previous == null || previous == incomingSort)) {
                validatedIncomingEdgeInputSorts.put(occurrence,
                        incomingSort);
            } else if (incomingSort != null) {
                validatedIncomingEdgeInputSorts.remove(occurrence);
                unsupported.add("IncomingEdgeInputSortConflict:"
                        + input + ":" + previous + "!=" + incomingSort);
            }
        }

        /**
         * States one exact binding's recorded order in the one order domain.
         *
         * <p>An RPC exchange used to get three fresh integers of its own -
         * caller, send, receive - in a domain nothing else shared, and two
         * assertions relating them. Three unconstrained integers admit every
         * assignment, so those assertions ruled nothing out; what they did do
         * was suggest an order model where there was none. They are gone. The
         * order of a recorded handoff is the ledger's own
         * {@code HANDOFF_EXPORT} / {@code HANDOFF_ATTACH} events, which reach
         * the formula through the same {@code event_position__} family as
         * every field event, and the delivery this binding rests on is
         * reported as evidence rather than as a position.</p>
         *
         * <p>An exact field read-from does have both of its events in that
         * family, so it is ordered there: {@code write < read}, proposed
         * through the recorded domain first so a proposal that would close a
         * cycle is refused before the solve rather than asserted into it.</p>
         */
        private void emitRecordedBindingOrder(JsonObject binding,
                                              String label,
                                              String equalityAssertion,
                                              boolean recordedExact) {
            JsonObject evidence = new JsonObject();
            evidence.addProperty("kind", "RECORDED_EXACT_VALUE_BINDING");
            evidence.addProperty("edgeId", string(binding, "edgeId"));
            evidence.addProperty("valueAssertion", equalityAssertion);
            evidence.addProperty("fromOccurrenceId",
                    string(binding, "fromOccurrenceId"));
            evidence.addProperty("toOccurrenceId",
                    string(binding, "toOccurrenceId"));
            evidence.addProperty("fromOutputPort",
                    string(binding, "fromOutputPort"));
            evidence.addProperty("toInputPort",
                    string(binding, "toInputPort"));
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
            if (recordedExact && recorded != null && version > 0L
                    && read > 0L) {
                evidence.addProperty("orderAssertion",
                        emitRecordedOrder(version, read, label));
            }
            recordedValueBindings.add(evidence);
        }

        /**
         * Asserts {@code before < after} in the shared position domain, after
         * offering it to the recorded relation. A refusal is named and never
         * asserted: a proposal the recorded order contradicts is a cycle
         * across channels, and this composition must not solve over one.
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
                    "(< " + RecordedSessionModel.positionName(before) + " "
                            + RecordedSessionModel.positionName(after) + ")");
        }

        /**
         * Whether the recorded evidence ruled this candidate writer out.
         *
         * <p>An excluded candidate stays on the edge - it is the trace's own
         * observation - and it is reported here, but it never becomes a
         * writer the formula may choose: this run's session named a different
         * write for that read, and admitting the ruled-out one anyway would
         * put a value in the model the run showed did not flow.</p>
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
         *
         * <p>{@code F_in = writerExpr} plus the recorded order, and no
         * selector: the session already answered which write the read took,
         * so a one-armed choice would only add a free Boolean between the two
         * sides of a proven equality.</p>
         *
         * @return whether this binding was an exact one and was bound
         */
        private boolean bindRecordedExactWriter(JsonObject binding,
                                                PortOccurrence source,
                                                PortOccurrence target,
                                                String label) {
            if (!RecordedReadFrom.PROVENANCE_EXACT.equals(string(binding,
                    RecordedReadFrom.EDGE_PROVENANCE))) {
                return false;
            }
            String equality = assertPortEqualityNamed(source, target, label);
            if (equality.isEmpty()) {
                heapGap("RecordedExactReadFromGap@" + target);
                return false;
            }
            recordProducerVersionBinding(binding, source, target, equality);
            emitRecordedBindingOrder(binding, label, equality, true);
            emittedEdgeBindings.add(edgeBindingKey(binding));
            mentionPort(target);
            boundPorts.add(target);
            recordInputAuthority(target, READ_FROM_ARM,
                    string(binding, "edgeId"));
            if (ports.isInput(target.portId)) markSuppliedInput(target);
            failureWitness.connect(binding, source, target, "true",
                    portName(target));
            return true;
        }

        /**
         * Hands one consumer port the value the read-from selectors choose.
         *
         * <p>A guarded field binding names a location and a consuming
         * activation; the recorded session names the read that activation
         * performed of that location, and that read's arms are already
         * lowered over the one selector family. Binding the port to the
         * read's own value term is what keeps them one family: a second
         * writer choice over the same read, with its own Booleans, could
         * select one writer's value while the cut selected another's.</p>
         *
         * @return whether the port was bound
         */
        private boolean bindRecordedGuardedRead(JsonObject binding,
                                                PortOccurrence producer,
                                                PortOccurrence consumer,
                                                String label) {
            if (recorded == null || !RecordedReadFrom.PROVENANCE_GUARDED
                    .equals(string(binding,
                            RecordedReadFrom.EDGE_PROVENANCE))) {
                return false;
            }
            long read = recorded.readEventOf(string(binding, "locationKey"),
                    RecordedEvidenceIdentity.siteKey(string(binding,
                            "toOccurrenceId")));
            Term value = read > 0L ? guardedReadTerms.get(read) : null;
            if (value != null) noteReadCase(read);
            if (value == null) {
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
            // One consumer port is one read.  The context relation and the
            // resolved edge are two views of that one binding, so the second
            // of them must not restate it.
            if (!recordedReadBoundPorts.add(consumer)) {
                emittedEdgeBindings.add(edgeBindingKey(binding));
                recordedCoverage.add(CoverageDivergence.of(
                        CoverageDivergence.Kind.FLOW,
                        "RECORDED_GUARDED_READ_ALREADY_BOUND",
                        string(binding, "edgeId"),
                        "consumer port " + consumer + " already holds a"
                                + " recorded guarded read's value; this edge"
                                + " adds no second one"));
                return true;
            }
            Sort portSort = portSort(consumer);
            if (portSort == Sort.MAP && value.sort != Sort.MAP) {
                return bindRecordedGuardedState(binding, producer, consumer,
                        read, label);
            }
            Term bound = portSort == Sort.VALUE
                    ? asValue(value, ports.get(consumer.portId) == null ? ""
                    : ports.get(consumer.portId).javaType) : value;
            if (bound.sort != portSort) {
                unsupported.add("RecordedReadPortSortConflict:" + consumer
                        + ":" + portSort + "!=" + bound.sort);
                return false;
            }
            declarePort(consumer, portSort);
            mentionPort(consumer);
            String assertion = assertNamed(label + "_recorded_read",
                    and(Arrays.asList(bound.precondition, "(= "
                            + portName(consumer) + " " + bound.text + ")")));
            boundPorts.add(consumer);
            recordInputAuthority(consumer, READ_FROM_ARM,
                    string(binding, "edgeId"));
            if (ports.isInput(consumer.portId)) markSuppliedInput(consumer);
            JsonObject evidence = new JsonObject();
            evidence.addProperty("kind", "RECORDED_GUARDED_READ_PORT_BINDING");
            evidence.addProperty("edgeId", string(binding, "edgeId"));
            evidence.addProperty("locationKey",
                    string(binding, "locationKey"));
            evidence.addProperty(RecordedReadFrom.EDGE_FIELD,
                    string(binding, RecordedReadFrom.EDGE_FIELD));
            evidence.addProperty("toOccurrenceId",
                    string(binding, "toOccurrenceId"));
            evidence.addProperty("toInputPort", consumer.portId);
            evidence.addProperty("readEventId", read);
            evidence.addProperty("valueTerm", value.text);
            evidence.addProperty("valueAssertion", assertion);
            evidence.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                    string(binding, RecordedReadFrom.EDGE_UNKNOWN_ARM));
            recordedValueBindings.add(evidence);
            emittedEdgeBindings.add(edgeBindingKey(binding));
            return true;
        }

        /**
         * Binds a container-state edge to the VM versions selected by its
         * guarded read.  The read expression itself is a leaf value; the edge
         * carries the state on which that read operates.  Candidate versions
         * are admitted only when their exact writer occurrence is this
         * edge's producer, and INITIAL is not a mutation produced by the
         * edge.
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
            for (JsonElement element : array(guarded, "candidates")) {
                if (!element.isJsonObject()) continue;
                JsonObject candidate = element.getAsJsonObject();
                if (bool(candidate, "unknown", false)) continue;
                JsonObject version = recorded.writerVersion(longInteger(
                        candidate, "fieldVersionId", 0L));
                if (version.size() == 0
                        || "INITIAL".equals(string(version, "versionKind"))
                        || !producer.equals(
                        SharedStateEvidence.writerSite(version))) {
                    continue;
                }
                String selector = RecordedSessionModel.selectorName(
                        readEventId, string(candidate, "selector"));
                selectors.add(selector);
            }
            if (selectors.isEmpty()) {
                unsupported.add("RecordedWriterOccurrenceHasNoStateArm:"
                        + string(binding, "edgeId") + ":" + producer);
                return false;
            }
            String stateBinding = assertPortEqualityNamed(producerPort,
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

        private void recordProducerVersionBinding(
                JsonObject binding, PortOccurrence source,
                PortOccurrence target, String assertionName) {
            String edgeId = string(binding, "edgeId");
            if (edgeId.isEmpty() || assertionName.isEmpty()) return;
            Term producer = producerSolverTerm(source);
            producerVersionBindings.add(new ProducerVersionBinding(
                    edgeId, target, producer.text,
                    producer.sort, assertionName));
        }

        /**
         * Projects a schema-level {@code Value} carrier back to the native
         * solver sort used by an exact fatal operand.  The edge assertion
         * equates the complete carriers, so applying the matching datatype
         * selector preserves that exact producer lineage without comparing
         * unrelated values of the same sort.
         */
        private Term producerSolverTerm(PortOccurrence source) {
            String carrier = portName(source);
            Sort carrierSort = portSort(source);
            Port schema = ports.get(source.portId);
            String javaType = schema == null ? "" : schema.javaType;
            Sort nativeSort = sortOfJava(javaType);
            if (carrierSort != Sort.VALUE || nativeSort == Sort.VALUE) {
                return new Term(carrier, carrierSort);
            }
            if (nativeSort == Sort.INT) {
                String integral = ContainerSmtCodec.unboxIntegral(
                        carrier, javaType);
                if (!integral.isEmpty()) {
                    return new Term(integral, Sort.INT,
                            integralWidthOfJava(javaType));
                }
            }
            if (nativeSort == Sort.BOOL) {
                return new Term("(valueBool " + carrier + ")", Sort.BOOL);
            }
            if (nativeSort == Sort.FLOAT32) {
                return new Term("(valueFloat " + carrier + ")",
                        Sort.FLOAT32);
            }
            if (nativeSort == Sort.FLOAT64) {
                return new Term("(valueDouble " + carrier + ")",
                        Sort.FLOAT64);
            }
            if (nativeSort == Sort.STRING) {
                return new Term("(valueString " + carrier + ")",
                        Sort.STRING);
            }
            if (nativeSort == Sort.REF) {
                return new Term("(valueRef " + carrier + ")", Sort.REF);
            }
            return new Term(carrier, carrierSort);
        }

        private static final class FatalOperand {
            private final String operandId;
            private final int pathOrdinal;
            private final String solverTerm;
            private final Sort solverSort;
            private final String pinTerm;
            private final Sort pinSort;
            private final PortOccurrence occurrence;

            private FatalOperand(String operandId, int pathOrdinal,
                                 String solverTerm, Sort solverSort,
                                 String pinTerm, Sort pinSort,
                                 PortOccurrence occurrence) {
                this.operandId = operandId;
                this.pathOrdinal = pathOrdinal;
                this.solverTerm = solverTerm;
                this.solverSort = solverSort;
                this.pinTerm = pinTerm;
                this.pinSort = pinSort;
                this.occurrence = occurrence;
            }
        }

        private static final class FatalPrefixEquality {
            private final String leftTerm;
            private final Sort leftSort;
            private final PortOccurrence leftOccurrence;
            private final String rightTerm;
            private final Sort rightSort;
            private final PortOccurrence rightOccurrence;

            private FatalPrefixEquality(
                    String leftTerm, Sort leftSort,
                    PortOccurrence leftOccurrence,
                    String rightTerm, Sort rightSort,
                    PortOccurrence rightOccurrence) {
                this.leftTerm = leftTerm;
                this.leftSort = leftSort;
                this.leftOccurrence = leftOccurrence;
                this.rightTerm = rightTerm;
                this.rightSort = rightSort;
                this.rightOccurrence = rightOccurrence;
            }
        }

        private static final class ProducerVersionBinding {
            private final String edgeId;
            private final PortOccurrence target;
            private final String solverTerm;
            private final Sort solverSort;
            private final String assertionName;

            private ProducerVersionBinding(
                    String edgeId, PortOccurrence target,
                    String solverTerm, Sort solverSort,
                    String assertionName) {
                this.edgeId = edgeId;
                this.target = target;
                this.solverTerm = solverTerm;
                this.solverSort = solverSort;
                this.assertionName = assertionName;
            }

            private JsonObject toJson() {
                JsonObject result = new JsonObject();
                result.addProperty("edgeId", edgeId);
                result.addProperty("solverTerm", solverTerm);
                result.addProperty("solverSort", solverSort.smt);
                result.addProperty("assertionName", assertionName);
                result.addProperty("targetPortId", target.portId);
                result.addProperty("targetOccurrenceId",
                        target.invocation.instanceId);
                return result;
            }
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
            // README SMT-1 is case-local: a selected input may legitimately
            // have different authorities in mutually-exclusive cases, but at
            // every use exactly one of those authority facts must be active.
            // The assertion belongs outside the case being checked; putting it
            // under currentGuard here would silently authorize only whichever
            // case happened to be lowered last.
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

        /**
         * One row per selected input port occurrence and the authority that
         * constrained it, in the deterministic order the ports were named.
         */
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
            for (Map.Entry<PortOccurrence, Set<String>> entry
                    : inputUseGuards.entrySet()) {
                ports++;
                uses += entry.getValue().size();
                List<String> guards = authorityGuards(
                        authoritiesOf(entry.getKey()));
                facts += guards.size();
                if (guards.isEmpty()) missing++;
                else if (authorityCasesDefinitelyAmbiguous(guards)) ambiguous++;
            }
            JsonObject audit = new JsonObject();
            audit.addProperty("schemaVersion", 3);
            audit.addProperty("kind", "SELECTED_INPUT_LEDGER_AUDIT");
            audit.addProperty("authority", "SELECTED_INPUT_LEDGER_V3");
            audit.addProperty("inputOccurrencesChecked", ports);
            audit.addProperty("inputUsesChecked", uses);
            audit.addProperty("authorityEvidenceChecked", facts);
            audit.addProperty("missingOccurrences", missing);
            audit.addProperty("ambiguousOccurrences", ambiguous);
            return audit;
        }

        private boolean assertPortEquality(String left, String right,
                                           String label) {
            return assertPortEquality(currentOccurrence(left),
                    currentOccurrence(right), label);
        }

        private boolean assertPortEquality(PortOccurrence left,
                                           PortOccurrence right,
                                           String label) {
            return !assertPortEqualityNamed(left, right, label).isEmpty();
        }

        private String assertPortEqualityNamed(PortOccurrence left,
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
            mentionPort(left);
            mentionPort(right);
            return true;
        }

        /**
         * Sharpens a port still carrying the neutral {@code Value} sort to
         * the container sort its counterpart already proved.
         *
         * <p>{@link #promotePort} already treats {@code Value} as an
         * unrefined carrier a container-valued binding may sharpen, so a
         * producer whose bound expression is a container reaches an equality
         * with a consumer port nothing has refined yet.  That is the same
         * refinement, applied from the other side of the edge.</p>
         *
         * <p>Both ports must name the same declared Java type before the
         * neutral one is sharpened, and a port already declared to the solver
         * keeps the sort it was declared with.  An unknown or differing
         * declaration decides nothing and keeps the sort-mismatch gap.</p>
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
         * Names the one authority that constrained a selected input port.
         *
         * <p>Recorded at the binding site rather than reconstructed later:
         * only the site knows whether the value arrived from this
         * occurrence's own relation, a VM communication leaf, or a read-from
         * selector, and a name-shaped guess at the end would be exactly the
         * provenance the README forbids.</p>
         */
        private void recordInputAuthority(PortOccurrence occurrence,
                                          String authority, String evidence) {
            // Filed for whatever the value arrived at.  Requiring the catalog
            // to declare that port an input first would drop the authority of
            // exactly the arrivals the catalog does not describe, and the
            // ledger below would then read them as inputs nothing constrained.
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
         *
         * <p>A port no edge bound is admitted only when the plan declared it
         * a value frontier: that is where the backward slice legitimately
         * stops, so the port is an external workload input rather than a
         * value the composition failed to connect.  A structure carrier that
         * reaches SMT unbound is the second case, and it stays unnamed here
         * so the caller refuses it.</p>
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
            // an exact read-from or VM handoff has constrained this concrete
            // port occurrence.
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

        private void recordSuppliedInput(String left, String right) {
            recordSuppliedInput(currentOccurrence(left),
                    currentOccurrence(right));
        }

        private Term asValue(Term term) {
            return asValue(term, "");
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
            asserted = CaseLocalLetCse.compress(asserted);
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
         * recorded by the caller, this closed value only keeps the diagnostic
         * SMT well-sorted, and {@link #finish()} makes every gapped query
         * non-executable.
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
                    // such as REGION.X.in.2 inside REGION.X.in.25 or a derived
                    // field name such as REGION.X.in.2.selectedField.
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
            fatalDependentAssertionNames.add(assertNamed(
                    "fatal_absence_mutation_witness",
                    or(failureWitness.clauses)));
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

    /**
     * Shares one repeated, closed SMT term inside one named assertion.
     *
     * <p>The VM expression format is a tree, even when hundreds of reads use
     * the same bounded container snapshot. Lowering that tree literally
     * repeats the snapshot in every read. A local SMT {@code let} restores
     * that lost DAG without adding a solver variable or moving a constraint
     * across an assertion or case boundary.</p>
     *
     * <p>This is deliberately bounded: one binding, terms of at least one
     * KiB, and a finite parser budget. A candidate that mentions an
     * identifier bound by an enclosing {@code let}, quantifier, or lambda is
     * not hoisted. Binder declaration lists are never terms. Any malformed
     * input is returned byte-for-byte.</p>
     */
    private static final class CaseLocalLetCse {
        private static final int MIN_TERM_LENGTH = 1024;
        private static final int MAX_NODES = 250_000;
        private static final int MAX_ATOMS = 500_000;
        private static final String NAME_PREFIX = "gc_case_cse__";

        private CaseLocalLetCse() {
        }

        private static String compress(String expression) {
            if (expression == null
                    || expression.length() < 2 * MIN_TERM_LENGTH) {
                return expression;
            }
            ParsedSmt parsed = ParsedSmt.parse(expression);
            if (parsed == null) return expression;

            Map<SpanKey, Repetitions> groups = new LinkedHashMap<>();
            for (SmtNode node : parsed.nodes) {
                if (node.end - node.start < MIN_TERM_LENGTH
                        || node.head.isEmpty()
                        || parsed.inBinderDeclarations(node)
                        || parsed.referencesAncestorBinding(node)) {
                    continue;
                }
                SpanKey key = parsed.span(node);
                Repetitions group = groups.get(key);
                if (group == null) {
                    group = new Repetitions(key);
                    groups.put(key, group);
                }
                group.occurrences.add(node);
            }

            Repetitions best = null;
            long bestSaving = 0L;
            for (Repetitions group : groups.values()) {
                if (group.occurrences.size() < 2) continue;
                long saving = group.estimatedSaving();
                if (saving > bestSaving
                        || saving == bestSaving && best != null
                        && group.key.length() > best.key.length()
                        || saving == bestSaving && best != null
                        && group.key.length() == best.key.length()
                        && group.key.start < best.key.start) {
                    best = group;
                    bestSaving = saving;
                }
            }
            if (best == null || bestSaving <= 0L) return expression;

            String term = expression.substring(best.key.start,
                    best.key.end);
            String stem = NAME_PREFIX + sha256(term).substring(0, 16);
            String name = parsed.freshAtom(stem);
            List<SmtNode> occurrences = new ArrayList<>(best.occurrences);
            Collections.sort(occurrences,
                    Comparator.comparingInt(node -> node.start));
            StringBuilder body = new StringBuilder(
                    expression.length() - occurrences.size()
                            * (term.length() - name.length()));
            int cursor = 0;
            for (SmtNode occurrence : occurrences) {
                if (occurrence.start < cursor) {
                    // Equal-length exact spans cannot overlap. Keep the
                    // fail-safe local in case a future parser admits one.
                    return expression;
                }
                body.append(expression, cursor, occurrence.start)
                        .append(name);
                cursor = occurrence.end;
            }
            body.append(expression, cursor, expression.length());
            String compressed = "(let ((" + name + " " + term + ")) "
                    + body + ")";
            return compressed.length() < expression.length()
                    ? compressed : expression;
        }

        private static final class Repetitions {
            private final SpanKey key;
            private final List<SmtNode> occurrences = new ArrayList<>();

            private Repetitions(SpanKey key) {
                this.key = key;
            }

            private long estimatedSaving() {
                int count = occurrences.size();
                // The deterministic name is 30 characters before a rare
                // collision suffix. This estimate only ranks candidates;
                // the exact final length is checked before returning it.
                return (long) (count - 1) * key.length()
                        - (long) count * 32L - 64L;
            }
        }

        private static final class SpanKey {
            private final String source;
            private final int start;
            private final int end;
            private final int hash;

            private SpanKey(String source, int start, int end, int hash) {
                this.source = source;
                this.start = start;
                this.end = end;
                this.hash = hash;
            }

            private int length() {
                return end - start;
            }

            @Override
            public int hashCode() {
                return 31 * hash + length();
            }

            @Override
            public boolean equals(Object other) {
                if (this == other) return true;
                if (!(other instanceof SpanKey)) return false;
                SpanKey value = (SpanKey) other;
                return length() == value.length()
                        && hash == value.hash
                        && source.regionMatches(start, value.source,
                        value.start, length());
            }
        }

        private static final class ParsedSmt {
            private final String source;
            private final List<SmtNode> nodes;
            private final List<SmtAtom> atoms;
            private final int[] prefixHashes;
            private final int[] powersOf31;

            private ParsedSmt(String source, List<SmtNode> nodes,
                              List<SmtAtom> atoms) {
                this.source = source;
                this.nodes = nodes;
                this.atoms = atoms;
                this.prefixHashes = new int[source.length() + 1];
                this.powersOf31 = new int[source.length() + 1];
                powersOf31[0] = 1;
                for (int index = 0; index < source.length(); index++) {
                    prefixHashes[index + 1] = 31 * prefixHashes[index]
                            + source.charAt(index);
                    powersOf31[index + 1] = 31 * powersOf31[index];
                }
            }

            private SpanKey span(SmtNode node) {
                int length = node.end - node.start;
                int hash = prefixHashes[node.end]
                        - prefixHashes[node.start] * powersOf31[length];
                return new SpanKey(source, node.start, node.end, hash);
            }

            private static ParsedSmt parse(String source) {
                List<SmtNode> nodes = new ArrayList<>();
                List<SmtAtom> atoms = new ArrayList<>();
                Deque<Integer> open = new ArrayDeque<>();
                int roots = 0;
                for (int index = 0; index < source.length();) {
                    char current = source.charAt(index);
                    if (Character.isWhitespace(current)) {
                        index++;
                        continue;
                    }
                    if (current == ';') {
                        // assertNamed emits no comments. Refuse rather than
                        // guess whether a parenthesis is commented out.
                        return null;
                    }
                    if (current == '(') {
                        int parent = open.isEmpty() ? -1 : open.peek();
                        if (parent < 0) roots++;
                        if (nodes.size() >= MAX_NODES || roots > 1) {
                            return null;
                        }
                        SmtNode node = new SmtNode(nodes.size(), parent,
                                index, atoms.size());
                        nodes.add(node);
                        if (parent >= 0) {
                            SmtNode owner = nodes.get(parent);
                            owner.sawElement = true;
                            owner.children.add(node.id);
                        }
                        open.push(node.id);
                        index++;
                        continue;
                    }
                    if (current == ')') {
                        if (open.isEmpty()) return null;
                        SmtNode node = nodes.get(open.pop());
                        node.end = index + 1;
                        node.atomEnd = atoms.size();
                        index++;
                        continue;
                    }
                    if (open.isEmpty() || atoms.size() >= MAX_ATOMS) {
                        return null;
                    }
                    int end = atomEnd(source, index);
                    if (end <= index) return null;
                    SmtNode owner = nodes.get(open.peek());
                    if (!owner.sawElement) {
                        owner.head = source.substring(index, end);
                    }
                    owner.sawElement = true;
                    atoms.add(new SmtAtom(index, end));
                    index = end;
                }
                if (!open.isEmpty() || roots != 1 || nodes.isEmpty()) {
                    return null;
                }
                return new ParsedSmt(source, nodes, atoms);
            }

            private static int atomEnd(String source, int start) {
                char first = source.charAt(start);
                if (first == '"') {
                    int cursor = start + 1;
                    while (cursor < source.length()) {
                        if (source.charAt(cursor) != '"') {
                            cursor++;
                            continue;
                        }
                        if (cursor + 1 < source.length()
                                && source.charAt(cursor + 1) == '"') {
                            cursor += 2;
                            continue;
                        }
                        return cursor + 1;
                    }
                    return -1;
                }
                if (first == '|') {
                    int cursor = start + 1;
                    while (cursor < source.length()) {
                        char current = source.charAt(cursor);
                        if (current == '\\') {
                            cursor += 2;
                        } else if (current == '|') {
                            return cursor + 1;
                        } else {
                            cursor++;
                        }
                    }
                    return -1;
                }
                int cursor = start;
                while (cursor < source.length()) {
                    char current = source.charAt(cursor);
                    if (Character.isWhitespace(current)
                            || current == '(' || current == ')') {
                        break;
                    }
                    cursor++;
                }
                return cursor;
            }

            private boolean inBinderDeclarations(SmtNode candidate) {
                int cursor = candidate.id;
                while (cursor >= 0) {
                    SmtNode node = nodes.get(cursor);
                    int parent = node.parent;
                    if (parent >= 0) {
                        SmtNode owner = nodes.get(parent);
                        if (binder(owner)
                                && !owner.children.isEmpty()
                                && owner.children.get(0) == cursor) {
                            return true;
                        }
                    }
                    cursor = parent;
                }
                return false;
            }

            private boolean referencesAncestorBinding(SmtNode candidate) {
                Set<String> bound = new LinkedHashSet<>();
                int cursor = candidate.parent;
                while (cursor >= 0) {
                    SmtNode ancestor = nodes.get(cursor);
                    if (binder(ancestor) && !ancestor.children.isEmpty()) {
                        SmtNode declarations = nodes.get(
                                ancestor.children.get(0));
                        for (Integer declarationId
                                : declarations.children) {
                            String identifier = nodes.get(
                                    declarationId).head;
                            if (!identifier.isEmpty()) bound.add(identifier);
                        }
                    }
                    cursor = ancestor.parent;
                }
                if (bound.isEmpty()) return false;
                for (int index = candidate.atomStart;
                     index < candidate.atomEnd; index++) {
                    SmtAtom atom = atoms.get(index);
                    for (String identifier : bound) {
                        if (atom.end - atom.start == identifier.length()
                                && source.regionMatches(atom.start,
                                identifier, 0, identifier.length())) {
                            return true;
                        }
                    }
                }
                return false;
            }

            private String freshAtom(String stem) {
                String value = stem;
                int suffix = 2;
                while (containsAtom(value)) {
                    value = stem + "_" + suffix++;
                }
                return value;
            }

            private boolean containsAtom(String value) {
                for (SmtAtom atom : atoms) {
                    if (atom.end - atom.start == value.length()
                            && source.regionMatches(atom.start, value,
                            0, value.length())) {
                        return true;
                    }
                }
                return false;
            }

            private static boolean binder(SmtNode node) {
                return "let".equals(node.head)
                        || "forall".equals(node.head)
                        || "exists".equals(node.head)
                        || "lambda".equals(node.head);
            }
        }

        private static final class SmtNode {
            private final int id;
            private final int parent;
            private final int start;
            private final int atomStart;
            private final List<Integer> children = new ArrayList<>();
            private int end;
            private int atomEnd;
            private String head = "";
            private boolean sawElement;

            private SmtNode(int id, int parent, int start, int atomStart) {
                this.id = id;
                this.parent = parent;
                this.start = start;
                this.atomStart = atomStart;
            }
        }

        private static final class SmtAtom {
            private final int start;
            private final int end;

            private SmtAtom(int start, int end) {
                this.start = start;
                this.end = end;
            }
        }
    }

    static String caseLocalLetCseForTests(String expression) {
        return CaseLocalLetCse.compress(expression);
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
         *
         * <p>Runtime activation ports record the field path they walked but
         * not always a materialized type, so the last declaration on that
         * path is the type Java itself gives the value.</p>
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
         * producer expression names the producer's ports, so lowering it in
         * the reader's invocation would mint a second, unconstrained
         * occurrence of them instead of the witness the producer binds.
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
     *
     * <p>A cell naming a parameter, a field, or a return value carries the
     * declaration Java itself made.  A cell naming a local carries none.</p>
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

    private static boolean isJavaParseInt(String name) {
        return "java/lang/Integer parseInt".equals(firstNonBlank(name));
    }

    private static boolean isJavaSplitElement(String name) {
        return "java/lang/String splitElement".equals(firstNonBlank(name));
    }

    private static String comparison(String operator) {
        if ("<".equals(operator) || ">".equals(operator)
                || "<=".equals(operator) || ">=".equals(operator)) {
            return operator;
        }
        return "";
    }

    private static String arithmetic(String operator) {
        if ("+".equals(operator) || "-".equals(operator)
                || "*".equals(operator)) return operator;
        return "";
    }

    private static boolean arithmeticOperator(String operator) {
        return "+".equals(operator) || "-".equals(operator)
                || "*".equals(operator) || "@".equals(operator)
                || "/".equals(operator) || "%".equals(operator);
    }

    private static boolean bitwiseOperator(String operator) {
        return "&".equals(operator) || "|".equals(operator)
                || "^".equals(operator);
    }

    private static boolean shiftOperator(String operator) {
        return "<<".equals(operator) || ">>".equals(operator)
                || ">>>".equals(operator);
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

    private static String constantPayload(String raw) {
        if (raw == null) return "0";
        int first = raw.indexOf('_');
        int second = first < 0 ? -1 : raw.indexOf('_', first + 1);
        return second < 0 ? raw : raw.substring(second + 1);
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

    private static String quote(String value) {
        String exact = value == null ? "" : value;
        return "\"" + exact.replace("\"", "\"\"") + "\"";
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
