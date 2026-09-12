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
    static final String CASE_MERGE_TYPE = "CaseMergeExpression";
    /** Prefix of the one value term of one guarded read. */
    static final String READ_VALUE_PREFIX = "rf_value__";
    private static final Pattern SMT_ATOM = Pattern.compile("[^()\\s]+");

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
    private static final String CASE_REGION_ID = "_caseRegionId";
    /** Whether this artifact may be accepted as the milestone result. */
    public static final String FINAL_STATUS = "finalStatus";
    /** Whether all selected producer and target path sets were explored. */
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
        emitter.finishGuardedReadSelections();
        emitter.finish();
        String composedSmt = emitter.render();

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
        manifest.add("caseSelectorPartitions",
                GSON.toJsonTree(emitter.casePartitions.values()));
        manifest.add(CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                emitter.configuredSourceMaterializationLedger());
        manifest.add(MANUAL_SOURCE_MATERIALIZATION_FIELD,
                emitter.manualSourceMaterializationLedger());
        manifest.add(BoundedLoopComposition.MANIFEST_FIELD,
                loops.manifest());
        manifest.add("guardedReadModel", emitter.guardedReadModel());
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
        return booleanNary(terms, true);
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

    private static final class Emitter implements VmTermLowering.Policy {
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
        /** Case/observation selector -> replay scope whose VM ids it owns. */
        private final Map<String, String> executionScopesByCase =
                new LinkedHashMap<>();
        /** One allocated container cannot have two unrelated state shapes. */
        private final Map<String, Sort> structuralStateSorts =
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
        private final Map<String, String> guardedOrderAssertions =
                new LinkedHashMap<>();
        private final Set<String> emittedGuardedReadArms =
                new LinkedHashSet<>();
        private boolean guardedReadComplete = true;
        /** One SMT definition per propagated guarded output. */
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

        private void registerSymbolicSources(List<JsonObject> owners) {
            locationProvenance = SharedStateEvidence.locationProvenance(
                    owners);
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
            assertNamed("fatal_path", pathTerm);
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
            return shareLargeTerm(lowerTerm(expression, expected));
        }

        /** Dispatch before the content-addressed SMT DAG boundary. */
        private Term lowerTerm(JsonElement expression, Sort expected) {
            if (expression == null || expression.isJsonNull()
                    || !expression.isJsonObject()) {
                unsupported.add("ABSENT_EXPRESSION");
                return unsupportedTerm(expected == null
                        ? Sort.REF : expected);
            }
            JsonObject object = expression.getAsJsonObject();
            String type = optionalString(object, "_type");
            if ("SymbolExpression".equals(type)) {
                return symbol(object, expected);
            }
            if (ContainerSmtCodec.constantKind(type)) {
                return constant(object, expected);
            }
            if ("BinaryExpression".equals(type)) return binary(object);
            if ("OpStrExpression".equals(type)) {
                return stringOperation(object);
            }
            if ("PlaceholderExpression".equals(type)) {
                String function = optionalString(object, "_place_holder_func");
                int count = optionalInteger(object, "_count", -1);
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
                String name = smtSymbols.mint(
                        scopedName("environment", identity) + "__",
                        scopedIdentity, 10);
                declare(name, Sort.INT);
                assertJavaIntegralDomain(name, Sort.INT, "J", identity);
                return Term.of(name, Sort.INT,
                        IntegralWidth.JAVA_LONG);
            }
            if ("TypeCastExpression".equals(type)) {
                return VmTermLowering.typeCast(this, object, "");
            }
            if (SharedStateEvidence.GUARDED_READ_TYPE.equals(type)) {
                return guardedReadTerm(object, expected);
            }
            if (CASE_MERGE_TYPE.equals(type)) {
                return caseMergeTerm(object, expected);
            }
            if (VmExpressionIr.CONSUMER_BOUNDARY_TYPE.equals(type)
                    || VmExpressionIr.CONSUMER_BOUNDARY_REFERENCE_TYPE
                    .equals(type)) {
                // Online path flipping and non-final SMT uses see an anchor
                // as the exact value already propagated by the VM. Final
                // composition normally replaces it with a case merge first.
                return term(object.get(VmExpressionIr.EXPRESSION), expected);
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

        private Term guardedReadTerm(JsonObject node, Sort expected) {
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
                                + firstNonBlank(readIdentity, "unnamed"),
                        fault.isEmpty()
                                ? "guarded read has no stable read/case identity"
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

            guardedReadActivations.computeIfAbsent(readIdentity,
                    ignored -> new LinkedHashSet<>()).add(activation);
            Set<String> selectors = guardedReadSelectors.computeIfAbsent(
                    readIdentity, ignored -> new LinkedHashSet<>());
            Map<String, Set<String>> selectorGuards =
                    guardedSelectorActivations.computeIfAbsent(readIdentity,
                            ignored -> new LinkedHashMap<>());
            Set<String> useSelectors = new LinkedHashSet<>();
            for (DirectReadArm arm : arms) {
                selectors.add(arm.selector);
                useSelectors.add(arm.selector);
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
        private List<String> mergeGuardedReadOrder(String read,
                                                   List<String> lowered) {
            List<List<String>> chains = guardedReadChains.getOrDefault(read,
                    Collections.emptyList());
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
                orderUnknown(read, "the merged chains do not cover every"
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
                        orderUnknown(read, forward
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

        private void orderUnknown(String readIdentity, String detail) {
            guardedReadOrders.remove(readIdentity);
            guardedReadOrderGaps.putIfAbsent(readIdentity, detail);
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
                emitGuardedReadOrder(read, selectors);
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
        private void emitGuardedReadOrder(String read,
                                          List<String> lowered) {
            if (guardedReadOrderGaps.containsKey(read)) return;
            List<String> chain = mergeGuardedReadOrder(read, lowered);
            if (chain == null) return;
            List<String> activity = new ArrayList<>(chain.size());
            for (String selector : chain) {
                String held = guardedReadArmActivity.get(read + "\n"
                        + selector);
                if (held == null) {
                    orderUnknown(read, "one candidate writer has no recorded"
                            + " activity condition");
                    return;
                }
                activity.add(held);
            }
            guardedReadOrders.put(read, chain);
            List<String> axioms = lastWriterWins(chain, activity);
            for (int index = 0; index < chain.size(); index++) {
                if (axioms.get(index).isEmpty()) continue;
                String key = read + "\n" + chain.get(index);
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
                JsonArray writerOrder = new JsonArray();
                for (String selector : guardedReadOrders.getOrDefault(identity,
                        Collections.emptyList())) {
                    JsonObject row = new JsonObject();
                    row.addProperty("selector", selector);
                    row.addProperty("orderAssertion",
                            guardedOrderAssertions.getOrDefault(
                                    identity + "\n" + selector, ""));
                    writerOrder.add(row);
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
            for (String identity : ungrouped) {
                JsonObject row = new JsonObject();
                row.addProperty("reason", GUARDED_READ_ORDER_UNKNOWN);
                row.addProperty("readIdentity", identity);
                row.addProperty("detail",
                        guardedReadOrderGaps.get(identity));
                orderGaps.add(row);
            }
            model.add("orderGaps", orderGaps);
            model.addProperty("orderedReads", guardedReadOrders.size());
            return model;
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
        private Term caseMergeTerm(JsonObject node, Sort expected) {
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
                String value = values.get(values.size() - 1).text;
                String nullness = sort == Sort.STRING
                        ? values.get(values.size() - 1).stringNullness : "";
                for (int index = values.size() - 2; index >= 0; index--) {
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

        private Term containerTerm(JsonObject expression) {
            return lowerContainerTerm(expression, false);
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
                    return new ContainerSmtCodec.Term(
                            (shape == ContainerSmtCodec.Sort.INDEXED
                                    ? "(indexed_state_of "
                                    : "(assoc_state_of ")
                                    + identityTerm.text + ")",
                            shape);
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
                public ContainerSmtCodec.Term share(
                        ContainerSmtCodec.Term value) {
                    return toContainerTerm(shareLargeTerm(
                            fromContainerTerm(value)));
                }

                @Override
                public ContainerSmtCodec.Term box(JsonElement expression) {
                    return toContainerTerm(asValue(term(expression, null),
                            VmTermLowering.expressionJavaType(expression)));
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
                        ? "manual__" + scopeToken(manualIdentity)
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
            if (held != null && !held.equals(row)) {
                unsupported.add("ConfiguredSourceMaterializationConflict:"
                        + optionalString(event, "sourceId"));
            }
        }

        private Term constant(JsonObject expression, Sort expected) {
            String raw = optionalString(expression, "_exp");
            String javaType = optionalString(expression, "_java_type");
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
                    result = Term.of("1".equals(value)
                            ? "true" : "false", Sort.BOOL);
                }
            } else if (expected == Sort.REF && ("0".equals(value)
                    || VmExpressionIr.SYMBOLIC_NULL.equals(raw))) {
                result = Term.of("nullRef", Sort.REF);
            } else if (sort.floating()) {
                String literal = JavaPrimitiveSmtSemantics.floatingLiteral(
                        value, floatingKind(sort));
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : Term.of(literal, sort);
            } else if (sort == Sort.INT) {
                String literal = SmtModelValueCodec.integerLiteral(value);
                result = literal == null
                        ? invalidNumericLiteral(raw, sort)
                        : Term.of(literal, Sort.INT,
                        JavaPrimitiveSmtSemantics.widthOfJavaType(javaType));
            } else if (sort == Sort.STRING) {
                result = Term.nonNullString(quote(value), "true");
            } else {
                String name = "const__" + smtName(raw);
                declare(name, sort == Sort.VALUE ? Sort.REF : sort);
                result = Term.of(name,
                        sort == Sort.VALUE ? Sort.REF : sort);
            }
            return result;
        }

        private Term invalidNumericLiteral(String raw, Sort sort) {
            unsupported.add("InvalidNumericLiteral:" + sort + ":"
                    + firstNonBlank(raw, "MISSING"));
            return unsupportedTerm(sort);
        }

        private Term binary(JsonObject expression) {
            String operator = JavaPrimitiveSmtSemantics.canonicalVmOperator(
                    optionalString(expression, "_op"));
            JsonElement leftExpression = expression.get("_left");
            if (leftExpression == null || leftExpression.isJsonNull()) {
                Term operand = term(expression.get("_right"), null);
                if ("-".equals(operator) && numeric(operand.sort)) {
                    if (operand.sort.floating()) {
                        return dependent(Term.of(JavaPrimitiveSmtSemantics
                                .floatingNegate(operand.text), operand.sort),
                                operand);
                    }
                    if (operand.integralWidth != IntegralWidth.NONE) {
                        return dependent(Term.of(JavaPrimitiveSmtSemantics.wrap("(- " + operand.text
                                + ")", operand.integralWidth), Sort.INT,
                                operand.integralWidth), operand);
                    }
                    unsupported.add("AmbiguousJavaIntegralUnaryWidth:"
                            + firstNonBlank(operator, "MISSING"));
                    return unsupportedTerm(Sort.INT);
                }
                if ("~".equals(operator) && operand.sort == Sort.INT
                        && operand.integralWidth != IntegralWidth.NONE) {
                    return dependent(Term.of(JavaPrimitiveSmtSemantics
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
                right = Term.of("nullRef", Sort.REF);
            } else if (left.sort != right.sort && left.isZero()
                    && right.sort == Sort.REF) {
                left = Term.of("nullRef", Sort.REF);
            }
            if ("--".equals(operator)) {
                if (left.sort == Sort.INT && right.sort == Sort.INT
                        && left.integralWidth == IntegralWidth.JAVA_LONG
                        && right.integralWidth == IntegralWidth.JAVA_LONG) {
                    return dependent(Term.of(JavaPrimitiveSmtSemantics
                            .integralCompareResult(left.text, right.text),
                            Sort.INT, IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmLcmpOperands:"
                        + left.sort + ":" + left.integralWidth + ":"
                        + right.sort + ":" + right.integralWidth);
                return Term.of("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if ("--l".equals(operator) || "--g".equals(operator)) {
                if (left.sort == right.sort && left.sort.floating()) {
                    return dependent(Term.of(JavaPrimitiveSmtSemantics
                            .floatingCompareResult(left.text, right.text,
                                    "--g".equals(operator)), Sort.INT,
                            IntegralWidth.JAVA_INT), left, right);
                }
                unsupported.add("MalformedJvmFloatingCompareOperands:"
                        + operator + ":" + left.sort + ":" + right.sort);
                return Term.of("0", Sort.INT,
                        IntegralWidth.JAVA_INT);
            }
            if (left.sort != right.sort && numeric(left.sort)
                    && numeric(right.sort)
                    && (left.sort.floating() || right.sort.floating())) {
                Sort promoted = left.sort == Sort.FLOAT64
                        || right.sort == Sort.FLOAT64
                        ? Sort.FLOAT64 : Sort.FLOAT32;
                left = VmTermLowering.floatingPromotion(this, left,
                        promoted, "left");
                right = VmTermLowering.floatingPromotion(this, right,
                        promoted, "right");
            }
            if (("==".equals(operator) || "!=".equals(operator))
                    && (left.sort == Sort.STRING && isNull(right)
                    || right.sort == Sort.STRING && isNull(left))) {
                Term string = left.sort == Sort.STRING ? left : right;
                String equality = string.stringNullness;
                return dependent(Term.of("!=".equals(operator)
                        ? "(not " + equality + ")" : equality,
                        Sort.BOOL), left, right);
            }
            if (left.sort != right.sort
                    && (("==".equals(operator) || "!=".equals(operator))
                    && (isNull(left) || isNull(right)))) {
                // Java primitives are never null.  This is the one mixed-sort
                // binary relation whose semantics can be closed without an
                return dependent(Term.of("!=".equals(operator)
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
                return Term.of("(" + (conjunction ? "and" : "or")
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
                if (left.text.equals(right.text)) {
                    return dependent(Term.of("==".equals(operator)
                            ? "true" : "false", Sort.BOOL), left, right);
                }
                if (left.sort == Sort.STRING) {
                    if (ContainerSmtCodec.handlesFieldBinding(expression)) {
                        Term symbol = ContainerSmtCodec.handlesField(
                                expression.get("_left")) ? right : left;
                        String materialization = ContainerSmtCodec
                                .materializedStringEquality(left.text,
                                right.text, symbol.stringNullness);
                        return dependent(Term.of(materialization,
                                Sort.BOOL), left, right);
                    }
                    if (!left.stringReferenceOrigin.isEmpty()
                            && left.stringReferenceOrigin.equals(
                            right.stringReferenceOrigin)) {
                        return dependent(Term.of("!=".equals(operator)
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
                    return dependent(Term.of(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                String equality = "(= " + left.text + " " + right.text + ")";
                return dependent(Term.of("!=".equals(operator)
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
                    return dependent(Term.of(JavaPrimitiveSmtSemantics
                            .floatingComparison(operator, left.text,
                                    right.text), Sort.BOOL), left, right);
                }
                return dependent(Term.of("(" + smt + " " + left.text + " "
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
                return dependent(Term.of(JavaPrimitiveSmtSemantics.bitwise(
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
                return dependent(Term.of(JavaPrimitiveSmtSemantics.shift(
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
                    if (floating != null) return dependent(Term.of(floating,
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
                    return dependent(Term.of(quotient, Sort.INT,
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
                return dependent(Term.of(JavaPrimitiveSmtSemantics.wrap(arithmeticExpression,
                        resultWidth), Sort.INT, resultWidth), left, right);
            }
            unsupported.add("BinaryOperator:" + operator);
            return unsupportedTerm(Sort.BOOL);
        }

        private boolean boxedPrimitiveReferenceEquality(
                JsonObject expression) {
            String operator = optionalString(expression, "_op");
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
            if (!"SymbolExpression".equals(optionalString(object, "_type"))
                    || sortOfJava(optionalString(object, "_java_type"))
                    != Sort.REF) {
                return false;
            }
            return JavaPrimitiveBoxing.wrapperType(
                    optionalString(object, "_java_type"));
        }

        /** Emits exact core Java String predicates/value operations plus the
         * materially different Java/SMT semantics remain fail-closed. */
        private Term stringOperation(JsonObject expression) {
            String operation = optionalString(expression, "_name");
            boolean negated = optionalBool(expression, "_is_not", false);
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
                Term length = Term.of("(str.len " + receiver.text + ")",
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
                return VmTermLowering.javaIntString(integer);
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
            return Term.of(negated ? "(not " + predicate + ")" : predicate,
                    Sort.BOOL).withPrecondition(precondition);
        }

        /**
         * Recognizes the sound Java round trip
         */

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
                    VmTermLowering.integralRange(domain.lower, term,
                            domain.upper));
        }

        private Term codecGap(String operation, String gap, Sort sort) {
            return VmTermLowering.codecGap(this, operation, gap, "",
                    sort);
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
            String name = optionalString(expression, "_name");
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
            String method = optionalString(expression, "_name");
            if (isJavaParseInt(method)) {
                return VmTermLowering.parseIntTerm(this, expression,
                        "");
            }
            if (isJavaSplitElement(method)) {
                return splitElementTerm(expression);
            }
            Term result = term(expression.get("_res_exp"), null);
            unsupported.add("MODEL_SEMANTICS_MISSING:MethodExpression:"
                    + firstNonBlank(method, "unknown"));
            return unsupportedTerm(result.sort);
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

        /** Boxes a primitive term for container and reference expressions. */
        private Term asValue(Term term, String javaType) {
            if (term.sort == Sort.VALUE) return term;
            if (term.sort == Sort.INT) {
                String boxed = ContainerSmtCodec.boxIntegral(
                        term.text, javaType);
                return dependent(Term.of(firstNonBlank(boxed,
                        "(VInt " + term.text + ")"), Sort.VALUE), term);
            }
            if (term.sort == Sort.FLOAT32) return dependent(Term.of(
                    "(VFloat " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.FLOAT64) return dependent(Term.of(
                    "(VDouble " + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.BOOL) return dependent(Term.of("(VBool "
                    + term.text + ")", Sort.VALUE), term);
            if (term.sort == Sort.STRING) {
                String boxed = "false".equals(term.stringNullness)
                        ? "(VString " + term.text + ")"
                        : "(ite " + term.stringNullness
                                + " (VRef nullRef) (VString "
                                + term.text + "))";
                return dependent(Term.of(boxed, Sort.VALUE), term);
            }
            if (term.sort == Sort.REF) return dependent(Term.of("(VRef "
                    + term.text + ")", Sort.VALUE), term);
            unsupported.add("CannotBox:" + term.sort);
            return unsupportedTerm(Sort.VALUE);
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
            for (Map.Entry<InvocationKey, Set<String>> entry
                    : casePartitions.entrySet()) {
                if (entry.getValue().isEmpty()) continue;
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
        String effectiveType = guardedReadJavaType(node);
        Sort result = sortOfJava(effectiveType);
        if (result == Sort.VALUE) result = expected;

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

    /** Java binary numeric promotion for the two integral JVM widths. */
    private static IntegralWidth promotedIntegralWidth(Term left,
                                                        Term right) {
        if (left.sort != Sort.INT || right.sort != Sort.INT) {
            return IntegralWidth.NONE;
        }
        return JavaPrimitiveSmtSemantics.promote(left.integralWidth,
                right.integralWidth);
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
