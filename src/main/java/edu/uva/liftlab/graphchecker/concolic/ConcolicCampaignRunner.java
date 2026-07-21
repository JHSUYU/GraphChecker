package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Executes the complete bounded feedback loop: discover an upstream region,
 * capture its seed path, import it, solve and replay output-relevant flips,
 * merge validated path transformers, update the cache, and repeat.
 */
public final class ConcolicCampaignRunner {
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final String CONCRETE_GUARD_PROOF_KIND =
            "REFERENCE_NULL_CONCRETE_GUARD_REPLAY_PROOF";
    private static final String CONCRETE_GUARD_PROOF_AUTHORITY =
            "SOLVER_EXACT_REFERENCE_NULL_GUARD_AND_MODEL_ASSIGNMENT_V1";
    private static final String NULLABLE_STRING_ENCODING_AUTHORITY =
            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1";
    private static final String REFERENCE_NULLNESS_ENCODING_AUTHORITY =
            "JAVA_REFERENCE_NULLNESS_AS_EXACT_REF_EQUALITY_V1";

    private ConcolicCampaignRunner() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result;
        try (CampaignLock ignored = acquireCampaignLock(
                arguments.outputDirectory)) {
            State state = readState(arguments);
            Path executionRegions = freezeExecutionRegions(
                    arguments.outputDirectory, state.regions);
            CommandBackend backend = new CommandBackend(
                    arguments.outputDirectory, executionRegions,
                    arguments.command, arguments.executionTimeoutMillis,
                    arguments.runtimeDiscoveryMode);
            result = run(state, backend, arguments.bounds,
                    arguments.z3, arguments.transitionFocus,
                    arguments.transitionFocusOnly);
            writeOutputs(arguments.outputDirectory, result);
        }
        System.out.println(GSON.toJson(result.manifest));
        if (!bool(result.manifest, "complete", false)) System.exit(2);
    }

    private static Path freezeExecutionRegions(Path outputDirectory,
                                               List<JsonObject> regions)
            throws IOException {
        Path path = outputDirectory.resolve("execution-inputs")
                .resolve(java.util.UUID.randomUUID().toString())
                .resolve("campaign_regions.jsonl");
        Files.createDirectories(path.getParent());
        writeJsonlAtomically(path, regions);
        return path;
    }

    static CampaignLock acquireCampaignLock(Path outputDirectory)
            throws IOException {
        Files.createDirectories(outputDirectory);
        Path path = outputDirectory.resolve("campaign.lock");
        FileChannel channel = FileChannel.open(path,
                StandardOpenOption.CREATE, StandardOpenOption.WRITE);
        try {
            FileLock lock = channel.tryLock();
            if (lock == null) {
                channel.close();
                throw new IOException("CAMPAIGN_ALREADY_RUNNING:" + path);
            }
            return new CampaignLock(channel, lock);
        } catch (OverlappingFileLockException exception) {
            channel.close();
            throw new IOException("CAMPAIGN_ALREADY_RUNNING:" + path,
                    exception);
        } catch (IOException | RuntimeException exception) {
            if (channel.isOpen()) channel.close();
            throw exception;
        }
    }

    private static State readState(Arguments arguments) throws IOException {
        Path currentSnapshot = arguments.outputDirectory.resolve(
                "campaign_state_manifest.json").toAbsolutePath()
                .normalize();
        Path requestedSnapshot = arguments.resumeStateManifest == null
                ? null : arguments.resumeStateManifest.toAbsolutePath()
                .normalize();
        if (Files.isRegularFile(currentSnapshot)) {
            if (requestedSnapshot != null
                    && !currentSnapshot.equals(requestedSnapshot)) {
                throw new IOException(
                        "CONFLICTING_CAMPAIGN_STATE_MANIFEST_AUTHORITY");
            }
            requestedSnapshot = currentSnapshot;
        }
        if (requestedSnapshot != null) {
            CampaignSnapshot snapshot = CampaignSnapshot.read(
                    requestedSnapshot);
            return new State(snapshot.regions,
                    snapshot.activations, snapshot.edges, snapshot.roots,
                    snapshot.summaries, snapshot.pathRecords,
                    snapshot.staticGraph);
        }
        return new State(readJsonl(arguments.regions),
                readActivations(arguments.activations,
                        arguments.resumeActivations),
                readEdges(arguments.edges, arguments.resumeEdges),
                readRoots(arguments.roots, arguments.resumeRoots),
                readSummaries(
                arguments.summaries),
                readOptionalJsonl(arguments.pathRecords),
                readOptionalJsonl(arguments.staticGraph));
    }

    static State readCliState(String[] argv) throws IOException {
        return readState(Arguments.parse(argv));
    }

    public static Result run(State input, ExecutionBackend backend,
                             Bounds bounds, Path z3) throws Exception {
        return run(input, backend, bounds, z3,
                RegionTransitionDiscoveryWorklist.Focus.none(), false);
    }

    static Result run(State input, ExecutionBackend backend,
                      Bounds bounds, Path z3,
                      RegionTransitionDiscoveryWorklist.Focus focus,
                      boolean transitionFocusOnly) throws Exception {
        Bounds effective = bounds == null ? Bounds.defaults() : bounds;
        RegionTransitionDiscoveryWorklist.Focus transitionFocus =
                focus == null
                        ? RegionTransitionDiscoveryWorklist.Focus.none()
                        : focus;
        if (transitionFocusOnly && (!transitionFocus.hasEdge()
                || !transitionFocus.hasActivation())) {
            throw new IllegalArgumentException("--transition-focus-only "
                    + "requires exact --transition-focus-edge and "
                    + "--transition-focus-activation values");
        }
        State state = input.copy();
        long started = System.nanoTime();
        List<JsonObject> campaignGaps = new ArrayList<>();
        List<JsonObject> admittedTargetRoots = admittedTargetRoots(
                state.roots, state.activations, state.summaries,
                campaignGaps);
        Map<String, JsonObject> seedPrecheckGaps = new LinkedHashMap<>();
        Set<String> seedAttempts = new LinkedHashSet<>();
        Set<String> transitionSeedAttempts = new LinkedHashSet<>();
        // Discovery seeds are quarantined from ordinary relation merging, but
        // they are durable campaign state.  A bounded run may stop after the
        // seed JVM and before the flip JVM; loading them from the summary
        // cache lets the next invocation resume at solve/replay instead of
        // paying for (and potentially observing a different) seed again.
        List<JsonObject> transitionSeeds = transitionDiscoverySeeds(
                state.summaries);
        int executionCount = 0;
        int solverQueryCount = 0;
        int transitionSeedExecutionCount = 0;
        int transitionReplayExecutionCount = 0;
        int transitionOutputReplayExecutionCount = 0;
        int transitionPromotionCount = 0;
        int targetRebaseExecutionCount = 0;
        int targetRebaseValidationCount = 0;
        List<JsonObject> targetRebaseHistory = new ArrayList<>();
        boolean focusedTargetComplete = focusedTransitionAlreadyPromoted(
                state, transitionFocus);
        int iteration = 0;
        boolean capacityReached = false;
        RecursiveRegionWorklist.Result graph = null;
        RegionPathWorklist.Result paths = null;
        RegionTransitionDiscoveryWorklist.Result transitions = null;
        RegionSummaryMerger.Result merged = null;
        RuntimeDiscoveryMode runtimeDiscoveryMode =
                backend == null ? RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED
                        : backend.runtimeDiscoveryMode();
        if (runtimeDiscoveryMode == null) {
            runtimeDiscoveryMode = RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED;
        }

        while (iteration++ < effective.maxIterations
                && elapsedMillis(started) < effective.maxWallClockMillis) {
            JsonObject pendingTargetRebase = postDiscoveryTargetRebase(state);
            if (bool(pendingTargetRebase, "ready", false)
                    && !targetRootUsesRebase(state,
                    pendingTargetRebase)) {
                String rebaseKey = targetRebaseKey(pendingTargetRebase);
                if (executionCount >= effective.maxExecutions) {
                    addGapOnce(campaignGaps, gap("BOUND_REACHED",
                            "TARGET_REBASE_EXECUTION_BOUND"));
                    capacityReached = true;
                    break;
                }
                JsonObject preparation = targetRebasePreparation(state,
                        pendingTargetRebase);
                if (!bool(preparation, "ready", false)) {
                    JsonObject failed = targetRebaseRecord(rebaseKey,
                            pendingTargetRebase, null, preparation,
                            "MATERIALIZATION_GAP", string(preparation,
                            "reason"));
                    addRecord(state.pathRecords, failed);
                    targetRebaseHistory.add(failed.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey + ":" + string(preparation,
                                    "reason")));
                    break;
                }
                JsonObject rebaseActivation = object(preparation,
                        "activation").deepCopy();
                addOrReplaceActivation(state.activations,
                        rebaseActivation);
                JsonObject capture = captureRequest("TARGET_REBASE",
                        rebaseKey, rebaseActivation, null);
                capture.add("targetRebase", pendingTargetRebase.deepCopy());
                ExecutionOutcome outcome = backend.execute(capture);
                executionCount++;
                targetRebaseExecutionCount++;
                JsonObject admission = targetRebaseAdmission(
                        pendingTargetRebase, rebaseActivation, outcome);
                JsonObject rebaseRecord = targetRebaseRecord(rebaseKey,
                        pendingTargetRebase, outcome, admission,
                        bool(admission, "valid", false)
                                ? "TARGET_REBASE_VALIDATED"
                                : "TARGET_REBASE_REJECTED",
                        string(admission, "reason"));
                if (!bool(admission, "valid", false)) {
                    addRecord(state.pathRecords, rebaseRecord);
                    targetRebaseHistory.add(rebaseRecord.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey + ":" + string(admission,
                                    "reason")));
                    break;
                }
                JsonObject formulaRebuild = targetRebaseFormulaRebuild(
                        state, pendingTargetRebase, rebaseActivation,
                        outcome.summary);
                if (!bool(formulaRebuild, "ready", false)) {
                    rebaseRecord.addProperty("status",
                            "TARGET_REBASE_FORMULA_REBUILD_REQUIRED");
                    rebaseRecord.addProperty("reason", string(
                            formulaRebuild, "reason"));
                    rebaseRecord.add("targetFormulaRebuild",
                            formulaRebuild.deepCopy());
                    addRecord(state.pathRecords, rebaseRecord);
                    targetRebaseHistory.add(rebaseRecord.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey + ":" + string(formulaRebuild,
                                    "reason")));
                    break;
                }
                rebaseRecord.add("targetFormulaRebuild",
                        formulaRebuild.deepCopy());
                String summaryCollision = freshTargetSummaryCollision(
                        state.summaries, outcome.summary);
                if (!summaryCollision.isEmpty()) {
                    rebaseRecord.addProperty("status",
                            "TARGET_REBASE_SUMMARY_CACHE_REJECTED");
                    rebaseRecord.addProperty("reason", summaryCollision);
                    addRecord(state.pathRecords, rebaseRecord);
                    targetRebaseHistory.add(rebaseRecord.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey + ":" + summaryCollision));
                    break;
                }
                List<JsonObject> candidateSummaries =
                        candidateFreshTargetSummaries(state.summaries,
                                outcome.summary, object(formulaRebuild,
                                        "query"), admission);
                JsonObject rebasedRoot = rebasedTargetRoot(
                        pendingTargetRebase, rebaseActivation,
                        outcome.summary, admission, object(formulaRebuild,
                                "query"));
                String rootRejection = targetRootRejection(rebasedRoot,
                        state.activations, candidateSummaries);
                ConcolicSmtComposer.FreshFatalArtifactValidation
                        artifactValidation =
                        ConcolicSmtComposer.validateFreshFatalArtifact(
                                rebasedRoot, candidateSummaries);
                rebaseRecord.add("freshFatalArtifactAdmission",
                        artifactValidation.toJson());
                if (rebasedRoot.size() == 0
                        || !rootRejection.isEmpty()
                        || !artifactValidation.valid) {
                    String reason = !rootRejection.isEmpty()
                            ? rootRejection : artifactValidation.reason;
                    rebaseRecord.addProperty("status",
                            "TARGET_REBASE_FRESH_ARTIFACT_REJECTED");
                    rebaseRecord.addProperty("reason", reason);
                    addRecord(state.pathRecords, rebaseRecord);
                    targetRebaseHistory.add(rebaseRecord.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey + ":" + reason));
                    break;
                }
                String replacedId = string(pendingTargetRebase,
                        "replacesActivationId");
                int stateRootIndex = targetRootIndex(state.roots,
                        replacedId);
                int admittedRootIndex = targetRootIndex(admittedTargetRoots,
                        replacedId);
                if (rebasedRoot.size() == 0 || stateRootIndex < 0
                        || admittedRootIndex < 0) {
                    rebaseRecord.addProperty("status",
                            "TARGET_REBASE_REJECTED");
                    rebaseRecord.addProperty("reason",
                            "TARGET_REBASE_ROOT_REPLACEMENT_FAILED");
                    addRecord(state.pathRecords, rebaseRecord);
                    targetRebaseHistory.add(rebaseRecord.deepCopy());
                    addGapOnce(campaignGaps, gap("TARGET_REBASE_GAP",
                            rebaseKey
                                    + ":TARGET_REBASE_ROOT_REPLACEMENT_FAILED"));
                    break;
                }
                // Validate both logical root slots before mutating either;
                // the rebase is one atomic campaign-state transition.
                state.roots.set(stateRootIndex, rebasedRoot.deepCopy());
                admittedTargetRoots.set(admittedRootIndex,
                        rebasedRoot.deepCopy());
                state.summaries.clear();
                state.summaries.addAll(candidateSummaries);
                addRecord(state.pathRecords, rebaseRecord);
                targetRebaseHistory.add(rebaseRecord.deepCopy());
                targetRebaseValidationCount++;
                // Do not admit this observer execution's freshly numbered
                // target activation as yet another rebase candidate.  The
                // imported primary summary is the authority for the logical
                // target instance selected by the transition execution.
                if (transitionFocusOnly && focusedTargetComplete) break;
                continue;
            }
            graph = RecursiveRegionWorklist.explore(state.regions,
                    state.activations, state.edges, state.summaries,
                    worklistTargetRoots(admittedTargetRoots, state),
                    effective.graphBounds);
            // Close output-relevant paths for summaries already in the cache
            // before launching another region seed.  This makes every region
            // follow the real record -> flip -> replay -> import loop instead
            // of collecting all seeds first and postponing every flip.
            paths = RegionPathWorklist.plan(pathSeedSummaries(
                            state.summaries, transitionSeeds,
                            transitionFocusOnly), state.activations,
                    state.pathRecords, effective.pathBounds);
            List<JsonObject> seedRequests = !transitionFocusOnly
                    && paths.tasks.isEmpty()
                    ? seedRequests(graph, seedAttempts)
                    : Collections.<JsonObject>emptyList();
            if (!seedRequests.isEmpty()) {
                boolean progressed = false;
                for (JsonObject request : seedRequests) {
                    if (executionCount >= effective.maxExecutions) {
                        campaignGaps.add(gap("BOUND_REACHED",
                                "MAX_CAMPAIGN_EXECUTIONS"));
                        capacityReached = true;
                        break;
                    }
                    String requestId = string(request, "requestId");
                    JsonObject activation = outputActivation(request, state);
                    if (activation == null) {
                        seedPrecheckGaps.put(requestId, gap(
                                "MISSING_OUTPUT_ACTIVATION", requestId));
                        continue;
                    }
                    if (!bool(activation, "requestedOutputSliceComplete",
                            false)) {
                        seedPrecheckGaps.put(requestId, gap(
                                "MISSING_COMPLETE_OUTPUT_SLICE_PLAN",
                                requestId));
                        continue;
                    }
                    if (bool(activation,
                            "requestedOutputCaptureRequired", false)
                            && !bool(activation,
                            "requestedOutputCaptureComplete", false)) {
                        seedPrecheckGaps.put(requestId, gap(
                                "OUTPUT_CAPTURE_RUNTIME_REFINEMENT_REQUIRED",
                                requestId));
                        continue;
                    }
                    if (!bool(activation, "schedulerReady", false)) {
                        seedPrecheckGaps.put(requestId, gap(
                                "OUTPUT_CAPTURE_MATERIALIZATION_NOT_READY",
                                requestId));
                        continue;
                    }
                    seedPrecheckGaps.remove(requestId);
                    // Only a concrete backend launch consumes this semantic
                    // request. A currently missing activation may be
                    // discovered by another valid execution in this same
                    // campaign and must remain retryable.
                    seedAttempts.add(requestId);
                    addOrReplaceActivation(state.activations, activation);
                    JsonObject capture = captureRequest("OUTPUT_SEED",
                            requestId, activation, null);
                    ExecutionOutcome outcome = backend.execute(capture);
                    executionCount++;
                    if (admitSeed(outcome, state, campaignGaps, requestId)) {
                        admitDiscoveredEvidence(outcome, state,
                                runtimeDiscoveryMode, activation);
                        progressed = true;
                        // One import may satisfy many recursive paths.  Rebuild
                        // the output-specific cache before executing another
                        // request so duplicate captures are never launched in
                        // the same iteration.
                        break;
                    }
                }
                if (progressed) continue;
                if (capacityReached) break;
            }

            paths = RegionPathWorklist.plan(pathSeedSummaries(
                            state.summaries, transitionSeeds,
                            transitionFocusOnly), state.activations,
                    state.pathRecords, effective.pathBounds);
            if (!paths.tasks.isEmpty()) {
                boolean progressed = false;
                for (JsonObject task : paths.tasks) {
                    if (solverQueryCount >= effective.maxSolverQueries
                            || executionCount >= effective.maxExecutions) {
                        campaignGaps.add(gap("BOUND_REACHED",
                                "CAMPAIGN_EXECUTION_OR_SOLVER_BOUND"));
                        capacityReached = true;
                        break;
                    }
                    JsonObject sourceActivation = activation(state.activations,
                            string(task, "sourceActivationId"));
                    if (sourceActivation == null) {
                        addRecord(state.pathRecords, record(task,
                                "MATERIALIZATION_GAP",
                                "SOURCE_ACTIVATION_NOT_FOUND"));
                        continue;
                    }
                    ConcolicConstraintSolver.Result solve =
                            ConcolicConstraintSolver.solve(task,
                                    sourceActivation, z3,
                                    effective.solverTimeoutMillis);
                    solverQueryCount++;
                    String solveStatus = string(solve.record, "status");
                    if (!"SAT_MODEL_READY".equals(solveStatus)) {
                        addRecord(state.pathRecords, solve.record);
                        progressed = true;
                        continue;
                    }
                    JsonObject replayActivation = replayActivation(task,
                            sourceActivation, solve.modelAssignments);
                    addOrReplaceActivation(state.activations,
                            replayActivation);
                    JsonObject capture = captureRequest("PATH_FLIP",
                            string(task, "queryKey"), replayActivation, task);
                    ExecutionOutcome outcome = backend.execute(capture);
                    executionCount++;
                    if (RegionCaptureGoal.from(task)
                            .isTransitionDiscovery()) {
                        transitionReplayExecutionCount++;
                    }
                    JsonObject replayValidation = validateReplayAdmission(
                            replayValidationPlan(task,
                                    solve.modelAssignments),
                            outcome.rawResult, outcome.summary);
                    JsonObject exploration = solve.record.deepCopy();
                    if (RegionCaptureGoal.from(task)
                            .isTransitionDiscovery()
                            && transitionOutputReplayRequired(
                            replayActivation, replayValidation)) {
                        JsonObject probeValidation = replayValidation;
                        JsonObject refinement = transitionOutputRefinement(
                                task, replayActivation, outcome);
                        exploration.add("transitionOutputProbeValidation",
                                probeValidation.deepCopy());
                        exploration.add("transitionOutputRefinement",
                                refinement.deepCopy());
                        if (!bool(refinement, "ready", false)) {
                            String reason = string(refinement, "reason");
                            exploration.addProperty("status",
                                    "MATERIALIZATION_GAP");
                            exploration.addProperty("reason", reason);
                            addRecord(state.pathRecords, exploration);
                            campaignGaps.add(gap(
                                    "TRANSITION_DISCOVERY_GAP",
                                    string(task, "queryKey") + ":"
                                            + reason));
                            progressed = true;
                            continue;
                        }
                        if (executionCount >= effective.maxExecutions) {
                            campaignGaps.add(gap("BOUND_REACHED",
                                    "CAMPAIGN_EXECUTION_OR_SOLVER_BOUND"));
                            capacityReached = true;
                            break;
                        }
                        JsonObject exactActivation = object(refinement,
                                "activation").deepCopy();
                        addOrReplaceActivation(state.activations,
                                exactActivation);
                        JsonObject retry = captureRequest(
                                "TRANSITION_OUTPUT_REPLAY",
                                string(task, "queryKey"), exactActivation,
                                task);
                        JsonObject refinementEvidence =
                                refinement.deepCopy();
                        refinementEvidence.remove("activation");
                        refinementEvidence.remove("ready");
                        refinementEvidence.remove("reason");
                        retry.add("transitionOutputRefinement",
                                refinementEvidence);
                        outcome = backend.execute(retry);
                        executionCount++;
                        transitionReplayExecutionCount++;
                        transitionOutputReplayExecutionCount++;
                        replayValidation = validateReplayAdmission(
                                replayValidationPlan(task,
                                        solve.modelAssignments),
                                outcome.rawResult, outcome.summary);
                    }
                    exploration.add("replayValidation", replayValidation);
                    if (!bool(replayValidation, "valid", false)) {
                        boolean outputGap = bool(replayValidation,
                                "outputClosureAdmissionGap", false);
                        String reason = string(replayValidation,
                                "outputClosureGapReason");
                        if (!outputGap) {
                            reason = "UNFORCED_REPLAY_VALIDATION_FAILED";
                        } else if (reason.isEmpty()) {
                            reason =
                                    "OUTPUT_CLOSURE_REPLAY_NOT_IMPORTABLE";
                        }
                        exploration.addProperty("status", outputGap
                                ? "MATERIALIZATION_GAP"
                                : "EXECUTION_ERROR");
                        exploration.addProperty("reason", reason);
                        addRecord(state.pathRecords, exploration);
                        campaignGaps.add(gap(outputGap
                                        ? "EXPLORATION_GAP"
                                        : "REPLAY_REJECTED",
                                outputGap ? string(task, "queryKey") + ":"
                                        + reason
                                        : string(task, "queryKey")));
                        progressed = true;
                        continue;
                    }
                    if (outcome.summary == null
                            || !bool(outcome.summary, "valid", false)) {
                        exploration.addProperty("status",
                                "MATERIALIZATION_GAP");
                        exploration.addProperty("reason",
                                "VALID_REPLAY_HAS_NO_IMPORTED_SUMMARY");
                        addRecord(state.pathRecords, exploration);
                        campaignGaps.add(gap("EXPLORATION_GAP",
                                string(task, "queryKey") + ":"
                                        + "VALID_REPLAY_HAS_NO_IMPORTED_SUMMARY"));
                        progressed = true;
                        continue;
                    }
                    if (RegionCaptureGoal.from(task)
                            .isTransitionDiscovery()) {
                        JsonObject admission = transitionPromotionAdmission(
                                task, outcome, runtimeDiscoveryMode);
                        exploration.add("transitionPromotionAdmission",
                                admission);
                        if (!bool(admission, "valid", false)) {
                            exploration.addProperty("status",
                                    "NO_RUNTIME_TRANSITION_EVIDENCE");
                            exploration.addProperty("reason", string(
                                    admission, "reason"));
                            addRecord(state.pathRecords, exploration);
                            campaignGaps.add(gap(
                                    "TRANSITION_DISCOVERY_GAP",
                                    string(task, "queryKey") + ":"
                                            + string(admission, "reason")));
                            progressed = true;
                            continue;
                        }
                        JsonObject promoted = promoteTransitionSummary(
                                outcome.summary, task, admission);
                        if (!containsPath(state.summaries, promoted)) {
                            state.summaries.add(promoted);
                        }
                        alignActivationWithPromotedSummary(
                                state.activations, promoted);
                        removeTransitionSeed(transitionSeeds, task);
                        removeTransitionSeed(state.summaries, task);
                        admitDiscoveredEvidence(outcome, state,
                                runtimeDiscoveryMode, replayActivation);
                        exploration.addProperty("status",
                                "TRANSITION_VALIDATED");
                        exploration.addProperty("summaryId", string(
                                promoted, "summaryId"));
                        addRecord(state.pathRecords, exploration);
                        transitionPromotionCount++;
                        if (transitionFocus.matchesTask(task)) {
                            focusedTargetComplete = true;
                        }
                        progressed = true;
                        if (transitionFocusOnly && focusedTargetComplete
                                && !targetRebaseRequired(state)) {
                            break;
                        }
                        continue;
                    }
                    boolean duplicate = containsPath(state.summaries,
                            outcome.summary);
                    if (!duplicate) state.summaries.add(outcome.summary);
                    admitDiscoveredEvidence(outcome, state,
                            runtimeDiscoveryMode, replayActivation);
                    exploration.addProperty("status", duplicate
                            ? "EXECUTED_DUPLICATE_PATH"
                            : "EXECUTED_NEW_PATH");
                    exploration.addProperty("observedPathKey",
                            RegionPathWorklist.stablePathKey(outcome.summary));
                    exploration.addProperty("summaryId",
                            string(outcome.summary, "summaryId"));
                    addRecord(state.pathRecords, exploration);
                    progressed = true;
                }
                if (transitionFocusOnly && focusedTargetComplete
                        && !targetRebaseRequired(state)) break;
                if (capacityReached) break;
                if (progressed) continue;
            }

            transitions = RegionTransitionDiscoveryWorklist.plan(
                    state.regions, state.activations,
                    runtimeDiscoveryMode.isFixedValidatedGraph()
                            ? Collections.<JsonObject>emptyList()
                            : state.edges,
                    worklistTargetRoots(admittedTargetRoots, state),
                    state.pathRecords,
                    RegionTransitionDiscoveryWorklist.Bounds.defaults(),
                    transitionFocus);
            JsonObject transitionRequest = firstUnattempted(
                    transitions.requests, transitionSeedAttempts);
            if (transitionRequest != null) {
                String requestId = string(transitionRequest, "requestId");
                if (executionCount >= effective.maxExecutions) {
                    campaignGaps.add(gap("BOUND_REACHED",
                            "MAX_CAMPAIGN_EXECUTIONS"));
                    capacityReached = true;
                    break;
                }
                JsonObject activation = transitionOutputActivation(
                        transitionRequest, state);
                String precheck = transitionSeedPrecheck(activation);
                if (!precheck.isEmpty()) {
                    JsonObject failed = record(transitionRequest,
                            "MATERIALIZATION_GAP", precheck);
                    failed.addProperty("requestId", requestId);
                    addRecord(state.pathRecords, failed);
                    campaignGaps.add(gap("TRANSITION_DISCOVERY_GAP",
                            requestId + ":" + precheck));
                    transitionSeedAttempts.add(requestId);
                    continue;
                }
                transitionSeedAttempts.add(requestId);
                addOrReplaceActivation(state.activations, activation);
                JsonObject capture = captureRequest(
                        "TRANSITION_DISCOVERY_SEED", requestId,
                        activation, null);
                ExecutionOutcome outcome = backend.execute(capture);
                executionCount++;
                transitionSeedExecutionCount++;
                JsonObject seed = transitionDiscoverySeed(
                        transitionRequest, outcome);
                if (seed == null) {
                    JsonObject failed = record(transitionRequest,
                            "MATERIALIZATION_GAP",
                            "DISCOVERY_SEED_HAS_NO_ADMISSIBLE_SYMBOLIC_PATH");
                    failed.addProperty("requestId", requestId);
                    addRecord(state.pathRecords, failed);
                    campaignGaps.add(gap("TRANSITION_DISCOVERY_GAP",
                            requestId + ":DISCOVERY_SEED_REJECTED"));
                    continue;
                }
                if (!containsSummaryId(state.summaries, seed)) {
                    state.summaries.add(seed.deepCopy());
                }
                if (!containsSummaryId(transitionSeeds, seed)) {
                    transitionSeeds.add(seed.deepCopy());
                }
                JsonObject captured = record(transitionRequest,
                        "TRANSITION_SEED_CAPTURED", "");
                captured.addProperty("requestId", requestId);
                captured.addProperty("summaryId", string(seed,
                        "summaryId"));
                captured.addProperty("executionId", outcome.executionId);
                captured.add("transitionDiscovery", object(seed,
                        "transitionDiscovery").deepCopy());
                captured.addProperty("summaryCacheAdmission",
                        "PERSISTED_QUARANTINED_DISCOVERY_SEED");
                addRecord(state.pathRecords, captured);
                continue;
            }

            // Re-plan after all terminal exploration records, then merge only
            // when the worklist itself says there is no pending or hidden gap.
            paths = RegionPathWorklist.plan(pathSeedSummaries(
                            state.summaries, transitionSeeds,
                            transitionFocusOnly), state.activations,
                    state.pathRecords, effective.pathBounds);
            merged = RegionSummaryMerger.merge(rawOutputSummaries(
                    state.summaries), paths.manifest);
            replaceMergedSummaries(state.summaries, merged.summaries);
            graph = RecursiveRegionWorklist.explore(state.regions,
                    state.activations, state.edges, state.summaries,
                    worklistTargetRoots(admittedTargetRoots, state),
                    effective.graphBounds);
            if (!transitionFocusOnly
                    && complete(graph, paths, merged, campaignGaps)
                    && bool(transitions.manifest, "complete", false)) break;
            if ((!transitionFocusOnly
                    && !hasExecutableSeedRequest(graph, seedAttempts, state)
                    || transitionFocusOnly)
                    && paths.tasks.isEmpty()
                    && firstUnattempted(transitions.requests,
                    transitionSeedAttempts) == null) break;
        }

        if (elapsedMillis(started) >= effective.maxWallClockMillis) {
            campaignGaps.add(gap("BOUND_REACHED",
                    "MAX_CAMPAIGN_WALL_CLOCK"));
        } else if (iteration > effective.maxIterations) {
            campaignGaps.add(gap("BOUND_REACHED",
                    "MAX_CAMPAIGN_ITERATIONS"));
        }
        if (graph == null) graph = RecursiveRegionWorklist.explore(
                state.regions, state.activations, state.edges,
                state.summaries, worklistTargetRoots(admittedTargetRoots,
                state), effective.graphBounds);
        if (!transitionFocusOnly) {
            refreshSeedPrecheckGaps(graph, seedAttempts, state,
                    seedPrecheckGaps);
            campaignGaps.addAll(seedPrecheckGaps.values());
        }
        if (paths == null) paths = RegionPathWorklist.plan(
                pathSeedSummaries(state.summaries, transitionSeeds,
                        transitionFocusOnly), state.activations,
                state.pathRecords, effective.pathBounds);
        if (merged == null) merged = RegionSummaryMerger.merge(
                rawOutputSummaries(state.summaries), paths.manifest);
        if (transitions == null || transitionFocusOnly) transitions =
                RegionTransitionDiscoveryWorklist.plan(state.regions,
                        state.activations,
                        runtimeDiscoveryMode.isFixedValidatedGraph()
                                ? Collections.<JsonObject>emptyList()
                                : state.edges,
                        worklistTargetRoots(admittedTargetRoots, state),
                        state.pathRecords,
                        RegionTransitionDiscoveryWorklist.Bounds.defaults(),
                        transitionFocus);
        for (JsonElement element : array(transitions.manifest, "gaps")) {
            if (element.isJsonObject()) {
                campaignGaps.add(element.getAsJsonObject().deepCopy());
            }
        }
        if (!bool(transitions.manifest, "complete", false)
                && array(transitions.manifest, "gaps").size() == 0) {
            campaignGaps.add(gap("TRANSITION_DISCOVERY_INCOMPLETE",
                    "PENDING_OR_EXHAUSTED_DISCOVERY_REQUEST"));
        }
        focusedTargetComplete = focusedTargetComplete
                || focusedTransitionAlreadyPromoted(state, transitionFocus);
        if (transitionFocusOnly && !focusedTargetComplete
                && campaignGaps.isEmpty()) {
            campaignGaps.add(gap("TRANSITION_DISCOVERY_FOCUS_GAP",
                    "FOCUSED_TRANSITION_NOT_PROMOTED"));
        }
        JsonObject pendingTargetRebase = postDiscoveryTargetRebase(state);
        boolean targetRebasePending = bool(pendingTargetRebase,
                "ready", false) && !targetRootUsesRebase(state,
                pendingTargetRebase);
        JsonObject persistedRebasedRoot = persistedRebasedTargetRoot(
                state);
        boolean targetRebaseCompleted = persistedRebasedRoot.size() > 0;
        JsonObject targetRebase = pendingTargetRebase.deepCopy();
        if (!bool(targetRebase, "ready", false)
                && targetRebaseCompleted) {
            JsonObject provenance = object(persistedRebasedRoot,
                    "targetRebaseProvenance");
            targetRebase.addProperty("required", false);
            targetRebase.addProperty("ready", true);
            targetRebase.addProperty("status",
                    "FRESH_TARGET_REBASE_VALIDATED");
            targetRebase.addProperty("activationId", string(
                    persistedRebasedRoot, "activationId"));
            targetRebase.addProperty("regionId", string(
                    persistedRebasedRoot, "regionId"));
            targetRebase.addProperty("regionInstanceId", string(
                    persistedRebasedRoot, "regionInstanceId"));
            targetRebase.addProperty("executionId", string(provenance,
                    "targetReplayExecutionId"));
            targetRebase.addProperty("replacesActivationId", string(
                    provenance, "replacesActivationId"));
            targetRebase.addProperty("replacesRegionInstanceId", string(
                    provenance, "replacesRegionInstanceId"));
            targetRebase.addProperty("authority", string(provenance,
                    "authority"));
        }
        if (targetRebasePending && !capacityReached
                && elapsedMillis(started) < effective.maxWallClockMillis
                && iteration <= effective.maxIterations) {
            addGapOnce(campaignGaps, gap(
                    "TARGET_REBASE_EXECUTION_PENDING",
                    string(targetRebase, "activationId") + ":"
                            + string(targetRebase, "regionInstanceId")));
        }

        boolean complete = transitionFocusOnly
                ? focusedTargetComplete && !targetRebasePending
                : complete(graph, paths, merged, campaignGaps)
                && bool(transitions.manifest, "complete", false);
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "CONCOLIC_REGION_CAMPAIGN");
        manifest.addProperty("iterationCount", Math.min(iteration,
                effective.maxIterations));
        manifest.addProperty("executionCount", executionCount);
        manifest.addProperty("solverQueryCount", solverQueryCount);
        manifest.addProperty("transitionSeedExecutionCount",
                transitionSeedExecutionCount);
        manifest.addProperty("transitionReplayExecutionCount",
                transitionReplayExecutionCount);
        manifest.addProperty("transitionOutputReplayExecutionCount",
                transitionOutputReplayExecutionCount);
        manifest.addProperty("transitionPromotionCount",
                transitionPromotionCount);
        manifest.addProperty("targetRebaseExecutionCount",
                targetRebaseExecutionCount);
        manifest.addProperty("targetRebaseValidationCount",
                targetRebaseValidationCount);
        manifest.add("targetRebaseHistory",
                GSON.toJsonTree(targetRebaseHistory));
        manifest.addProperty("transitionFocusConfigured",
                transitionFocus.configured());
        manifest.addProperty("transitionFocusOnly", transitionFocusOnly);
        manifest.addProperty("transitionFocusEdgeId",
                transitionFocus.edgeId);
        manifest.addProperty("transitionFocusActivationId",
                transitionFocus.activationId);
        manifest.addProperty("transitionFocusGuardSiteId",
                transitionFocus.guardSiteId);
        manifest.addProperty("focusedTargetComplete",
                focusedTargetComplete);
        manifest.add("postDiscoveryTargetRebase",
                targetRebase.deepCopy());
        manifest.addProperty("postDiscoveryTargetRebaseRequired",
                targetRebasePending);
        manifest.addProperty("postDiscoveryTargetRebaseCompleted",
                targetRebaseCompleted);
        manifest.addProperty("postDiscoveryTargetRebaseReady",
                bool(targetRebase, "ready", false));
        manifest.addProperty("postDiscoveryTargetRebaseActivationId",
                string(targetRebase, "activationId"));
        manifest.addProperty("postDiscoveryTargetRebaseRegionInstanceId",
                string(targetRebase, "regionInstanceId"));
        manifest.addProperty("postDiscoveryTargetRebaseStatus",
                string(targetRebase, "status"));
        manifest.addProperty("targetWorklistUsesRebasedInstance",
                targetRebaseCompleted
                        || bool(targetRebase, "ready", false));
        manifest.addProperty("admittedTargetRootCount",
                admittedTargetRoots.size());
        manifest.addProperty("targetRootAdmissionComplete",
                admittedTargetRoots.size() == state.roots.size()
                        && !admittedTargetRoots.isEmpty());
        manifest.addProperty("rawPathSummaryCount",
                rawOutputSummaries(state.summaries).size());
        manifest.addProperty("mergedRegionRelationCount",
                merged.summaries.size());
        manifest.addProperty("explorationRecordCount",
                state.pathRecords.size());
        manifest.add("graphWorklist", graph.manifest.deepCopy());
        manifest.add("pathWorklist", paths.manifest.deepCopy());
        manifest.add("relationMerge", merged.manifest.deepCopy());
        manifest.add("transitionDiscovery",
                transitions.manifest.deepCopy());
        manifest.addProperty("gapCount", campaignGaps.size());
        manifest.add("gaps", GSON.toJsonTree(campaignGaps));
        manifest.addProperty("complete", complete);
        manifest.addProperty("status", transitionFocusOnly
                ? complete
                    ? "COMPLETE_FOCUSED_TRANSITION_DISCOVERY"
                    : "FOCUSED_TRANSITION_DISCOVERY_WITH_EXPLICIT_GAPS"
                : complete
                ? runtimeDiscoveryMode.isFixedValidatedGraph()
                    ? "COMPLETE_BOUNDED_FIXED_RUNTIME_GRAPH_CLOSURE"
                    : "COMPLETE_AUTOMATIC_REGION_CLOSURE"
                : "REGION_CLOSURE_WITH_EXPLICIT_GAPS");
        manifest.addProperty("targetPolicy",
                "ONE_DIRECTED_FATAL_BRANCH_FLIP");
        manifest.addProperty("upstreamPolicy",
                "BOUNDED_CONCOLIC_PATH_CLOSURE_AND_GUARDED_MERGE");
        manifest.addProperty("domainSemanticAdapterUsed", false);
        manifest.addProperty("branchOverrideAccepted", false);
        manifest.addProperty("automaticallyEligibleUpstreamRequestCount",
                countRequests(graph, true));
        manifest.addProperty("deferredUnprovenMappingRequestCount",
                countRequests(graph, false));
        manifest.addProperty("unprovenMappingRequestsExecuted",
                transitionSeedExecutionCount > 0
                        || transitionReplayExecutionCount > 0);
        manifest.addProperty("unprovenMappingRequestsAdmittedToComposition",
                false);
        manifest.addProperty("runtimeDiscoveryMode",
                runtimeDiscoveryMode.name());
        manifest.addProperty("sameExecutionRuntimeDiscoveryRequired",
                !runtimeDiscoveryMode.isFixedValidatedGraph());
        manifest.addProperty("runtimeGraphClosureClaimed",
                complete && !transitionFocusOnly
                        && !runtimeDiscoveryMode.isFixedValidatedGraph());
        manifest.addProperty("eligibleToReportAutomaticRelationship",
                complete && !transitionFocusOnly
                        && !runtimeDiscoveryMode.isFixedValidatedGraph());
        manifest.addProperty("eligibleToReportBoundedFixedGraphRelationship",
                complete && !transitionFocusOnly
                        && runtimeDiscoveryMode.isFixedValidatedGraph());
        manifest.addProperty("runtimeGraphEvidenceAdmissionPolicy",
                runtimeDiscoveryMode.isFixedValidatedGraph()
                        ? "IMMUTABLE_RUNTIME_SELECTED_FIXED_GRAPH"
                        : "VALIDATED_SAME_EXECUTION_DISCOVERY");
        manifest.addProperty("soundnessScope",
                runtimeDiscoveryMode.isFixedValidatedGraph()
                        ? "VALIDATED_UNFORCED_REPLAYS_WITHIN_RUNTIME_SELECTED_FIXED_GRAPH_AND_DECLARED_BOUNDS"
                        : "VALIDATED_UNFORCED_REPLAYS_WITHIN_DECLARED_BOUNDS");
        return new Result(state, merged.summaries, manifest);
    }

    /**
     * Campaign recursion starts only after the directed target replay has been
     * imported and re-scheduled.  A merely solver-ready branch query is not a
     * proof that the desired target outcome occurred without an override.
     */
    private static List<JsonObject> admittedTargetRoots(
            List<JsonObject> roots, List<JsonObject> activations,
            List<JsonObject> summaries, List<JsonObject> gaps) {
        List<JsonObject> admitted = new ArrayList<>();
        if (roots == null || roots.isEmpty()) {
            gaps.add(gap("INVALID_TARGET_ROOT",
                    "MISSING_VALIDATED_TARGET_ROOT"));
            return admitted;
        }
        boolean rejected = false;
        for (JsonObject root : roots) {
            String rejection = targetRootRejection(root, activations,
                    summaries);
            if (rejection.isEmpty()) admitted.add(root);
            else {
                rejected = true;
                gaps.add(gap("INVALID_TARGET_ROOT", rejection));
            }
        }
        if (rejected) admitted.clear();
        return admitted;
    }

    /**
     * Uses a fresh same-execution fatal-root instance only as the recursive
     * topology anchor.  It does not inherit the old instance's target replay
     * validation; the manifest keeps the scheduler rebase requirement open
     * until that exact activation is scheduled and validated independently.
     */
    private static List<JsonObject> worklistTargetRoots(
            List<JsonObject> validatedRoots, State state) {
        JsonObject rebase = postDiscoveryTargetRebase(state);
        if (!bool(rebase, "ready", false)) return validatedRoots;
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject root : validatedRoots) {
            JsonObject value = root.deepCopy();
            if (string(root, "activationId").equals(string(rebase,
                    "replacesActivationId"))) {
                value.addProperty("activationId", string(rebase,
                        "activationId"));
                value.addProperty("regionInstanceId", string(rebase,
                        "regionInstanceId"));
                value.addProperty("worklistRebaseOnly", true);
                value.addProperty("worklistRebaseAuthority",
                        "SAME_EXECUTION_EXACT_FATAL_ROOT_ACTIVATION");
            }
            result.add(value);
        }
        return result;
    }

    private static JsonObject postDiscoveryTargetRebase(State state) {
        JsonObject result = new JsonObject();
        result.addProperty("required", false);
        result.addProperty("ready", false);
        result.addProperty("status", "NOT_DISCOVERED");
        result.addProperty("candidateCount", 0);
        if (state == null) return result;
        JsonObject selected = null;
        JsonObject selectedRoot = null;
        int candidates = 0;
        boolean staleRejected = false;
        for (JsonObject activation : state.activations) {
            if (!bool(activation,
                    "postDiscoveryTargetRebaseCandidate", false)) continue;
            for (JsonObject root : state.roots) {
                if (!string(root, "activationId").equals(string(activation,
                        "replacesTargetActivationId"))
                        || !string(root, "regionId").equals(string(
                        activation, "regionId"))) continue;
                String instance = string(activation, "regionInstanceId");
                if (instance.isEmpty() || instance.equals(string(root,
                        "regionInstanceId"))) {
                    staleRejected = true;
                    continue;
                }
                if (string(activation,
                        "postDiscoveryTargetExecutionId").isEmpty()) {
                    continue;
                }
                candidates++;
                // Admissions are appended in execution order. The latest
                // exact activation is the only safe post-discovery target.
                selected = activation;
                selectedRoot = root;
            }
        }
        result.addProperty("candidateCount", candidates);
        result.addProperty("required", candidates > 0);
        if (selected == null) {
            if (staleRejected) result.addProperty("status",
                    "STALE_INSTANCE_REJECTED");
            return result;
        }
        result.addProperty("ready", true);
        result.addProperty("status",
                "EXACT_SAME_EXECUTION_TARGET_ACTIVATION_READY");
        result.addProperty("activationId", string(selected,
                "activationId"));
        result.addProperty("regionId", string(selected, "regionId"));
        result.addProperty("regionInstanceId", string(selected,
                "regionInstanceId"));
        result.addProperty("executionId", string(selected,
                "postDiscoveryTargetExecutionId"));
        result.addProperty("replacesActivationId", string(selectedRoot,
                "activationId"));
        result.addProperty("replacesRegionInstanceId", string(selectedRoot,
                "regionInstanceId"));
        result.addProperty("authority",
                "SAME_EXECUTION_EXACT_FATAL_ROOT_ACTIVATION");
        return result;
    }

    private static boolean targetRebaseRequired(State state) {
        JsonObject rebase = postDiscoveryTargetRebase(state);
        return bool(rebase, "ready", false)
                && !targetRootUsesRebase(state, rebase);
    }

    private static String targetRebaseKey(JsonObject rebase) {
        return "TARGET.REBASE." + shortHash(string(rebase,
                "replacesActivationId") + "\n"
                + string(rebase, "activationId") + "\n"
                + string(rebase, "regionInstanceId") + "\n"
                + string(rebase, "executionId"));
    }

    /**
     * Rebinds a previously validated directed target query to the exact fresh
     * target activation observed by the transition execution.  The upstream
     * replay prefix is retained, while every downstream value injection and
     * branch override is explicitly removed.  The fresh target is therefore
     * an observer of naturally propagated state, not another model endpoint.
     */
    private static JsonObject targetRebasePreparation(
            State state, JsonObject rebase) {
        JsonObject result = new JsonObject();
        result.addProperty("ready", false);
        JsonObject oldRoot = uniqueTargetRoot(state.roots,
                string(rebase, "replacesActivationId"));
        JsonObject oldActivation = activation(state.activations,
                string(rebase, "replacesActivationId"));
        JsonObject freshActivation = activation(state.activations,
                string(rebase, "activationId"));
        if (oldRoot == null || oldActivation == null
                || freshActivation == null) {
            result.addProperty("reason",
                    "TARGET_REBASE_IDENTITY_NOT_UNIQUE_OR_MISSING");
            return result;
        }
        String regionId = string(rebase, "regionId");
        String freshInstance = string(rebase, "regionInstanceId");
        if (regionId.isEmpty() || freshInstance.isEmpty()
                || !regionId.equals(string(oldRoot, "regionId"))
                || !regionId.equals(string(freshActivation, "regionId"))
                || !freshInstance.equals(string(freshActivation,
                "regionInstanceId"))) {
            result.addProperty("reason",
                    "TARGET_REBASE_FRESH_INSTANCE_MISMATCH");
            return result;
        }

        JsonObject target = object(oldActivation,
                "targetBranch").deepCopy();
        if (target.size() == 0) {
            target.addProperty("siteId", string(oldRoot, "siteId"));
            target.addProperty("occurrence", integer(oldRoot,
                    "occurrence", -1));
            target.addProperty("desiredOutcome", bool(oldRoot,
                    "desiredOutcome", false));
        }
        target.addProperty("validationOnly", true);
        target.addProperty("branchOverrideAllowed", false);

        JsonObject query = object(oldActivation,
                "directedTargetQuery").deepCopy();
        if (query.size() == 0 && oldRoot.has("originalTargetCondition")
                && oldRoot.has("negatedTargetCondition")) {
            query = oldRoot.deepCopy();
        }
        if (string(target, "siteId").isEmpty()
                || integer(target, "occurrence", -1) < 1
                || query.size() == 0
                || !string(target, "siteId").equals(string(query,
                "siteId"))
                || integer(target, "occurrence", -1) != integer(query,
                "occurrence", -2)
                || bool(target, "desiredOutcome", false) != bool(query,
                "desiredOutcome", true)
                || !bool(query, "readyForSolver", false)
                || !query.has("originalTargetCondition")
                || !query.has("negatedTargetCondition")
                || array(query, "constraints").size() == 0) {
            result.addProperty("reason",
                    "TARGET_REBASE_DIRECTED_QUERY_INCOMPLETE");
            return result;
        }

        query.addProperty("activationId", string(freshActivation,
                "activationId"));
        query.addProperty("regionId", regionId);
        query.addProperty("regionInstanceId", freshInstance);
        query.addProperty("readyForReplay", true);
        query.addProperty("replayAlreadyValidated", false);
        query.addProperty("targetReplayValidated", false);
        query.remove("validatedSummaryId");
        query.remove("validatedTargetSummary");
        query.remove("targetRebaseProvenance");
        query.addProperty("replayValidationAuthority", "NONE");
        query.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        JsonObject context = object(query,
                "symbolicContext").deepCopy();
        context.addProperty("regionId", regionId);
        context.addProperty("regionInstanceId", freshInstance);
        context.addProperty("targetRebaseAuthority",
                "FRESH_SAME_EXECUTION_TARGET_INSTANCE");
        query.add("symbolicContext", context);

        JsonObject prepared = oldActivation.deepCopy();
        for (Map.Entry<String, JsonElement> entry
                : freshActivation.entrySet()) {
            prepared.add(entry.getKey(), entry.getValue().deepCopy());
        }
        prepared.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        prepared.add("targetBranch", target);
        prepared.add("directedTargetQuery", query);
        prepared.add("modelAssignments", new JsonArray());
        prepared.add("replayMaterializations", new JsonArray());
        prepared.add("forcedBranches", new JsonArray());
        prepared.addProperty("targetReplayRequired", true);
        prepared.addProperty("executionPhase", "REPLAY_REBASED_TARGET");
        prepared.addProperty("branchOverrideProhibited", true);
        prepared.addProperty("downstreamInjectionProhibited", true);
        prepared.addProperty("targetObservationOnly", true);
        prepared.addProperty("replayable", true);
        prepared.addProperty("targetRebaseKey", targetRebaseKey(rebase));
        prepared.addProperty("replacesTargetActivationId", string(rebase,
                "replacesActivationId"));
        prepared.addProperty("replacesTargetRegionInstanceId", string(rebase,
                "replacesRegionInstanceId"));
        prepared.addProperty("targetRebaseSourceExecutionId", string(rebase,
                "executionId"));
        prepared.addProperty("targetRebaseAuthority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_TARGET_OBSERVATION");
        JsonArray support = flattenedReachabilitySupport(prepared);
        prepared.addProperty("upstreamReachabilitySupportRequired", true);
        prepared.addProperty("upstreamReachabilitySupportCount",
                support.size());
        if (support.size() == 0) {
            result.addProperty("reason",
                    "TARGET_REBASE_REACHABILITY_SUPPORT_MISSING");
            return result;
        }

        result.addProperty("ready", true);
        result.addProperty("reason", "");
        result.add("activation", prepared);
        result.addProperty("oldActivationId", string(rebase,
                "replacesActivationId"));
        result.addProperty("newActivationId", string(rebase,
                "activationId"));
        result.addProperty("oldRegionInstanceId", string(rebase,
                "replacesRegionInstanceId"));
        result.addProperty("newRegionInstanceId", freshInstance);
        result.addProperty("upstreamReachabilitySupportCount",
                support.size());
        result.addProperty("authority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_TARGET_OBSERVATION");
        return result;
    }

    private static JsonObject targetRebaseAdmission(
            JsonObject rebase, JsonObject activation,
            ExecutionOutcome outcome) {
        if (outcome == null || outcome.summary == null) {
            return targetRebaseAdmission(false,
                    "TARGET_REBASE_RESULT_OR_SUMMARY_MISSING", outcome,
                    activation);
        }
        JsonObject raw = outcome.rawResult;
        JsonObject summary = outcome.summary;
        String activationId = string(activation, "activationId");
        String regionId = string(activation, "regionId");
        String instance = string(activation, "regionInstanceId");
        String rawInstance = string(raw, "regionInstanceId");
        String rawExecution = string(raw, "executionId");
        String summaryExecution = string(summary, "executionId");
        if (!"CONCOLIC_REGION_RESULT".equals(string(raw, "event"))
                || !activationId.equals(string(raw, "activationId"))
                || !regionId.equals(string(raw, "regionId"))
                // Current custom-JDK rows identify the scheduled invocation
                // by activation id and do not always repeat the logical
                // region-instance id.  If a future row supplies it, it must
                // agree; the imported summary below always binds the exact
                // instance from the authoritative activation plan.
                || !rawInstance.isEmpty()
                && !instance.equals(rawInstance)
                || !rawExecution.isEmpty()
                && !rawExecution.equals(outcome.executionId)
                || !summaryExecution.isEmpty()
                && !summaryExecution.equals(outcome.executionId)) {
            return targetRebaseAdmission(false,
                    "TARGET_REBASE_RAW_INSTANCE_MISMATCH", outcome,
                    activation);
        }
        if (!bool(summary, "valid", false)
                || !activationId.equals(string(summary, "activationId"))
                || !regionId.equals(string(summary, "regionId"))
                || !instance.equals(string(summary, "regionInstanceId"))
                || !RegionCaptureGoal.from(summary).isTargetBranch()) {
            return targetRebaseAdmission(false,
                    "TARGET_REBASE_SUMMARY_INSTANCE_MISMATCH", outcome,
                    activation);
        }
        if (bool(raw, "branchOverrideUsed", false)
                || bool(summary, "branchOverrideUsed", false)
                || bool(raw, "forcedBranchUsed", false)
                || integer(raw, "forcedBranchCount", 0) != 0
                || array(raw, "replayMaterializationsApplied").size() != 0
                || array(raw, "modelAssignmentsApplied").size() != 0) {
            return targetRebaseAdmission(false,
                    "TARGET_REBASE_DOWNSTREAM_INJECTION_OR_OVERRIDE_USED",
                    outcome, activation);
        }
        JsonObject importedAdmission = object(summary,
                "executionAdmission");
        if (!bool(summary, "targetReplayValidated", false)
                || !bool(importedAdmission, "required", false)
                || !bool(importedAdmission, "valid", false)
                || bool(importedAdmission, "branchOverrideAccepted", true)
                || !"SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_"
                .concat("OBSERVATION").equals(string(importedAdmission,
                        "authority"))) {
            return targetRebaseAdmission(false,
                    "TARGET_REBASE_UNFORCED_TARGET_ADMISSION_INVALID",
                    outcome, activation);
        }
        JsonObject result = targetRebaseAdmission(true, "", outcome,
                activation);
        result.addProperty("oldActivationId", string(rebase,
                "replacesActivationId"));
        result.addProperty("oldRegionInstanceId", string(rebase,
                "replacesRegionInstanceId"));
        result.addProperty("authority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                        + "TARGET_REPLAY");
        return result;
    }

    private static JsonObject targetRebaseAdmission(
            boolean valid, String reason, ExecutionOutcome outcome,
            JsonObject activation) {
        JsonObject result = new JsonObject();
        result.addProperty("required", true);
        result.addProperty("valid", valid);
        result.addProperty("reason", reason);
        result.addProperty("activationId", string(activation,
                "activationId"));
        result.addProperty("regionId", string(activation, "regionId"));
        result.addProperty("regionInstanceId", string(activation,
                "regionInstanceId"));
        result.addProperty("executionId", outcome == null ? ""
                : outcome.executionId);
        result.addProperty("summaryId", outcome == null
                || outcome.summary == null ? "" : string(outcome.summary,
                "summaryId"));
        result.addProperty("branchOverrideAccepted", false);
        result.addProperty("downstreamInjectionAccepted", false);
        result.addProperty("upstreamReachabilitySupportCount",
                flattenedReachabilitySupport(activation).size());
        result.addProperty("downstreamPlannedModelAssignmentCount",
                array(activation, "modelAssignments").size());
        result.addProperty("downstreamPlannedReplayMaterializationCount",
                array(activation, "replayMaterializations").size());
        result.addProperty("downstreamAppliedModelAssignmentCount",
                outcome == null ? 0 : array(outcome.rawResult,
                        "modelAssignmentsApplied").size());
        result.addProperty("downstreamAppliedReplayMaterializationCount",
                outcome == null ? 0 : array(outcome.rawResult,
                        "replayMaterializationsApplied").size());
        result.addProperty("authority", valid
                ? "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                + "TARGET_REPLAY" : "NONE");
        return result;
    }

    private static JsonObject targetRebaseFormulaRebuild(
            State state, JsonObject rebase, JsonObject activation,
            JsonObject summary) {
        JsonObject result = new JsonObject();
        result.addProperty("ready", false);
        result.addProperty("reason",
                "TARGET_REBASE_FORMULA_REBUILD_REQUIRED");
        JsonObject template = uniqueTargetRoot(state.roots,
                string(rebase, "replacesActivationId"));
        if (summary == null || template == null) return result;
        ConcolicScheduler.FreshTargetQueryResult rebuilt =
                ConcolicScheduler.rebuildFreshObservedTargetQuery(
                        state.regions, state.activations, state.edges,
                        template, activation, summary,
                        string(rebase, "executionId"));
        result.add("schedulerAdmission", rebuilt.admission.deepCopy());
        if (!rebuilt.ready) {
            result.addProperty("reason", rebuilt.reason);
            return result;
        }
        JsonObject query = rebuilt.query.deepCopy();
        String activationId = string(activation, "activationId");
        String regionId = string(activation, "regionId");
        String instance = string(activation, "regionInstanceId");
        String oldInstance = string(rebase, "replacesRegionInstanceId");
        JsonObject context = object(query, "symbolicContext");
        if (query.size() == 0
                || !"FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_PLUS_"
                .concat("OBSERVED_TARGET").equals(string(query,
                        "formulaAuthority"))
                || !string(summary, "summaryId").equals(string(object(
                query, "freshQueryRebuildProvenance"), "freshSummaryId"))
                || !activationId.equals(string(query, "activationId"))
                || !regionId.equals(string(query, "regionId"))
                || !instance.equals(string(query, "regionInstanceId"))
                || !instance.equals(string(context, "regionInstanceId"))
                || !bool(query, "readyForSolver", false)
                || !query.has("originalTargetCondition")
                || !query.has("negatedTargetCondition")
                || !query.has("freshObservedTargetCondition")
                || array(query, "constraints").size() == 0
                || bool(query, "observedOutcome", true) != bool(template,
                "desiredOutcome", false)
                || containsExactString(array(query, "constraints"),
                oldInstance)
                || containsExactString(array(query,
                "engineArrayInputBindings"), oldInstance)
                || containsExactString(context, oldInstance)
                || !targetInstanceReferencesFresh(query, regionId,
                instance)) {
            result.addProperty("reason",
                    "TARGET_REBASE_FRESH_FORMULA_OR_CONTEXT_INVALID");
            return result;
        }
        result.addProperty("ready", true);
        result.addProperty("reason", "");
        result.addProperty("authority",
                string(query, "formulaAuthority"));
        result.add("query", query);
        return result;
    }

    private static boolean containsExactString(JsonElement element,
                                               String expected) {
        if (element == null || element.isJsonNull()
                || expected == null || expected.isEmpty()) return false;
        if (element.isJsonPrimitive()
                && element.getAsJsonPrimitive().isString()) {
            return expected.equals(element.getAsString());
        }
        if (element.isJsonArray()) {
            for (JsonElement value : element.getAsJsonArray()) {
                if (containsExactString(value, expected)) return true;
            }
        } else if (element.isJsonObject()) {
            for (Map.Entry<String, JsonElement> entry
                    : element.getAsJsonObject().entrySet()) {
                if (containsExactString(entry.getValue(), expected)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean targetInstanceReferencesFresh(
            JsonElement element, String regionId, String freshInstance) {
        if (element == null || element.isJsonNull()) return true;
        if (element.isJsonArray()) {
            for (JsonElement value : element.getAsJsonArray()) {
                if (!targetInstanceReferencesFresh(value, regionId,
                        freshInstance)) return false;
            }
            return true;
        }
        if (!element.isJsonObject()) return true;
        JsonObject object = element.getAsJsonObject();
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            JsonElement value = entry.getValue();
            if (entry.getKey().toLowerCase().contains("regioninstance")
                    && value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()) {
                String instance = value.getAsString();
                if (targetInstanceLike(instance, regionId)
                        && !freshInstance.equals(instance)) return false;
            }
            if (!targetInstanceReferencesFresh(value, regionId,
                    freshInstance)) return false;
        }
        return true;
    }

    private static boolean targetInstanceLike(String instance,
                                              String regionId) {
        return instance != null && !instance.isEmpty()
                && regionId != null && !regionId.isEmpty()
                && (instance.contains(regionId + "@")
                || instance.contains(regionId + "#"));
    }

    private static JsonObject rebasedTargetRoot(
            JsonObject rebase, JsonObject activation,
            JsonObject summary, JsonObject admission,
            JsonObject rebuiltQuery) {
        if (summary == null || !bool(admission, "valid", false)) {
            return new JsonObject();
        }
        JsonObject root = rebuiltQuery == null
                ? new JsonObject() : rebuiltQuery.deepCopy();
        root.addProperty("activationId", string(activation,
                "activationId"));
        root.addProperty("regionId", string(activation, "regionId"));
        root.addProperty("regionInstanceId", string(activation,
                "regionInstanceId"));
        root.addProperty("rootMethod", string(activation, "rootMethod"));
        root.addProperty("test", string(activation, "test"));
        root.addProperty("invocationOrdinal", integer(activation,
                "invocationOrdinal", 1));
        root.addProperty("readyForSolver", true);
        root.addProperty("readyForReplay", false);
        root.addProperty("replayAlreadyValidated", true);
        root.addProperty("targetReplayValidated", true);
        root.addProperty("validatedSummaryId", string(summary,
                "summaryId"));
        root.addProperty("replayValidationAuthority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                        + "TARGET_REPLAY");
        root.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        JsonObject context = object(root,
                "symbolicContext").deepCopy();
        context.addProperty("regionId", string(activation, "regionId"));
        context.addProperty("regionInstanceId", string(activation,
                "regionInstanceId"));
        root.add("symbolicContext", context);
        JsonObject validated = new JsonObject();
        validated.addProperty("summaryId", string(summary, "summaryId"));
        validated.addProperty("activationId", string(activation,
                "activationId"));
        validated.addProperty("regionId", string(activation, "regionId"));
        validated.addProperty("regionInstanceId", string(activation,
                "regionInstanceId"));
        validated.addProperty("targetReplayValidated", true);
        validated.addProperty("branchOverrideUsed", false);
        validated.add("executionAdmission", object(summary,
                "executionAdmission").deepCopy());
        root.add("validatedTargetSummary", validated);
        JsonObject provenance = new JsonObject();
        provenance.addProperty("replacesActivationId", string(rebase,
                "replacesActivationId"));
        provenance.addProperty("replacesRegionInstanceId", string(rebase,
                "replacesRegionInstanceId"));
        provenance.addProperty("activationId", string(activation,
                "activationId"));
        provenance.addProperty("regionInstanceId", string(activation,
                "regionInstanceId"));
        provenance.addProperty("transitionExecutionId", string(rebase,
                "executionId"));
        provenance.addProperty("targetReplayExecutionId", string(admission,
                "executionId"));
        provenance.addProperty("upstreamReachabilitySupportCount",
                integer(admission, "upstreamReachabilitySupportCount", 0));
        provenance.addProperty("downstreamInjectionUsed", false);
        provenance.addProperty("branchOverrideUsed", false);
        provenance.addProperty("authority", string(admission, "authority"));
        provenance.addProperty("formulaAuthority", string(root,
                "formulaAuthority"));
        provenance.addProperty("freshSummaryId", string(summary,
                "summaryId"));
        root.add("targetRebaseProvenance", provenance);
        return root;
    }

    private static JsonObject targetRebaseRecord(
            String key, JsonObject rebase, ExecutionOutcome outcome,
            JsonObject admission, String status, String reason) {
        JsonObject record = new JsonObject();
        record.addProperty("schemaVersion", 1);
        record.addProperty("kind", "TARGET_REBASE_RECORD");
        record.addProperty("queryKey", key);
        record.addProperty("requestId", key);
        record.addProperty("status", status);
        record.addProperty("reason", reason);
        record.addProperty("oldActivationId", string(rebase,
                "replacesActivationId"));
        record.addProperty("oldRegionInstanceId", string(rebase,
                "replacesRegionInstanceId"));
        record.addProperty("newActivationId", string(rebase,
                "activationId"));
        record.addProperty("newRegionInstanceId", string(rebase,
                "regionInstanceId"));
        record.addProperty("transitionExecutionId", string(rebase,
                "executionId"));
        record.addProperty("targetReplayExecutionId", outcome == null
                ? "" : outcome.executionId);
        record.addProperty("summaryId", outcome == null
                || outcome.summary == null ? "" : string(outcome.summary,
                "summaryId"));
        record.add("targetRebaseAdmission", admission == null
                ? new JsonObject() : admission.deepCopy());
        return record;
    }

    private static String freshTargetSummaryCollision(
            List<JsonObject> summaries, JsonObject imported) {
        String summaryId = string(imported, "summaryId");
        String activationId = string(imported, "activationId");
        String regionId = string(imported, "regionId");
        String regionInstanceId = string(imported, "regionInstanceId");
        if (summaryId.isEmpty() || activationId.isEmpty()
                || regionId.isEmpty() || regionInstanceId.isEmpty()) {
            return "FRESH_TARGET_SUMMARY_IDENTITY_INCOMPLETE";
        }
        JsonObject match = null;
        for (JsonObject summary : summaries) {
            if (!summaryId.equals(string(summary, "summaryId"))) continue;
            if (match != null) {
                return "FRESH_TARGET_SUMMARY_ID_NOT_UNIQUE";
            }
            match = summary;
        }
        if (match == null) return "";
        if (string(match, "cacheKey").isEmpty()
                || string(imported, "cacheKey").isEmpty()
                || !sameJsonField(match, imported, "cacheKey")
                || !activationId.equals(string(match, "activationId"))
                || !regionId.equals(string(match, "regionId"))
                || !regionInstanceId.equals(string(match,
                "regionInstanceId"))) {
            return "FRESH_TARGET_SUMMARY_ID_COLLISION";
        }
        return "";
    }

    private static boolean sameJsonField(JsonObject left,
                                         JsonObject right,
                                         String field) {
        JsonElement leftValue = left == null ? null : left.get(field);
        JsonElement rightValue = right == null ? null : right.get(field);
        return leftValue == null ? rightValue == null
                : leftValue.equals(rightValue);
    }

    private static List<JsonObject> candidateFreshTargetSummaries(
            List<JsonObject> summaries, JsonObject imported,
            JsonObject rebuiltQuery, JsonObject admission) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject summary : summaries) result.add(summary.deepCopy());
        JsonObject admitted = enrichedFreshTargetSummary(imported,
                rebuiltQuery, admission);
        String summaryId = string(admitted, "summaryId");
        for (int index = 0; index < result.size(); index++) {
            if (summaryId.equals(string(result.get(index), "summaryId"))) {
                result.set(index, admitted);
                return result;
            }
        }
        result.add(admitted);
        return result;
    }

    private static JsonObject enrichedFreshTargetSummary(
            JsonObject imported, JsonObject rebuiltQuery,
            JsonObject admission) {
        JsonObject admitted = imported.deepCopy();
        // directedTargetQuery belongs to the execution-time importer and is
        // intentionally left untouched.  The post-observation formula is a
        // derived artifact with its own authority and digest.
        admitted.add("freshObservedTargetQuery", rebuiltQuery.deepCopy());
        admitted.add("derivedDirectedTargetQuery",
                rebuiltQuery.deepCopy());
        String derivedQuerySha256 = jsonSha256(rebuiltQuery);
        admitted.addProperty("derivedQuerySha256", derivedQuerySha256);
        admitted.addProperty("formulaAuthority", string(rebuiltQuery,
                "formulaAuthority"));
        admitted.addProperty("summaryCacheAdmission",
                "ADMITTED_FRESH_VALIDATED_TARGET");
        JsonObject provenance = new JsonObject();
        provenance.addProperty("authority",
                "FRESH_SUMMARY_PATH_AND_CURRENT_RUNTIME_EDGE_LEDGER");
        provenance.addProperty("targetReplayExecutionId", string(admission,
                "executionId"));
        provenance.addProperty("sourceSummaryId", string(imported,
                "summaryId"));
        provenance.addProperty("sourceCacheKey", string(imported,
                "cacheKey"));
        provenance.addProperty("sourceDirectedTargetQuerySha256",
                jsonSha256(imported.get("directedTargetQuery")));
        provenance.addProperty("derivedQuerySha256",
                derivedQuerySha256);
        provenance.addProperty("edgeAuthority",
                "CURRENT_EDGE_LEDGER_EXACT_TARGET_ENDPOINT_INSTANCE");
        provenance.addProperty("upstreamReachabilitySupportCount",
                integer(admission, "upstreamReachabilitySupportCount", 0));
        provenance.addProperty("downstreamInjectionUsed", false);
        admitted.add("freshTargetSummaryAdmission", provenance);
        return admitted;
    }

    private static String jsonSha256(JsonElement value) {
        if (value == null || value.isJsonNull()) return "";
        return sha256(GSON.toJson(value).getBytes(StandardCharsets.UTF_8));
    }

    private static JsonObject uniqueTargetRoot(List<JsonObject> roots,
                                               String activationId) {
        JsonObject match = null;
        for (JsonObject root : roots) {
            if (!activationId.equals(string(root, "activationId"))) continue;
            if (match != null) return null;
            match = root;
        }
        return match;
    }

    private static int targetRootIndex(List<JsonObject> roots,
                                       String activationId) {
        int match = -1;
        for (int index = 0; index < roots.size(); index++) {
            if (!activationId.equals(string(roots.get(index),
                    "activationId"))) continue;
            if (match >= 0) return -2;
            match = index;
        }
        return match;
    }

    private static boolean replaceTargetRoot(List<JsonObject> roots,
                                             String activationId,
                                             JsonObject replacement) {
        int index = targetRootIndex(roots, activationId);
        if (index < 0) return false;
        roots.set(index, replacement.deepCopy());
        return true;
    }

    private static JsonObject persistedRebasedTargetRoot(
            State state) {
        JsonObject selected = null;
        if (state == null) return new JsonObject();
        for (JsonObject root : state.roots) {
            if (object(root, "targetRebaseProvenance").size() == 0
                    || !"FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                    .concat("TARGET_REPLAY").equals(string(root,
                            "replayValidationAuthority"))
                    || !targetRootRejection(root, state.activations,
                    state.summaries).isEmpty()) continue;
            if (selected != null) return new JsonObject();
            selected = root;
        }
        return selected == null ? new JsonObject() : selected;
    }

    private static boolean targetRootUsesRebase(State state,
                                                JsonObject rebase) {
        if (state == null || !bool(rebase, "ready", false)) return false;
        for (JsonObject root : state.roots) {
            if (string(rebase, "activationId").equals(string(root,
                    "activationId"))
                    && string(rebase, "regionInstanceId").equals(string(
                    root, "regionInstanceId"))
                    && targetRootRejection(root, state.activations,
                    state.summaries).isEmpty()) return true;
        }
        return false;
    }

    private static String targetRootRejection(
            JsonObject root, List<JsonObject> activations,
            List<JsonObject> summaries) {
        String activationId = string(root, "activationId");
        String regionId = string(root, "regionId");
        String regionInstanceId = string(root, "regionInstanceId");
        if (activationId.isEmpty() || regionId.isEmpty()
                || regionInstanceId.isEmpty()
                || string(root, "siteId").isEmpty()
                || integer(root, "occurrence", -1) < 1) {
            return "INCOMPLETE_TARGET_ROOT_IDENTITY";
        }
        if (!RegionCaptureGoal.from(root).isTargetBranch()
                || !bool(root, "readyForSolver", false)
                || !bool(root, "replayAlreadyValidated", false)
                || !bool(root, "targetReplayValidated", false)
                || bool(root, "readyForReplay", true)
                || !("SAME_INSTANCE_IMPORTED_UNFORCED_TARGET_REPLAY".equals(
                string(root, "replayValidationAuthority"))
                || "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                .concat("TARGET_REPLAY").equals(string(root,
                        "replayValidationAuthority")))) {
            return "TARGET_REPLAY_NOT_VALIDATED";
        }
        JsonObject context = object(root, "symbolicContext");
        if (!regionInstanceId.equals(string(context, "regionInstanceId"))) {
            return "TARGET_ROOT_SYMBOLIC_CONTEXT_INSTANCE_MISMATCH";
        }
        String summaryId = string(root, "validatedSummaryId");
        JsonObject summary = object(root, "validatedTargetSummary");
        JsonObject admission = object(summary, "executionAdmission");
        if (summaryId.isEmpty()
                || !summaryId.equals(string(summary, "summaryId"))
                || !activationId.equals(string(summary, "activationId"))
                || !regionId.equals(string(summary, "regionId"))
                || !regionInstanceId.equals(string(summary,
                "regionInstanceId"))) {
            return "VALIDATED_TARGET_SUMMARY_INSTANCE_MISMATCH";
        }
        if (!bool(summary, "targetReplayValidated", false)
                || bool(summary, "branchOverrideUsed", true)
                || !bool(admission, "required", false)
                || !bool(admission, "valid", false)
                || bool(admission, "branchOverrideAccepted", true)
                || !"SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION"
                .equals(string(admission, "authority"))) {
            return "VALIDATED_TARGET_SUMMARY_ADMISSION_INVALID";
        }
        List<JsonObject> exactSummaries = new ArrayList<>();
        if (summaries != null) {
            for (JsonObject candidate : summaries) {
                if (summaryId.equals(string(candidate, "summaryId"))
                        && activationId.equals(string(candidate,
                        "activationId"))
                        && regionId.equals(string(candidate, "regionId"))
                        && regionInstanceId.equals(string(candidate,
                        "regionInstanceId"))) {
                    exactSummaries.add(candidate);
                }
            }
        }
        if (exactSummaries.size() != 1) {
            return exactSummaries.isEmpty()
                    ? "EXACT_TARGET_SUMMARY_MISSING"
                    : "EXACT_TARGET_SUMMARY_NOT_UNIQUE";
        }
        JsonObject selectedSummary = exactSummaries.get(0);
        JsonObject selectedAdmission = object(selectedSummary,
                "executionAdmission");
        if (!bool(selectedSummary, "valid", false)
                || !bool(selectedSummary, "targetReplayValidated", false)
                || bool(selectedSummary, "branchOverrideUsed", true)
                || !RegionCaptureGoal.from(selectedSummary).isTargetBranch()
                || !admission.equals(selectedAdmission)) {
            return "EXACT_TARGET_SUMMARY_ADMISSION_INVALID";
        }
        if ("FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                .concat("TARGET_REPLAY").equals(string(root,
                        "replayValidationAuthority"))) {
            ConcolicSmtComposer.FreshFatalArtifactValidation validation =
                    ConcolicSmtComposer.validateFreshFatalArtifact(root,
                            summaries);
            if (!validation.valid) return validation.reason;
        }
        JsonObject activation = activation(activations, activationId);
        if (activation == null
                || !regionId.equals(string(activation, "regionId"))
                || !regionInstanceId.equals(string(activation,
                "regionInstanceId"))
                || !RegionCaptureGoal.from(activation).isTargetBranch()) {
            return "TARGET_ACTIVATION_INSTANCE_MISMATCH";
        }
        return "";
    }

    private static boolean complete(RecursiveRegionWorklist.Result graph,
                                    RegionPathWorklist.Result paths,
                                    RegionSummaryMerger.Result merged,
                                    List<JsonObject> gaps) {
        return gaps.isEmpty()
                && bool(graph.manifest, "complete", false)
                && bool(paths.manifest, "complete", false)
                && bool(merged.manifest, "complete", false)
                && seedRequests(graph,
                Collections.<String>emptySet()).isEmpty();
    }

    private static List<JsonObject> seedRequests(
            RecursiveRegionWorklist.Result graph, Set<String> attempted) {
        List<JsonObject> candidates = new ArrayList<>();
        for (JsonObject request : graph.upstreamRequests) {
            if (!bool(request, "captureRequired", false)) continue;
            if (!bool(request, "automaticRelationEligible", false)) continue;
            String id = string(request, "requestId");
            if (!attempted.contains(id)) candidates.add(request);
        }
        Collections.sort(candidates, Comparator
                .comparingInt((JsonObject value) -> integer(value,
                        "depth", Integer.MAX_VALUE))
                .thenComparing(value -> string(value, "upstreamRegion"))
                .thenComparing(value -> string(value,
                        "upstreamOutputPort"))
                .thenComparing(value -> string(value, "requestId")));
        List<JsonObject> result = new ArrayList<>();
        Set<String> emittedCaptureKeys = new LinkedHashSet<>();
        for (JsonObject candidate : candidates) {
            String captureKey = string(candidate, "upstreamRegion") + "\n"
                    + string(candidate, "upstreamOutputPort");
            if (emittedCaptureKeys.add(captureKey)) result.add(candidate);
        }
        return result;
    }

    private static boolean hasExecutableSeedRequest(
            RecursiveRegionWorklist.Result graph, Set<String> attempted,
            State state) {
        for (JsonObject request : seedRequests(graph, attempted)) {
            if (seedPrecheckGap(request, state) == null) return true;
        }
        return false;
    }

    private static void refreshSeedPrecheckGaps(
            RecursiveRegionWorklist.Result graph, Set<String> attempted,
            State state, Map<String, JsonObject> gaps) {
        Set<String> current = new LinkedHashSet<>();
        for (JsonObject request : seedRequests(graph, attempted)) {
            String id = string(request, "requestId");
            current.add(id);
            JsonObject gap = seedPrecheckGap(request, state);
            if (gap == null) gaps.remove(id);
            else gaps.put(id, gap);
        }
        gaps.keySet().retainAll(current);
    }

    private static JsonObject seedPrecheckGap(JsonObject request,
                                              State state) {
        String id = string(request, "requestId");
        JsonObject activation = outputActivation(request, state);
        if (activation == null) {
            return gap("MISSING_OUTPUT_ACTIVATION", id);
        }
        if (!bool(activation, "requestedOutputSliceComplete", false)) {
            return gap("MISSING_COMPLETE_OUTPUT_SLICE_PLAN", id);
        }
        if (bool(activation, "requestedOutputCaptureRequired", false)
                && !bool(activation, "requestedOutputCaptureComplete",
                false)) {
            return gap("OUTPUT_CAPTURE_RUNTIME_REFINEMENT_REQUIRED", id);
        }
        if (!bool(activation, "schedulerReady", false)) {
            return gap("OUTPUT_CAPTURE_MATERIALIZATION_NOT_READY", id);
        }
        return null;
    }

    private static int countRequests(RecursiveRegionWorklist.Result graph,
                                     boolean automaticallyEligible) {
        int result = 0;
        for (JsonObject request : graph.upstreamRequests) {
            if (bool(request, "automaticRelationEligible", false)
                    == automaticallyEligible) result++;
        }
        return result;
    }

    static JsonObject outputActivation(JsonObject request, State state) {
        String region = string(request, "upstreamRegion");
        String outputPort = string(request, "upstreamOutputPort");
        List<JsonObject> candidates = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        String exactSourceActivation = RegionCaptureGoal.from(request)
                .isTransitionDiscovery()
                ? string(request, "sourceActivationId") : "";
        if (!exactSourceActivation.isEmpty()) {
            JsonObject exact = activation(state.activations,
                    exactSourceActivation);
            if (exact == null || !region.equals(string(exact,
                    "regionId"))) return null;
            candidates.add(exact);
            seen.add(exactSourceActivation);
        }
        for (JsonElement reference : exactSourceActivation.isEmpty()
                ? array(request, "upstreamActivations") : new JsonArray()) {
            if (!reference.isJsonObject()) continue;
            JsonObject candidate = activation(state.activations,
                    string(reference.getAsJsonObject(), "activationId"));
            if (candidate == null) continue;
            String id = string(candidate, "activationId");
            if (seen.add(id)) candidates.add(candidate);
        }
        if (candidates.isEmpty() && exactSourceActivation.isEmpty()) {
            for (JsonObject candidate : state.activations) {
                if (region.equals(string(candidate, "regionId"))) {
                    String id = string(candidate, "activationId");
                    if (seen.add(id)) candidates.add(candidate);
                }
            }
        }
        JsonObject selected = null;
        int selectedScore = Integer.MIN_VALUE;
        for (JsonObject candidate : candidates) {
            int score = outputActivationScore(candidate, request, state,
                    region, outputPort);
            if (selected == null || score > selectedScore) {
                selected = candidate;
                selectedScore = score;
            }
        }
        if (selected == null) return null;
        return canonicalOutputActivation(selected, request, state, region,
                outputPort);
    }

    private static int outputActivationScore(JsonObject candidate,
                                             JsonObject request,
                                             State state, String region,
                                             String outputPort) {
        int score = region.equals(string(candidate, "regionId")) ? 1 : 0;
        boolean outputClosure = RegionCaptureGoal.from(candidate)
                .isOutputClosure();
        boolean outputMatch = requestedOutputMatches(candidate, state.regions,
                region, outputPort);
        if (outputClosure && outputMatch) score += 100;
        else if (outputMatch) score += 40;
        else if (outputClosure) score += 20;
        if (targetsDownstreamInstance(candidate, request, outputPort)) {
            score += 50;
        }
        if (bool(candidate, "requestedOutputSliceComplete", false)) {
            score += 10;
        }
        if (bool(candidate, "schedulerReady", false)) score += 2;
        return score;
    }

    private static boolean targetsDownstreamInstance(JsonObject candidate,
                                                     JsonObject request,
                                                     String outputPort) {
        String downstream = string(request, "downstreamRegionInstance");
        if (downstream.isEmpty()) return false;
        String requestedEdge = string(request, "edgeId");
        String requestedInput = string(request, "downstreamInputPort");
        for (JsonElement element : array(candidate, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!downstream.equals(string(binding, "toRegionInstance"))) {
                continue;
            }
            if (!requestedEdge.isEmpty()
                    && !requestedEdge.equals(string(binding, "edgeId"))) {
                continue;
            }
            if (!endpointMatches(outputPort, binding, "fromOutputPort",
                    "fromOutputCell")) {
                continue;
            }
            if (!endpointMatches(requestedInput, binding, "toInputPort",
                    "toInputCell")) {
                continue;
            }
            return true;
        }
        return false;
    }

    private static boolean endpointMatches(String requested,
                                           JsonObject binding,
                                           String portField,
                                           String cellField) {
        if (requested.isEmpty()) return true;
        String expected = canonicalPort(requested);
        return expected.equals(canonicalPort(string(binding, portField)))
                || expected.equals(canonicalPort(string(binding,
                cellField)));
    }

    private static JsonObject canonicalOutputActivation(JsonObject selected,
                                                        JsonObject request,
                                                        State state,
                                                        String region,
                                                        String outputPort) {
        JsonObject result = selected.deepCopy();
        String id = "ACT.OUTPUT." + shortHash(string(request, "requestId"));
        result.addProperty("selectedUpstreamActivationId",
                string(selected, "activationId"));
        result.addProperty("activationId", id);
        result.add("captureGoal", (RegionCaptureGoal.from(request)
                .isTransitionDiscovery()
                ? RegionCaptureGoal.transitionDiscovery()
                : RegionCaptureGoal.outputClosure()).toJson());
        result.remove("summaryMode");
        result.remove("targetBranch");
        result.remove("forcedBranches");
        result.remove("replayMaterializations");
        result.remove("modelAssignments");
        JsonObject output = resolveOutput(state.regions, region, outputPort);
        if (output.size() == 0) {
            output.addProperty("portId", outputPort);
        }
        output.addProperty("selectionAuthority",
                "VALIDATED_UPSTREAM_REGION_EDGE");
        result.add("requestedOutput", output);
        applyOutputClosure(result, selected, state.regions, region,
                outputPort, output);
        result.addProperty("captureOnly", true);
        result.addProperty("branchOverrideProhibited", true);
        return ConcolicScheduler.prepareOutputCapture(result,
                state.staticGraph);
    }

    /** Ensures a synthetic ACT.OUTPUT never inherits another port's slice. */
    private static void applyOutputClosure(JsonObject result,
                                           JsonObject selected,
                                           List<JsonObject> regions,
                                           String regionId,
                                           String requestedPortOrCell,
                                           JsonObject requestedOutput) {
        JsonObject selectedRequested = object(selected, "requestedOutput");
        JsonObject selectedSlice = object(selected, "requestedOutputSlice");
        String resolvedPort = string(requestedOutput, "portId");
        if (resolvedPort.isEmpty()) resolvedPort = requestedPortOrCell;
        String selectedEndpoint = string(selectedRequested, "portId");
        if (selectedEndpoint.isEmpty()) {
            selectedEndpoint = string(selectedRequested, "cell");
        }
        String selectedSlicePort = string(selectedSlice, "outputPort");
        boolean legacyUnscopedSlice = selectedEndpoint.isEmpty()
                && selectedSlicePort.isEmpty()
                && bool(selected, "requestedOutputSliceComplete", false)
                && !"SINK_STATE".equals(string(requestedOutput, "kind"));
        boolean sameSelectedOutput = resolvedPort.equals(selectedEndpoint)
                && resolvedPort.equals(selectedSlicePort)
                || legacyUnscopedSlice;
        if (sameSelectedOutput) {
            result.add("requestedOutputSlice", selectedSlice.deepCopy());
            result.addProperty("requestedOutputSliceComplete", bool(selected,
                    "requestedOutputSliceComplete", false));
            result.add("requestedOutputCapture", array(selected,
                    "requestedOutputCapture").deepCopy());
            result.addProperty("requestedOutputCaptureRequired", bool(selected,
                    "requestedOutputCaptureRequired", false));
            result.addProperty("requestedOutputCaptureComplete", bool(selected,
                    "requestedOutputCaptureComplete",
                    !bool(selected, "requestedOutputCaptureRequired", false)));
            copyIfPresent(result, selected,
                    "requestedOutputCaptureRefinementRequired");
            copyIfPresent(result, selected,
                    "requestedOutputCaptureTemplateReady");
            copyIfPresent(result, selected,
                    "requestedOutputCaptureTemplateAuthority");
            copyIfPresent(result, selected,
                    "requestedOutputCaptureRefinementPolicy");
            copyIfPresent(result, selected, "outputCaptureGap");
            return;
        }

        JsonObject staticSlice = new JsonObject();
        for (JsonObject region : regions) {
            if (!regionId.equals(string(region, "regionId"))) continue;
            for (JsonElement element : array(region, "outputSlices")) {
                if (!element.isJsonObject()) continue;
                JsonObject candidate = element.getAsJsonObject();
                if (resolvedPort.equals(string(candidate, "outputPort"))
                        || requestedPortOrCell.equals(string(candidate,
                        "outputCell"))) {
                    staticSlice = candidate.deepCopy();
                    break;
                }
            }
        }
        result.add("requestedOutputSlice", staticSlice);
        boolean sliceComplete = staticSlice.size() > 0
                && bool(staticSlice, "complete", false);
        result.addProperty("requestedOutputSliceComplete", sliceComplete);
        result.addProperty("requestedOutputSlicePolicy", string(staticSlice,
                "selection"));
        JsonArray staticCaptures = array(staticSlice,
                "captureBindings").deepCopy();
        result.add("requestedOutputCapture", staticCaptures);
        boolean captureRequired = bool(staticSlice,
                "captureBindingsRequired", false);
        result.addProperty("requestedOutputCaptureRequired", captureRequired);
        // Static alternatives do not identify the concrete invocation
        // occurrence. Only a runtime-refined activation can authorize replay.
        result.addProperty("requestedOutputCaptureComplete",
                !captureRequired && bool(staticSlice,
                        "captureBindingsComplete", true));
        if (captureRequired) {
            boolean templateReady = sliceComplete
                    && bool(staticSlice, "captureBindingsComplete", false)
                    && staticOutputCaptureTemplateReady(staticCaptures);
            result.addProperty("requestedOutputCaptureRefinementRequired",
                    true);
            result.addProperty("requestedOutputCaptureTemplateReady",
                    templateReady);
            result.addProperty("requestedOutputCaptureTemplateAuthority",
                    templateReady
                            ? "STATIC_EXACT_OUTPUT_ENDPOINT_RUNTIME_"
                            + "OCCURRENCE_PENDING"
                            : "NONE");
            result.addProperty("requestedOutputCaptureRefinementPolicy",
                    "FRESH_RUNTIME_UNIQUE_ENDPOINT_LAST_WRITE_OR_EXACT_"
                            + "CALL_ARGUMENT_THEN_EXACT_REPLAY");
            result.addProperty("outputCaptureGap", templateReady
                    ? "RUNTIME_OUTPUT_OCCURRENCE_REFINEMENT_PENDING"
                    : "STATIC_OUTPUT_CAPTURE_TEMPLATE_INVALID");
        }
    }

    private static boolean staticOutputCaptureTemplateReady(
            JsonArray captures) {
        if (captures == null || captures.size() != 1
                || !captures.get(0).isJsonObject()) return false;
        JsonObject capture = captures.get(0).getAsJsonObject();
        if (integer(capture, "occurrence", -1) != 0
                || !"RUNTIME_INSTANCE_REFINEMENT_REQUIRED".equals(
                string(capture, "occurrenceAuthority"))
                || string(capture, "captureBindingId").isEmpty()
                || string(capture, "outputPort").isEmpty()
                || string(capture, "outputCell").isEmpty()
                || string(capture, "siteId").isEmpty()
                || integer(capture, "unitIndex", -1) < 0) return false;
        String kind = string(capture, "captureKind");
        if (kind.isEmpty()) kind = "CALL_ARGUMENT";
        if ("FIELD_ASSIGNMENT_RHS".equals(kind)) {
            return !string(capture, "method").isEmpty()
                    && !string(capture, "fieldSignature").isEmpty()
                    && "STATIC_EXACT_INSTANCE_FIELD_ASSIGNMENT_RHS".equals(
                    string(capture, "bindingAuthority"));
        }
        return "CALL_ARGUMENT".equals(kind)
                && !string(capture, "callerMethod").isEmpty()
                && !string(capture, "calleeMethod").isEmpty()
                && integer(capture, "argumentIndex", -1) >= 0;
    }

    private static void copyIfPresent(JsonObject target, JsonObject source,
                                      String field) {
        if (source != null && source.has(field)) {
            target.add(field, source.get(field).deepCopy());
        }
    }

    private static boolean requestedOutputMatches(JsonObject activation,
                                                  List<JsonObject> regions,
                                                  String region,
                                                  String outputPort) {
        JsonObject requested = object(activation, "requestedOutput");
        JsonObject resolved = resolveOutput(regions, region, outputPort);
        String expectedPort = string(resolved, "portId");
        String expectedCell = string(resolved, "cell");
        return outputPort.equals(string(requested, "portId"))
                || outputPort.equals(string(requested, "cell"))
                || !expectedPort.isEmpty() && expectedPort.equals(
                string(requested, "portId"))
                || !expectedCell.isEmpty() && expectedCell.equals(
                string(requested, "cell"));
    }

    private static JsonObject resolveOutput(List<JsonObject> regions,
                                            String regionId,
                                            String requestedPortOrCell) {
        for (JsonObject region : regions) {
            if (!regionId.equals(string(region, "regionId"))) continue;
            for (JsonElement element : array(region, "outputs")) {
                if (!element.isJsonObject()) continue;
                JsonObject output = element.getAsJsonObject();
                if (requestedPortOrCell.equals(string(output, "portId"))
                        || requestedPortOrCell.equals(string(output,
                        "cell"))) return output.deepCopy();
            }
        }
        return new JsonObject();
    }

    /**
     * Builds the one-row, input-model-only replay plan for a solved path
     * task.  Package visibility lets the standalone path-flip planner reuse
     * exactly the same activation contract as the full campaign runner.
     */
    static JsonObject replayActivation(JsonObject task,
                                       JsonObject source,
                                       JsonArray assignments) {
        JsonObject result = source.deepCopy();
        String pathId = shortHash(string(task, "queryKey"));
        String activationId = "ACT.PATH." + pathId;
        String scheduleId = "SCHEDULE.PATH." + pathId;
        result.addProperty("activationId", activationId);
        // A solver replay is a new executable activation, not another use of
        // the seed row copied above.  Give its one-row activation bundle a
        // self-consistent identity so static instrumentation and runtime
        // selection cannot accidentally bind the replay to the seed's
        // schedule or bundle root.
        result.addProperty("scheduleId", scheduleId);
        result.addProperty("executionPhase", "REPLAY_OUTPUT_PATH_FLIP");
        result.addProperty("activationSelectionRequired", activationId);
        result.addProperty("activationBundleRootActivationId",
                activationId);
        result.addProperty("activationBundleScheduleId", scheduleId);
        result.addProperty("activationBundleSize", 1);
        result.addProperty("activationBundleIndex", 0);
        result.addProperty("activationBundleMemberRole", "PRIMARY");
        result.remove("reachabilitySupportForActivationId");
        result.add("captureGoal", (RegionCaptureGoal.from(task)
                .isTransitionDiscovery()
                ? RegionCaptureGoal.transitionDiscovery()
                : RegionCaptureGoal.outputClosure()).toJson());
        result.add("modelAssignments", assignments.deepCopy());
        JsonObject target = new JsonObject();
        target.addProperty("siteId", string(task, "flipSite"));
        target.addProperty("occurrence", integer(task,
                "flipOccurrence", 1));
        target.addProperty("desiredOutcome", bool(task,
                "desiredOutcome", false));
        target.addProperty("validationOnly", true);
        target.addProperty("branchOverrideAllowed", false);
        if (hasBoolean(task, "concreteGuardReplayProofRequired")) {
            target.addProperty("concreteGuardReplayProofRequired",
                    bool(task, "concreteGuardReplayProofRequired", false));
        }
        result.add("targetBranch", target);
        result.add("expectedBranchPrefix", array(task,
                "expectedBranchPrefix").deepCopy());
        result.addProperty("pathQueryKey", string(task, "queryKey"));
        result.add("pathReplayConstraints", array(task,
                "constraints").deepCopy());
        JsonElement negated = task.get("negatedCondition");
        if (negated != null && negated.isJsonObject()) {
            result.add("pathReplayNegatedCondition", negated.deepCopy());
        } else {
            result.remove("pathReplayNegatedCondition");
        }
        result.addProperty("pathReplayTargetConditionIndex", integer(task,
                "conditionIndex", -1));
        result.add("concreteGuardReplayProofs",
                concreteGuardReplayProofs(task, activationId,
                        assignments));
        // A single scheduled-target proof cannot certify NULL-dependent
        // prefix guards.  Do not emit or trust the superseded singleton
        // envelope.
        result.remove("concreteGuardReplayProof");
        result.addProperty("branchOverrideProhibited", true);
        result.remove("forcedBranches");
        result.remove("replayMaterializations");
        result.remove("summaryMode");
        return result;
    }

    /**
     * Issues a narrowly scoped proof catalog for every replay guard that can
     * legitimately have no symbolic VM path-condition element: an exact
     * solver assignment changed a declared reference input to Java null and
     * the satisfied prefix/target constraint is the exact equality between
     * that engine symbol and the VM null literal.  Semantic path constraints
     * without a branch event remain in {@code constraints} but deliberately
     * receive no proof.  The runtime independently joins each proof to its
     * exact VM event and applied model-assignment row before the importer can
     * treat it as path evidence.
     */
    private static JsonArray concreteGuardReplayProofs(
            JsonObject task, String activationId, JsonArray assignments) {
        JsonArray result = new JsonArray();
        if (task == null || assignments == null
                || activationId == null || activationId.isEmpty()
                || string(task, "queryKey").isEmpty()) {
            return result;
        }

        // Duplicate assignment keys make an applied-row join ambiguous even
        // when only one of the duplicate rows happens to mention a guard.
        Set<String> assignmentKeys = new LinkedHashSet<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) return result;
            String key = modelAssignmentKey(element.getAsJsonObject());
            if (key.isEmpty() || !assignmentKeys.add(key)) return result;
        }

        JsonArray constraints = array(task, "constraints");
        JsonArray prefix = array(task, "prefix");
        JsonArray expectedPrefix = array(task, "expectedBranchPrefix");
        JsonElement targetElement = task.get("negatedCondition");
        int targetConditionIndex = integer(task, "conditionIndex", -1);
        if (targetElement == null || !targetElement.isJsonObject()
                || constraints.size() != prefix.size() + 1
                || targetConditionIndex != prefix.size()
                || !sameJson(constraints.get(constraints.size() - 1),
                targetElement)) {
            return result;
        }
        for (int index = 0; index < prefix.size(); index++) {
            if (!sameJson(prefix.get(index), constraints.get(index))) {
                return new JsonArray();
            }
        }

        Set<String> proofEvents = new LinkedHashSet<>();
        Set<Integer> mappedPrefixConditions = new LinkedHashSet<>();
        int previousSourceCondition = -1;
        for (int ordinal = 0; ordinal < expectedPrefix.size(); ordinal++) {
            JsonElement expectedElement = expectedPrefix.get(ordinal);
            if (!expectedElement.isJsonObject()) {
                return new JsonArray();
            }
            JsonObject expected = expectedElement.getAsJsonObject();
            String siteId = string(expected, "siteId");
            int occurrence = integer(expected, "occurrence", -1);
            int sourceConditionIndex = integer(expected,
                    "conditionIndex", -1);
            if (siteId.isEmpty() || occurrence <= 0
                    || sourceConditionIndex < 0
                    || sourceConditionIndex >= prefix.size()
                    || sourceConditionIndex <= previousSourceCondition
                    || !mappedPrefixConditions.add(sourceConditionIndex)
                    || !hasBoolean(expected, "outcome")
                    || expected.has("concreteGuardReplayProofRequired")
                    && !hasBoolean(expected,
                    "concreteGuardReplayProofRequired")) {
                return new JsonArray();
            }
            previousSourceCondition = sourceConditionIndex;
            if (!exactBoolean(expected,
                    "concreteGuardReplayProofRequired", true)) {
                // Ordinary VM-symbolic guards already carry their exact path
                // condition.  A concrete-guard certificate is reserved for
                // a mapping that the importer previously synthesized from a
                // conditionless, exactly attested NULL branch event.
                continue;
            }
            JsonElement conditionElement = constraints.get(
                    sourceConditionIndex);
            if (!conditionElement.isJsonObject()) return new JsonArray();
            int witnessCount = exactNullGuardWitnessCount(
                    conditionElement.getAsJsonObject(), assignments);
            if (witnessCount > 1) return new JsonArray();
            JsonObject proof = concreteGuardReplayProof(
                    conditionElement.getAsJsonObject(), task,
                    activationId, assignments, "PREFIX", siteId,
                    occurrence, bool(expected, "outcome", false),
                    sourceConditionIndex, sourceConditionIndex, ordinal);
            if (proof != null) {
                String event = siteId + "\u0000" + occurrence;
                if (!proofEvents.add(event)) return new JsonArray();
                result.add(proof);
            }
        }
        for (int index = 0; index < prefix.size(); index++) {
            JsonElement condition = constraints.get(index);
            if (condition.isJsonObject()
                    && exactNullGuardWitnessCount(
                    condition.getAsJsonObject(), assignments) > 0
                    && !mappedPrefixConditions.contains(index)) {
                // Even a VM-symbolic NULL condition must map to one exact
                // branch event.  The per-event marker decides whether that
                // event needs a concrete-guard certificate; it does not make
                // an unmapped path constraint admissible.
                return new JsonArray();
            }
        }
        String targetSite = string(task, "flipSite");
        int targetOccurrence = integer(task, "flipOccurrence", -1);
        if (targetSite.isEmpty() || targetOccurrence <= 0
                || !hasBoolean(task, "desiredOutcome")
                || task.has("concreteGuardReplayProofRequired")
                && !hasBoolean(task,
                "concreteGuardReplayProofRequired")) {
            return new JsonArray();
        }
        if (!exactBoolean(task, "concreteGuardReplayProofRequired", true)) {
            return result;
        }
        if (exactNullGuardWitnessCount(targetElement.getAsJsonObject(),
                assignments) > 1) {
            return new JsonArray();
        }
        JsonObject targetProof = concreteGuardReplayProof(
                targetElement.getAsJsonObject(), task, activationId,
                assignments, "TARGET", targetSite, targetOccurrence,
                bool(task, "desiredOutcome", false),
                targetConditionIndex, constraints.size() - 1, -1);
        if (targetProof != null) {
            String event = targetSite + "\u0000" + targetOccurrence;
            if (!proofEvents.add(event)) return new JsonArray();
            result.add(targetProof);
        }
        return result;
    }

    private static int exactNullGuardWitnessCount(
            JsonObject condition, JsonArray assignments) {
        int count = 0;
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if (!exactNullModelAssignment(assignment)) continue;
            String engineSymbol = string(assignment, "engineSymbol");
            if (!exactSatisfiedNullEquality(condition, engineSymbol)) {
                continue;
            }
            JsonObject target = object(assignment, "target");
            if (!declaresReferenceValue(target)
                    || !string(assignment, "inputSymbol").equals(
                    string(target, "symbol"))) {
                continue;
            }
            boolean stringTarget = declaresJavaString(target);
            String encodingAuthority = string(assignment, stringTarget
                    ? "nullableStringEncodingAuthority"
                    : "referenceNullnessEncodingAuthority");
            if ((stringTarget ? NULLABLE_STRING_ENCODING_AUTHORITY
                    : REFERENCE_NULLNESS_ENCODING_AUTHORITY).equals(
                    encodingAuthority)
                    && bool(assignment, "modelIsNull", false)
                    && !string(assignment,
                    "nullnessSolverSymbol").isEmpty()) {
                count++;
            }
        }
        return count;
    }

    private static JsonObject concreteGuardReplayProof(
            JsonObject condition, JsonObject task, String activationId,
            JsonArray assignments, String proofRole, String siteId,
            int occurrence, boolean outcome, int sourceConditionIndex,
            int constraintIndex, int expectedPrefixOrdinal) {
        JsonObject selected = null;
        JsonObject selectedTarget = null;
        String selectedSymbol = "";
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if (!exactNullModelAssignment(assignment)) continue;
            String engineSymbol = string(assignment, "engineSymbol");
            if (!exactSatisfiedNullEquality(condition, engineSymbol)) {
                continue;
            }
            JsonObject target = object(assignment, "target");
            if (!declaresReferenceValue(target)
                    || !string(assignment, "inputSymbol").equals(
                    string(target, "symbol"))) {
                continue;
            }
            boolean stringTarget = declaresJavaString(target);
            String encodingAuthority = string(assignment, stringTarget
                    ? "nullableStringEncodingAuthority"
                    : "referenceNullnessEncodingAuthority");
            if (!(stringTarget ? NULLABLE_STRING_ENCODING_AUTHORITY
                    : REFERENCE_NULLNESS_ENCODING_AUTHORITY).equals(
                    encodingAuthority)
                    || !bool(assignment, "modelIsNull", false)
                    || string(assignment,
                    "nullnessSolverSymbol").isEmpty()) {
                continue;
            }
            if (selected != null) {
                // More than one NULL assignment capable of witnessing the
                // same guard is ambiguous and must remain ordinary
                // conditionless concrete execution, not certified evidence.
                return null;
            }
            selected = assignment;
            selectedTarget = target;
            selectedSymbol = engineSymbol;
        }
        if (selected == null) return null;

        String pathQueryKey = string(task, "queryKey");
        if (activationId.isEmpty() || siteId.isEmpty()
                || occurrence <= 0 || pathQueryKey.isEmpty()
                || !("PREFIX".equals(proofRole)
                || "TARGET".equals(proofRole))
                || sourceConditionIndex < 0 || constraintIndex < 0
                || "PREFIX".equals(proofRole)
                && expectedPrefixOrdinal < 0
                || "TARGET".equals(proofRole)
                && expectedPrefixOrdinal != -1) {
            return null;
        }
        String assignmentKey = modelAssignmentKey(selected);
        if (assignmentKey.isEmpty()) return null;

        JsonObject proof = new JsonObject();
        proof.addProperty("schemaVersion", 1);
        proof.addProperty("kind", CONCRETE_GUARD_PROOF_KIND);
        proof.addProperty("authority", CONCRETE_GUARD_PROOF_AUTHORITY);
        proof.addProperty("activationId", activationId);
        proof.addProperty("pathQueryKey", pathQueryKey);
        proof.addProperty("proofRole", proofRole);
        proof.addProperty("sourceConditionIndex", sourceConditionIndex);
        proof.addProperty("constraintIndex", constraintIndex);
        proof.addProperty("expectedBranchPrefixOrdinal",
                expectedPrefixOrdinal);
        proof.addProperty("siteId", siteId);
        proof.addProperty("occurrence", occurrence);
        proof.addProperty("outcome", outcome);
        proof.addProperty("modelAssignmentKey", assignmentKey);
        proof.addProperty("engineSymbol", selectedSymbol);
        proof.addProperty("inputSymbol", string(selected, "inputSymbol"));
        proof.addProperty("targetActionSha256", sha256(selectedTarget
                .toString().getBytes(StandardCharsets.UTF_8)));
        proof.add("condition", condition.deepCopy());
        proof.addProperty("conditionSha256", sha256(condition.toString()
                .getBytes(StandardCharsets.UTF_8)));
        proof.addProperty("requiresExactVmBranchEvent", true);
        proof.addProperty("requiresZeroPathConditionSuffix", true);
        proof.addProperty("requiresUniqueAppliedNullModelAssignment", true);
        proof.addProperty("branchOverrideProhibited", true);
        return proof;
    }

    private static boolean sameJson(JsonElement left, JsonElement right) {
        return left != null && right != null
                && left.toString().equals(right.toString());
    }

    private static boolean exactNullModelAssignment(JsonObject assignment) {
        return assignment != null
                && "NULL".equals(string(assignment, "valueType"))
                && "null".equals(string(assignment, "value"))
                && "Z3_PATH_FLIP_MODEL".equals(string(assignment,
                "authority"))
                && bool(assignment, "materializeAtRealDefinition", false)
                && !string(assignment, "engineSymbol").isEmpty()
                && !string(assignment, "solverSymbol").isEmpty()
                && !string(assignment, "inputSymbol").isEmpty();
    }

    private static boolean exactSatisfiedNullEquality(
            JsonObject condition, String engineSymbol) {
        if (condition == null || engineSymbol == null
                || engineSymbol.isEmpty()
                || !"BinaryExpression".equals(string(condition, "_type"))
                || !"==".equals(string(condition, "_op"))) {
            return false;
        }
        JsonObject left = object(condition, "_left");
        JsonObject right = object(condition, "_right");
        return exactEngineSymbol(left, engineSymbol) && exactNull(right)
                || exactNull(left) && exactEngineSymbol(right, engineSymbol);
    }

    private static boolean exactEngineSymbol(JsonObject expression,
                                             String engineSymbol) {
        return expression != null
                && "SymbolExpression".equals(string(expression, "_type"))
                && engineSymbol.equals(string(expression, "_exp"));
    }

    private static boolean exactNull(JsonObject expression) {
        return expression != null
                && "SymbolExpression".equals(string(expression, "_type"))
                && "N".equals(string(expression, "_exp"));
    }

    private static boolean declaresReferenceValue(JsonObject action) {
        String type = firstNonBlank(string(action, "javaType"),
                string(action, "inputJavaType"),
                declaredCellType(string(action, "cell")));
        if (type.isEmpty()) return false;
        String normalized = type.trim();
        if (normalized.startsWith("[") || normalized.endsWith("[]")
                || normalized.startsWith("L")
                && normalized.endsWith(";")) {
            return true;
        }
        if (normalized.length() == 1
                && "ZBCSIJFDV".contains(normalized)) {
            return false;
        }
        if (Arrays.asList("boolean", "byte", "char", "short", "int",
                "long", "float", "double", "void").contains(normalized)) {
            return false;
        }
        // Planner-authored Java reference types are fully qualified binary,
        // internal, or source names.  Do not treat an unknown empty/scalar
        // label as reference evidence.
        return normalized.indexOf('.') >= 0 || normalized.indexOf('/') >= 0
                || normalized.indexOf('$') >= 0;
    }

    private static boolean declaresJavaString(JsonObject action) {
        String type = firstNonBlank(string(action, "javaType"),
                string(action, "inputJavaType"),
                declaredCellType(string(action, "cell")))
                .replace('.', '/');
        return "java/lang/String".equals(type)
                || "Ljava/lang/String;".equals(type);
    }

    private static String declaredCellType(String cell) {
        String value = cell == null ? "" : cell.trim();
        if (!value.startsWith("<")) return "";
        int colon = value.indexOf(':');
        int space = colon < 0 ? -1 : value.indexOf(' ', colon + 2);
        return colon < 0 || space < 0 ? ""
                : value.substring(colon + 1, space).trim();
    }

    private static String modelAssignmentKey(JsonObject assignment) {
        String dynamic = string(assignment, "dynamicBindingId");
        if (!dynamic.isEmpty()) return dynamic;
        String engine = string(assignment, "engineSymbol");
        if (!engine.isEmpty()) return engine;
        String input = string(assignment, "inputSymbol");
        if (input.isEmpty()) return "";
        StringBuilder path = new StringBuilder();
        for (JsonElement element : array(assignment,
                "materializationPath")) {
            if (!element.isJsonPrimitive()) return "";
            if (path.length() > 0) path.append('.');
            path.append(element.getAsString());
        }
        return input + ":" + path;
    }

    private static String firstNonBlank(String... values) {
        if (values == null) return "";
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return "";
    }

    static JsonObject replayValidationPlan(JsonObject task,
                                           JsonArray assignments) {
        JsonObject result = task == null
                ? new JsonObject() : task.deepCopy();
        result.add("modelAssignments", assignments == null
                ? new JsonArray() : assignments.deepCopy());
        return result;
    }

    /**
     * Campaign-local replay admission.  The ordinary replay validator owns
     * assignment, output, and unforced-branch validation; the exact schedule
     * gate additionally proves that the retained prefix occurred in trace
     * order and that the unique scheduled target produced the requested
     * outcome.  This intentionally mirrors the in-memory portion of
     * {@link ConcolicPathReplayVerifier} so a campaign cannot admit evidence
     * that the standalone gate would reject.
     */
    static JsonObject validateReplayAdmission(JsonObject task,
                                               JsonObject rawResult,
                                               JsonObject summary) {
        JsonObject result = ConcolicReplayValidator.validate(task,
                rawResult, summary);
        JsonObject exact = exactReplayScheduleAdmission(task, rawResult);
        JsonObject scheduled = object(exact,
                "scheduledTargetValidation");
        JsonObject prefix = object(exact, "orderedPrefixValidation");
        result.add("scheduledTargetValidation", scheduled.deepCopy());
        result.add("orderedPrefixValidation", prefix.deepCopy());
        result.addProperty("exactReplayScheduleValidated",
                bool(exact, "valid", false));

        JsonArray failures = array(result, "failures");
        int exactFailureCount = 0;
        if (!bool(scheduled, "valid", false)) {
            failures.add("SCHEDULED_FLIP_TARGET_NOT_EXACT");
            exactFailureCount++;
        }
        if (!bool(prefix, "valid", false)) {
            failures.add("REPLAY_BRANCH_PREFIX_NOT_EXACT");
            exactFailureCount++;
        }
        int baseOutputFailures = integer(result,
                "outputClosureFailureCount", 0);
        int baseNonOutputFailures = integer(result,
                "nonOutputClosureFailureCount", 0);
        boolean valid = bool(result, "valid", false)
                && exactFailureCount == 0;
        result.addProperty("exactReplayScheduleFailureCount",
                exactFailureCount);
        result.addProperty("failureCount", failures.size());
        result.addProperty("nonOutputClosureFailureCount",
                baseNonOutputFailures + exactFailureCount);
        result.addProperty("outputClosureFailureCount",
                baseOutputFailures);
        result.addProperty("prefixValidated",
                bool(result, "prefixValidated", false)
                        && bool(prefix, "valid", false));
        result.addProperty("flippedBranchValidated",
                bool(result, "flippedBranchValidated", false)
                        && bool(scheduled, "valid", false));
        result.addProperty("branchAndInputReplayValidated",
                bool(result, "branchAndInputReplayValidated", false)
                        && exactFailureCount == 0);
        result.addProperty("valid", valid);
        result.addProperty("status", valid
                ? "VALIDATED_EXACT_UNFORCED_REPLAY"
                : "REPLAY_REJECTED");
        result.addProperty("admissionAuthority", valid
                ? "SOLVER_MODEL_PLUS_ORDERED_PREFIX_AND_EXACT_"
                + "SCHEDULED_TARGET_V1" : "NONE");
        return result;
    }

    static JsonObject exactReplayScheduleAdmission(JsonObject task,
                                                   JsonObject rawResult) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "EXACT_REPLAY_SCHEDULE_ADMISSION");
        JsonObject scheduled = exactScheduledTarget(task, rawResult);
        JsonObject prefix = exactOrderedPrefix(task, rawResult);
        result.add("scheduledTargetValidation", scheduled);
        result.add("orderedPrefixValidation", prefix);
        JsonArray failures = new JsonArray();
        if (!bool(scheduled, "valid", false)) {
            failures.add("SCHEDULED_FLIP_TARGET_NOT_EXACT");
        }
        if (!bool(prefix, "valid", false)) {
            failures.add("REPLAY_BRANCH_PREFIX_NOT_EXACT");
        }
        result.add("failures", failures);
        result.addProperty("failureCount", failures.size());
        result.addProperty("valid", failures.size() == 0);
        result.addProperty("status", failures.size() == 0
                ? "VALIDATED_EXACT_REPLAY_SCHEDULE"
                : "EXACT_REPLAY_SCHEDULE_REJECTED");
        return result;
    }

    private static JsonObject exactScheduledTarget(JsonObject task,
                                                   JsonObject rawResult) {
        String site = string(task, "flipSite");
        int occurrence = integer(task, "flipOccurrence", -1);
        int condition = integer(task, "conditionIndex", -1);
        boolean desired = bool(task, "desiredOutcome", false);
        List<JsonObject> matches = new ArrayList<>();
        for (JsonElement element : array(rawResult, "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (site.equals(string(mapping, "siteId"))
                    && occurrence == integer(mapping, "occurrence", -2)) {
                matches.add(mapping);
            }
        }
        JsonObject result = new JsonObject();
        result.addProperty("siteId", site);
        result.addProperty("occurrence", occurrence);
        result.addProperty("conditionIndex", condition);
        result.addProperty("desiredOutcome", desired);
        result.addProperty("matchCount", matches.size());
        JsonObject mapping = matches.size() == 1
                ? matches.get(0) : new JsonObject();
        boolean unique = matches.size() == 1;
        boolean conditionMatched = unique && condition >= 0
                && integer(mapping, "conditionIndex", -2) == condition;
        boolean scheduled = unique
                && exactBoolean(mapping, "scheduledTarget", true);
        boolean scheduledDesired = unique && exactBoolean(mapping,
                "scheduledDesiredOutcome", desired);
        boolean scheduledMatched = unique && exactBoolean(mapping,
                "scheduledOutcomeMatched", true);
        boolean observed = unique
                && exactBoolean(mapping, "observedOutcome", desired);
        boolean effective = unique
                && exactBoolean(mapping, "effectiveOutcome", desired);
        boolean unforced = unique
                && exactBoolean(mapping, "overrideApplied", false);
        result.addProperty("unique", unique);
        result.addProperty("conditionIndexMatched", conditionMatched);
        result.addProperty("scheduledTarget", scheduled);
        result.addProperty("scheduledDesiredOutcomeMatched",
                scheduledDesired);
        result.addProperty("scheduledOutcomeMatched", scheduledMatched);
        result.addProperty("observedOutcomeMatched", observed);
        result.addProperty("effectiveOutcomeMatched", effective);
        result.addProperty("overrideAbsent", unforced);
        result.addProperty("valid", unique && conditionMatched && scheduled
                && scheduledDesired && scheduledMatched && observed
                && effective && unforced);
        return result;
    }

    private static JsonObject exactOrderedPrefix(JsonObject task,
                                                 JsonObject rawResult) {
        JsonArray expectedRows = array(task, "expectedBranchPrefix");
        JsonArray mappings = array(rawResult, "branchMappings");
        int previousCondition = -1;
        int previousPosition = -1;
        boolean conditionOrder = hasArray(task, "expectedBranchPrefix");
        boolean tupleUnique = true;
        boolean mappingUnique = true;
        boolean ordered = true;
        boolean conditionIndicesMatch = true;
        boolean outcomesMatch = true;
        Set<String> tuples = new LinkedHashSet<>();
        JsonArray positions = new JsonArray();
        int matched = 0;
        for (JsonElement element : expectedRows) {
            if (!element.isJsonObject()) {
                conditionOrder = false;
                mappingUnique = false;
                continue;
            }
            JsonObject expected = element.getAsJsonObject();
            String site = string(expected, "siteId");
            int occurrence = integer(expected, "occurrence", -1);
            int condition = integer(expected, "conditionIndex", -1);
            boolean exactOutcome = hasBoolean(expected, "outcome");
            boolean outcome = bool(expected, "outcome", false);
            conditionOrder &= !site.isEmpty() && occurrence > 0
                    && condition >= 0 && condition > previousCondition
                    && exactOutcome;
            previousCondition = condition;
            String tuple = site + "\u0000" + occurrence + "\u0000"
                    + condition + "\u0000" + outcome;
            tupleUnique &= tuples.add(tuple);

            List<Integer> matches = new ArrayList<>();
            for (int index = 0; index < mappings.size(); index++) {
                JsonElement candidate = mappings.get(index);
                if (!candidate.isJsonObject()) continue;
                JsonObject mapping = candidate.getAsJsonObject();
                if (site.equals(string(mapping, "siteId"))
                        && occurrence == integer(mapping,
                        "occurrence", -2)) {
                    matches.add(index);
                }
            }
            if (matches.size() != 1) {
                mappingUnique = false;
                continue;
            }
            int position = matches.get(0);
            JsonObject mapping = mappings.get(position).getAsJsonObject();
            ordered &= position > previousPosition;
            previousPosition = position;
            conditionIndicesMatch &= integer(mapping, "conditionIndex", -2)
                    == condition;
            boolean rowOutcome = exactBoolean(mapping, "observedOutcome",
                    outcome) && exactBoolean(mapping, "effectiveOutcome",
                    outcome) && exactBoolean(mapping, "overrideApplied",
                    false);
            outcomesMatch &= rowOutcome;
            matched++;
            positions.add(position);
        }

        String flipSite = string(task, "flipSite");
        int flipOccurrence = integer(task, "flipOccurrence", -1);
        List<Integer> targetPositions = new ArrayList<>();
        for (int index = 0; index < mappings.size(); index++) {
            JsonElement element = mappings.get(index);
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (flipSite.equals(string(mapping, "siteId"))
                    && flipOccurrence == integer(mapping,
                    "occurrence", -2)) {
                targetPositions.add(index);
            }
        }
        boolean targetUnique = targetPositions.size() == 1;
        int targetPosition = targetUnique ? targetPositions.get(0) : -1;
        boolean beforeTarget = targetUnique
                && (expectedRows.size() == 0
                || previousPosition >= 0
                && previousPosition < targetPosition);

        JsonObject result = new JsonObject();
        result.addProperty("expectedCount", expectedRows.size());
        result.addProperty("matchedCount", matched);
        result.addProperty("conditionIndicesStrictlyIncreasing",
                conditionOrder);
        result.addProperty("expectedTuplesUnique", tupleUnique);
        result.addProperty("runtimeMappingsUnique", mappingUnique);
        result.addProperty("runtimePositionsStrictlyIncreasing", ordered);
        result.addProperty("runtimeConditionIndicesExact",
                conditionIndicesMatch);
        result.addProperty("runtimeOutcomesExactAndUnforced",
                outcomesMatch);
        result.addProperty("targetMappingUnique", targetUnique);
        result.addProperty("targetPosition", targetPosition);
        result.add("runtimePositions", positions);
        result.addProperty("allPrefixMappingsBeforeTarget", beforeTarget);
        result.addProperty("valid", conditionOrder && tupleUnique
                && mappingUnique && matched == expectedRows.size()
                && ordered && conditionIndicesMatch && outcomesMatch
                && beforeTarget);
        return result;
    }

    private static JsonObject captureRequest(String kind, String key,
                                             JsonObject activation,
                                             JsonObject task) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", kind);
        result.addProperty("requestKey", key);
        result.addProperty("regionId", string(activation, "regionId"));
        result.addProperty("activationId", string(activation,
                "activationId"));
        result.add("activation", activation.deepCopy());
        result.add("reachabilitySupportActivations",
                flattenedReachabilitySupport(activation));
        if (task != null) result.add("pathTask", task.deepCopy());
        result.addProperty("requiresImport", true);
        result.addProperty("requiresUnforcedBranchValidation",
                "PATH_FLIP".equals(kind)
                        || "TRANSITION_OUTPUT_REPLAY".equals(kind)
                        || "TARGET_REBASE".equals(kind));
        return result;
    }

    /**
     * Returns the ordered replay prefix needed to make {@code activation}
     * reachable.  Support rows are flattened and de-duplicated by activation
     * id so a recursively discovered chain can be persisted and resumed
     * without nesting activation plans inside activation plans.
     */
    private static JsonArray flattenedReachabilitySupport(
            JsonObject activation) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        appendReachabilitySupport(result, seen, activation);
        return result;
    }

    private static void appendReachabilitySupport(JsonArray result,
                                                  Set<String> seen,
                                                  JsonObject activation) {
        if (activation == null) return;
        for (JsonElement element : array(activation,
                "reachabilitySupportActivations")) {
            if (!element.isJsonObject()) continue;
            JsonObject support = element.getAsJsonObject();
            appendReachabilitySupport(result, seen, support);
            JsonObject flattened = support.deepCopy();
            flattened.remove("reachabilitySupportActivations");
            String id = string(flattened, "activationId");
            if (!id.isEmpty() && seen.add(id)) result.add(flattened);
        }
    }

    private static JsonArray reachabilitySupportIncluding(
            JsonObject sourceReplayActivation) {
        JsonArray result = flattenedReachabilitySupport(
                sourceReplayActivation);
        Set<String> seen = new LinkedHashSet<>();
        for (JsonElement element : result) {
            if (element.isJsonObject()) seen.add(string(
                    element.getAsJsonObject(), "activationId"));
        }
        if (sourceReplayActivation != null) {
            JsonObject primary = sourceReplayActivation.deepCopy();
            primary.remove("reachabilitySupportActivations");
            String id = string(primary, "activationId");
            if (!id.isEmpty() && seen.add(id)) result.add(primary);
        }
        return result;
    }

    private static List<JsonObject> pathSeedSummaries(
            List<JsonObject> summaries, List<JsonObject> transitionSeeds,
            boolean transitionFocusOnly) {
        List<JsonObject> result = transitionFocusOnly
                ? new ArrayList<JsonObject>()
                : rawOutputSummaries(summaries);
        for (JsonObject seed : transitionSeeds) result.add(seed.deepCopy());
        return result;
    }

    private static List<JsonObject> transitionDiscoverySeeds(
            List<JsonObject> summaries) {
        List<JsonObject> result = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (JsonObject summary : summaries == null
                ? Collections.<JsonObject>emptyList() : summaries) {
            if (!RegionCaptureGoal.from(summary).isTransitionDiscovery()
                    || !"QUARANTINED".equals(string(summary,
                    "summaryCacheAdmission"))
                    || summary.has("transitionDiscoveryProvenance")) {
                continue;
            }
            String identity = string(summary, "summaryId");
            if (identity.isEmpty()) {
                identity = RegionPathWorklist.stablePathKey(summary);
            }
            if (seen.add(identity)) result.add(summary.deepCopy());
        }
        return result;
    }

    private static boolean containsSummaryId(List<JsonObject> summaries,
                                             JsonObject candidate) {
        String id = string(candidate, "summaryId");
        if (!id.isEmpty()) {
            for (JsonObject summary : summaries) {
                if (id.equals(string(summary, "summaryId"))) return true;
            }
            return false;
        }
        String path = RegionPathWorklist.stablePathKey(candidate);
        for (JsonObject summary : summaries) {
            if (string(summary, "regionId").equals(string(candidate,
                    "regionId"))
                    && path.equals(RegionPathWorklist.stablePathKey(summary))) {
                return true;
            }
        }
        return false;
    }

    private static JsonObject firstUnattempted(List<JsonObject> requests,
                                               Set<String> attempted) {
        for (JsonObject request : requests) {
            if (!attempted.contains(string(request, "requestId"))) {
                return request;
            }
        }
        return null;
    }

    private static JsonObject transitionOutputActivation(JsonObject request,
                                                         State state) {
        JsonObject result = outputActivation(request, state);
        if (result == null) return null;
        String exactSource = string(request, "sourceActivationId");
        if (exactSource.isEmpty() || !exactSource.equals(string(result,
                "selectedUpstreamActivationId"))) return null;
        RegionCaptureGoal.transitionDiscovery().writeTo(result);
        result.addProperty("discoveryOnly", true);
        result.addProperty("summaryCacheAdmission", "QUARANTINED");
        result.add("transitionDiscovery",
                transitionMetadata(request, ""));
        JsonObject requested = object(result, "requestedOutput");
        requested.addProperty("selectionAuthority",
                "STATIC_EXACT_OUTPUT_SLICE_DISCOVERY_HINT");
        return result;
    }

    private static String transitionSeedPrecheck(JsonObject activation) {
        if (activation == null) return "MISSING_PRODUCER_ACTIVATION";
        if (!RegionCaptureGoal.from(activation).isTransitionDiscovery()) {
            return "DISCOVERY_CAPTURE_GOAL_NOT_PRESERVED";
        }
        if (!bool(activation, "requestedOutputSliceComplete", false)) {
            return "MISSING_COMPLETE_EXACT_OUTPUT_SLICE";
        }
        if (bool(activation, "requestedOutputCaptureRequired", false)
                && !bool(activation, "requestedOutputCaptureComplete",
                false)
                && (!bool(activation,
                "requestedOutputCaptureTemplateReady", false)
                || !bool(activation,
                "transitionDiscoveryCaptureTemplateReady", false))) {
            return "DISCOVERY_OUTPUT_CAPTURE_TEMPLATE_NOT_READY";
        }
        if (!bool(activation, "schedulerReady", false)) {
            return "DISCOVERY_OUTPUT_MATERIALIZATION_NOT_READY";
        }
        return "";
    }

    /** Returns a normalized but quarantined path seed, never a cache entry. */
    private static JsonObject transitionDiscoverySeed(JsonObject request,
                                                      ExecutionOutcome outcome) {
        String expectedActivationId = "ACT.OUTPUT."
                + shortHash(string(request, "requestId"));
        if (outcome == null || outcome.summary == null
                || !bool(outcome.summary, "valid", false)
                || !expectedActivationId.equals(string(outcome.summary,
                "activationId"))
                || !RegionCaptureGoal.from(outcome.summary)
                .isTransitionDiscovery()
                || !bool(outcome.summary, "normalExit", false)
                || !bool(outcome.summary,
                "requestedOutputSliceComplete", false)
                || bool(outcome.rawResult, "branchOverrideUsed", false)) {
            return null;
        }
        JsonObject guard = object(request, "transitionGuard");
        String site = string(guard, "siteId");
        int occurrence = integer(guard, "occurrence", 1);
        boolean observed = bool(guard, "observedOutcome", false);
        boolean mapped = false;
        for (JsonElement element : array(outcome.summary,
                "branchMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (site.equals(string(mapping, "siteId"))
                    && occurrence == integer(mapping, "occurrence", 1)
                    && observed == bool(mapping, "outcome", false)
                    && integer(mapping, "conditionIndex", -1) >= 0) {
                mapped = true;
                break;
            }
        }
        if (!mapped || array(outcome.summary, "pathCondition").size() == 0) {
            return null;
        }
        JsonObject seed = outcome.summary.deepCopy();
        RegionCaptureGoal.transitionDiscovery().writeTo(seed);
        seed.add("transitionDiscovery", transitionMetadata(request,
                outcome.executionId));
        seed.addProperty("discoveryOnly", true);
        seed.addProperty("summaryCacheAdmission", "QUARANTINED");
        return seed;
    }

    private static JsonObject transitionMetadata(JsonObject request,
                                                 String executionId) {
        JsonObject guard = object(request, "transitionGuard");
        JsonObject result = new JsonObject();
        String candidateEdgeId = string(request, "candidateEdgeId");
        if (candidateEdgeId.isEmpty()) candidateEdgeId = string(object(
                request, "transitionDiscovery"), "candidateEdgeId");
        result.addProperty("candidateEdgeId", candidateEdgeId);
        String seedRequestId = string(request, "requestId");
        if (seedRequestId.isEmpty()) seedRequestId = string(object(request,
                "transitionDiscovery"), "seedRequestId");
        result.addProperty("seedRequestId", seedRequestId);
        result.addProperty("fromRegion", string(request, "upstreamRegion"));
        result.addProperty("sourceActivationId", string(request,
                "sourceActivationId"));
        result.addProperty("sourceRegionInstanceId", string(request,
                "sourceRegionInstanceId"));
        result.addProperty("runtimeFromPort", string(request,
                "edgeOutputEndpoint"));
        result.addProperty("fromOutputPort", string(request,
                "upstreamOutputPort"));
        result.addProperty("fromOutputCell", string(request,
                "upstreamOutputCell"));
        result.addProperty("toRegion", string(request, "downstreamRegion"));
        result.addProperty("toPort", string(request,
                "downstreamInputPort"));
        result.addProperty("guardSiteId", string(guard, "siteId"));
        result.addProperty("guardOccurrence", integer(guard,
                "occurrence", 1));
        result.addProperty("observedOutcome", bool(guard,
                "observedOutcome", false));
        result.addProperty("desiredOutcome", bool(guard,
                "desiredOutcome", false));
        result.add("aliasProofEdgeIds", array(request,
                "aliasProofEdgeIds").deepCopy());
        if (executionId != null && !executionId.isEmpty()) {
            result.addProperty("seedExecutionId", executionId);
        }
        result.addProperty("promotionPolicy",
                "SAME_EXECUTION_NORMAL_OUTPUT_CONSUMER_AND_COMPOSABLE_EDGE");
        return result;
    }

    private static boolean transitionOutputReplayRequired(
            JsonObject activation, JsonObject replayValidation) {
        return RegionCaptureGoal.from(activation).isTransitionDiscovery()
                && bool(activation, "requestedOutputCaptureRequired", false)
                && !bool(activation, "requestedOutputCaptureComplete", false)
                && bool(activation,
                "requestedOutputCaptureRefinementRequired", false)
                && bool(replayValidation, "outputClosureAdmissionGap", false)
                && bool(replayValidation,
                "branchAndInputReplayValidated", false);
    }

    /**
     * Resolves an occurrence-zero static capture template from the rich trace
     * produced by the same flipped execution.  The returned activation keeps
     * the solver model and target branch from the probe, but replaces only
     * the requested-output slice/capture contract with the unique
     * runtime-refined producer activation.  A second replay is intentional:
     * the bytecode for the probe was instrumented before that occurrence was
     * knowable.
     */
    static JsonObject transitionOutputRefinement(
            JsonObject task, JsonObject replayActivation,
            ExecutionOutcome probe) {
        JsonObject result = new JsonObject();
        result.addProperty("ready", false);
        JsonObject discovery = object(task, "transitionDiscovery");
        String sourceActivation = string(discovery,
                "sourceActivationId");
        String sourceInstance = string(discovery,
                "sourceRegionInstanceId");
        String region = firstPresent(string(discovery, "fromRegion"),
                string(task, "regionId"),
                string(replayActivation, "regionId"));
        JsonObject requested = object(replayActivation,
                "requestedOutput");
        String outputPort = firstPresent(string(requested, "portId"),
                string(discovery, "fromOutputPort"));
        String outputCell = firstPresent(string(requested, "cell"),
                string(discovery, "fromOutputCell"));
        if (probe == null || probe.executionId.trim().isEmpty()
                || sourceActivation.isEmpty() || sourceInstance.isEmpty()
                || region.isEmpty() || outputPort.isEmpty()) {
            result.addProperty("reason",
                    "FRESH_RUNTIME_OUTPUT_CAPTURE_REFINEMENT_MISSING");
            return result;
        }

        List<JsonObject> candidates = new ArrayList<>();
        for (JsonObject candidate : probe.discoveredActivations) {
            if (!region.equals(string(candidate, "regionId"))
                    || !sourceInstance.equals(string(candidate,
                    "regionInstanceId"))
                    || !refinesSourceActivation(candidate,
                    sourceActivation)
                    || !sameRequestedOutput(candidate, outputPort,
                    outputCell)
                    || !bool(candidate,
                    "requestedOutputSliceComplete", false)
                    || !bool(candidate,
                    "requestedOutputCaptureRequired", false)
                    || !bool(candidate,
                    "requestedOutputCaptureComplete", false)
                    || !exactRuntimeOutputCapture(candidate, outputPort,
                    outputCell)) {
                continue;
            }
            candidates.add(candidate);
        }
        result.addProperty("candidateCount", candidates.size());
        if (candidates.size() != 1) {
            result.addProperty("reason", candidates.isEmpty()
                    ? "FRESH_RUNTIME_OUTPUT_CAPTURE_REFINEMENT_MISSING"
                    : "FRESH_RUNTIME_OUTPUT_CAPTURE_REFINEMENT_AMBIGUOUS");
            return result;
        }

        JsonObject candidate = candidates.get(0);
        JsonObject exact = replayActivation.deepCopy();
        for (String field : new String[]{
                "requestedOutput", "requestedOutputSlice",
                "requestedOutputSliceComplete",
                "requestedOutputSlicePolicy",
                "requestedOutputSliceRefinementPolicy",
                "requestedOutputSliceRefinementComplete",
                "requestedOutputMethods", "requestedOutputCapture",
                "requestedOutputCaptureRequired",
                "requestedOutputCaptureComplete", "outputs",
                "containerElementFieldBindings"}) {
            copyIfPresent(exact, candidate, field);
        }
        exact.addProperty("requestedOutputCaptureRefinementRequired",
                false);
        exact.addProperty("requestedOutputCaptureTemplateReady", false);
        exact.addProperty("requestedOutputCaptureTemplateAuthority",
                "RUNTIME_REFINED_EXACT_OUTPUT_CAPTURE");
        exact.remove("outputCaptureGap");
        RegionCaptureGoal.transitionDiscovery().writeTo(exact);

        JsonObject capture = array(candidate,
                "requestedOutputCapture").get(0).getAsJsonObject();
        result.addProperty("probeExecutionId", probe.executionId);
        result.addProperty("refinedActivationId", string(candidate,
                "activationId"));
        result.addProperty("sourceActivationId", sourceActivation);
        result.addProperty("sourceRegionInstanceId", sourceInstance);
        result.addProperty("captureBindingId", string(capture,
                "captureBindingId"));
        result.addProperty("occurrence", integer(capture,
                "occurrence", -1));
        result.addProperty("authority",
                "FRESH_RUNTIME_REFINED_EXACT_OUTPUT_CAPTURE");
        JsonObject activationEvidence = result.deepCopy();
        activationEvidence.remove("ready");
        activationEvidence.remove("reason");
        exact.add("transitionOutputRefinement", activationEvidence);
        result.add("activation", exact);
        result.addProperty("ready", true);
        result.addProperty("reason", "");
        return result;
    }

    private static boolean refinesSourceActivation(JsonObject candidate,
                                                   String source) {
        return source.equals(string(candidate,
                "selectedUpstreamActivationId"))
                || source.equals(string(candidate,
                "selectedBaseActivationId"))
                || source.equals(string(candidate,
                "derivedFromActivationId"));
    }

    private static boolean sameRequestedOutput(JsonObject activation,
                                               String port, String cell) {
        JsonObject requested = object(activation, "requestedOutput");
        if (!canonicalPort(port).equals(canonicalPort(
                string(requested, "portId")))) return false;
        return cell.isEmpty() || cell.equals(string(requested, "cell"));
    }

    private static boolean exactRuntimeOutputCapture(
            JsonObject activation, String port, String cell) {
        JsonArray captures = array(activation, "requestedOutputCapture");
        if (captures.size() != 1 || !captures.get(0).isJsonObject()) {
            return false;
        }
        JsonObject capture = captures.get(0).getAsJsonObject();
        if (!canonicalPort(port).equals(canonicalPort(
                string(capture, "outputPort")))
                || !cell.isEmpty()
                && !cell.equals(string(capture, "outputCell"))
                || integer(capture, "occurrence", 0) < 1) return false;
        String kind = string(capture, "captureKind");
        if (kind.isEmpty()) kind = "CALL_ARGUMENT";
        if ("FIELD_ASSIGNMENT_RHS".equals(kind)) {
            return "RUNTIME_UNIQUE_STATIC_FIELD_ASSIGNMENT_SITE_"
                    .concat("LAST_WRITE_OCCURRENCE").equals(string(capture,
                            "occurrenceAuthority"))
                    && integer(capture,
                    "runtimeFieldOwnerObjectId", 0) > 0
                    && "RUNTIME_EXACT_FIELD_WRITE_RECEIVER_IDENTITY".equals(
                    string(capture,
                            "runtimeFieldOwnerBindingAuthority"));
        }
        return "CALL_ARGUMENT".equals(kind)
                && "RUNTIME_EXACT_CALL_ARGUMENT_OCCURRENCE".equals(
                string(capture, "occurrenceAuthority"));
    }

    private static String exactOutputCaptureKind(JsonObject capture) {
        String kind = string(capture, "captureKind");
        return kind.isEmpty() ? "CALL_ARGUMENT" : kind;
    }

    private static String firstPresent(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    static JsonObject transitionPromotionAdmission(
            JsonObject task, ExecutionOutcome outcome,
            RuntimeDiscoveryMode mode) {
        JsonObject result = new JsonObject();
        result.addProperty("valid", false);
        if (mode == null || mode.isFixedValidatedGraph()) {
            result.addProperty("reason",
                    "TRANSITION_DISCOVERY_REQUIRES_FRESH_RUNTIME_GRAPH");
            return result;
        }
        if (outcome == null || outcome.executionId.trim().isEmpty()) {
            result.addProperty("reason", "MISSING_FRESH_EXECUTION_ID");
            return result;
        }
        JsonObject discovery = object(task, "transitionDiscovery");
        String expectedSourceActivation = string(discovery,
                "sourceActivationId");
        String expectedSourceInstance = string(discovery,
                "sourceRegionInstanceId");
        String edgeId = string(discovery, "candidateEdgeId");
        String fromRegion = string(discovery, "fromRegion");
        String fromPort = string(discovery, "runtimeFromPort");
        String fromOutputPort = string(discovery, "fromOutputPort");
        String toRegion = string(discovery, "toRegion");
        String toPort = string(discovery, "toPort");
        if (expectedSourceActivation.isEmpty()
                || expectedSourceInstance.isEmpty()
                || fromRegion.isEmpty() || toRegion.isEmpty()) {
            result.addProperty("reason",
                    "INCOMPLETE_EXACT_DISCOVERY_SOURCE_IDENTITY");
            return result;
        }
        JsonObject summary = outcome.summary;
        if (summary == null) {
            result.addProperty("reason",
                    "NORMAL_EXACT_REQUESTED_OUTPUT_NOT_IMPORTED");
            return result;
        }
        String requestedPort = string(object(summary, "requestedOutput"),
                "portId");
        if (!bool(summary, "valid", false)
                || !bool(summary, "normalExit", false)
                || !bool(summary, "relationallyComplete", false)
                || requestedPort.isEmpty()
                || !object(summary, "outputExpressions").has(
                requestedPort)) {
            result.addProperty("reason",
                    "NORMAL_EXACT_REQUESTED_OUTPUT_NOT_IMPORTED");
            return result;
        }
        if (!fromRegion.equals(string(summary, "regionId"))
                || !expectedSourceInstance.equals(string(summary,
                "regionInstanceId"))) {
            result.addProperty("reason",
                    "IMPORTED_SUMMARY_SOURCE_INSTANCE_MISMATCH");
            return result;
        }

        JsonObject outputCaptureAdmission =
                sameExecutionOutputCaptureAdmission(task, outcome);
        result.add("sameExecutionOutputCaptureAdmission",
                outputCaptureAdmission);
        if (!bool(outputCaptureAdmission, "valid", false)) {
            result.addProperty("reason", string(outputCaptureAdmission,
                    "reason"));
            return result;
        }

        List<JsonObject> exactSources = new ArrayList<>();
        for (JsonObject activation : outcome.discoveredActivations) {
            if (expectedSourceActivation.equals(string(activation,
                    "activationId"))
                    && expectedSourceInstance.equals(string(activation,
                    "regionInstanceId"))
                    && fromRegion.equals(string(activation, "regionId"))) {
                exactSources.add(activation);
            }
        }
        if (exactSources.size() != 1) {
            result.addProperty("reason", exactSources.isEmpty()
                    ? "SAME_EXECUTION_EXACT_SOURCE_ACTIVATION_NOT_OBSERVED"
                    : "SAME_EXECUTION_EXACT_SOURCE_ACTIVATION_AMBIGUOUS");
            return result;
        }

        List<JsonObject> provenEdges = new ArrayList<>();
        for (JsonObject edge : outcome.discoveredEdges) {
            if ((!edgeId.isEmpty() && !edgeId.equals(string(edge,
                    "edgeId")))
                    || !fromRegion.equals(string(edge, "fromRegion"))
                    || !canonicalPort(fromPort).equals(canonicalPort(
                    string(edge, "fromPort")))
                    || !toRegion.equals(string(edge, "toRegion"))
                    || !canonicalPort(toPort).equals(canonicalPort(
                    string(edge, "toPort")))) {
                continue;
            }
            if (AutomaticRegionEdge.composable(edge)) {
                provenEdges.add(edge);
            }
        }
        if (provenEdges.isEmpty()) {
            result.addProperty("reason",
                    "SAME_EXECUTION_COMPOSABLE_EDGE_NOT_OBSERVED");
            return result;
        }

        List<JsonObject> matchedEdges = new ArrayList<>();
        List<JsonObject> matchedBindings = new ArrayList<>();
        List<JsonObject> matchedConsumers = new ArrayList<>();
        Set<String> matchedKeys = new LinkedHashSet<>();
        for (JsonObject provenEdge : provenEdges) {
            for (JsonElement element : array(provenEdge,
                    "validatedBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!expectedSourceInstance.equals(string(binding,
                        "fromRegionInstance"))) continue;
                String boundSourceActivation = string(binding,
                        "fromActivationId");
                if (!boundSourceActivation.isEmpty()
                        && !expectedSourceActivation.equals(
                        boundSourceActivation)) continue;
                String consumerInstance = string(binding,
                        "toRegionInstance");
                if (consumerInstance.isEmpty()) continue;
                for (JsonObject consumer : outcome.discoveredActivations) {
                    if (!toRegion.equals(string(consumer, "regionId"))
                            || !consumerInstance.equals(string(consumer,
                            "regionInstanceId"))) continue;
                    String boundConsumerActivation = string(binding,
                            "toActivationId");
                    if (!boundConsumerActivation.isEmpty()
                            && !boundConsumerActivation.equals(
                            string(consumer, "activationId"))) continue;
                    String matchKey = string(provenEdge, "edgeId") + "\n"
                            + binding.toString() + "\n"
                            + string(consumer, "activationId");
                    if (!matchedKeys.add(matchKey)) continue;
                    matchedEdges.add(provenEdge);
                    matchedBindings.add(binding);
                    matchedConsumers.add(consumer);
                }
            }
        }
        if (matchedBindings.isEmpty()) {
            boolean consumerObserved = false;
            for (JsonObject activation : outcome.discoveredActivations) {
                consumerObserved |= toRegion.equals(string(activation,
                        "regionId"));
            }
            result.addProperty("reason",
                    consumerObserved
                            ? "COMPOSABLE_EDGE_NOT_EXACTLY_BOUND_FROM_"
                            + "DISCOVERED_SOURCE_TO_CONSUMER"
                            : "SAME_EXECUTION_CONSUMER_ACTIVATION_NOT_OBSERVED");
            return result;
        }
        if (matchedBindings.size() != 1) {
            result.addProperty("reason",
                    "AMBIGUOUS_SAME_EXECUTION_SOURCE_CONSUMER_BINDING");
            return result;
        }

        JsonObject provenEdge = matchedEdges.get(0);
        JsonObject consumer = matchedConsumers.get(0);
        JsonObject binding = matchedBindings.get(0).deepCopy();
        binding.addProperty("edgeId", string(provenEdge, "edgeId"));
        binding.addProperty("fromRegion", fromRegion);
        binding.addProperty("toRegion", toRegion);
        if (!fromOutputPort.isEmpty()) {
            binding.addProperty("fromOutputPort", fromOutputPort);
        }
        binding.addProperty("toInputPort", toPort);
        String execution = outcome.executionId.trim();
        JsonObject normalizedBinding = namespaceDynamicIds(binding,
                execution);
        JsonObject normalizedSource = namespaceDynamicIds(
                exactSources.get(0), execution);
        JsonObject normalizedConsumer = namespaceDynamicIds(consumer,
                execution);
        result.addProperty("valid", true);
        result.addProperty("reason", "");
        result.addProperty("executionId", execution);
        result.addProperty("edgeId", string(provenEdge, "edgeId"));
        result.addProperty("sourceActivationId", string(normalizedSource,
                "activationId"));
        result.addProperty("sourceRegionInstance", string(normalizedBinding,
                "fromRegionInstance"));
        result.addProperty("consumerActivationId", string(
                normalizedConsumer, "activationId"));
        result.addProperty("consumerRegionInstance", string(
                normalizedBinding, "toRegionInstance"));
        result.add("validatedBinding", normalizedBinding);
        result.addProperty("authority",
                "ONE_FRESH_EXECUTION_EXACT_SOURCE_CONSUMER_ACTIVATIONS_"
                        + "AND_VALIDATED_BINDING");
        return result;
    }

    /**
     * Re-validates an exact output-capture plan against the runtime planner
     * output emitted by the very execution whose raw expression is being
     * promoted.  The preceding probe is allowed to choose an occurrence for
     * instrumentation, but it is never authority for the final execution:
     * the endpoint and occurrence must be rediscovered unchanged here.  A
     * changed field-owner trace id is retained as fresh provenance because
     * the raw post-assignment hook independently verifies the actual owner
     * and assigned value by activation-local identity.
     */
    static JsonObject sameExecutionOutputCaptureAdmission(
            JsonObject task, ExecutionOutcome outcome) {
        JsonObject result = new JsonObject();
        result.addProperty("valid", false);
        if (outcome == null || outcome.summary == null
                || outcome.executionId.trim().isEmpty()) {
            result.addProperty("reason",
                    "FINAL_OUTPUT_CAPTURE_EXECUTION_EVIDENCE_MISSING");
            return result;
        }
        JsonObject summary = outcome.summary;
        if (!bool(summary, "requestedOutputCaptureRequired", false)) {
            result.addProperty("valid", true);
            result.addProperty("reason", "");
            result.addProperty("authority",
                    "EXACT_OUTPUT_CAPTURE_NOT_REQUIRED");
            return result;
        }
        JsonObject discovery = object(task, "transitionDiscovery");
        String sourceActivation = string(discovery,
                "sourceActivationId");
        String sourceInstance = string(discovery,
                "sourceRegionInstanceId");
        String region = firstPresent(string(discovery, "fromRegion"),
                string(summary, "regionId"));
        JsonObject requested = object(summary, "requestedOutput");
        String outputPort = firstPresent(string(requested, "portId"),
                string(discovery, "fromOutputPort"));
        String outputCell = firstPresent(string(requested, "cell"),
                string(discovery, "fromOutputCell"));
        if (sourceActivation.isEmpty() || sourceInstance.isEmpty()
                || region.isEmpty() || outputPort.isEmpty()) {
            result.addProperty("reason",
                    "FINAL_OUTPUT_CAPTURE_SOURCE_IDENTITY_INCOMPLETE");
            return result;
        }
        JsonArray plannedCaptures = array(summary,
                "requestedOutputCapture");
        if (plannedCaptures.size() != 1
                || !plannedCaptures.get(0).isJsonObject()) {
            result.addProperty("reason",
                    "FINAL_OUTPUT_CAPTURE_PLAN_NOT_EXACT");
            return result;
        }
        JsonObject planned = plannedCaptures.get(0).getAsJsonObject();

        List<JsonObject> candidates = new ArrayList<>();
        for (JsonObject candidate : outcome.discoveredActivations) {
            if (!region.equals(string(candidate, "regionId"))
                    || !sourceInstance.equals(string(candidate,
                    "regionInstanceId"))
                    || !refinesSourceActivation(candidate,
                    sourceActivation)
                    || !sameRequestedOutput(candidate, outputPort,
                    outputCell)
                    || !bool(candidate,
                    "requestedOutputSliceComplete", false)
                    || !bool(candidate,
                    "requestedOutputCaptureRequired", false)
                    || !bool(candidate,
                    "requestedOutputCaptureComplete", false)
                    || !exactRuntimeOutputCapture(candidate, outputPort,
                    outputCell)) {
                continue;
            }
            JsonObject current = array(candidate,
                    "requestedOutputCapture").get(0).getAsJsonObject();
            if (sameOutputCaptureEndpointAndOccurrence(planned, current)) {
                candidates.add(candidate);
            }
        }
        result.addProperty("matchingCandidateCount", candidates.size());
        if (candidates.size() != 1) {
            result.addProperty("reason", candidates.isEmpty()
                    ? "FINAL_EXECUTION_EXACT_OUTPUT_CAPTURE_NOT_RECONFIRMED"
                    : "FINAL_EXECUTION_EXACT_OUTPUT_CAPTURE_AMBIGUOUS");
            return result;
        }
        JsonObject candidate = candidates.get(0);
        JsonObject current = array(candidate,
                "requestedOutputCapture").get(0).getAsJsonObject();
        result.addProperty("valid", true);
        result.addProperty("reason", "");
        result.addProperty("executionId", outcome.executionId.trim());
        result.addProperty("activationId", string(candidate,
                "activationId"));
        result.addProperty("sourceActivationId", sourceActivation);
        result.addProperty("sourceRegionInstanceId", sourceInstance);
        result.addProperty("captureBindingId", string(current,
                "captureBindingId"));
        result.addProperty("occurrence", integer(current,
                "occurrence", -1));
        result.add("currentCapture", current.deepCopy());
        result.addProperty("authority",
                "FINAL_EXECUTION_RUNTIME_RECONFIRMED_EXACT_OUTPUT_CAPTURE");
        return result;
    }

    private static boolean sameOutputCaptureEndpointAndOccurrence(
            JsonObject left, JsonObject right) {
        if (!exactOutputCaptureKind(left).equals(
                exactOutputCaptureKind(right))
                || !string(left, "captureBindingId").equals(string(right,
                "captureBindingId"))
                || !canonicalPort(string(left, "outputPort")).equals(
                canonicalPort(string(right, "outputPort")))
                || !string(left, "outputCell").equals(string(right,
                "outputCell"))
                || integer(left, "unitIndex", -1) != integer(right,
                "unitIndex", -2)
                || !string(left, "siteId").equals(string(right,
                "siteId"))
                || integer(left, "occurrence", -1) != integer(right,
                "occurrence", -2)) {
            return false;
        }
        if ("FIELD_ASSIGNMENT_RHS".equals(
                exactOutputCaptureKind(left))) {
            return string(left, "method").equals(string(right, "method"))
                    && string(left, "fieldSignature").equals(string(right,
                    "fieldSignature"));
        }
        return string(left, "callerMethod").equals(string(right,
                "callerMethod"))
                && string(left, "calleeMethod").equals(string(right,
                "calleeMethod"))
                && integer(left, "argumentIndex", -1) == integer(right,
                "argumentIndex", -2);
    }

    private static JsonObject promoteTransitionSummary(JsonObject summary,
                                                       JsonObject task,
                                                       JsonObject admission) {
        JsonObject result = summary.deepCopy();
        RegionCaptureGoal.outputClosure().writeTo(result);
        result.remove("discoveryOnly");
        result.remove("summaryCacheAdmission");
        JsonObject exactBinding = object(admission,
                "validatedBinding").deepCopy();
        JsonArray normalizedBindings = new JsonArray();
        Set<String> seenBindings = new LinkedHashSet<>();
        String execution = string(admission, "executionId");
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject normalized = namespaceDynamicIds(
                    element.getAsJsonObject(), execution);
            if (seenBindings.add(normalized.toString())) {
                normalizedBindings.add(normalized);
            }
        }
        if (exactBinding.size() > 0
                && seenBindings.add(exactBinding.toString())) {
            normalizedBindings.add(exactBinding);
        }
        result.add("edgeBindings", normalizedBindings);
        String logicalInstance = string(exactBinding,
                "fromRegionInstance");
        if (!logicalInstance.isEmpty()) {
            result.addProperty("regionInstanceId", logicalInstance);
            result.addProperty("logicalRegionInstanceId", logicalInstance);
            result.addProperty("regionInstanceAuthority",
                    "PROMOTED_VALIDATED_BINDING_SOURCE");
        }
        JsonObject outputCaptureAdmission = object(admission,
                "sameExecutionOutputCaptureAdmission");
        JsonObject currentCapture = object(outputCaptureAdmission,
                "currentCapture");
        if (currentCapture.size() > 0) {
            JsonArray captures = new JsonArray();
            captures.add(currentCapture.deepCopy());
            result.add("requestedOutputCapture", captures);
            JsonObject slice = object(result,
                    "requestedOutputSlice").deepCopy();
            slice.add("captureBindings", captures.deepCopy());
            result.add("requestedOutputSlice", slice);
            result.add("finalExecutionOutputCaptureAdmission",
                    outputCaptureAdmission.deepCopy());
        }
        JsonObject provenance = object(task, "transitionDiscovery").deepCopy();
        provenance.add("promotionAdmission", admission.deepCopy());
        result.add("transitionDiscoveryProvenance", provenance);
        return result;
    }

    private static void alignActivationWithPromotedSummary(
            List<JsonObject> activations, JsonObject summary) {
        JsonObject activation = activation(activations,
                string(summary, "activationId"));
        if (activation == null) return;
        JsonObject aligned = activation.deepCopy();
        aligned.addProperty("regionInstanceId", string(summary,
                "regionInstanceId"));
        aligned.add("edgeBindings", array(summary,
                "edgeBindings").deepCopy());
        addOrReplaceActivation(activations, aligned);
    }

    private static boolean focusedTransitionAlreadyPromoted(
            State state, RegionTransitionDiscoveryWorklist.Focus focus) {
        if (state == null || focus == null || !focus.configured()) {
            return false;
        }
        for (JsonObject summary : state.summaries) {
            JsonObject provenance = object(summary,
                    "transitionDiscoveryProvenance");
            if (focus.matchesDiscovery(provenance)
                    && bool(object(provenance, "promotionAdmission"),
                    "valid", false)) {
                return true;
            }
        }
        for (JsonObject record : state.pathRecords) {
            if ("TRANSITION_VALIDATED".equals(string(record, "status"))
                    && focus.matchesTask(record)
                    && bool(object(record, "transitionPromotionAdmission"),
                    "valid", false)) {
                return true;
            }
        }
        return false;
    }

    private static void removeTransitionSeed(List<JsonObject> seeds,
                                             JsonObject task) {
        String id = string(task, "sourceSummaryId");
        seeds.removeIf(seed -> id.equals(string(seed, "summaryId")));
    }

    private static boolean admitSeed(ExecutionOutcome outcome, State state,
                                     List<JsonObject> gaps, String requestId) {
        if (outcome == null || outcome.summary == null
                || !bool(outcome.summary, "valid", false)) {
            gaps.add(gap("OUTPUT_SEED_CAPTURE_FAILED", requestId));
            return false;
        }
        if (!RegionCaptureGoal.from(outcome.summary).isOutputClosure()) {
            gaps.add(gap("OUTPUT_SEED_WRONG_CAPTURE_GOAL", requestId));
            return false;
        }
        if (RegionCaptureGoal.from(outcome.summary)
                .isTransitionDiscovery()) {
            gaps.add(gap("OUTPUT_SEED_DISCOVERY_SUMMARY_NOT_PROMOTABLE",
                    requestId));
            return false;
        }
        if (!bool(outcome.summary, "normalExit", bool(object(
                outcome.summary, "regionRelation"), "complete", false))) {
            gaps.add(gap("OUTPUT_SEED_EXCEPTIONAL_EXIT", requestId));
            return false;
        }
        if (!bool(outcome.summary, "relationallyComplete", false)) {
            gaps.add(gap("OUTPUT_SEED_RELATION_INCOMPLETE", requestId));
            return false;
        }
        String requestedPort = string(object(outcome.summary,
                "requestedOutput"), "portId");
        if (requestedPort.isEmpty() || object(outcome.summary,
                "regionRelation").size() == 0 && !object(outcome.summary,
                "outputExpressions").has(requestedPort)) {
            gaps.add(gap("OUTPUT_SEED_REQUESTED_OUTPUT_MISSING",
                    requestId));
            return false;
        }
        if (!containsPath(state.summaries, outcome.summary)) {
            state.summaries.add(outcome.summary);
        }
        return true;
    }

    private static boolean containsPath(List<JsonObject> summaries,
                                        JsonObject candidate) {
        String key = RegionPathWorklist.stablePathKey(candidate);
        for (JsonObject summary : summaries) {
            if (string(summary, "regionId").equals(
                    string(candidate, "regionId"))
                    && key.equals(RegionPathWorklist.stablePathKey(summary))) {
                return true;
            }
        }
        return false;
    }

    private static List<JsonObject> rawOutputSummaries(
            List<JsonObject> summaries) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject summary : summaries) {
            if (RegionCaptureGoal.from(summary).isOutputClosure()
                    && !RegionCaptureGoal.from(summary)
                    .isTransitionDiscovery()
                    && object(summary, "regionRelation").size() == 0) {
                result.add(summary);
            }
        }
        return result;
    }

    private static void replaceMergedSummaries(List<JsonObject> all,
                                               List<JsonObject> merged) {
        Set<String> regions = new LinkedHashSet<>();
        for (JsonObject summary : merged) regions.add(string(summary,
                "regionId"));
        all.removeIf(summary -> regions.contains(string(summary, "regionId"))
                && object(summary, "regionRelation").size() > 0);
        all.addAll(merged);
    }

    private static void addRecord(List<JsonObject> records,
                                  JsonObject record) {
        String key = string(record, "queryKey");
        for (int index = 0; index < records.size(); index++) {
            if (key.equals(string(records.get(index), "queryKey"))) {
                records.set(index, record);
                return;
            }
        }
        records.add(record);
    }

    private static JsonObject record(JsonObject task, String status,
                                     String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_EXPLORATION_RECORD");
        result.addProperty("queryKey", string(task, "queryKey"));
        result.addProperty("regionId", string(task, "regionId"));
        result.addProperty("status", status);
        result.addProperty("reason", reason);
        return result;
    }

    private static JsonObject gap(String kind, String reason) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", kind);
        result.addProperty("reason", reason);
        return result;
    }

    private static void addGapOnce(List<JsonObject> gaps,
                                   JsonObject candidate) {
        for (JsonObject existing : gaps) {
            if (string(existing, "kind").equals(string(candidate, "kind"))
                    && string(existing, "reason").equals(string(candidate,
                    "reason"))) return;
        }
        gaps.add(candidate);
    }

    private static JsonObject activation(List<JsonObject> activations,
                                         String id) {
        for (JsonObject activation : activations) {
            if (id.equals(string(activation, "activationId"))) {
                return activation;
            }
        }
        return null;
    }

    private static void addOrReplaceActivation(List<JsonObject> activations,
                                               JsonObject activation) {
        String id = string(activation, "activationId");
        for (int index = 0; index < activations.size(); index++) {
            if (id.equals(string(activations.get(index), "activationId"))) {
                activations.set(index, activation);
                return;
            }
        }
        activations.add(activation);
    }

    /**
     * Admits runtime graph evidence produced by the same accepted execution.
     * Dynamic ids restart in every JVM, so rows are namespaced before they can
     * participate in another worklist iteration. Static region and edge ids
     * deliberately remain stable across executions.
     */
    private static void admitDiscoveredEvidence(ExecutionOutcome outcome,
                                                State state,
                                                RuntimeDiscoveryMode mode,
                                                JsonObject sourceReplay) {
        // FIXED_VALIDATED_GRAPH deliberately freezes the runtime-selected
        // activation/edge graph supplied at campaign start.  Even a custom
        // backend that accidentally returns discovery rows cannot widen that
        // graph and silently turn a bounded fixed-graph result into a dynamic
        // closure claim.
        if (mode == RuntimeDiscoveryMode.FIXED_VALIDATED_GRAPH) return;
        if (outcome == null || state == null
                || outcome.discoveredActivations.isEmpty()
                && outcome.discoveredEdges.isEmpty()) {
            return;
        }
        String execution = outcome.executionId.trim();
        if (execution.isEmpty()) {
            execution = "EXEC." + shortHash(outcome.rawResult.toString()
                    + "\n" + outcome.discoveredActivations.toString()
                    + "\n" + outcome.discoveredEdges.toString());
        }
        List<JsonObject> normalizedEdges = new ArrayList<>();
        for (JsonObject edge : outcome.discoveredEdges) {
            JsonObject admitted = namespaceDynamicIds(edge, execution);
            admitted.addProperty("discoveredExecutionId", execution);
            normalizedEdges.add(admitted);
        }
        JsonArray reachabilitySupport = reachabilitySupportIncluding(
                sourceReplay);
        for (JsonObject activation : outcome.discoveredActivations) {
            JsonObject admitted = namespaceDynamicIds(activation, execution);
            admitted.addProperty("discoveredExecutionId", execution);
            admitted.add("reachabilitySupportActivations",
                    reachabilitySupport.deepCopy());
            JsonArray outboundBindings = outboundBindings(admitted,
                    normalizedEdges);
            if (outboundBindings.size() > 0) {
                admitted.add("edgeBindings", outboundBindings);
            }
            JsonObject targetRoot = exactTargetRootTemplate(activation,
                    state.roots);
            if (targetRoot != null) {
                admitted.addProperty("postDiscoveryTargetRebaseCandidate",
                        true);
                admitted.addProperty("postDiscoveryTargetRebaseAuthority",
                        "SAME_EXECUTION_EXACT_FATAL_ROOT_ACTIVATION");
                admitted.addProperty("replacesTargetActivationId",
                        string(targetRoot, "activationId"));
                admitted.addProperty("replacesTargetRegionInstanceId",
                        string(targetRoot, "regionInstanceId"));
                admitted.addProperty("postDiscoveryTargetExecutionId",
                        execution);
            }
            addOrReplaceActivation(state.activations, admitted);
        }
        for (JsonObject admitted : normalizedEdges) {
            mergeDiscoveredEdge(state.edges, admitted, execution);
        }
    }

    private static JsonArray outboundBindings(JsonObject activation,
                                               List<JsonObject> edges) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        String instance = string(activation, "regionInstanceId");
        for (JsonElement element : array(activation, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!instance.equals(string(binding,
                    "fromRegionInstance"))) continue;
            if (seen.add(binding.toString())) result.add(binding.deepCopy());
        }
        for (JsonObject edge : edges) {
            for (JsonElement element : array(edge, "validatedBindings")) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!instance.equals(string(binding,
                        "fromRegionInstance"))) continue;
                JsonObject enriched = binding.deepCopy();
                enriched.addProperty("edgeId", string(edge, "edgeId"));
                enriched.addProperty("fromRegion", string(edge,
                        "fromRegion"));
                enriched.addProperty("toRegion", string(edge,
                        "toRegion"));
                enriched.addProperty("fromOutputPort", string(edge,
                        "fromPort"));
                enriched.addProperty("toInputPort", string(edge,
                        "toPort"));
                if (seen.add(enriched.toString())) result.add(enriched);
            }
        }
        return result;
    }

    /** Finds one exact fresh activation corresponding to a fatal root. */
    private static JsonObject exactTargetRootTemplate(JsonObject activation,
                                                      List<JsonObject> roots) {
        JsonObject match = null;
        for (JsonObject root : roots) {
            if (!string(root, "regionId").equals(string(activation,
                    "regionId"))) continue;
            String rootMethod = string(root, "rootMethod");
            if (!rootMethod.isEmpty() && !rootMethod.equals(string(
                    activation, "rootMethod"))) continue;
            String test = string(root, "test");
            if (!test.isEmpty() && !test.equals(string(activation,
                    "test"))) continue;
            if (root.has("invocationOrdinal")
                    && integer(root, "invocationOrdinal", 1) != integer(
                    activation, "invocationOrdinal", 1)) continue;
            if (string(activation, "activationId").isEmpty()
                    || string(activation, "regionInstanceId").isEmpty()) {
                continue;
            }
            if (match != null) return null;
            match = root;
        }
        return match;
    }

    private static JsonObject namespaceDynamicIds(JsonObject source,
                                                  String execution) {
        JsonObject result = source == null
                ? new JsonObject() : source.deepCopy();
        namespaceDynamicIds((JsonElement) result, execution);
        return result;
    }

    private static void namespaceDynamicIds(JsonElement element,
                                            String execution) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement item : element.getAsJsonArray()) {
                namespaceDynamicIds(item, execution);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        for (String key : new ArrayList<>(object.keySet())) {
            JsonElement value = object.get(key);
            if (value != null && value.isJsonPrimitive()
                    && value.getAsJsonPrimitive().isString()
                    && dynamicIdentityField(key)) {
                String identifier = value.getAsString();
                if (!identifier.isEmpty()
                        && !identifier.startsWith(execution + "::")) {
                    object.addProperty(key, execution + "::" + identifier);
                }
            } else {
                namespaceDynamicIds(value, execution);
            }
        }
    }

    private static boolean dynamicIdentityField(String field) {
        return "activationId".equals(field)
                || field.endsWith("ActivationId")
                || "regionInstanceId".equals(field)
                || field.endsWith("RegionInstance")
                || field.endsWith("RegionInstanceId");
    }

    private static void mergeDiscoveredEdge(List<JsonObject> edges,
                                            JsonObject incoming,
                                            String execution) {
        String identity = edgeIdentity(incoming);
        for (int index = 0; index < edges.size(); index++) {
            JsonObject existing = edges.get(index);
            if (!identity.equals(edgeIdentity(existing))) continue;
            JsonObject preferred = edgeRank(incoming) > edgeRank(existing)
                    ? incoming.deepCopy() : existing.deepCopy();
            JsonArray bindings = union(existing, incoming,
                    "validatedBindings");
            JsonArray evidence = union(existing, incoming, "evidence");
            preferred.add("validatedBindings", bindings);
            preferred.addProperty("validatedBindingCount", bindings.size());
            preferred.add("evidence", evidence);
            preferred.add("discoveredExecutionIds", unionString(
                    array(existing, "discoveredExecutionIds"),
                    array(incoming, "discoveredExecutionIds"), execution));
            preserveMaximum(preferred, existing, incoming,
                    "endpointPairCount", "orderedPairCount",
                    "siteObservedPairCount");
            int readFrom = Math.max(Math.max(integer(existing,
                    "confirmedReadFromPairCount", 0), integer(incoming,
                    "confirmedReadFromPairCount", 0)),
                    countBindings(bindings, true));
            int equality = Math.max(Math.max(integer(existing,
                    "confirmedValueEqualityPairCount", 0), integer(incoming,
                    "confirmedValueEqualityPairCount", 0)),
                    countBindings(bindings, false));
            preferred.addProperty("confirmedReadFromPairCount", readFrom);
            preferred.addProperty("confirmedValueEqualityPairCount",
                    equality);
            edges.set(index, preferred);
            return;
        }
        JsonObject added = incoming.deepCopy();
        JsonArray executions = array(added, "discoveredExecutionIds")
                .deepCopy();
        if (execution != null && !execution.isEmpty()) {
            executions.add(execution);
        }
        if (executions.size() > 0) {
            added.add("discoveredExecutionIds", executions);
        }
        edges.add(added);
    }

    private static String edgeIdentity(JsonObject edge) {
        return string(edge, "edgeId") + "\n"
                + string(edge, "fromRegion") + "\n"
                + canonicalPort(string(edge, "fromPort")) + "\n"
                + string(edge, "toRegion") + "\n"
                + canonicalPort(string(edge, "toPort"));
    }

    private static int edgeRank(JsonObject edge) {
        if (AutomaticRegionEdge.composable(edge)) return 3;
        if (AutomaticRegionEdge.discoverable(edge)) return 2;
        return 1;
    }

    private static JsonArray union(JsonObject left, JsonObject right,
                                   String field) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        appendUnique(result, seen, array(left, field));
        appendUnique(result, seen, array(right, field));
        return result;
    }

    private static void appendUnique(JsonArray result, Set<String> seen,
                                     JsonArray values) {
        for (JsonElement value : values) {
            String key = value.toString();
            if (seen.add(key)) result.add(value.deepCopy());
        }
    }

    private static JsonArray unionString(JsonArray left, JsonArray right,
                                         String value) {
        JsonArray result = new JsonArray();
        Set<String> seen = new LinkedHashSet<>();
        appendUniqueString(result, seen, left);
        appendUniqueString(result, seen, right);
        if (value != null && !value.isEmpty() && seen.add(value)) {
            result.add(value);
        }
        return result;
    }

    private static void appendUniqueString(JsonArray result, Set<String> seen,
                                           JsonArray values) {
        for (JsonElement item : values) {
            if (!item.isJsonPrimitive()) continue;
            String value = item.getAsString();
            if (seen.add(value)) result.add(value);
        }
    }

    private static void preserveMaximum(JsonObject target, JsonObject left,
                                        JsonObject right, String... fields) {
        for (String field : fields) {
            target.addProperty(field, Math.max(integer(left, field, 0),
                    integer(right, field, 0)));
        }
    }

    private static int countBindings(JsonArray bindings,
                                     boolean readFrom) {
        int result = 0;
        for (JsonElement element : bindings) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (readFrom && binding.has("writeSeq")
                    && binding.has("readSeq")) {
                result++;
            } else if (!readFrom
                    && bool(binding, "valueEqualityObserved", false)) {
                result++;
            }
        }
        return result;
    }

    /**
     * Authority used for the runtime activation/edge graph during a campaign.
     * The default remains fail-closed same-execution discovery.  The fixed
     * mode is explicit and limits every result to the validated graph that was
     * selected as campaign input; it never claims discovery outside it.
     */
    public enum RuntimeDiscoveryMode {
        SAME_EXECUTION_REQUIRED,
        FIXED_VALIDATED_GRAPH;

        boolean isFixedValidatedGraph() {
            return this == FIXED_VALIDATED_GRAPH;
        }

        static RuntimeDiscoveryMode parse(String value) {
            String normalized = value == null ? "" : value.trim();
            if (normalized.isEmpty()) return SAME_EXECUTION_REQUIRED;
            try {
                return RuntimeDiscoveryMode.valueOf(normalized);
            } catch (IllegalArgumentException exception) {
                throw new IllegalArgumentException(
                        "Unsupported --runtime-discovery-mode " + value
                                + "; expected SAME_EXECUTION_REQUIRED or "
                                + "FIXED_VALIDATED_GRAPH", exception);
            }
        }
    }

    public interface ExecutionBackend {
        ExecutionOutcome execute(JsonObject captureRequest) throws Exception;

        default RuntimeDiscoveryMode runtimeDiscoveryMode() {
            return RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED;
        }
    }

    public static final class ExecutionOutcome {
        public final String status;
        public final JsonObject rawResult;
        public final JsonObject summary;
        public final String executionId;
        public final List<JsonObject> discoveredActivations;
        public final List<JsonObject> discoveredEdges;

        public ExecutionOutcome(String status, JsonObject rawResult,
                                JsonObject summary) {
            this(status, rawResult, summary, "",
                    Collections.<JsonObject>emptyList(),
                    Collections.<JsonObject>emptyList());
        }

        public ExecutionOutcome(String status, JsonObject rawResult,
                                JsonObject summary, String executionId,
                                List<JsonObject> discoveredActivations,
                                List<JsonObject> discoveredEdges) {
            this.status = status == null ? "" : status;
            this.rawResult = rawResult == null ? new JsonObject() : rawResult;
            this.summary = summary;
            this.executionId = executionId == null ? "" : executionId;
            this.discoveredActivations = State.copy(discoveredActivations);
            this.discoveredEdges = State.copy(discoveredEdges);
        }
    }

    /** External command adapter; the command receives only file locations. */
    static final class CommandBackend implements ExecutionBackend {
        private final Path outputDirectory;
        private final Path regions;
        private final List<String> command;
        private final long timeoutMillis;
        private final RuntimeDiscoveryMode runtimeDiscoveryMode;

        CommandBackend(Path outputDirectory, Path regions,
                       List<String> command, long timeoutMillis) {
            this(outputDirectory, regions, command, timeoutMillis,
                    RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED);
        }

        CommandBackend(Path outputDirectory, Path regions,
                       List<String> command, long timeoutMillis,
                       RuntimeDiscoveryMode runtimeDiscoveryMode) {
            this.outputDirectory = outputDirectory;
            this.regions = regions;
            this.command = command;
            this.timeoutMillis = timeoutMillis;
            this.runtimeDiscoveryMode = runtimeDiscoveryMode == null
                    ? RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED
                    : runtimeDiscoveryMode;
        }

        @Override
        public RuntimeDiscoveryMode runtimeDiscoveryMode() {
            return runtimeDiscoveryMode;
        }

        @Override
        public ExecutionOutcome execute(JsonObject request) throws Exception {
            if (command.isEmpty()) return new ExecutionOutcome(
                    "NO_EXECUTION_COMMAND", new JsonObject(), null);
            String key = shortHash(string(request, "requestKey"));
            // Keep the semantic request slot stable for resume/provenance,
            // but never share mutable JVM products between concrete attempts.
            // A timed-out process may continue shutting down briefly and must
            // not be able to overwrite a retry's raw/import/discovery files.
            String executionId = "EXEC." + key + "."
                    + java.util.UUID.randomUUID().toString();
            Path requestDirectory = outputDirectory.resolve("executions")
                    .resolve(key);
            Path directory = requestDirectory.resolve("attempts").resolve(
                    filesystemSafeExecutionId(executionId));
            Files.createDirectories(directory);
            Path plan = directory.resolve("activation_plan.jsonl");
            Path requestFile = directory.resolve("capture_request.json");
            Path executionManifest = directory.resolve(
                    "execution_manifest.json");
            Path raw = directory.resolve("concolic_region_results.jsonl");
            Path summaries = directory.resolve(
                    "concolic_region_summaries.jsonl");
            Path diagnostics = directory.resolve(
                    "concolic_import_diagnostics.jsonl");
            Path discoveredActivations = directory.resolve(
                    "discovered_activation_plan.jsonl");
            Path discoveredEdges = directory.resolve(
                    "discovered_edge_validation.jsonl");
            List<JsonObject> activationPlan = activationPlan(request);
            if (activationPlan.size() > 1) {
                for (JsonObject activation : activationPlan) {
                    activation.addProperty("activationSelectionRequired",
                            "ALL");
                }
            }
            writeJsonl(plan, activationPlan);
            JsonObject persistedRequest = request.deepCopy();
            persistedRequest.addProperty("runtimeDiscoveryMode",
                    runtimeDiscoveryMode.name());
            Files.write(requestFile, GSON.toJson(persistedRequest)
                            .getBytes(StandardCharsets.UTF_8),
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);
            JsonObject attemptManifest = new JsonObject();
            attemptManifest.addProperty("schemaVersion", 1);
            attemptManifest.addProperty("kind",
                    "CONCOLIC_CAMPAIGN_EXECUTION");
            attemptManifest.addProperty("executionId", executionId);
            attemptManifest.addProperty("runtimeDiscoveryMode",
                    runtimeDiscoveryMode.name());
            attemptManifest.addProperty("sameExecutionRuntimeDiscoveryRequired",
                    !runtimeDiscoveryMode.isFixedValidatedGraph());
            attemptManifest.addProperty("runtimeGraphScope",
                    runtimeDiscoveryMode.isFixedValidatedGraph()
                            ? "RUNTIME_SELECTED_FIXED_VALIDATED_GRAPH"
                            : "SAME_EXECUTION_DISCOVERED_GRAPH");
            attemptManifest.addProperty("activationPlanCount",
                    activationPlan.size());
            attemptManifest.addProperty("reachabilitySupportActivationCount",
                    Math.max(0, activationPlan.size() - 1));
            attemptManifest.addProperty("activationSelection",
                    activationPlan.size() > 1
                            ? "ALL_REQUIRED_REACHABILITY_BUNDLE"
                            : "PRIMARY_ONLY");
            Files.write(executionManifest,
                    (GSON.toJson(attemptManifest) + System.lineSeparator())
                            .getBytes(StandardCharsets.UTF_8),
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.inheritIO();
            Map<String, String> environment = builder.environment();
            environment.put("CAUSYNTH_CAMPAIGN_ACTIVATION_PLAN",
                    plan.toAbsolutePath().toString());
            environment.put("CAUSYNTH_CAMPAIGN_ACTIVATION_ID",
                    activationPlan.size() > 1 ? "ALL"
                            : string(request, "activationId"));
            environment.put("CAUSYNTH_CAMPAIGN_RESULTS",
                    raw.toAbsolutePath().toString());
            environment.put("CAUSYNTH_CAMPAIGN_REQUEST",
                    requestFile.toAbsolutePath().toString());
            environment.put("CAUSYNTH_CAMPAIGN_EXECUTION_ID", executionId);
            environment.put("CAUSYNTH_CAMPAIGN_RUNTIME_DISCOVERY_MODE",
                    runtimeDiscoveryMode.name());
            if (runtimeDiscoveryMode.isFixedValidatedGraph()) {
                // Remove inherited values too: their mere presence causes the
                // HDFS wrapper to aggregate a whole-JVM runtime graph.
                environment.remove(
                        "CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS");
                environment.remove("CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES");
            } else {
                environment.put("CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS",
                        discoveredActivations.toAbsolutePath().toString());
                environment.put("CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES",
                        discoveredEdges.toAbsolutePath().toString());
            }
            Process process = builder.start();
            boolean finished = process.waitFor(timeoutMillis,
                    java.util.concurrent.TimeUnit.MILLISECONDS);
            if (!finished) {
                process.destroyForcibly();
                process.waitFor();
                return new ExecutionOutcome("TIMEOUT", new JsonObject(), null,
                        executionId, Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList());
            }
            int processExit = process.exitValue();
            // A naturally reached target bug commonly makes the HDFS-owned
            // JUnit process exit non-zero after the selected region has
            // already emitted its raw custom-JDK result.  Exit status alone
            // is not admission authority: the importer and unforced replay
            // validator below still have to accept the fresh raw evidence.
            if (!Files.isRegularFile(raw)) {
                return new ExecutionOutcome("EXECUTION_FAILED",
                        new JsonObject(), null, executionId,
                        Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList());
            }
            // SAME_EXECUTION_REQUIRED stays fail-closed: both files must
            // exist even when they contain zero rows. FIXED_VALIDATED_GRAPH
            // intentionally supplies no discovery destinations and uses only
            // the immutable validated graph selected at campaign start.
            if (!runtimeDiscoveryMode.isFixedValidatedGraph()
                    && (!Files.isRegularFile(discoveredActivations)
                    || !Files.isRegularFile(discoveredEdges))) {
                return new ExecutionOutcome("DISCOVERY_FAILED",
                        new JsonObject(), null, executionId,
                        Collections.<JsonObject>emptyList(),
                        Collections.<JsonObject>emptyList());
            }
            List<JsonObject> freshActivations = runtimeDiscoveryMode
                    .isFixedValidatedGraph()
                    ? Collections.<JsonObject>emptyList()
                    : readOptionalJsonl(discoveredActivations);
            List<JsonObject> freshEdges = runtimeDiscoveryMode
                    .isFixedValidatedGraph()
                    ? Collections.<JsonObject>emptyList()
                    : readOptionalJsonl(discoveredEdges);
            Path importPlan = plan;
            if ("TRANSITION_OUTPUT_REPLAY".equals(string(request,
                    "kind")) && !runtimeDiscoveryMode
                    .isFixedValidatedGraph()) {
                ExecutionOutcome finalEvidence = new ExecutionOutcome(
                        processExit == 0 ? "SUCCEEDED"
                                : "SUCCEEDED_WITH_NONZERO_EXIT_"
                                + processExit,
                        new JsonObject(), null, executionId,
                        freshActivations, freshEdges);
                JsonObject refinement = transitionOutputRefinement(
                        object(request, "pathTask"),
                        object(request, "activation"), finalEvidence);
                Path evidenceFile = directory.resolve(
                        "final_output_capture_refinement.json");
                Files.write(evidenceFile,
                        (GSON.toJson(refinement)
                                + System.lineSeparator()).getBytes(
                                StandardCharsets.UTF_8),
                        StandardOpenOption.CREATE,
                        StandardOpenOption.TRUNCATE_EXISTING,
                        StandardOpenOption.WRITE);
                if (!bool(refinement, "ready", false)) {
                    List<JsonObject> rawRows = readJsonl(raw);
                    JsonObject primaryRaw = primaryExecutionRow(rawRows,
                            request);
                    return new ExecutionOutcome(processExit == 0
                                    ? "OUTPUT_REFINEMENT_FAILED"
                                    : "OUTPUT_REFINEMENT_FAILED_WITH_"
                                    + "NONZERO_EXIT_" + processExit,
                            primaryRaw == null ? new JsonObject()
                                    : primaryRaw,
                            null, executionId, freshActivations,
                            freshEdges);
                }
                JsonObject rebasedPrimary = object(refinement,
                        "activation").deepCopy();
                List<JsonObject> rebasedPlan = new ArrayList<>();
                String primaryId = string(object(request, "activation"),
                        "activationId");
                int replaced = 0;
                for (JsonObject activation : activationPlan) {
                    if (primaryId.equals(string(activation,
                            "activationId"))) {
                        rebasedPlan.add(rebasedPrimary.deepCopy());
                        replaced++;
                    } else {
                        rebasedPlan.add(activation.deepCopy());
                    }
                }
                if (replaced != 1) {
                    List<JsonObject> rawRows = readJsonl(raw);
                    JsonObject primaryRaw = primaryExecutionRow(rawRows,
                            request);
                    return new ExecutionOutcome(
                            "OUTPUT_REFINEMENT_REBASE_FAILED",
                            primaryRaw == null ? new JsonObject()
                                    : primaryRaw,
                            null, executionId, freshActivations,
                            freshEdges);
                }
                importPlan = directory.resolve(
                        "import_activation_plan.jsonl");
                writeJsonl(importPlan, rebasedPlan);
            }
            boolean discoveryOnly = RegionCaptureGoal.from(object(request,
                    "activation")).isTransitionDiscovery();
            ConcolicSummaryImporter.importSummaries(raw, importPlan, regions,
                    summaries, diagnostics, directory.resolve(discoveryOnly
                            ? "discovery-summary-quarantine"
                            : "summary-cache"));
            List<JsonObject> rawRows = readJsonl(raw);
            List<JsonObject> summaryRows = readJsonl(summaries);
            JsonObject primaryRaw = primaryExecutionRow(rawRows, request);
            JsonObject primarySummary = primaryExecutionRow(summaryRows,
                    request);
            return new ExecutionOutcome(processExit == 0
                            ? "SUCCEEDED"
                            : "SUCCEEDED_WITH_NONZERO_EXIT_" + processExit,
                    primaryRaw == null ? new JsonObject() : primaryRaw,
                    primarySummary,
                    executionId,
                    freshActivations, freshEdges);
        }

        /** Fail closed instead of mistaking a support replay for capture. */
        static JsonObject primaryExecutionRow(List<JsonObject> rows,
                                              JsonObject request) {
            String activationId = string(request, "activationId");
            String regionId = string(request, "regionId");
            JsonObject selected = null;
            for (JsonObject row : rows == null
                    ? Collections.<JsonObject>emptyList() : rows) {
                if (!activationId.equals(string(row, "activationId"))
                        || !regionId.isEmpty() && !regionId.equals(string(
                        row, "regionId"))) continue;
                if (selected != null) return null;
                selected = row;
            }
            return selected == null ? null : selected.deepCopy();
        }

        static List<JsonObject> activationPlan(JsonObject request) {
            LinkedHashMap<String, JsonObject> ordered = new LinkedHashMap<>();
            JsonArray support = array(request,
                    "reachabilitySupportActivations");
            if (support.size() == 0) {
                support = flattenedReachabilitySupport(object(request,
                        "activation"));
            }
            for (JsonElement element : support) {
                if (!element.isJsonObject()) continue;
                appendPlanActivation(ordered, element.getAsJsonObject());
            }
            JsonObject primary = object(request, "activation").deepCopy();
            primary.remove("reachabilitySupportActivations");
            String primaryId = string(primary, "activationId");
            if (!primaryId.isEmpty()) {
                // The capture row is authoritative and must remain last even
                // if a malformed bundle repeated its id as support.
                ordered.remove(primaryId);
                ordered.put(primaryId, primary);
            }
            return new ArrayList<>(ordered.values());
        }

        private static void appendPlanActivation(
                LinkedHashMap<String, JsonObject> ordered,
                JsonObject activation) {
            for (JsonElement nested : array(activation,
                    "reachabilitySupportActivations")) {
                if (nested.isJsonObject()) appendPlanActivation(ordered,
                        nested.getAsJsonObject());
            }
            JsonObject flattened = activation.deepCopy();
            flattened.remove("reachabilitySupportActivations");
            String id = string(flattened, "activationId");
            if (!id.isEmpty() && !ordered.containsKey(id)) {
                ordered.put(id, flattened);
            }
        }

        /** A single path component with deterministic collision resistance. */
        static String filesystemSafeExecutionId(String executionId) {
            String original = executionId == null ? "" : executionId;
            StringBuilder safe = new StringBuilder();
            for (int index = 0; index < original.length(); index++) {
                char value = original.charAt(index);
                if ((value >= 'a' && value <= 'z')
                        || (value >= 'A' && value <= 'Z')
                        || (value >= '0' && value <= '9')
                        || value == '.' || value == '-' || value == '_') {
                    safe.append(value);
                } else {
                    safe.append('_');
                }
            }
            String component = safe.toString();
            if (component.isEmpty() || ".".equals(component)
                    || "..".equals(component)) component = "execution";
            if (component.length() > 96) component = component.substring(0,
                    96);
            // Always suffix the original hash: distinct unsafe ids that
            // sanitize to the same component still get distinct directories.
            return component + "-" + shortHash(original);
        }
    }

    public static final class State {
        public final List<JsonObject> regions;
        public final List<JsonObject> activations;
        public final List<JsonObject> edges;
        public final List<JsonObject> roots;
        public final List<JsonObject> summaries;
        public final List<JsonObject> pathRecords;
        public final List<JsonObject> staticGraph;

        public State(List<JsonObject> regions, List<JsonObject> activations,
                     List<JsonObject> edges, List<JsonObject> roots,
                     List<JsonObject> summaries,
                     List<JsonObject> pathRecords) {
            this(regions, activations, edges, roots, summaries, pathRecords,
                    Collections.<JsonObject>emptyList());
        }

        public State(List<JsonObject> regions, List<JsonObject> activations,
                     List<JsonObject> edges, List<JsonObject> roots,
                     List<JsonObject> summaries,
                     List<JsonObject> pathRecords,
                     List<JsonObject> staticGraph) {
            this.regions = copy(regions);
            this.activations = copy(activations);
            this.edges = copy(edges);
            this.roots = copy(roots);
            this.summaries = copy(summaries);
            this.pathRecords = copy(pathRecords);
            this.staticGraph = copy(staticGraph);
        }

        private State copy() {
            return new State(regions, activations, edges, roots, summaries,
                    pathRecords, staticGraph);
        }

        private static List<JsonObject> copy(List<JsonObject> values) {
            List<JsonObject> result = new ArrayList<>();
            if (values != null) {
                for (JsonObject value : values) result.add(value.deepCopy());
            }
            return result;
        }
    }

    public static final class Bounds {
        public final int maxIterations;
        public final int maxExecutions;
        public final int maxSolverQueries;
        public final long maxWallClockMillis;
        public final long solverTimeoutMillis;
        public final RecursiveRegionWorklist.Bounds graphBounds;
        public final RegionPathWorklist.Bounds pathBounds;

        public Bounds(int maxIterations, int maxExecutions,
                      int maxSolverQueries, long maxWallClockMillis,
                      long solverTimeoutMillis,
                      RecursiveRegionWorklist.Bounds graphBounds,
                      RegionPathWorklist.Bounds pathBounds) {
            this.maxIterations = Math.max(1, maxIterations);
            this.maxExecutions = Math.max(1, maxExecutions);
            this.maxSolverQueries = Math.max(1, maxSolverQueries);
            this.maxWallClockMillis = Math.max(1L, maxWallClockMillis);
            this.solverTimeoutMillis = Math.max(1L, solverTimeoutMillis);
            this.graphBounds = graphBounds == null
                    ? RecursiveRegionWorklist.Bounds.defaults() : graphBounds;
            this.pathBounds = pathBounds == null
                    ? RegionPathWorklist.Bounds.defaults() : pathBounds;
        }

        public static Bounds defaults() {
            return new Bounds(128, 512, 512, 300_000L, 20_000L,
                    RecursiveRegionWorklist.Bounds.defaults(),
                    RegionPathWorklist.Bounds.defaults());
        }
    }

    public static final class Result {
        public final State state;
        public final List<JsonObject> mergedSummaries;
        public final JsonObject manifest;

        private Result(State state, List<JsonObject> mergedSummaries,
                       JsonObject manifest) {
            this.state = state;
            this.mergedSummaries = new ArrayList<>(mergedSummaries);
            this.manifest = manifest;
        }
    }

    static final class CampaignLock implements AutoCloseable {
        private final FileChannel channel;
        private final FileLock lock;

        private CampaignLock(FileChannel channel, FileLock lock) {
            this.channel = channel;
            this.lock = lock;
        }

        @Override
        public void close() throws IOException {
            try {
                if (lock != null && lock.isValid()) lock.release();
            } finally {
                channel.close();
            }
        }
    }

    private static final class CampaignSnapshot {
        private final List<JsonObject> regions;
        private final List<JsonObject> activations;
        private final List<JsonObject> edges;
        private final List<JsonObject> roots;
        private final List<JsonObject> summaries;
        private final List<JsonObject> pathRecords;
        private final List<JsonObject> staticGraph;

        private CampaignSnapshot(List<JsonObject> regions,
                                 List<JsonObject> activations,
                                 List<JsonObject> edges,
                                 List<JsonObject> roots,
                                 List<JsonObject> summaries,
                                 List<JsonObject> pathRecords,
                                 List<JsonObject> staticGraph) {
            this.regions = regions;
            this.activations = activations;
            this.edges = edges;
            this.roots = roots;
            this.summaries = summaries;
            this.pathRecords = pathRecords;
            this.staticGraph = staticGraph;
        }

        private static CampaignSnapshot read(Path manifestPath)
                throws IOException {
            if (manifestPath == null || !Files.isRegularFile(manifestPath)) {
                throw new IOException("CAMPAIGN_STATE_MANIFEST_MISSING:"
                        + manifestPath);
            }
            byte[] pointerBytes = Files.readAllBytes(manifestPath);
            JsonObject pointer = parseObject(pointerBytes,
                    "CAMPAIGN_STATE_POINTER_INVALID_JSON");
            if (!"CONCOLIC_CAMPAIGN_STATE_POINTER".equals(string(pointer,
                    "kind"))
                    || !bool(pointer, "complete", false)
                    || string(pointer, "generation").isEmpty()
                    || string(pointer, "manifest").isEmpty()
                    || string(pointer, "manifestSha256").isEmpty()) {
                throw new IOException("CAMPAIGN_STATE_POINTER_INCOMPLETE");
            }
            Path directory = manifestPath.toAbsolutePath().normalize()
                    .getParent();
            Path generationRoot = directory.resolve("state-generations")
                    .normalize();
            Path immutableManifest = directory.resolve(string(pointer,
                    "manifest")).normalize();
            if (!immutableManifest.startsWith(generationRoot)
                    || !Files.isRegularFile(immutableManifest)) {
                throw new IOException(
                        "CAMPAIGN_STATE_GENERATION_MANIFEST_MISSING");
            }
            byte[] manifestBytes = Files.readAllBytes(immutableManifest);
            if (!sha256(manifestBytes).equals(string(pointer,
                    "manifestSha256"))) {
                throw new IOException(
                        "CAMPAIGN_STATE_GENERATION_MANIFEST_HASH_MISMATCH");
            }
            JsonObject manifest = parseObject(manifestBytes,
                    "CAMPAIGN_STATE_GENERATION_MANIFEST_INVALID_JSON");
            if (!"CONCOLIC_CAMPAIGN_STATE_GENERATION".equals(string(
                    manifest, "kind"))
                    || !bool(manifest, "complete", false)
                    || !string(pointer, "generation").equals(string(
                    manifest, "generation"))) {
                throw new IOException(
                        "CAMPAIGN_STATE_GENERATION_MANIFEST_INCOMPLETE");
            }
            if (integer(pointer, "schemaVersion", 1) >= 2
                    || integer(manifest, "schemaVersion", 1) >= 2) {
                String completionFile = string(pointer,
                        "campaignCompleteManifest");
                String completionHash = string(pointer,
                        "campaignCompleteManifestSha256");
                if (completionFile.isEmpty() || completionHash.isEmpty()
                        || !completionHash.equals(string(manifest,
                        "campaignCompleteManifestSha256"))) {
                    throw new IOException(
                            "CAMPAIGN_COMPLETION_SNAPSHOT_BINDING_MISMATCH");
                }
                Path completionPath = directory.resolve(completionFile)
                        .normalize();
                if (!completionPath.getParent().equals(
                        immutableManifest.getParent())
                        || !completionPath.getFileName().toString().equals(
                        string(manifest, "campaignCompleteManifest"))
                        || !Files.isRegularFile(completionPath)) {
                    throw new IOException(
                            "CAMPAIGN_COMPLETION_SNAPSHOT_MISSING");
                }
                byte[] completionBytes = Files.readAllBytes(completionPath);
                if (!sha256(completionBytes).equals(completionHash)) {
                    throw new IOException(
                            "CAMPAIGN_COMPLETION_SNAPSHOT_HASH_MISMATCH");
                }
                JsonObject completion = parseObject(completionBytes,
                        "CAMPAIGN_COMPLETION_SNAPSHOT_INVALID_JSON");
                if (!"CONCOLIC_REGION_CAMPAIGN".equals(string(completion,
                        "kind"))) {
                    throw new IOException(
                            "CAMPAIGN_COMPLETION_SNAPSHOT_INVALID_KIND");
                }
            }
            Map<String, List<JsonObject>> rowsByRole = new LinkedHashMap<>();
            Path immutableDirectory = immutableManifest.getParent();
            for (JsonElement element : array(manifest, "stateFiles")) {
                if (!element.isJsonObject()) {
                    throw new IOException(
                            "CAMPAIGN_STATE_FILE_ENTRY_INVALID");
                }
                JsonObject entry = element.getAsJsonObject();
                String role = string(entry, "role");
                String file = string(entry, "file");
                if (role.isEmpty() || file.isEmpty()
                        || rowsByRole.containsKey(role)
                        || !Paths.get(file).getFileName().toString()
                        .equals(file)) {
                    throw new IOException(
                            "CAMPAIGN_STATE_FILE_IDENTITY_INVALID:" + role);
                }
                Path path = immutableDirectory.resolve(file).normalize();
                if (!path.getParent().equals(immutableDirectory)
                        || !Files.isRegularFile(path)) {
                    throw new IOException(
                            "CAMPAIGN_STATE_FILE_MISSING:" + role);
                }
                // One immutable read supplies both the digest and parsed
                // rows; no hash-then-reopen TOCTOU window is accepted.
                byte[] bytes = Files.readAllBytes(path);
                if (!sha256(bytes).equals(string(entry, "sha256"))) {
                    throw new IOException(
                            "CAMPAIGN_STATE_FILE_HASH_MISMATCH:" + role);
                }
                List<JsonObject> rows = parseJsonl(bytes, role);
                int expected = integer(entry, "lineCount", -1);
                if (expected < 0 || rows.size() != expected) {
                    throw new IOException(
                            "CAMPAIGN_STATE_FILE_LINE_COUNT_MISMATCH:"
                                    + role);
                }
                rowsByRole.put(role, rows);
            }
            List<String> required = Arrays.asList("REGIONS", "ACTIVATIONS",
                    "EDGES", "ROOTS", "SUMMARIES", "PATH_RECORDS",
                    "STATIC_GRAPH");
            if (rowsByRole.size() != required.size()
                    || !rowsByRole.keySet().containsAll(required)) {
                throw new IOException(
                        "CAMPAIGN_STATE_FILE_SET_INCOMPLETE");
            }
            List<JsonObject> roots = rowsByRole.get("ROOTS");
            if (roots.isEmpty()) {
                throw new IOException("CAMPAIGN_STATE_ROOTS_EMPTY");
            }
            List<JsonObject> edges = new ArrayList<>();
            for (JsonObject edge : rowsByRole.get("EDGES")) {
                mergeDiscoveredEdge(edges, edge, "");
            }
            return new CampaignSnapshot(rowsByRole.get("REGIONS"),
                    rowsByRole.get("ACTIVATIONS"), edges, roots,
                    rowsByRole.get("SUMMARIES"),
                    rowsByRole.get("PATH_RECORDS"),
                    rowsByRole.get("STATIC_GRAPH"));
        }

        private static JsonObject parseObject(byte[] bytes, String problem)
                throws IOException {
            try {
                JsonElement parsed = JsonParser.parseString(new String(bytes,
                        StandardCharsets.UTF_8));
                if (parsed.isJsonObject()) return parsed.getAsJsonObject();
            } catch (RuntimeException ignored) {
                // Report the stable snapshot diagnostic below.
            }
            throw new IOException(problem);
        }

        private static List<JsonObject> parseJsonl(byte[] bytes, String role)
                throws IOException {
            List<JsonObject> result = new ArrayList<>();
            String[] lines = new String(bytes, StandardCharsets.UTF_8)
                    .split("\\R", -1);
            try {
                for (String line : lines) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalArgumentException();
                    }
                    result.add(parsed.getAsJsonObject());
                }
            } catch (RuntimeException exception) {
                throw new IOException("CAMPAIGN_STATE_FILE_INVALID_JSON:"
                        + role, exception);
            }
            return result;
        }
    }

    private static final class Arguments {
        private Path regions;
        private Path activations;
        private final List<Path> resumeActivations = new ArrayList<>();
        private Path edges;
        private final List<Path> resumeEdges = new ArrayList<>();
        private Path roots;
        private Path resumeRoots;
        private final List<Path> summaries = new ArrayList<>();
        private Path pathRecords;
        private Path resumeStateManifest;
        private Path staticGraph;
        private Path outputDirectory;
        private Path z3 = Paths.get("z3");
        private long executionTimeoutMillis = 600_000L;
        private Bounds bounds = Bounds.defaults();
        private RuntimeDiscoveryMode runtimeDiscoveryMode =
                RuntimeDiscoveryMode.SAME_EXECUTION_REQUIRED;
        private RegionTransitionDiscoveryWorklist.Focus transitionFocus =
                RegionTransitionDiscoveryWorklist.Focus.none();
        private boolean transitionFocusOnly;
        private final List<String> command = new ArrayList<>();

        private static Arguments parse(String[] argv) {
            Arguments result = new Arguments();
            Map<String, String> values = new LinkedHashMap<>();
            boolean command = false;
            for (int index = 0; argv != null && index < argv.length; index++) {
                String item = argv[index];
                if (command) {
                    result.command.add(item);
                    continue;
                }
                if ("--".equals(item)) {
                    command = true;
                    continue;
                }
                if (!item.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException(
                            "Expected --key value, got " + item);
                }
                String value = argv[++index];
                if ("--summaries".equals(item)) {
                    result.summaries.add(Paths.get(value));
                } else if ("--resume-activations".equals(item)) {
                    result.resumeActivations.add(Paths.get(value));
                } else if ("--resume-edges".equals(item)) {
                    result.resumeEdges.add(Paths.get(value));
                } else {
                    values.put(item.substring(2), value);
                }
            }
            result.regions = required(values, "regions");
            result.activations = required(values, "activations");
            result.edges = required(values, "edges");
            result.roots = required(values, "roots");
            result.outputDirectory = required(values, "output-dir");
            if (values.containsKey("path-records")) result.pathRecords =
                    Paths.get(values.get("path-records"));
            if (values.containsKey("resume-state-manifest")) {
                result.resumeStateManifest = Paths.get(values.get(
                        "resume-state-manifest"));
            }
            if (values.containsKey("resume-roots")) result.resumeRoots =
                    Paths.get(values.get("resume-roots"));
            if (values.containsKey("static-graph")) result.staticGraph =
                    Paths.get(values.get("static-graph"));
            if (values.containsKey("z3")) result.z3 =
                    Paths.get(values.get("z3"));
            result.executionTimeoutMillis = longValue(values,
                    "execution-timeout-ms", 600_000L);
            result.runtimeDiscoveryMode = RuntimeDiscoveryMode.parse(
                    values.get("runtime-discovery-mode"));
            result.transitionFocus = new RegionTransitionDiscoveryWorklist
                    .Focus(values.get("transition-focus-edge"),
                    values.get("transition-focus-activation"),
                    values.get("transition-focus-guard"));
            result.transitionFocusOnly = Boolean.parseBoolean(values.get(
                    "transition-focus-only"));
            if (result.transitionFocus.configured()
                    && !result.transitionFocus.hasEdge()) {
                throw new IllegalArgumentException("Transition focus "
                        + "requires --transition-focus-edge");
            }
            if (result.transitionFocusOnly
                    && !result.transitionFocus.hasActivation()) {
                throw new IllegalArgumentException(
                        "--transition-focus-only requires "
                                + "--transition-focus-activation");
            }
            result.bounds = parseBounds(values);
            if (result.command.isEmpty()) throw new IllegalArgumentException(
                    "Execution command is required after --");
            return result;
        }

        private static Path required(Map<String, String> values, String key) {
            String value = values.get(key);
            if (value == null || value.trim().isEmpty()) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return Paths.get(value);
        }
    }

    /** Parses the real CLI grammar while exposing only bounds to tests. */
    static Bounds parseCliBounds(String[] argv) {
        return Arguments.parse(argv).bounds;
    }

    /** Exposes the CLI authority choice to regression tests. */
    static RuntimeDiscoveryMode parseCliRuntimeDiscoveryMode(String[] argv) {
        return Arguments.parse(argv).runtimeDiscoveryMode;
    }

    static RegionTransitionDiscoveryWorklist.Focus parseCliTransitionFocus(
            String[] argv) {
        return Arguments.parse(argv).transitionFocus;
    }

    static boolean parseCliTransitionFocusOnly(String[] argv) {
        return Arguments.parse(argv).transitionFocusOnly;
    }

    /** Package-private so CLI-to-bound wiring can be regression tested. */
    static Bounds parseBounds(Map<String, String> values) {
        Map<String, String> effective = values == null
                ? Collections.<String, String>emptyMap() : values;
        Bounds defaults = Bounds.defaults();
        RecursiveRegionWorklist.Bounds graphDefaults = defaults.graphBounds;
        RecursiveRegionWorklist.Bounds graph =
                new RecursiveRegionWorklist.Bounds(
                        integerValue(effective, "graph-max-depth",
                                graphDefaults.maxDepth),
                        integerValue(effective, "graph-max-regions",
                                graphDefaults.maxRegions),
                        integerValue(effective,
                                "graph-max-activations-per-region",
                                graphDefaults.maxActivationsPerRegion),
                        integerValue(effective,
                                "graph-max-alternative-writers-per-read",
                                graphDefaults.maxAlternativeWritersPerRead),
                        integerValue(effective, "graph-max-queries",
                                graphDefaults.maxQueries),
                        integerValue(effective, "graph-max-paths",
                                graphDefaults.maxPaths),
                        longValue(effective, "graph-max-wall-clock-ms",
                                graphDefaults.maxWallClockMillis));
        RegionPathWorklist.Bounds pathDefaults = defaults.pathBounds;
        RegionPathWorklist.Bounds path = new RegionPathWorklist.Bounds(
                integerValue(effective, "path-max-paths-per-region",
                        pathDefaults.maxPathsPerRegion),
                integerValue(effective, "path-max-flips-per-path",
                        pathDefaults.maxFlipsPerPath),
                integerValue(effective, "path-max-tasks",
                        pathDefaults.maxTasks),
                longValue(effective, "path-max-wall-clock-ms",
                        pathDefaults.maxWallClockMillis));
        return new Bounds(integerValue(effective,
                "max-iterations", defaults.maxIterations),
                integerValue(effective, "max-executions",
                        defaults.maxExecutions),
                integerValue(effective, "max-solver-queries",
                        defaults.maxSolverQueries),
                longValue(effective, "max-wall-clock-ms",
                        defaults.maxWallClockMillis),
                longValue(effective, "solver-timeout-ms",
                        defaults.solverTimeoutMillis), graph, path);
    }

    static void writeOutputs(Path directory, Result result)
            throws IOException {
        Files.createDirectories(directory);
        String generation = java.util.UUID.randomUUID().toString();
        Path generationDirectory = directory.resolve("state-generations")
                .resolve(generation);
        Files.createDirectories(generationDirectory);
        byte[] campaignManifestBytes = (GSON.toJson(result.manifest)
                + System.lineSeparator()).getBytes(StandardCharsets.UTF_8);
        Path immutableCampaignManifest = generationDirectory.resolve(
                "campaign_complete_manifest.json");
        writeBytesAtomically(immutableCampaignManifest,
                campaignManifestBytes);
        Path regions = generationDirectory.resolve(
                "campaign_regions.jsonl");
        Path activations = generationDirectory.resolve(
                "campaign_activations.jsonl");
        Path edges = generationDirectory.resolve(
                "campaign_edge_validations.jsonl");
        Path roots = generationDirectory.resolve("campaign_roots.jsonl");
        Path summaries = generationDirectory.resolve(
                "campaign_summaries.jsonl");
        Path records = generationDirectory.resolve(
                "region_path_records.jsonl");
        Path staticGraph = generationDirectory.resolve(
                "campaign_static_graph.jsonl");
        writeJsonlAtomically(regions, result.state.regions);
        writeJsonlAtomically(activations, result.state.activations);
        writeJsonlAtomically(edges, result.state.edges);
        writeJsonlAtomically(roots, result.state.roots);
        writeJsonlAtomically(summaries, result.state.summaries);
        writeJsonlAtomically(records, result.state.pathRecords);
        writeJsonlAtomically(staticGraph, result.state.staticGraph);

        JsonObject generationManifest = new JsonObject();
        generationManifest.addProperty("schemaVersion", 2);
        generationManifest.addProperty("kind",
                "CONCOLIC_CAMPAIGN_STATE_GENERATION");
        generationManifest.addProperty("generation", generation);
        generationManifest.addProperty("complete", true);
        generationManifest.addProperty("campaignCompleteManifest",
                immutableCampaignManifest.getFileName().toString());
        generationManifest.addProperty("campaignCompleteManifestSha256",
                sha256(campaignManifestBytes));
        JsonArray files = new JsonArray();
        files.add(snapshotFile("REGIONS", regions,
                result.state.regions.size()));
        files.add(snapshotFile("ACTIVATIONS", activations,
                result.state.activations.size()));
        files.add(snapshotFile("EDGES", edges,
                result.state.edges.size()));
        files.add(snapshotFile("ROOTS", roots,
                result.state.roots.size()));
        files.add(snapshotFile("SUMMARIES", summaries,
                result.state.summaries.size()));
        files.add(snapshotFile("PATH_RECORDS", records,
                result.state.pathRecords.size()));
        files.add(snapshotFile("STATIC_GRAPH", staticGraph,
                result.state.staticGraph.size()));
        generationManifest.add("stateFiles", files);
        Path immutableManifest = generationDirectory.resolve(
                "state_manifest.json");
        writeBytesAtomically(immutableManifest,
                (GSON.toJson(generationManifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));

        // Convenience artifacts remain available to humans and older tools,
        // but resume authority is exclusively the immutable generation named
        // by campaign_state_manifest.json below.
        writeJsonlAtomically(directory.resolve("campaign_regions.jsonl"),
                result.state.regions);
        writeJsonlAtomically(directory.resolve(
                        "campaign_activations.jsonl"),
                result.state.activations);
        writeJsonlAtomically(directory.resolve(
                        "campaign_edge_validations.jsonl"),
                result.state.edges);
        writeJsonlAtomically(directory.resolve("campaign_roots.jsonl"),
                result.state.roots);
        writeJsonlAtomically(directory.resolve("campaign_summaries.jsonl"),
                result.state.summaries);
        writeJsonlAtomically(directory.resolve("region_path_records.jsonl"),
                result.state.pathRecords);
        writeJsonlAtomically(directory.resolve(
                        "campaign_static_graph.jsonl"),
                result.state.staticGraph);
        writeJsonlAtomically(directory.resolve(
                "merged_region_summaries.jsonl"),
                result.mergedSummaries);
        writeBytesAtomically(directory.resolve(
                        "concolic_campaign_manifest.json"),
                campaignManifestBytes);

        // Publish one atomic pointer last. Concurrent writers use disjoint,
        // immutable generation directories, so whichever pointer wins names
        // one internally consistent generation rather than a file mixture.
        JsonObject stateManifest = new JsonObject();
        stateManifest.addProperty("schemaVersion", 2);
        stateManifest.addProperty("kind",
                "CONCOLIC_CAMPAIGN_STATE_POINTER");
        stateManifest.addProperty("generation", generation);
        stateManifest.addProperty("complete", true);
        stateManifest.addProperty("manifest",
                directory.toAbsolutePath().normalize().relativize(
                        immutableManifest.toAbsolutePath().normalize())
                        .toString());
        stateManifest.addProperty("manifestSha256",
                sha256(immutableManifest));
        stateManifest.addProperty("campaignCompleteManifest",
                directory.toAbsolutePath().normalize().relativize(
                        immutableCampaignManifest.toAbsolutePath().normalize())
                        .toString());
        stateManifest.addProperty("campaignCompleteManifestSha256",
                sha256(campaignManifestBytes));
        writeBytesAtomically(directory.resolve(
                        "campaign_state_manifest.json"),
                (GSON.toJson(stateManifest) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static JsonObject snapshotFile(String role, Path path,
                                           int lineCount)
            throws IOException {
        JsonObject result = new JsonObject();
        result.addProperty("role", role);
        result.addProperty("file", path.getFileName().toString());
        result.addProperty("sha256", sha256(path));
        result.addProperty("lineCount", lineCount);
        return result;
    }

    private static List<JsonObject> readRoots(Path primary, Path resume)
            throws IOException {
        // A resume root file is a complete authoritative replacement, never
        // an overlay: retaining both old and rebased roots would make target
        // admission ambiguous and could schedule the stale fatal instance.
        return readJsonl(resume == null ? primary : resume);
    }

    private static List<JsonObject> readSummaries(List<Path> paths)
            throws IOException {
        List<JsonObject> result = new ArrayList<>();
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        Set<String> anonymous = new LinkedHashSet<>();
        for (Path path : paths) {
            for (JsonObject summary : readJsonl(path)) {
                String id = string(summary, "summaryId");
                if (id.isEmpty()) {
                    if (anonymous.add(summary.toString())) {
                        result.add(summary);
                    }
                    continue;
                }
                JsonObject prior = byId.get(id);
                if (prior != null && !prior.equals(summary)) {
                    throw new IOException(
                            "CONFLICTING_RESUME_SUMMARY_ID:" + id);
                }
                byId.put(id, summary);
            }
        }
        result.addAll(byId.values());
        return result;
    }

    private static List<JsonObject> readActivations(Path primary,
                                                    List<Path> resumes)
            throws IOException {
        Map<String, JsonObject> byId = new LinkedHashMap<>();
        Map<String, JsonObject> recoveredById = new LinkedHashMap<>();
        List<JsonObject> anonymous = new ArrayList<>();
        for (JsonObject activation : readJsonl(primary)) {
            String id = string(activation, "activationId");
            if (id.isEmpty()) anonymous.add(activation);
            else byId.put(id, activation);
        }
        if (resumes != null) {
            for (Path path : resumes) {
                for (JsonObject activation : readJsonl(path)) {
                    String id = string(activation, "activationId");
                    if (id.isEmpty()) {
                        anonymous.add(activation);
                        continue;
                    }
                    JsonObject prior = recoveredById.get(id);
                    if (prior != null && !prior.equals(activation)) {
                        throw new IOException(
                                "CONFLICTING_RECOVERY_ACTIVATION_ID:" + id);
                    }
                    recoveredById.put(id, activation);
                }
            }
        }
        byId.putAll(recoveredById);
        List<JsonObject> result = new ArrayList<>(byId.values());
        result.addAll(anonymous);
        return result;
    }

    static List<JsonObject> readEdges(Path primary, List<Path> resumes)
            throws IOException {
        List<JsonObject> result = new ArrayList<>();
        for (JsonObject edge : readJsonl(primary)) {
            mergeDiscoveredEdge(result, edge, "");
        }
        if (resumes != null) {
            for (Path path : resumes) {
                for (JsonObject edge : readJsonl(path)) {
                    mergeDiscoveredEdge(result, edge, "");
                }
            }
        }
        return result;
    }

    private static List<JsonObject> readOptionalJsonl(Path path)
            throws IOException {
        return path == null || !Files.isRegularFile(path)
                ? new ArrayList<JsonObject>() : readJsonl(path);
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        if (path == null || !Files.isRegularFile(path)) return result;
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement value = JsonParser.parseString(line);
                if (value.isJsonObject()) result.add(value.getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> values)
            throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        StringBuilder output = new StringBuilder();
        for (JsonObject value : values) output.append(new GsonBuilder()
                .disableHtmlEscaping().create().toJson(value))
                .append(System.lineSeparator());
        Files.write(path, output.toString().getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE);
    }

    private static void writeJsonlAtomically(Path path,
                                             List<JsonObject> values)
            throws IOException {
        StringBuilder output = new StringBuilder();
        for (JsonObject value : values) output.append(new GsonBuilder()
                .disableHtmlEscaping().create().toJson(value))
                .append(System.lineSeparator());
        writeBytesAtomically(path, output.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static void writeBytesAtomically(Path path, byte[] bytes)
            throws IOException {
        Path absolute = path.toAbsolutePath();
        Path parent = absolute.getParent();
        if (parent != null) Files.createDirectories(parent);
        Path temporary = absolute.resolveSibling(absolute.getFileName()
                + ".tmp." + java.util.UUID.randomUUID());
        try {
            Files.write(temporary, bytes, StandardOpenOption.CREATE_NEW,
                    StandardOpenOption.WRITE);
            Files.move(temporary, absolute,
                    StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } finally {
            Files.deleteIfExists(temporary);
        }
    }

    private static String sha256(Path path) throws IOException {
        return sha256(Files.readAllBytes(path));
    }

    private static String sha256(byte[] bytes) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hash = digest.digest(bytes == null ? new byte[0] : bytes);
            StringBuilder result = new StringBuilder();
            for (byte item : hash) result.append(String.format("%02x",
                    item & 0xff));
            return result.toString();
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static long elapsedMillis(long started) {
        return (System.nanoTime() - started) / 1_000_000L;
    }

    private static String shortHash(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest((value == null ? "" : value)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) result.append(String.format("%02x",
                    item & 0xff));
            return result.substring(0, 16);
        } catch (NoSuchAlgorithmException exception) {
            throw new IllegalStateException(exception);
        }
    }

    private static int integerValue(Map<String, String> values, String key,
                                    int fallback) {
        try {
            return Integer.parseInt(values.get(key));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longValue(Map<String, String> values, String key,
                                  long fallback) {
        try {
            return Long.parseLong(values.get(key));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static JsonObject object(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static JsonArray array(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static boolean hasArray(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonArray();
    }

    private static String string(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static String canonicalPort(String value) {
        return value == null ? "" : value.replaceAll("\\s+", " ").trim();
    }

    private static boolean bool(JsonObject owner, String field,
                                boolean fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean exactBoolean(JsonObject owner, String field,
                                        boolean expected) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                && value.getAsBoolean() == expected;
    }

    private static boolean hasBoolean(JsonObject owner, String field) {
        JsonElement value = owner == null ? null : owner.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean();
    }

    private static int integer(JsonObject owner, String field, int fallback) {
        JsonElement value = owner == null ? null : owner.get(field);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }
}
