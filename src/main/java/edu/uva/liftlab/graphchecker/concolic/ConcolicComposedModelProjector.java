package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Projects a satisfiable bounded composed SMT model onto concrete upstream
 * region inputs and emits a bounded natural-propagation replay plan: the same
 * upstream model is applied to every explicitly bounded pre-target producer
 * candidate, followed by one downstream observation-only activation.
 *
 * <p>The projector is deliberately fail-closed.  It selects one guarded case
 * through the composer's declared Boolean selectors and consumes that case's
 * exact raw-symbol-to-SMT-term catalog.  Existing map state is preserved only
 * when the selected activation or raw summary carries a runtime-confirmed
 * producer/state relation; an empty map is never substituted as evidence.
 * Inserted references are constrained non-null before Z3 is invoked.  No
 * downstream replay materialization or branch override is copied into the
 * emitted plan.</p>
 */
public final class ConcolicComposedModelProjector {
    private static final String NULLABLE_STRING_ENCODING_AUTHORITY =
            "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1";
    private static final String TARGET_MAP_STATE = "TARGET_MAP_STATE";
    private static final String LOOKUP_KEY_PRODUCER =
            "LOOKUP_KEY_PRODUCER";
    private static final String CONTAINER_REPLAY_REBINDING_AUTHORITY =
            "EXACT_STATIC_ARRAY_SELECTOR_THEN_ACTIVATION_LOCAL_"
                    + "IDENTITY_REBIND_V1";
    private static final Gson GSON = new GsonBuilder()
            .disableHtmlEscaping().create();
    private static final Gson PRETTY = new GsonBuilder()
            .disableHtmlEscaping().setPrettyPrinting().create();
    private static final Pattern CODE_POSITION = Pattern.compile(
            "^(?:virtual|static)\\s+\\S+\\s+([^.(]+(?:[.$/][^.(]+)*)"
                    + "\\.([^.(]+)\\([^)]*\\):(-?[0-9]+)$");
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "^<([^:]+):\\s+(.+)\\s+([^\\s>]+)>(?:#.*)?$");
    private static final Pattern FIELD_PROJECTION = Pattern.compile(
            "#field:([^#]+)");
    private static final Pattern REGION_INPUT_PORT = Pattern.compile(
            "REGION\\.[0-9]+\\.in\\.[0-9]+");

    private ConcolicComposedModelProjector() {
    }

    public static void main(String[] argv) throws Exception {
        Arguments arguments = Arguments.parse(argv);
        Result result = project(arguments);
        writeJsonl(arguments.output, result.activations);
        write(arguments.manifest, PRETTY.toJson(result.manifest)
                + System.lineSeparator());
        System.out.println(PRETTY.toJson(result.manifest));
    }

    static Result project(Arguments arguments) throws Exception {
        require(arguments.smt, "composed SMT");
        require(arguments.compositionManifest, "composition manifest");
        require(arguments.upstreamSummaries, "upstream summaries");
        require(arguments.staticGraph, "static dataflow graph");
        require(arguments.targetActivations, "target activation plan");
        require(arguments.fatalQueries, "fatal branch queries");
        if (arguments.producerGroups != null) {
            require(arguments.producerGroups, "producer group catalog");
            return projectProducerGroups(arguments);
        }
        require(arguments.upstreamActivations, "upstream activation plan");
        require(arguments.broadcastActivations,
                "bounded broadcast activation plan");

        JsonObject composition = readJson(arguments.compositionManifest);
        if (!bool(composition, "complete", false)
                || !bool(composition, "boundedComposition", false)
                || !bool(composition, "fatalReplayValidated", false)) {
            throw new IOException("Projection requires a complete bounded "
                    + "composition with validated fatal replay");
        }
        if (!strings(array(composition, "boundedUpstreamRegions"))
                .contains(arguments.upstreamRegion)) {
            throw new IOException("Composition is not bounded to requested "
                    + "upstream region " + arguments.upstreamRegion);
        }

        String baseSmt = new String(Files.readAllBytes(arguments.smt),
                StandardCharsets.UTF_8);
        CaseProjectionRegistry caseRegistry = CaseProjectionRegistry.from(
                composition, arguments.upstreamRegion);
        List<String> selectorTerms = caseRegistry.selectorTerms();
        String selectorInput = solverInput(baseSmt,
                Collections.<String>emptyList(), selectorTerms);
        SolverOutput selectorSolver = run(arguments.z3, selectorInput,
                arguments.timeoutMillis);
        requireSuccessfulSolver(selectorSolver,
                "case selector projection");
        String selectorStatus = firstLine(selectorSolver.stdout);
        if (!"sat".equals(selectorStatus)) {
            throw new IOException("Composed case selector model is "
                    + selectorStatus);
        }
        Map<String, String> selectorValues = parseGetValues(
                selectorSolver.stdout, new LinkedHashSet<>(selectorTerms));
        JsonObject selectedCase = caseRegistry.select(selectorValues);
        String selectedSourceSummary = string(selectedCase,
                "sourceSummaryId");

        JsonObject upstreamSummary = selectUpstreamSummary(
                readJsonl(arguments.upstreamSummaries),
                arguments.upstreamRegion, selectedSourceSummary);
        DynamicProjectionRegistry dynamicBindings =
                DynamicProjectionRegistry.fromCatalog(selectedCase,
                        upstreamSummary);
        JsonObject upstreamActivation = selectUpstreamActivation(
                readJsonl(arguments.upstreamActivations), upstreamSummary,
                arguments.upstreamRegion);
        JsonObject targetActivation = selectTargetActivation(
                readJsonl(arguments.targetActivations),
                arguments.targetActivationId,
                string(composition, "fatalRegion"));
        List<JsonObject> broadcastCandidates = selectBroadcastCandidates(
                readJsonl(arguments.broadcastActivations),
                upstreamActivation, targetActivation,
                arguments.upstreamRegion,
                arguments.expectedBroadcastCandidates);
        JsonObject fatalQuery = selectFatalQuery(
                readJsonl(arguments.fatalQueries), targetActivation,
                string(composition, "fatalRegion"));
        List<JsonObject> graph = readJsonl(arguments.staticGraph);

        List<EffectProjection> projections = effectProjections(
                upstreamSummary, upstreamActivation, graph, selectedCase);
        if (projections.isEmpty()) {
            throw new IOException("No projectable finite-map effects in "
                    + arguments.upstreamRegion);
        }
        String preMapInput = projections.get(0).preMapInput;
        for (EffectProjection projection : projections) {
            if (!preMapInput.equals(projection.preMapInput)) {
                throw new IOException("Projectable effects do not share one "
                        + "concrete map pre-state");
            }
        }
        JsonObject mapAction = action(upstreamActivation, preMapInput);
        if (mapAction.size() == 0) {
            throw new IOException("Missing map materialization action for "
                    + preMapInput);
        }
        JsonObject preMapEvidence = preMapProducerEvidence(upstreamSummary,
                upstreamActivation, preMapInput);
        TargetMapBinding targetMap = targetMapInput(upstreamSummary,
                fatalQuery, targetActivation);
        String targetInput = targetMap.inputPort;
        String targetKeyRaw = targetLookupKey(fatalQuery, targetInput);
        if (targetKeyRaw.isEmpty()) {
            throw new IOException("Could not identify the target finite-map "
                    + "lookup key for " + targetInput);
        }

        String targetKeyName = actualTargetLookupTerm(baseSmt, targetInput);
        List<DynamicTermProjection> dynamicProjections =
                dynamicTermProjections(selectedCase, dynamicBindings,
                        upstreamActivation);
        if (dynamicProjections.isEmpty()) {
            throw projectionGap("NO_SELECTED_DYNAMIC_FIELD_BINDING");
        }

        List<String> keyNames = new ArrayList<>();
        List<String> valueNames = new ArrayList<>();
        for (EffectProjection projection : projections) {
            keyNames.add(projection.keySolverTerm);
            valueNames.add(projection.valueSolverTerm);
        }
        List<String> dynamicNames = new ArrayList<>();
        List<String> dynamicQueryNames = new ArrayList<>();
        List<String> dynamicKeys = new ArrayList<>();
        for (DynamicTermProjection projection : dynamicProjections) {
            dynamicNames.add(projection.solverTerm);
            dynamicQueryNames.add(projection.solverTerm);
            if (!projection.nullnessSolverTerm.isEmpty()) {
                dynamicQueryNames.add(projection.nullnessSolverTerm);
            }
            if (!projection.concreteEntryKey.isEmpty()) {
                dynamicKeys.add(projection.concreteEntryKey);
            }
        }
        List<String> refinements = materializabilityRefinements(
                selectedCase, caseRegistry, targetKeyName, keyNames,
                valueNames, dynamicKeys);
        LinkedHashSet<String> queriedSet = new LinkedHashSet<>();
        queriedSet.addAll(selectorTerms);
        queriedSet.add(targetKeyName);
        queriedSet.addAll(keyNames);
        queriedSet.addAll(dynamicQueryNames);
        List<String> queried = new ArrayList<>(queriedSet);

        String solverInput = solverInput(baseSmt, refinements, queried);
        SolverOutput solver = run(arguments.z3, solverInput,
                arguments.timeoutMillis);
        requireSuccessfulSolver(solver, "materializable model projection");
        String status = firstLine(solver.stdout);
        if (!"sat".equals(status)) {
            throw new IOException("Materializable composed model is " + status);
        }
        Map<String, String> values = parseGetValues(solver.stdout,
                queriedSet);
        for (String name : queried) {
            if (!values.containsKey(name)) {
                throw new IOException("Z3 omitted projected scalar " + name);
            }
        }
        JsonObject refinedSelectedCase = caseRegistry.select(values);
        if (!string(selectedCase, "caseId").equals(string(
                refinedSelectedCase, "caseId"))) {
            throw projectionGap("CASE_CHANGED_AFTER_MATERIALIZABILITY_"
                    + "REFINEMENT");
        }
        String targetValue = normalizeModelValue(values.get(targetKeyName));
        DynamicTermProjection targetDynamic = null;
        for (DynamicTermProjection projection : dynamicProjections) {
            if (!targetValue.equals(projection.concreteEntryKey)) continue;
            if (targetDynamic != null) {
                throw projectionGap("AMBIGUOUS_TARGET_DYNAMIC_ENTRY_KEY:"
                        + targetValue);
            }
            targetDynamic = projection;
        }
        if (!dynamicKeys.isEmpty() && targetDynamic == null) {
            throw projectionGap("TARGET_LOOKUP_KEY_NOT_SELECTED_DYNAMIC_"
                    + "ENTRY_KEY:" + targetValue);
        }
        for (String name : keyNames) {
            String keyValue = normalizeModelValue(values.get(name));
            if (targetValue.equals(keyValue)) {
                throw new IOException("Non-materializable lookup model: "
                        + name + " equals target key " + targetValue);
            }
        }

        JsonArray assignments = new JsonArray();
        assignments.add(detachArrayAssignment(projections.get(0)));
        for (int index = 0; index < projections.size(); index++) {
            EffectProjection projection = projections.get(index);
            assignments.add(scalarAssignment(projection,
                    normalizeModelValue(values.get(keyNames.get(index)))));
        }
        for (DynamicTermProjection projection : dynamicProjections) {
            assignments.add(dynamicBindings.retainSelector(
                    dynamicScalarAssignment(projection, values),
                    upstreamActivation));
        }
        List<String> controlledTerms = new ArrayList<>();
        controlledTerms.addAll(keyNames);
        controlledTerms.addAll(dynamicNames);
        validateUniqueMaterializations(assignments, controlledTerms);

        String stable = sha256(solverInput + "\n" + GSON.toJson(assignments))
                .substring(0, 12);
        String ambiguitySetId = "PRODUCER.SET."
                + arguments.upstreamRegion + "." + stable;
        List<JsonObject> upstreamReplays = new ArrayList<>();
        JsonObject sourceReplay = null;
        for (JsonObject candidate : broadcastCandidates) {
            JsonObject upstreamReplay = broadcastReplay(upstreamActivation,
                    candidate, assignments, arguments.upstreamRegion, stable,
                    ambiguitySetId);
            addModelProjectionProvenance(upstreamReplay,
                    sha256(solverInput), 1);
            upstreamReplays.add(upstreamReplay);
            if (string(candidate, "regionInstanceId").equals(
                    string(upstreamActivation, "regionInstanceId"))) {
                sourceReplay = upstreamReplay;
            }
        }
        if (sourceReplay == null) {
            throw new IOException("Bounded producer set omitted the captured "
                    + "upstream source instance " + string(
                    upstreamActivation, "regionInstanceId"));
        }

        JsonObject targetObserver = targetActivation.deepCopy();
        targetObserver.addProperty("derivedFromActivationId",
                string(targetActivation, "activationId"));
        targetObserver.addProperty("activationId", "ACT.OBSERVE."
                + string(composition, "fatalRegion") + "." + stable);
        targetObserver.add("modelAssignments", new JsonArray());
        targetObserver.add("replayMaterializations", new JsonArray());
        targetObserver.add("forcedBranches", new JsonArray());
        targetObserver.addProperty("observationOnlyReplay", true);
        targetObserver.addProperty("concreteReplayOnly", true);
        targetObserver.addProperty("downstreamInjectionForbidden", true);
        targetObserver.addProperty("branchOverrideAllowed", false);
        targetObserver.addProperty("boundedProducerInstanceSetId",
                ambiguitySetId);

        List<JsonObject> activations = new ArrayList<>();
        activations.addAll(upstreamReplays);
        activations.add(targetObserver);

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_MODEL_PROJECTION");
        manifest.addProperty("status", "SAT_UPSTREAM_MODEL_READY");
        manifest.addProperty("projectionComplete", true);
        manifest.addProperty("compositionComplete", true);
        manifest.addProperty("boundedComposition", true);
        manifest.add("boundedUpstreamRegions", array(composition,
                "boundedUpstreamRegions").deepCopy());
        manifest.addProperty("upstreamRegion", arguments.upstreamRegion);
        manifest.addProperty("selectedCaseId",
                string(selectedCase, "caseId"));
        manifest.addProperty("selectedCasePathKey",
                string(selectedCase, "pathKey"));
        manifest.addProperty("selectedCaseSymbolScope",
                string(selectedCase, "symbolScope"));
        manifest.addProperty("selectedCaseSelector",
                string(selectedCase, "selectorSolverSymbol"));
        manifest.addProperty("selectedCaseSourceSummaryId",
                selectedSourceSummary);
        manifest.add("caseSelectorModelValues",
                GSON.toJsonTree(selectorValues));
        manifest.addProperty("upstreamRegionInstance",
                string(upstreamActivation, "regionInstanceId"));
        manifest.addProperty("upstreamSourceActivation",
                string(upstreamActivation, "activationId"));
        manifest.addProperty("upstreamBoundedSourceCandidateActivation",
                string(upstreamActivation,
                        "selectedUpstreamActivationId"));
        manifest.addProperty("upstreamReplayActivation",
                string(sourceReplay, "activationId"));
        JsonArray replayActivationIds = new JsonArray();
        JsonArray replayInstances = new JsonArray();
        JsonArray producerSet = new JsonArray();
        for (int index = 0; index < broadcastCandidates.size(); index++) {
            JsonObject candidate = broadcastCandidates.get(index);
            JsonObject replay = upstreamReplays.get(index);
            replayActivationIds.add(string(replay, "activationId"));
            replayInstances.add(string(candidate, "regionInstanceId"));
            JsonObject member = new JsonObject();
            member.addProperty("sourceActivationId",
                    string(candidate, "activationId"));
            member.addProperty("replayActivationId",
                    string(replay, "activationId"));
            member.addProperty("regionInstanceId",
                    string(candidate, "regionInstanceId"));
            member.addProperty("invocationOrdinal",
                    integer(candidate, "invocationOrdinal", -1));
            member.addProperty("rootCallId",
                    integer(candidate, "rootCallId", -1));
            member.addProperty("capturedSourceInstance",
                    string(candidate, "regionInstanceId").equals(
                            string(upstreamActivation,
                                    "regionInstanceId")));
            member.addProperty("capturedSourceActivation",
                    string(candidate, "activationId").equals(
                            string(upstreamActivation,
                                    "selectedUpstreamActivationId")));
            member.addProperty("selectionAuthority",
                    "EXPLICIT_PRE_TARGET_EQUIVALENT_PRODUCER_BOUND");
            producerSet.add(member);
        }
        manifest.add("upstreamReplayActivations", replayActivationIds);
        manifest.add("upstreamReplayRegionInstances", replayInstances);
        manifest.addProperty("upstreamReplayActivationCount",
                upstreamReplays.size());
        manifest.addProperty("boundedProducerInstanceSetId",
                ambiguitySetId);
        manifest.addProperty("boundedProducerInstanceCount",
                broadcastCandidates.size());
        manifest.addProperty("expectedBoundedProducerInstanceCount",
                arguments.expectedBroadcastCandidates);
        manifest.add("boundedProducerInstances", producerSet);
        manifest.addProperty("boundedProducerInstanceSetComplete", true);
        manifest.addProperty("producerCorrelationRisk",
                "CROSS_THREAD_GLOBAL_INVOCATION_ORDINAL_CAN_DRIFT");
        manifest.addProperty("producerCorrelationMitigation",
                "BROADCAST_MODEL_TO_EXACT_BOUNDED_PRE_TARGET_EQUIVALENCE_SET");
        manifest.addProperty("producerCandidateSelectionPolicy",
                "SAME_TEST_REGION_ROOT_OUTPUT_AND_INPUT_SHAPE_WITH_OBSERVED_"
                        + "UPSTREAM_EVENT_AND_ROOT_CALL_BEFORE_TARGET");
        manifest.addProperty("concreteReplayOnly", true);
        manifest.addProperty("targetRegion",
                string(composition, "fatalRegion"));
        manifest.addProperty("targetRegionInstance",
                string(targetActivation, "regionInstanceId"));
        manifest.addProperty("targetObservationActivation",
                string(targetObserver, "activationId"));
        manifest.addProperty("targetMapInput", targetInput);
        manifest.addProperty("targetMapCell", targetMap.inputCell);
        manifest.addProperty("targetLookupKeyEngineSymbol", targetKeyRaw);
        manifest.addProperty("targetLookupKeySolverSymbol", targetKeyName);
        manifest.addProperty("targetLookupKeyModelValue", targetValue);
        manifest.addProperty("targetLookupKeySolverTermAuthority",
                "SMT_EMITTED_EXACT_MAP_LOOKUP_TERM_FOR_TARGET_RECEIVER");
        manifest.addProperty("targetDynamicBindingId",
                string(targetDynamic.binding, "dynamicBindingId"));
        manifest.addProperty("targetDynamicEntryKey", targetValue);
        manifest.addProperty("targetDynamicEntryKeyAuthority",
                string(targetDynamic.binding,
                        "keyExpressionAuthority"));
        manifest.addProperty("upstreamPreMapInput", preMapInput);
        manifest.addProperty("upstreamPreMapOperation",
                "PRESERVE_RUNTIME_CONFIRMED_EXISTING_STATE");
        manifest.add("upstreamPreMapProducerEvidence",
                preMapEvidence.deepCopy());
        manifest.addProperty("selectedCaseContainsMapRemove",
                hasHeapEffect(upstreamSummary, "MAP_REMOVE"));
        manifest.addProperty("solver", arguments.z3.toString());
        manifest.addProperty("solverStatus", status);
        manifest.addProperty("solverInputSha256", sha256(solverInput));
        manifest.addProperty("finalModelSolverInvocationCount", 1);
        manifest.addProperty("modelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        manifest.add("materializabilityRefinements",
                GSON.toJsonTree(refinements));
        JsonObject modelValues = new JsonObject();
        for (String name : queried) {
            modelValues.addProperty(name,
                    normalizeModelValue(values.get(name)));
        }
        manifest.add("modelValues", modelValues);
        manifest.add("upstreamModelAssignments", assignments.deepCopy());
        JsonArray evidence = new JsonArray();
        for (EffectProjection projection : projections) {
            evidence.add(projection.evidence.deepCopy());
        }
        manifest.add("projectionEvidence", evidence);
        manifest.addProperty("upstreamModelAssignmentCount",
                assignments.size());
        manifest.addProperty("selectedControlledTermCount",
                controlledTerms.size());
        manifest.addProperty("selectedControlledTermsHaveUniqueMaterialization",
                true);
        manifest.addProperty("downstreamModelAssignmentCount", 0);
        manifest.addProperty("downstreamReplayMaterializationCount", 0);
        manifest.addProperty("downstreamBranchOverrideCount", 0);
        manifest.addProperty("downstreamInjectionForbidden", true);
        manifest.addProperty("naturalPropagationReplayRequired", true);
        manifest.addProperty("domainSemanticAdapterUsed", false);
        manifest.addProperty("projectionPolicy",
                "FINITE_MAP_EFFECT_PROVENANCE_AND_STATIC_ACCESSOR_FIELD_PATH");
        return new Result(activations, manifest);
    }

    private static void requireGloballyUniqueInputActivations(
            GroupProjection group, Set<String> global) throws IOException {
        Set<String> local = new LinkedHashSet<>();
        local.add(string(group.upstreamActivation, "activationId"));
        for (JsonObject candidate : group.broadcastCandidates) {
            local.add(string(candidate, "activationId"));
        }
        for (String activationId : local) {
            if (activationId.isEmpty()) {
                throw projectionGap("PRODUCER_GROUP_ACTIVATION_ID_MISSING:"
                        + group.spec.groupId);
            }
            if (!global.add(activationId)) {
                throw projectionGap("ACTIVATION_ID_SHARED_ACROSS_PRODUCER_"
                        + "GROUPS:" + activationId);
            }
        }
    }

    private static void requireUniqueControlledTerm(Set<String> terms,
                                                    String term,
                                                    String groupId)
            throws IOException {
        if (!terms.add(term)) {
            throw projectionGap("CONTROLLED_SOLVER_TERM_SHARED_ACROSS_"
                    + "PRODUCER_GROUPS:" + term + ":" + groupId);
        }
    }

    private static String exactLookupKeyProducerTerm(GroupProjection group)
            throws IOException {
        JsonObject witness = group.spec.witnessForCase(string(
                group.selectedCase, "caseId"));
        String raw = string(witness, "rawEngineSymbol");
        String witnessedEffect = string(witness, "summaryEffectId");
        if (!group.spec.upstreamRegion.equals(string(witness,
                "producerRegion"))
                || !string(group.upstreamActivation,
                "regionInstanceId").equals(string(witness,
                "producerRegionInstanceId"))) {
            throw projectionGap("LOOKUP_KEY_PRODUCER_WITNESS_INSTANCE_"
                    + "MISMATCH:" + group.spec.groupId);
        }
        Map<String, JsonObject> runtimeWitnesses = new LinkedHashMap<>();
        collectLookupKeyProducerWitnesses(group.summary, runtimeWitnesses);
        collectLookupKeyProducerWitnesses(group.upstreamActivation,
                runtimeWitnesses);
        if (runtimeWitnesses.size() != 1
                || runtimeWitnesses.get(GSON.toJson(witness)) == null
                || !string(group.summary, "summaryId").equals(string(witness,
                "sourceSummaryId"))
                || !string(group.upstreamActivation,
                "activationId").equals(string(witness,
                "producerActivationId"))) {
            throw projectionGap("LOOKUP_KEY_PRODUCER_WITNESS_NOT_PRESENT_IN_"
                    + "RUNTIME_SUMMARY_OR_ACTIVATION:" + group.spec.groupId);
        }
        JsonObject selectedEffect = null;
        for (JsonElement element : array(group.summary, "heapEffects")) {
            if (!element.isJsonObject()) continue;
            JsonObject effect = element.getAsJsonObject();
            if (!"MAP_PUT".equals(string(effect, "kind"))
                    || !raw.equals(expressionSymbol(
                    effect.get("keyExpression")))) continue;
            if (selectedEffect != null) {
                throw projectionGap("AMBIGUOUS_LOOKUP_KEY_PRODUCER_MAP_PUT:"
                        + group.spec.groupId + ":" + raw);
            }
            selectedEffect = effect;
        }
        if (selectedEffect == null
                || !witnessedEffect.equals(string(selectedEffect,
                "effectId"))) {
            throw projectionGap("LOOKUP_KEY_PRODUCER_EFFECT_WITNESS_"
                    + "MISMATCH:" + group.spec.groupId + ":"
                    + witnessedEffect);
        }
        String solverTerm = caseSolverTerm(group.selectedCase, raw, "Int");
        int matchingProjectionCount = 0;
        for (EffectProjection projection : group.projections) {
            if (!raw.equals(projection.keyRaw)) continue;
            matchingProjectionCount++;
            if (!solverTerm.equals(projection.keySolverTerm)) {
                throw projectionGap("LOOKUP_KEY_PRODUCER_EFFECT_TERM_"
                        + "MISMATCH:" + group.spec.groupId);
            }
        }
        if (matchingProjectionCount != 1) {
            throw projectionGap("LOOKUP_KEY_PRODUCER_PROJECTION_COUNT:"
                    + group.spec.groupId + ":" + matchingProjectionCount);
        }
        group.lookupKeyProducerEffectId = witnessedEffect;
        group.lookupKeyProducerWitness = witness;
        group.lookupKeyProducerRawEngineSymbol = raw;
        return solverTerm;
    }

    private static void collectLookupKeyProducerWitnesses(
            JsonObject source, Map<String, JsonObject> result) {
        for (JsonElement element : array(source,
                "lookupKeyProducerWitnesses")) {
            if (!element.isJsonObject()) continue;
            JsonObject witness = element.getAsJsonObject();
            result.put(GSON.toJson(witness), witness);
        }
    }

    private static String groupAssignmentsJson(List<GroupProjection> groups) {
        JsonObject result = new JsonObject();
        for (GroupProjection group : groups) {
            result.add(group.spec.groupId, group.assignments.deepCopy());
        }
        return GSON.toJson(result);
    }

    private static void buildGroupReplays(GroupProjection group,
                                          String modelStable)
            throws IOException {
        String selectedCandidate = string(group.upstreamActivation,
                "selectedUpstreamActivationId");
        if (selectedCandidate.isEmpty()) {
            throw projectionGap("CAPTURED_SOURCE_ACTIVATION_ID_MISSING:"
                    + group.spec.groupId);
        }
        String groupStable = sha256(modelStable + "\n"
                + group.spec.groupId + "\n" + GSON.toJson(
                group.assignments)).substring(0, 12);
        group.producerSetId = "PRODUCER.SET."
                + group.spec.upstreamRegion + "." + groupStable;
        for (JsonObject candidate : group.broadcastCandidates) {
            JsonObject replay = broadcastReplay(group.upstreamActivation,
                    candidate, group.assignments,
                    group.spec.upstreamRegion, groupStable,
                    group.producerSetId);
            replay.addProperty("producerGroupId", group.spec.groupId);
            group.upstreamReplays.add(replay);
            boolean exactSource = string(candidate,
                    "regionInstanceId").equals(string(
                    group.upstreamActivation, "regionInstanceId"))
                    && selectedCandidate.equals(string(candidate,
                    "activationId"));
            if (!exactSource) continue;
            if (group.sourceReplay != null) {
                throw projectionGap("MULTIPLE_EXACT_CAPTURED_SOURCES:"
                        + group.spec.groupId);
            }
            group.sourceReplay = replay;
        }
        if (group.sourceReplay == null) {
            throw new IOException("Bounded producer set omitted the exact "
                    + "captured upstream source instance/activation for "
                    + group.spec.groupId);
        }
    }

    private static JsonObject groupManifest(GroupProjection group) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "CONCOLIC_PRODUCER_GROUP_PROJECTION");
        result.addProperty("complete", true);
        result.addProperty("producerGroupId", group.spec.groupId);
        result.addProperty("upstreamRegion", group.spec.upstreamRegion);
        result.addProperty("projectionRole", group.spec.projectionRole);
        result.addProperty("projectionRoleAuthority",
                group.spec.projectionRoleAuthority);
        result.addProperty("verifiedCaseWitnessCount",
                group.spec.witnessesByCase.size());
        result.addProperty("selectedCaseId",
                string(group.selectedCase, "caseId"));
        result.addProperty("selectedCasePathKey",
                string(group.selectedCase, "pathKey"));
        result.addProperty("selectedCaseSymbolScope",
                string(group.selectedCase, "symbolScope"));
        result.addProperty("selectedCaseSelector",
                string(group.selectedCase, "selectorSolverSymbol"));
        result.addProperty("selectedCaseSourceSummaryId",
                group.selectedSourceSummary);
        result.addProperty("upstreamRegionInstance", string(
                group.upstreamActivation, "regionInstanceId"));
        result.addProperty("upstreamSourceActivation", string(
                group.upstreamActivation, "activationId"));
        result.addProperty("upstreamBoundedSourceCandidateActivation",
                string(group.upstreamActivation,
                        "selectedUpstreamActivationId"));
        result.addProperty("upstreamReplayActivation",
                string(group.sourceReplay, "activationId"));
        JsonArray replayIds = new JsonArray();
        JsonArray instances = new JsonArray();
        JsonArray producerSet = new JsonArray();
        for (int index = 0; index < group.broadcastCandidates.size(); index++) {
            JsonObject candidate = group.broadcastCandidates.get(index);
            JsonObject replay = group.upstreamReplays.get(index);
            replayIds.add(string(replay, "activationId"));
            instances.add(string(candidate, "regionInstanceId"));
            JsonObject member = new JsonObject();
            member.addProperty("sourceActivationId",
                    string(candidate, "activationId"));
            member.addProperty("replayActivationId",
                    string(replay, "activationId"));
            member.addProperty("regionInstanceId",
                    string(candidate, "regionInstanceId"));
            member.addProperty("invocationOrdinal",
                    integer(candidate, "invocationOrdinal", -1));
            member.addProperty("rootCallId",
                    integer(candidate, "rootCallId", -1));
            boolean capturedInstance = string(candidate,
                    "regionInstanceId").equals(string(
                    group.upstreamActivation, "regionInstanceId"));
            boolean capturedActivation = string(candidate,
                    "activationId").equals(string(group.upstreamActivation,
                    "selectedUpstreamActivationId"));
            member.addProperty("capturedSourceInstance", capturedInstance);
            member.addProperty("capturedSourceActivation",
                    capturedActivation);
            member.addProperty("selectionAuthority",
                    "EXPLICIT_PRE_TARGET_EQUIVALENT_PRODUCER_BOUND");
            producerSet.add(member);
        }
        result.add("upstreamReplayActivations", replayIds);
        result.add("upstreamReplayRegionInstances", instances);
        result.addProperty("upstreamReplayActivationCount",
                replayIds.size());
        result.addProperty("boundedProducerInstanceSetId",
                group.producerSetId);
        result.addProperty("boundedProducerInstanceCount",
                group.broadcastCandidates.size());
        result.addProperty("expectedBoundedProducerInstanceCount",
                group.spec.expectedBroadcastCandidates);
        result.add("boundedProducerInstances", producerSet);
        result.addProperty("boundedProducerInstanceSetComplete", true);
        result.add("upstreamModelAssignments", group.assignments.deepCopy());
        result.addProperty("upstreamModelAssignmentCount",
                group.assignments.size());
        result.addProperty("selectedControlledTermCount",
                group.controlledTerms.size());
        result.addProperty("selectedControlledTermsHaveUniqueMaterialization",
                true);
        result.addProperty("upstreamPreMapInput", group.preMapInput);
        result.addProperty("upstreamPreMapOperation",
                "PRESERVE_RUNTIME_CONFIRMED_EXISTING_STATE");
        result.add("upstreamPreMapProducerEvidence",
                group.preMapEvidence.deepCopy());
        result.addProperty("selectedCaseContainsMapRemove",
                hasHeapEffect(group.summary, "MAP_REMOVE"));
        if (TARGET_MAP_STATE.equals(group.spec.projectionRole)) {
            result.addProperty("targetDynamicBindingId", string(
                    group.targetDynamic.binding, "dynamicBindingId"));
            result.addProperty("targetDynamicEntryKey",
                    group.targetDynamic.concreteEntryKey);
        } else {
            result.addProperty("lookupKeyProducerRawEngineSymbol",
                    group.lookupKeyProducerRawEngineSymbol);
            result.addProperty("lookupKeyProducerSolverTerm",
                    group.lookupKeyProducerSolverTerm);
            result.addProperty("lookupKeyProducerAuthority",
                    group.spec.projectionRoleAuthority);
            result.addProperty("lookupKeyProducerSummaryEffectId",
                    group.lookupKeyProducerEffectId);
            result.add("lookupKeyProducerWitness",
                    group.lookupKeyProducerWitness.deepCopy());
        }
        JsonArray evidence = new JsonArray();
        for (EffectProjection projection : group.projections) {
            evidence.add(projection.evidence.deepCopy());
        }
        result.add("projectionEvidence", evidence);
        return result;
    }

    private static JsonArray producerSetIds(List<GroupProjection> groups) {
        JsonArray result = new JsonArray();
        for (GroupProjection group : groups) {
            result.add(group.producerSetId);
        }
        return result;
    }

    private static void requireUniqueOutputActivation(JsonObject activation,
                                                      Set<String> ids)
            throws IOException {
        String id = string(activation, "activationId");
        if (id.isEmpty() || !ids.add(id)) {
            throw projectionGap("OUTPUT_ACTIVATION_ID_NOT_GLOBALLY_UNIQUE:"
                    + id);
        }
    }

    /**
     * Projects every declared producer group from one complete composed SMT
     * model.  The preliminary selector query is shared by all groups and is
     * used only to discover the guarded cases whose materializability
     * constraints must be added.  All such constraints and queried terms are
     * then submitted in one final solver invocation; group-local models are
     * never solved independently or stitched together.
     */
    private static Result projectProducerGroups(Arguments arguments)
            throws Exception {
        require(arguments.runtimeEdges, "runtime edge validation");
        JsonObject composition = readJson(arguments.compositionManifest);
        if (!bool(composition, "complete", false)
                || !bool(composition, "boundedComposition", false)
                || !bool(composition, "fatalReplayValidated", false)) {
            throw new IOException("Projection requires a complete bounded "
                    + "composition with validated fatal replay");
        }
        ConcolicProducerGroupPlanner.VerifiedCatalog verifiedCatalog =
                ConcolicProducerGroupPlanner.verifyCatalog(
                        arguments.producerGroups,
                        arguments.compositionManifest, arguments.smt,
                        arguments.upstreamSummaries,
                        arguments.targetActivations,
                        arguments.fatalQueries, arguments.runtimeEdges,
                        arguments.z3, arguments.timeoutMillis);
        List<ProducerGroupSpec> specs = ProducerGroupSpec.read(
                arguments.producerGroups, verifiedCatalog);
        if (specs.size() < 2) {
            throw projectionGap("SCHEMA2_REQUIRES_MULTIPLE_PRODUCER_GROUPS");
        }
        Set<String> boundedRegions = new LinkedHashSet<>(strings(array(
                composition, "boundedUpstreamRegions")));
        Set<String> groupIds = new LinkedHashSet<>();
        Set<String> groupRegions = new LinkedHashSet<>();
        int targetStateGroups = 0;
        int lookupKeyGroups = 0;
        for (ProducerGroupSpec spec : specs) {
            require(spec.upstreamActivations, "producer-group upstream "
                    + "activation plan " + spec.groupId);
            require(spec.broadcastActivations, "producer-group bounded "
                    + "broadcast activation plan " + spec.groupId);
            if (!boundedRegions.contains(spec.upstreamRegion)) {
                throw new IOException("Composition is not bounded to requested "
                        + "upstream region " + spec.upstreamRegion);
            }
            if (!groupIds.add(spec.groupId)) {
                throw projectionGap("DUPLICATE_PRODUCER_GROUP_ID:"
                        + spec.groupId);
            }
            if (!groupRegions.add(spec.upstreamRegion)) {
                throw projectionGap("DUPLICATE_PRODUCER_GROUP_REGION:"
                        + spec.upstreamRegion);
            }
            if (TARGET_MAP_STATE.equals(spec.projectionRole)) {
                targetStateGroups++;
            } else if (LOOKUP_KEY_PRODUCER.equals(spec.projectionRole)) {
                lookupKeyGroups++;
            }
        }
        if (targetStateGroups != 1 || lookupKeyGroups < 1) {
            throw projectionGap("PRODUCER_GROUP_ROLE_CARDINALITY:targetMapState="
                    + targetStateGroups + ":lookupKeyProducer="
                    + lookupKeyGroups);
        }

        String baseSmt = new String(Files.readAllBytes(arguments.smt),
                StandardCharsets.UTF_8);
        List<JsonObject> summaries = readJsonl(arguments.upstreamSummaries);
        List<JsonObject> graph = readJsonl(arguments.staticGraph);
        JsonObject targetActivation = selectTargetActivation(
                readJsonl(arguments.targetActivations),
                arguments.targetActivationId,
                string(composition, "fatalRegion"));
        JsonObject fatalQuery = selectFatalQuery(
                readJsonl(arguments.fatalQueries), targetActivation,
                string(composition, "fatalRegion"));

        List<GroupProjection> groups = new ArrayList<>();
        LinkedHashSet<String> selectorSet = new LinkedHashSet<>();
        for (ProducerGroupSpec spec : specs) {
            CaseProjectionRegistry registry = CaseProjectionRegistry.from(
                    composition, spec.upstreamRegion);
            for (String selector : registry.selectorTerms()) {
                if (!selectorSet.add(selector)) {
                    throw projectionGap("CASE_SELECTOR_SHARED_BY_PRODUCER_"
                            + "GROUPS:" + selector);
                }
            }
            groups.add(new GroupProjection(spec, registry));
        }

        List<String> allSelectors = new ArrayList<>(selectorSet);
        String selectorInput = solverInput(baseSmt,
                Collections.<String>emptyList(), allSelectors);
        SolverOutput selectorSolver = run(arguments.z3, selectorInput,
                arguments.timeoutMillis);
        requireSuccessfulSolver(selectorSolver,
                "multi-group case selector projection");
        String selectorStatus = firstLine(selectorSolver.stdout);
        if (!"sat".equals(selectorStatus)) {
            throw new IOException("Composed case selector model is "
                    + selectorStatus);
        }
        Map<String, String> selectorValues = parseGetValues(
                selectorSolver.stdout, selectorSet);

        String targetInput = "";
        String targetMapCell = "";
        String targetKeyRaw = "";
        String targetKeyName = "";
        Set<String> inputActivationIds = new LinkedHashSet<>();
        inputActivationIds.add(string(targetActivation, "activationId"));
        for (GroupProjection group : groups) {
            group.selectedCase = group.registry.select(selectorValues);
            group.selectedSourceSummary = string(group.selectedCase,
                    "sourceSummaryId");
            group.summary = selectUpstreamSummary(summaries,
                    group.spec.upstreamRegion,
                    group.selectedSourceSummary);
            group.dynamicBindings = DynamicProjectionRegistry.fromCatalog(
                    group.selectedCase, group.summary);
            group.upstreamActivation = selectUpstreamActivation(readJsonl(
                    group.spec.upstreamActivations), group.summary,
                    group.spec.upstreamRegion);
            if (!string(group.summary, "activationId").equals(string(
                    group.upstreamActivation, "activationId"))
                    || string(group.summary, "regionInstanceId").isEmpty()
                    || !string(group.summary, "regionInstanceId").equals(
                    string(group.upstreamActivation,
                            "regionInstanceId"))) {
                throw projectionGap("SUMMARY_ACTIVATION_INSTANCE_NOT_EXACT:"
                        + group.spec.groupId);
            }
            group.broadcastCandidates = selectBroadcastCandidates(readJsonl(
                    group.spec.broadcastActivations),
                    group.upstreamActivation, targetActivation,
                    group.spec.upstreamRegion,
                    group.spec.expectedBroadcastCandidates);
            requireGloballyUniqueInputActivations(group, inputActivationIds);

            group.projections = effectProjections(group.summary,
                    group.upstreamActivation, graph, group.selectedCase);
            if (group.projections.isEmpty()) {
                throw new IOException("No projectable finite-map effects in "
                        + group.spec.upstreamRegion);
            }
            group.preMapInput = group.projections.get(0).preMapInput;
            for (EffectProjection projection : group.projections) {
                if (!group.preMapInput.equals(projection.preMapInput)) {
                    throw new IOException("Projectable effects in "
                            + group.spec.upstreamRegion
                            + " do not share one concrete map pre-state");
                }
            }
            if (action(group.upstreamActivation,
                    group.preMapInput).size() == 0) {
                throw new IOException("Missing map materialization action for "
                        + group.preMapInput);
            }
            group.preMapEvidence = preMapProducerEvidence(group.summary,
                    group.upstreamActivation, group.preMapInput);

            if (TARGET_MAP_STATE.equals(group.spec.projectionRole)) {
                TargetMapBinding targetMap = targetMapInput(group.summary,
                        fatalQuery, targetActivation);
                targetInput = targetMap.inputPort;
                targetMapCell = targetMap.inputCell;
                targetKeyRaw = targetLookupKey(fatalQuery, targetInput);
                targetKeyName = actualTargetLookupTerm(baseSmt, targetInput);
            } else {
                group.lookupKeyProducerSolverTerm =
                        exactLookupKeyProducerTerm(group);
            }

            group.dynamicProjections = dynamicTermProjections(
                    group.selectedCase, group.dynamicBindings,
                    group.upstreamActivation);
            if (TARGET_MAP_STATE.equals(group.spec.projectionRole)
                    && group.dynamicProjections.isEmpty()) {
                throw projectionGap("NO_SELECTED_DYNAMIC_FIELD_BINDING:"
                        + group.spec.groupId);
            }
            for (EffectProjection projection : group.projections) {
                group.keyNames.add(projection.keySolverTerm);
                group.valueNames.add(projection.valueSolverTerm);
            }
            for (DynamicTermProjection projection
                    : group.dynamicProjections) {
                group.dynamicNames.add(projection.solverTerm);
                group.dynamicQueryNames.add(projection.solverTerm);
                if (!projection.nullnessSolverTerm.isEmpty()) {
                    group.dynamicQueryNames.add(
                            projection.nullnessSolverTerm);
                }
                group.dynamicKeys.add(projection.concreteEntryKey);
            }
        }
        if (targetInput.isEmpty() || targetKeyRaw.isEmpty()
                || targetKeyName.isEmpty()) {
            throw projectionGap("TARGET_MAP_STATE_DID_NOT_RESOLVE_FATAL_"
                    + "LOOKUP_RECEIVER");
        }

        List<String> refinements = new ArrayList<>();
        LinkedHashSet<String> queriedSet = new LinkedHashSet<>();
        queriedSet.addAll(allSelectors);
        queriedSet.add(targetKeyName);
        Set<String> globallyControlledTerms = new LinkedHashSet<>();
        for (GroupProjection group : groups) {
            if (TARGET_MAP_STATE.equals(group.spec.projectionRole)) {
                refinements.addAll(materializabilityRefinements(
                        group.selectedCase, group.registry, targetKeyName,
                        group.keyNames, group.valueNames, group.dynamicKeys,
                        smtName(group.spec.groupId)));
            } else {
                refinements.addAll(lookupKeyMaterializabilityRefinements(
                        group.selectedCase, group.registry, targetKeyName,
                        group.keyNames, group.valueNames,
                        group.lookupKeyProducerSolverTerm,
                        smtName(group.spec.groupId)));
            }
            for (String term : group.keyNames) {
                requireUniqueControlledTerm(globallyControlledTerms, term,
                        group.spec.groupId);
            }
            for (String term : group.dynamicNames) {
                requireUniqueControlledTerm(globallyControlledTerms, term,
                        group.spec.groupId);
            }
            queriedSet.addAll(group.keyNames);
            queriedSet.addAll(group.dynamicQueryNames);
        }
        List<String> queried = new ArrayList<>(queriedSet);
        String solverInput = solverInput(baseSmt, refinements, queried);
        SolverOutput solver = run(arguments.z3, solverInput,
                arguments.timeoutMillis);
        requireSuccessfulSolver(solver,
                "multi-group materializable model projection");
        String status = firstLine(solver.stdout);
        if (!"sat".equals(status)) {
            throw new IOException("Materializable composed model is " + status);
        }
        Map<String, String> values = parseGetValues(solver.stdout,
                queriedSet);
        for (String name : queried) {
            if (!values.containsKey(name)) {
                throw new IOException("Z3 omitted projected scalar " + name);
            }
        }

        String targetValue = normalizeModelValue(values.get(targetKeyName));
        for (GroupProjection group : groups) {
            JsonObject refined = group.registry.select(values);
            if (!string(group.selectedCase, "caseId").equals(string(refined,
                    "caseId"))) {
                throw projectionGap("CASE_CHANGED_AFTER_MATERIALIZABILITY_"
                        + "REFINEMENT:" + group.spec.groupId);
            }
            if (TARGET_MAP_STATE.equals(group.spec.projectionRole)) {
                for (DynamicTermProjection projection
                        : group.dynamicProjections) {
                    if (!targetValue.equals(
                            projection.concreteEntryKey)) continue;
                    if (group.targetDynamic != null) {
                        throw projectionGap(
                                "AMBIGUOUS_TARGET_DYNAMIC_ENTRY_KEY:"
                                        + group.spec.groupId + ":"
                                        + targetValue);
                    }
                    group.targetDynamic = projection;
                }
                if (group.targetDynamic == null) {
                    throw projectionGap(
                            "TARGET_LOOKUP_KEY_NOT_SELECTED_DYNAMIC_"
                                    + "ENTRY_KEY:" + group.spec.groupId + ":"
                                    + targetValue);
                }
                for (String name : group.keyNames) {
                    if (targetValue.equals(normalizeModelValue(
                            values.get(name)))) {
                        throw new IOException(
                                "Non-materializable lookup model: "
                                        + name + " equals target key "
                                        + targetValue);
                    }
                }
            } else if (!targetValue.equals(normalizeModelValue(values.get(
                    group.lookupKeyProducerSolverTerm)))) {
                throw projectionGap("LOOKUP_KEY_PRODUCER_MODEL_MISMATCH:"
                        + group.spec.groupId);
                }
            group.assignments.add(detachArrayAssignment(
                    group.projections.get(0)));
            for (int index = 0; index < group.projections.size(); index++) {
                group.assignments.add(scalarAssignment(
                        group.projections.get(index), normalizeModelValue(
                                values.get(group.keyNames.get(index)))));
            }
            for (DynamicTermProjection projection
                    : group.dynamicProjections) {
                group.assignments.add(group.dynamicBindings.retainSelector(
                        dynamicScalarAssignment(projection, values),
                        group.upstreamActivation));
            }
            List<String> controlled = new ArrayList<>();
            controlled.addAll(group.keyNames);
            controlled.addAll(group.dynamicNames);
            validateUniqueMaterializations(group.assignments, controlled);
            group.controlledTerms = controlled;
        }

        String stable = sha256(solverInput + "\n"
                + groupAssignmentsJson(groups)).substring(0, 12);
        List<JsonObject> activations = new ArrayList<>();
        JsonArray producerGroupManifest = new JsonArray();
        JsonArray flattenedReplayIds = new JsonArray();
        JsonArray flattenedReplayInstances = new JsonArray();
        Set<String> outputActivationIds = new LinkedHashSet<>();
        int assignmentDefinitionCount = 0;
        int expectedAppliedAssignmentCount = 0;
        for (GroupProjection group : groups) {
            buildGroupReplays(group, stable);
            for (JsonObject replay : group.upstreamReplays) {
                addModelProjectionProvenance(replay,
                        sha256(solverInput), 2);
                requireUniqueOutputActivation(replay, outputActivationIds);
                activations.add(replay);
                flattenedReplayIds.add(string(replay, "activationId"));
            }
            for (JsonObject candidate : group.broadcastCandidates) {
                flattenedReplayInstances.add(string(candidate,
                        "regionInstanceId"));
            }
            producerGroupManifest.add(groupManifest(group));
            assignmentDefinitionCount += group.assignments.size();
            expectedAppliedAssignmentCount += group.assignments.size()
                    * group.upstreamReplays.size();
        }

        JsonObject targetObserver = targetActivation.deepCopy();
        targetObserver.addProperty("derivedFromActivationId",
                string(targetActivation, "activationId"));
        targetObserver.addProperty("activationId", "ACT.OBSERVE."
                + string(composition, "fatalRegion") + "." + stable);
        targetObserver.add("modelAssignments", new JsonArray());
        targetObserver.add("replayMaterializations", new JsonArray());
        targetObserver.add("forcedBranches", new JsonArray());
        targetObserver.addProperty("observationOnlyReplay", true);
        targetObserver.addProperty("concreteReplayOnly", true);
        targetObserver.addProperty("downstreamInjectionForbidden", true);
        targetObserver.addProperty("branchOverrideAllowed", false);
        targetObserver.add("boundedProducerInstanceSetIds",
                producerSetIds(groups));
        requireUniqueOutputActivation(targetObserver, outputActivationIds);
        activations.add(targetObserver);

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_MODEL_PROJECTION");
        manifest.addProperty("status", "SAT_UPSTREAM_MODEL_READY");
        manifest.addProperty("projectionComplete", true);
        manifest.addProperty("compositionComplete", true);
        manifest.addProperty("boundedComposition", true);
        manifest.add("boundedUpstreamRegions", array(composition,
                "boundedUpstreamRegions").deepCopy());
        manifest.add("producerGroups", producerGroupManifest);
        manifest.addProperty("producerGroupCount", groups.size());
        manifest.add("upstreamReplayActivations", flattenedReplayIds);
        manifest.add("upstreamReplayRegionInstances",
                flattenedReplayInstances);
        manifest.addProperty("upstreamReplayActivationCount",
                flattenedReplayIds.size());
        manifest.addProperty("boundedProducerInstanceSetComplete", true);
        manifest.addProperty("allProducerGroupsComplete", true);
        manifest.addProperty("upstreamModelAssignmentDefinitionCount",
                assignmentDefinitionCount);
        manifest.addProperty("expectedTotalUpstreamModelAssignmentCount",
                expectedAppliedAssignmentCount);
        manifest.addProperty("concreteReplayOnly", true);
        manifest.addProperty("targetRegion",
                string(composition, "fatalRegion"));
        manifest.addProperty("targetRegionInstance",
                string(targetActivation, "regionInstanceId"));
        manifest.addProperty("targetObservationActivation",
                string(targetObserver, "activationId"));
        manifest.addProperty("targetMapInput", targetInput);
        manifest.addProperty("targetMapCell", targetMapCell);
        manifest.addProperty("targetLookupKeyEngineSymbol", targetKeyRaw);
        manifest.addProperty("targetLookupKeySolverSymbol", targetKeyName);
        manifest.addProperty("targetLookupKeyModelValue", targetValue);
        manifest.addProperty("targetLookupKeySolverTermAuthority",
                "SMT_EMITTED_EXACT_MAP_LOOKUP_TERM_FOR_TARGET_RECEIVER");
        manifest.addProperty("solver", arguments.z3.toString());
        manifest.addProperty("solverStatus", status);
        manifest.addProperty("solverInputSha256", sha256(solverInput));
        manifest.addProperty("selectorSolverInvocationCount", 1);
        manifest.addProperty("finalModelSolverInvocationCount", 1);
        manifest.addProperty("modelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        manifest.add("caseSelectorModelValues",
                GSON.toJsonTree(selectorValues));
        manifest.add("materializabilityRefinements",
                GSON.toJsonTree(refinements));
        JsonObject modelValues = new JsonObject();
        for (String name : queried) {
            modelValues.addProperty(name,
                    normalizeModelValue(values.get(name)));
        }
        manifest.add("modelValues", modelValues);
        manifest.addProperty("downstreamModelAssignmentCount", 0);
        manifest.addProperty("downstreamReplayMaterializationCount", 0);
        manifest.addProperty("downstreamBranchOverrideCount", 0);
        manifest.addProperty("downstreamInjectionForbidden", true);
        manifest.addProperty("naturalPropagationReplayRequired", true);
        manifest.addProperty("domainSemanticAdapterUsed", false);
        manifest.addProperty("projectionPolicy",
                "MULTI_PRODUCER_GROUP_FINITE_MAP_EFFECT_PROVENANCE_AND_"
                        + "STATIC_ACCESSOR_FIELD_PATH");
        return new Result(activations, manifest);
    }

    /**
     * Selects the complete, finite producer-instance set that can exchange
     * invocation ordinals before the target root.  Nothing is truncated: a
     * changed trace that grows or shrinks this set invalidates the declared
     * bound and must be reviewed before replay.
     */
    static List<JsonObject> selectBroadcastCandidates(
            List<JsonObject> rows, JsonObject source,
            JsonObject target, String region, int expectedCount)
            throws IOException {
        if (expectedCount < 1) {
            throw new IOException("Expected producer-instance bound must be "
                    + "positive");
        }
        int targetRootCall = integer(target, "rootCallId", -1);
        if (targetRootCall < 1) {
            throw new IOException("Target activation has no positive "
                    + "rootCallId for the pre-target producer bound");
        }
        String sourceRoot = firstNonBlank(string(source, "rootMethod"),
                string(source, "observedRootMethod"));
        String sourceTest = string(source, "test");
        String sourceInstance = string(source, "regionInstanceId");
        String sourceCandidateActivation = string(source,
                "selectedUpstreamActivationId");
        JsonObject requestedOutput = object(source, "requestedOutput");
        String outputPort = string(requestedOutput, "portId");
        String outputCell = string(requestedOutput, "cell");
        String actionShape = logicalActionShape(source);
        if (sourceRoot.isEmpty() || sourceTest.isEmpty()
                || sourceInstance.isEmpty() || outputPort.isEmpty()
                || outputCell.isEmpty() || actionShape.isEmpty()) {
            throw new IOException("Captured upstream activation lacks the "
                    + "identity/output/input shape required for bounded "
                    + "producer correlation");
        }

        Map<Integer, JsonObject> byOrdinal = new LinkedHashMap<>();
        boolean containsSource = false;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))
                    || !sourceTest.equals(string(row, "test"))
                    || !sourceRoot.equals(firstNonBlank(
                    string(row, "rootMethod"),
                    string(row, "observedRootMethod")))
                    || !bool(row, "upstreamEventObserved", false)
                    || object(row, "selectedUpstreamEvent").size() == 0) {
                continue;
            }
            JsonObject candidateOutput = object(row, "requestedOutput");
            if (!outputPort.equals(string(candidateOutput, "portId"))
                    || !outputCell.equals(string(candidateOutput, "cell"))
                    || !actionShape.equals(logicalActionShape(row))) {
                continue;
            }
            int call = integer(row, "rootCallId", -1);
            int ordinal = integer(row, "invocationOrdinal", -1);
            JsonObject event = object(row, "selectedUpstreamEvent");
            if (call < 1 || call >= targetRootCall || ordinal < 1
                    || integer(event, "rootCallId", -1) != call
                    || integer(event, "writerCallId", -1) != call) {
                continue;
            }
            if (byOrdinal.put(ordinal, row) != null) {
                throw new IOException("More than one bounded producer "
                        + "activation has invocation ordinal " + ordinal);
            }
            if (sourceInstance.equals(string(row, "regionInstanceId"))
                    && (sourceCandidateActivation.isEmpty()
                    || sourceCandidateActivation.equals(string(row,
                    "activationId")))) {
                containsSource = true;
            }
        }
        if (byOrdinal.size() != expectedCount) {
            throw new IOException("Bounded producer-instance count changed: "
                    + "expected " + expectedCount + " but selected "
                    + byOrdinal.size());
        }
        if (!containsSource) {
            throw new IOException("Bounded producer-instance set does not "
                    + "contain captured source " + sourceInstance);
        }
        List<Integer> ordinals = new ArrayList<>(byOrdinal.keySet());
        Collections.sort(ordinals);
        List<JsonObject> result = new ArrayList<>();
        for (Integer ordinal : ordinals) result.add(byOrdinal.get(ordinal));
        return result;
    }

    private static JsonObject broadcastReplay(JsonObject modelSource,
                                              JsonObject candidate,
                                              JsonArray assignments,
                                              String region, String stable,
                                              String ambiguitySetId) {
        JsonObject replay = candidate.deepCopy();
        JsonArray materializations = candidateMaterializations(modelSource,
                candidate);
        replay.add("materializations", materializations);
        replay.addProperty("derivedFromActivationId",
                string(candidate, "activationId"));
        replay.addProperty("modelDerivedFromActivationId",
                string(modelSource, "activationId"));
        replay.addProperty("modelDerivedFromRegionInstanceId",
                string(modelSource, "regionInstanceId"));
        String replayActivationId = "ACT.MODEL." + region + "."
                + stable + ".ORDINAL."
                + integer(candidate, "invocationOrdinal", -1);
        replay.addProperty("activationId", replayActivationId);
        replay.add("modelAssignments", candidateAssignments(assignments,
                materializations, replayActivationId));
        replay.add("replayMaterializations", new JsonArray());
        replay.add("forcedBranches", new JsonArray());
        replay.addProperty("modelProjectionAuthority",
                "Z3_BOUNDED_COMPOSITION_WITH_MATERIALIZABILITY_REFINEMENT");
        replay.addProperty("branchOverrideAllowed", false);
        replay.addProperty("concreteReplayOnly", true);
        replay.addProperty("boundedProducerBroadcast", true);
        replay.addProperty("boundedProducerInstanceSetId", ambiguitySetId);
        replay.addProperty("broadcastCandidateActivationId",
                string(candidate, "activationId"));
        replay.addProperty("broadcastSelectionAuthority",
                "EXPLICIT_PRE_TARGET_EQUIVALENT_PRODUCER_BOUND");
        return replay;
    }

    private static void addModelProjectionProvenance(
            JsonObject replay, String solverInputSha256,
            int manifestSchemaVersion) {
        replay.addProperty("modelProjectionAuthority",
                "Z3_BOUNDED_COMPOSITION_WITH_MATERIALIZABILITY_REFINEMENT");
        replay.addProperty("modelProjectionSolverInputSha256",
                solverInputSha256);
        replay.addProperty("modelProjectionModelScope",
                "ONE_SHARED_COMPLETE_COMPOSED_SMT_MODEL");
        replay.addProperty("modelProjectionManifestSchemaVersion",
                manifestSchemaVersion);
    }

    private static JsonArray candidateMaterializations(JsonObject source,
                                                       JsonObject candidate) {
        JsonArray result = actionArray(source).deepCopy();
        Map<String, JsonObject> candidateActions = new LinkedHashMap<>();
        for (JsonElement element : actionArray(candidate)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            candidateActions.put(actionIdentity(action), action);
        }
        for (JsonElement element : result) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            JsonObject candidateAction = candidateActions.get(
                    actionIdentity(action));
            if (candidateAction == null) continue;
            copyMember(candidateAction, action, "fieldReceiverObjectId");
            copyMember(candidateAction, action, "valueObjectId");
            copyMember(candidateAction, action, "primitiveValue");
            copyMember(candidateAction, action, "observed");
        }
        return result;
    }

    private static JsonArray candidateAssignments(JsonArray assignments,
                                                   JsonArray actions,
                                                   String replayActivationId) {
        Map<String, JsonObject> actionBySymbol = new LinkedHashMap<>();
        for (JsonElement element : actions) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            actionBySymbol.put(string(action, "symbol"), action);
        }
        JsonArray result = assignments.deepCopy();
        for (JsonElement element : result) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            JsonObject target = actionBySymbol.get(string(assignment,
                    "inputSymbol"));
            if (target != null) assignment.add("target", target.deepCopy());
            JsonObject mapSelector = object(assignment,
                    "mapProjectionSelector");
            if (mapSelector.size() > 0) {
                mapSelector.addProperty("sourceObjectTokenScope",
                        string(mapSelector, "objectTokenScope"));
                mapSelector.addProperty("objectTokenScope",
                        replayActivationId);
                mapSelector.addProperty("replayScopeRebindingAuthority",
                        "SOURCE_CASE_SELECTOR_VALIDATED_THEN_REPLAY_"
                                + "ACTIVATION_SCOPE_REBOUND_TOKENS_NOT_"
                                + "COMPARED_ACROSS_EXECUTIONS");
            }
        }
        return result;
    }

    private static void copyMember(JsonObject from, JsonObject to,
                                   String member) {
        JsonElement value = from.get(member);
        if (value != null) to.add(member, value);
    }

    private static String logicalActionShape(JsonObject activation) {
        List<String> actions = new ArrayList<>();
        for (JsonElement element : actionArray(activation)) {
            if (!element.isJsonObject()) continue;
            actions.add(actionIdentity(element.getAsJsonObject()));
        }
        Collections.sort(actions);
        StringBuilder result = new StringBuilder();
        for (String action : actions) {
            if (result.length() > 0) result.append('\n');
            result.append(action);
        }
        return result.toString();
    }

    private static String actionIdentity(JsonObject action) {
        return string(action, "symbol") + "\u0001"
                + string(action, "cell") + "\u0001"
                + string(action, "sourceKind") + "\u0001"
                + string(action, "projection") + "\u0001"
                + string(action, "location");
    }

    private static List<EffectProjection> effectProjections(
            JsonObject summary, JsonObject activation,
            List<JsonObject> graph, JsonObject selectedCase)
            throws IOException {
        JsonObject arrayAction = uniqueArrayAction(activation);
        List<String> arrayBase = actionFieldPath(arrayAction);
        if (arrayBase.isEmpty()) {
            throw new IOException("Array action has no concrete field path");
        }
        Map<String, String> familyInputs = new LinkedHashMap<>();
        for (JsonElement element : array(summary, "heapEffects")) {
            if (!element.isJsonObject()) continue;
            JsonObject effect = element.getAsJsonObject();
            if ("ACTIVATION_SYMBOL".equals(string(effect,
                    "inputBinding"))) {
                familyInputs.put(string(effect, "stateFamily"),
                        string(effect, "inputPort"));
            }
        }
        List<EffectProjection> result = new ArrayList<>();
        for (JsonElement element : array(summary, "heapEffects")) {
            if (!element.isJsonObject()) continue;
            JsonObject effect = element.getAsJsonObject();
            if (!"MAP_PUT".equals(string(effect, "kind"))) continue;
            String key = expressionSymbol(effect.get("keyExpression"));
            String value = expressionSymbol(effect.get("valueExpression"));
            String preMap = firstNonBlank(familyInputs.get(string(effect,
                    "stateFamily")), string(effect, "inputPort"));
            if (key.isEmpty() || value.isEmpty() || preMap.isEmpty()) {
                throw new IOException("Incomplete MAP_PUT projection in "
                        + string(effect, "effectId"));
            }
            ArrayLoad load = arrayLoad(array(summary, "pathCondition"),
                    value);
            String keySolver = caseSolverTerm(selectedCase, key, "Int");
            String valueSolver = caseSolverTerm(selectedCase, value, "Ref");
            String arraySolver = caseSolverTerm(selectedCase, load.array,
                    "(Array Int Value)");
            StaticField field = staticField(graph,
                    string(effect, "codePosition"));
            List<String> path = new ArrayList<>(arrayBase);
            path.add("[" + load.index + "]");
            path.addAll(field.path);
            JsonObject evidence = new JsonObject();
            evidence.addProperty("effectId", string(effect, "effectId"));
            evidence.addProperty("keyEngineSymbol", key);
            evidence.addProperty("keySolverTerm", keySolver);
            evidence.addProperty("valueEngineSymbol", value);
            evidence.addProperty("valueSolverTerm", valueSolver);
            evidence.addProperty("arrayEngineId", load.array);
            evidence.addProperty("arraySolverTerm", arraySolver);
            evidence.addProperty("arrayIndex", load.index);
            evidence.addProperty("staticEdgeId", field.edgeId);
            evidence.addProperty("staticFieldPath", field.rawPath);
            evidence.add("materializationPath", GSON.toJsonTree(path));
            evidence.addProperty("authority",
                    "VM_ARRAY_LOAD_PLUS_STATIC_ACCESSOR_FIELD_RETURN");
            result.add(new EffectProjection(key, keySolver, value,
                    valueSolver, load.array, arraySolver, preMap,
                    string(arrayAction, "symbol"), arrayAction, path,
                    evidence));
        }
        return result;
    }

    private static ArrayLoad arrayLoad(JsonArray conditions,
                                       String valueSymbol)
            throws IOException {
        ArrayLoad selected = null;
        for (JsonElement element : conditions) {
            if (!element.isJsonObject()) continue;
            JsonObject condition = element.getAsJsonObject();
            if (!"_array_expr".equals(string(condition, "_type"))
                    || !bool(condition, "_is_load", false)
                    || !valueSymbol.equals(expressionSymbol(
                    condition.get("_value_exp")))) continue;
            JsonObject index = object(condition, "_index_exp");
            String raw = string(index, "_exp");
            Integer parsed = constantInteger(raw);
            if (parsed == null) {
                throw new IOException("Array index is not a concrete integer: "
                        + raw);
            }
            ArrayLoad candidate = new ArrayLoad(string(condition,
                    "_arr_str"), parsed);
            if (selected != null && (!selected.array.equals(candidate.array)
                    || selected.index != candidate.index)) {
                throw new IOException("Ambiguous array provenance for "
                        + valueSymbol);
            }
            selected = candidate;
        }
        if (selected == null) {
            throw new IOException("Missing array-load provenance for "
                    + valueSymbol);
        }
        return selected;
    }

    private static StaticField staticField(List<JsonObject> graph,
                                           String codePosition)
            throws IOException {
        Matcher code = CODE_POSITION.matcher(firstNonBlank(codePosition));
        if (!code.matches()) {
            throw new IOException("Unsupported VM code position: "
                    + codePosition);
        }
        String owner = code.group(1).replace('/', '.');
        String methodName = code.group(2);
        int line = Integer.parseInt(code.group(3));
        Map<String, JsonObject> byPath = new LinkedHashMap<>();
        for (JsonObject edge : graph) {
            if (!"accessor_field_return".equals(string(edge, "kind"))
                    || integer(edge, "line", Integer.MIN_VALUE) != line) {
                continue;
            }
            String method = string(edge, "method");
            if (!method.startsWith("<" + owner + ":")
                    || !method.contains(" " + methodName + "(")) continue;
            String path = string(edge, "fieldPath");
            if (!path.isEmpty()) byPath.put(path, edge);
        }
        if (byPath.size() != 1) {
            throw new IOException("Expected one static accessor field path at "
                    + codePosition + ", found " + byPath.keySet());
        }
        Map.Entry<String, JsonObject> selected = byPath.entrySet().iterator()
                .next();
        List<String> segments = projectedFields(selected.getKey());
        if (segments.isEmpty()) {
            throw new IOException("Static accessor path is empty at "
                    + codePosition);
        }
        return new StaticField(string(selected.getValue(), "id"),
                selected.getKey(), segments);
    }

    private static JsonObject uniqueArrayAction(JsonObject activation)
            throws IOException {
        JsonObject selected = null;
        for (JsonElement element : actionArray(activation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            Matcher field = DECLARED_FIELD.matcher(string(action, "cell"));
            if (!field.matches() || !field.group(2).trim().endsWith("[]")) {
                continue;
            }
            if (selected != null) {
                throw new IOException("More than one array input action is "
                        + "eligible for finite-map projection");
            }
            selected = action;
        }
        if (selected == null) {
            throw new IOException("No array input action is eligible for "
                    + "finite-map projection");
        }
        return selected;
    }

    private static JsonObject scalarAssignment(EffectProjection projection,
                                               String value) {
        JsonObject assignment = assignmentBase(projection.keyRaw,
                projection.keySolverTerm, projection.inputSymbol, "INT",
                value, projection.action);
        assignment.add("materializationPath",
                GSON.toJsonTree(projection.path));
        assignment.addProperty("projectionEffectId",
                string(projection.evidence, "effectId"));
        assignment.addProperty("projectionRefinement",
                "NON_NULL_INSERTED_REFERENCE_AND_JAVA_INT_RANGE");
        return assignment;
    }

    private static JsonObject detachArrayAssignment(
            EffectProjection projection) {
        JsonObject assignment = assignmentBase(projection.arrayRaw,
                projection.arraySolverTerm, projection.inputSymbol,
                "REF_ARRAY", "FRESH_SHALLOW_COPIES", projection.action);
        assignment.addProperty("modelOperation",
                "ARRAY_SHALLOW_COPY_ELEMENTS");
        assignment.add("materializationPath",
                GSON.toJsonTree(actionFieldPath(projection.action)));
        assignment.addProperty("projectionRefinement",
                "DISTINCT_NON_NULL_ARRAY_ELEMENT_REFERENCES");
        return assignment;
    }

    static JsonObject dynamicScalarAssignment(
            DynamicTermProjection projection, Map<String, String> values)
            throws IOException {
        String solverSort = string(projection.binding, "solverSort");
        String valueType;
        String floatingDescriptor = "";
        if ("Int".equals(solverSort)) valueType = "INT";
        else if ("(_ FloatingPoint 8 24)".equals(solverSort)) {
            valueType = "REAL";
            floatingDescriptor = "F";
        } else if ("(_ FloatingPoint 11 53)".equals(solverSort)) {
            valueType = "REAL";
            floatingDescriptor = "D";
        }
        else if ("Bool".equals(solverSort)) valueType = "BOOL";
        else if ("String".equals(solverSort)) valueType = "STRING";
        else valueType = "INT";
        String modelValue = normalizeModelValue(values.get(
                projection.solverTerm));
        String replayValue = modelValue;
        String nullnessModelValue = "";
        if ("String".equals(solverSort)) {
            nullnessModelValue = normalizeModelValue(values.get(
                    projection.nullnessSolverTerm));
            if (!("true".equals(nullnessModelValue)
                    || "false".equals(nullnessModelValue))) {
                throw projectionGap("DYNAMIC_STRING_NULLNESS_MODEL_INVALID:"
                        + projection.nullnessSolverTerm + ":"
                        + nullnessModelValue);
            }
            if ("true".equals(nullnessModelValue)) {
                valueType = "NULL";
                replayValue = "null";
            }
        }
        if (!floatingDescriptor.isEmpty()) {
            replayValue = SmtModelValueCodec
                    .floatingPointTermToJavaLiteral(modelValue,
                            floatingDescriptor);
            if (replayValue == null) {
                throw projectionGap("FLOATING_MODEL_TERM_UNSUPPORTED:"
                        + projection.solverTerm + ":" + modelValue);
            }
        }
        JsonObject assignment = assignmentBase(projection.rawEngineSymbol,
                projection.solverTerm, string(projection.binding,
                        "baseInputSymbol"), valueType, replayValue,
                projection.targetAction);
        if (!projection.nullnessSolverTerm.isEmpty()) {
            assignment.addProperty("nullnessSolverTerm",
                    projection.nullnessSolverTerm);
            assignment.addProperty("nullnessModelValue",
                    nullnessModelValue);
            assignment.addProperty("contentSolverTerm",
                    projection.solverTerm);
            assignment.addProperty("contentModelValue", modelValue);
            assignment.addProperty("nullableStringEncodingAuthority",
                    NULLABLE_STRING_ENCODING_AUTHORITY);
        }
        if (!floatingDescriptor.isEmpty()) {
            assignment.addProperty("floatingPointFormat",
                    floatingDescriptor);
            assignment.addProperty("modelFloatingPointTerm", modelValue);
        }
        assignment.add("materializationPath", array(projection.binding,
                "fieldPath").deepCopy());
        assignment.addProperty("projectionRefinement",
                "SELECTED_CASE_DYNAMIC_FIELD_ACTUAL_EMITTER_TERM");
        assignment.addProperty("caseProjectionAuthority",
                isMapProjectionBinding(projection.binding)
                ? "SELECTED_SOURCE_CASE_EXACT_RUNTIME_SYMBOLIZE_FIELD_"
                + "TERM" : "CASE_PROJECTION_CATALOG_ACTUAL_TERM");
        copyMember(projection.binding, assignment,
                "termBindingAuthority");
        return assignment;
    }

    private static JsonObject assignmentBase(String engine, String solver,
                                             String input, String type,
                                             String value,
                                             JsonObject target) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", engine);
        assignment.addProperty("solverSymbol", solver);
        assignment.addProperty("inputSymbol", input);
        assignment.addProperty("valueType", type);
        assignment.addProperty("value", value);
        assignment.addProperty("authority",
                "Z3_BOUNDED_COMPOSED_MODEL_PROJECTION");
        assignment.addProperty("materializeAtRealDefinition", true);
        assignment.add("target", target.deepCopy());
        return assignment;
    }

    static JsonObject retainDynamicSelector(JsonObject summary,
                                            JsonObject activation,
                                            JsonObject assignment)
            throws IOException {
        return DynamicProjectionRegistry.from(summary).retainSelector(
                assignment, activation);
    }

    private static List<DynamicTermProjection> dynamicTermProjections(
            JsonObject selectedCase, DynamicProjectionRegistry registry,
            JsonObject activation) throws IOException {
        List<DynamicTermProjection> result = new ArrayList<>();
        Set<String> solverTerms = new LinkedHashSet<>();
        Set<String> entryKeys = new LinkedHashSet<>();
        String selectorGuard = string(selectedCase,
                "selectorGuardFormula");
        for (JsonElement element : array(selectedCase,
                "dynamicFieldBindings")) {
            if (!element.isJsonObject()) {
                throw projectionGap("NON_OBJECT_SELECTED_DYNAMIC_BINDING");
            }
            JsonObject binding = element.getAsJsonObject();
            String raw = string(binding,
                    "fieldExpressionRawEngineSymbol");
            String solver = string(binding, "solverTerm");
            String dynamic = string(binding, "dynamicFieldSymbol");
            String base = string(binding, "baseInputSymbol");
            boolean mapProjection = isMapProjectionBinding(binding);
            String expectedTermAuthority = mapProjection
                    ? "EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_PC_EXPRESSION"
                    : "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM";
            if (raw.isEmpty() || solver.isEmpty() || dynamic.isEmpty()
                    || base.isEmpty()
                    || !expectedTermAuthority.equals(string(binding,
                    "termBindingAuthority"))
                    || !bool(binding, "observationMatched", false)) {
                throw projectionGap("INCOMPLETE_SELECTED_DYNAMIC_TERM:"
                        + string(binding, "dynamicBindingId"));
            }
            String bindingSort = string(binding, "solverSort");
            JsonObject caseMapping = caseSolverMapping(selectedCase, raw,
                    bindingSort);
            String mapped = string(caseMapping, "solverTerm");
            if (!solver.equals(mapped)) {
                throw projectionGap("DYNAMIC_TERM_CATALOG_MISMATCH:"
                        + string(binding, "dynamicBindingId"));
            }
            String nullnessSolverTerm = "";
            if ("String".equals(bindingSort)) {
                nullnessSolverTerm = string(caseMapping,
                        "nullnessSolverTerm");
                if (nullnessSolverTerm.isEmpty()
                        || !nullnessSolverTerm.equals(string(binding,
                        "nullnessSolverTerm"))
                        || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                        caseMapping, "nullableStringEncodingAuthority"))
                        || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                        binding, "nullableStringEncodingAuthority"))) {
                    throw projectionGap("DYNAMIC_STRING_NULLNESS_CATALOG_"
                            + "MISMATCH:" + string(binding,
                            "dynamicBindingId"));
                }
            }
            boolean mapEntry = "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(
                    string(binding, "kind"));
            if (!mapProjection
                    && !formulaReferencesTerm(selectorGuard, solver)
                    && (nullnessSolverTerm.isEmpty()
                    || !formulaReferencesTerm(selectorGuard,
                    nullnessSolverTerm))) {
                continue;
            }
            if (registry.byDynamic.get(dynamic) == null) {
                throw projectionGap("DYNAMIC_BINDING_NOT_IN_SELECTED_"
                        + "REGISTRY:" + dynamic);
            }
            String concreteKey = mapEntry
                    ? concreteImmutableEntryKey(binding) : "";
            if (!solverTerms.add(solver)) {
                throw projectionGap("DUPLICATE_DYNAMIC_SOLVER_TERM:"
                        + solver);
            }
            if (!nullnessSolverTerm.isEmpty()
                    && !solverTerms.add(nullnessSolverTerm)) {
                throw projectionGap("DUPLICATE_DYNAMIC_SOLVER_TERM:"
                        + nullnessSolverTerm);
            }
            if (!concreteKey.isEmpty() && !entryKeys.add(concreteKey)) {
                throw projectionGap("AMBIGUOUS_DYNAMIC_ENTRY_KEY:"
                        + concreteKey);
            }
            JsonObject target = DynamicProjectionRegistry.uniqueAction(
                    activation, base);
            if (target == null) {
                throw projectionGap("NO_UNIQUE_STATIC_ACTION_FOR_BASE:"
                        + base);
            }
            result.add(new DynamicTermProjection(binding.deepCopy(), raw,
                    solver, nullnessSolverTerm, concreteKey,
                    target.deepCopy()));
        }
        return result;
    }

    private static boolean formulaReferencesTerm(String formula,
                                                 String term) {
        if (formula == null || term == null || term.isEmpty()) return false;
        return Pattern.compile("(?<![A-Za-z0-9_])" + Pattern.quote(term)
                + "(?![A-Za-z0-9_])").matcher(formula).find();
    }

    private static boolean isMapProjectionBinding(JsonObject binding) {
        return "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING"
                .equals(string(binding, "kind"));
    }

    private static String concreteImmutableEntryKey(JsonObject binding)
            throws IOException {
        String authority = string(binding, "keyExpressionAuthority");
        if (!("CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT".equals(authority)
                || "CONCRETE_REPLAY_RUNTIME_VALUE_AT_ITERATOR_NEXT".equals(
                authority)
                || "CUSTOM_JDK_PUBLIC_EXPRESSION_API_AT_ITERATOR_NEXT".equals(
                authority))) {
            throw projectionGap("NON_IMMUTABLE_DYNAMIC_ENTRY_KEY_AUTHORITY:"
                    + authority);
        }
        JsonObject expression = object(binding, "keyExpression");
        if (!"ConstExpr".equals(string(expression, "_type"))) {
            throw projectionGap("NON_CONCRETE_DYNAMIC_ENTRY_KEY:"
                    + string(binding, "dynamicBindingId"));
        }
        Integer value = constantInteger(string(expression, "_exp"));
        if (value == null) {
            throw projectionGap("NON_INTEGER_DYNAMIC_ENTRY_KEY:"
                    + string(expression, "_exp"));
        }
        return String.valueOf(value);
    }

    private static String caseSolverTerm(JsonObject selectedCase, String raw,
                                         String expectedSolverSort)
            throws IOException {
        return string(caseSolverMapping(selectedCase, raw,
                expectedSolverSort), "solverTerm");
    }

    private static JsonObject caseSolverMapping(JsonObject selectedCase,
                                                String raw,
                                                String expectedSolverSort)
            throws IOException {
        JsonObject selected = null;
        for (JsonElement element : array(selectedCase,
                "rawEngineSymbolMappings")) {
            if (!element.isJsonObject()) continue;
            JsonObject mapping = element.getAsJsonObject();
            if (!raw.equals(string(mapping, "rawEngineSymbol"))) continue;
            if (selected != null) {
                throw projectionGap("DUPLICATE_RAW_ENGINE_SYMBOL_MAPPING:"
                        + raw);
            }
            selected = mapping;
        }
        if (selected == null
                || string(selected, "solverTerm").isEmpty()
                || string(selected, "solverSort").isEmpty()
                || !"EMITTER_ACTUAL_TERM".equals(string(selected,
                "authority"))) {
            throw projectionGap("MISSING_ACTUAL_CASE_SOLVER_TERM:" + raw);
        }
        if (!firstNonBlank(expectedSolverSort).isEmpty()
                && !expectedSolverSort.equals(string(selected,
                "solverSort"))) {
            throw projectionGap("CASE_SOLVER_TERM_SORT_MISMATCH:" + raw
                    + ":expected=" + expectedSolverSort + ":actual="
                    + string(selected, "solverSort"));
        }
        if ("String".equals(string(selected, "solverSort"))
                && (string(selected, "nullnessSolverTerm").isEmpty()
                || !NULLABLE_STRING_ENCODING_AUTHORITY.equals(string(
                selected, "nullableStringEncodingAuthority")))) {
            throw projectionGap("CASE_STRING_NULLNESS_MAPPING_INCOMPLETE:"
                    + raw);
        }
        return selected;
    }

    private static final class DynamicProjectionRegistry {
        private final List<JsonObject> bindings = new ArrayList<>();
        private final Map<String, JsonObject> byDynamic =
                new LinkedHashMap<>();
        private final Map<String, List<JsonObject>> byBase =
                new LinkedHashMap<>();

        private static DynamicProjectionRegistry from(JsonObject summary)
                throws IOException {
            DynamicProjectionRegistry result =
                    new DynamicProjectionRegistry();
            Set<String> ids = new LinkedHashSet<>();
            for (JsonElement element : array(summary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) {
                    throw projectionGap("NON_OBJECT_DYNAMIC_BINDING");
                }
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "dynamicBindingId");
                String base = string(binding, "baseInputSymbol");
                String dynamic = string(binding, "dynamicFieldSymbol");
                String site = string(binding, "materializationSiteId");
                int occurrence = integer(binding,
                        "materializationOccurrence", -1);
                String kind = string(binding, "kind");
                boolean map = "DYNAMIC_MAP_ENTRY_FIELD_BINDING".equals(kind);
                boolean container =
                        "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(kind);
                boolean mapProjection = isMapProjectionBinding(binding);
                boolean kindComplete = map
                        && integer(binding, "schemaVersion", -1) == 1
                        && binding.get("keyExpression") != null
                        && !string(binding,
                        "keyExpressionAuthority").isEmpty()
                        || container
                        && integer(binding, "schemaVersion", -1) == 2
                        && "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                        .concat("IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE")
                        .equals(string(binding, "authority"))
                        && completeContainerSelector(binding);
                kindComplete |= mapProjection
                        && integer(binding, "schemaVersion", -1) == 3
                        && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_"
                        .concat("WITH_EXACT_OUTPUT_IDENTITY")
                        .equals(string(binding, "authority"))
                        && "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_"
                        .concat("SYMBOLIZED_INPUT").equals(string(binding,
                                "runtimeSymbolizationAuthority"))
                        && "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_"
                        .concat("IDENTITY_VALIDATION").equals(string(binding,
                                "projectionEvidenceAuthority"))
                        && completeMapProjectionSelector(binding);
                if (!kindComplete
                        || !bool(binding, "complete", false)
                        || id.isEmpty() || base.isEmpty()
                        || dynamic.isEmpty() || site.isEmpty()
                        || occurrence < 1
                        || !id.equals("DYNAMIC_FIELD:" + dynamic)) {
                    throw projectionGap("INCOMPLETE_DYNAMIC_BINDING:" + id);
                }
                String expected = base + ".field."
                        + sha256(site).substring(0, 12) + ".occ."
                        + occurrence;
                if (!expected.equals(dynamic)) {
                    throw projectionGap(
                            "DYNAMIC_SYMBOL_SITE_OCCURRENCE_MISMATCH:"
                                    + dynamic);
                }
                if (!ids.add(id) || result.byDynamic.put(dynamic,
                        binding.deepCopy()) != null) {
                    throw projectionGap("DUPLICATE_DYNAMIC_BINDING:" + id);
                }
                JsonObject copy = binding.deepCopy();
                result.bindings.add(copy);
                List<JsonObject> family = result.byBase.get(base);
                if (family == null) {
                    family = new ArrayList<>();
                    result.byBase.put(base, family);
                }
                family.add(copy);
            }
            return result;
        }

        private static DynamicProjectionRegistry fromCatalog(
                JsonObject selectedCase, JsonObject rawSummary)
                throws IOException {
            Map<String, JsonObject> rawById = new LinkedHashMap<>();
            for (JsonElement element : array(rawSummary,
                    "dynamicFieldBindings")) {
                if (!element.isJsonObject()) {
                    throw projectionGap("NON_OBJECT_RAW_DYNAMIC_BINDING");
                }
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "dynamicBindingId");
                if (id.isEmpty() || rawById.put(id, binding) != null) {
                    throw projectionGap("DUPLICATE_RAW_DYNAMIC_BINDING:" + id);
                }
            }
            JsonArray selectedBindings = array(selectedCase,
                    "dynamicFieldBindings");
            JsonObject selectedSummary = new JsonObject();
            JsonArray normalized = new JsonArray();
            Set<String> selectedIds = new LinkedHashSet<>();
            for (JsonElement element : selectedBindings) {
                if (!element.isJsonObject()) {
                    throw projectionGap("NON_OBJECT_CATALOG_DYNAMIC_BINDING");
                }
                JsonObject binding = element.getAsJsonObject();
                String id = string(binding, "dynamicBindingId");
                JsonObject runtime = object(binding, "runtimeBinding");
                JsonObject raw = rawById.get(id);
                if (id.isEmpty() || !selectedIds.add(id) || raw == null
                        || runtime.size() == 0 || !runtime.equals(raw)) {
                    throw projectionGap("SELECTED_DYNAMIC_BINDING_RAW_"
                            + "SUMMARY_MISMATCH:" + id);
                }
                normalized.add(binding.deepCopy());
            }
            if (selectedIds.size() != rawById.size()) {
                throw projectionGap("SELECTED_DYNAMIC_BINDING_COUNT_"
                        + "MISMATCH:selected=" + selectedIds.size()
                        + ":raw=" + rawById.size());
            }
            selectedSummary.add("dynamicFieldBindings", normalized);
            return from(selectedSummary);
        }

        private JsonObject retainSelector(JsonObject source,
                                          JsonObject activation)
                throws IOException {
            JsonObject assignment = source.deepCopy();
            String engine = string(assignment, "engineSymbol");
            JsonObject selected = exactDynamic(engine);
            if (selected == null) {
                for (Map.Entry<String, List<JsonObject>> entry
                        : byBase.entrySet()) {
                    String base = entry.getKey();
                    boolean ownsAssignment = base.equals(string(assignment,
                            "inputSymbol")) || base.equals(string(assignment,
                            "baseInputSymbol"));
                    if (!exactEngineSymbol(engine, base)) {
                        if (ownsAssignment) {
                            throw projectionGap(
                                    "ENGINE_SYMBOL_NOT_EXACT_DYNAMIC_BINDING:"
                                            + engine);
                        }
                        continue;
                    }
                    if (entry.getValue().size() > 1) {
                        throw projectionGap("AMBIGUOUS_DYNAMIC_BASE_INPUT:"
                                + base + ":"
                                + entry.getValue().size());
                    }
                    throw projectionGap("BASE_ONLY_DYNAMIC_INPUT_PROHIBITED:"
                            + base);
                }
            }
            if (selected == null) return assignment;

            requireCompatibleSelector(assignment, selected);

            String base = string(selected, "baseInputSymbol");
            JsonObject target = uniqueAction(activation, base);
            if (target == null) {
                throw projectionGap("NO_UNIQUE_STATIC_ACTION_FOR_BASE:"
                        + base);
            }
            if (isContainerBinding(selected)) {
                JsonObject selector = object(selected,
                        "containerSelector");
                JsonObject containerAction = uniqueAction(activation,
                        string(selector, "containerInputPort"));
                if (containerAction == null || !string(selector,
                        "containerInputCell").equals(string(containerAction,
                        "cell"))) {
                    throw projectionGap(
                            "NO_EXACT_CONTAINER_ACTION_FOR_DYNAMIC_BINDING:"
                                    + string(selector,
                                    "containerInputPort"));
                }
            } else if (isMapProjectionBinding(selected)) {
                JsonObject selector = object(selected,
                        "mapProjectionSelector");
                JsonObject mapAction = uniqueAction(activation,
                        string(selector, "mapInputPort"));
                if (mapAction == null || !string(selector,
                        "mapInputCell").equals(string(mapAction, "cell"))) {
                    throw projectionGap(
                            "NO_EXACT_MAP_ACTION_FOR_MAP_PROJECTION:"
                                    + string(selector, "mapInputPort"));
                }
            }
            assignment.addProperty("inputSymbol", base);
            assignment.add("target", target.deepCopy());
            copyMember(selected, assignment, "dynamicBindingId");
            copyMember(selected, assignment, "baseInputSymbol");
            copyMember(selected, assignment, "dynamicFieldSymbol");
            copyMember(selected, assignment, "materializationSiteId");
            copyMember(selected, assignment, "materializationOccurrence");
            copyMember(selected, assignment, "fieldSignature");
            copyMember(selected, assignment, "fieldPath");
            assignment.addProperty("dynamicFieldBindingKind",
                    string(selected, "kind"));
            if (isContainerBinding(selected)) {
                assignment.add("containerSelector",
                        normalizedContainerSelector(selected));
                assignment.addProperty("containerReplayRebindingAuthority",
                        CONTAINER_REPLAY_REBINDING_AUTHORITY);
                assignment.addProperty(
                        "sourceContainerObjectTokensRetained", false);
            } else if (isMapProjectionBinding(selected)) {
                assignment.add("mapProjectionSelector",
                        normalizedMapProjectionSelector(selected));
            } else {
                copyMember(selected, assignment, "entryReadObservationId");
                copyMember(selected, assignment, "keyExpression");
                copyMember(selected, assignment, "keyExpressionAuthority");
                JsonElement key = selected.get("keyExpression");
                assignment.add("expectedEntryKey", key.deepCopy());
                assignment.addProperty("expectedEntryKeyAuthority",
                        string(selected, "keyExpressionAuthority"));
            }
            if (selected.get("fieldPath") != null
                    && selected.get("fieldPath").isJsonArray()) {
                assignment.add("materializationPath",
                        selected.get("fieldPath").deepCopy());
            }
            return assignment;
        }

        private JsonObject exactDynamic(String engine) throws IOException {
            JsonObject direct = byDynamic.get(engine);
            if (direct != null) return direct;
            JsonObject result = null;
            for (JsonObject binding : bindings) {
                if (!exactEngineSymbol(engine, string(binding,
                        "dynamicFieldSymbol"))) continue;
                if (result != null) {
                    throw projectionGap(
                            "AMBIGUOUS_DYNAMIC_ENGINE_SYMBOL:" + engine);
                }
                result = binding;
            }
            return result;
        }

        private static void requireCompatibleSelector(JsonObject assignment,
                                                       JsonObject binding)
                throws IOException {
            if (assignment.has("inputSymbol")
                    && !assignment.get("inputSymbol").getAsString().equals(
                    string(binding, "baseInputSymbol"))) {
                throw projectionGap("CROSS_BINDING_SELECTOR:inputSymbol");
            }
            requireEqualIfPresent(assignment, binding, "dynamicBindingId");
            requireEqualIfPresent(assignment, binding, "baseInputSymbol");
            requireEqualIfPresent(assignment, binding,
                    "dynamicFieldSymbol");
            requireEqualIfPresent(assignment, binding,
                    "materializationSiteId");
            requireEqualIfPresent(assignment, binding,
                    "materializationOccurrence");
            if (isContainerBinding(binding)) {
                if (assignment.has("containerSelector")
                        && !assignment.get("containerSelector").equals(
                        normalizedContainerSelector(binding))) {
                    throw projectionGap(
                            "CROSS_BINDING_CONTAINER_SELECTOR");
                }
                if (assignment.has("expectedEntryKey")) {
                    throw projectionGap(
                            "CONTAINER_BINDING_HAS_MAP_KEY_SELECTOR");
                }
            } else if (isMapProjectionBinding(binding)) {
                if (assignment.has("mapProjectionSelector")
                        && !assignment.get("mapProjectionSelector").equals(
                        normalizedMapProjectionSelector(binding))) {
                    throw projectionGap(
                            "CROSS_BINDING_MAP_PROJECTION_SELECTOR");
                }
                if (assignment.has("containerSelector")
                        || assignment.has("expectedEntryKey")) {
                    throw projectionGap(
                            "MAP_PROJECTION_HAS_FOREIGN_SELECTOR");
                }
            } else {
                requireEqualIfPresent(assignment, binding,
                        "entryReadObservationId");
                if (assignment.has("expectedEntryKey")
                        && !assignment.get("expectedEntryKey").equals(
                        binding.get("keyExpression"))) {
                    throw projectionGap("CROSS_BINDING_EXPECTED_ENTRY_KEY");
                }
            }
        }

        private static boolean isContainerBinding(JsonObject binding) {
            return "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING".equals(
                    string(binding, "kind"));
        }

        private static boolean completeContainerSelector(JsonObject binding) {
            JsonObject selector = object(binding, "containerSelector");
            long leaf = longInteger(binding,
                    "leafOwnerObjectToken", 0L);
            long container = longInteger(selector,
                    "containerObjectToken", 0L);
            long element = longInteger(selector,
                    "elementObjectToken", 0L);
            String scope = string(binding, "objectTokenScope");
            String resolved = string(selector,
                    "resolvedFromSelectorAuthority");
            String selectorBindingId = string(selector, "bindingId");
            int occurrence = integer(binding,
                    "materializationOccurrence", -1);
            boolean directLeafOwner = array(binding, "fieldPath").size() == 1
                    && leaf == element;
            boolean bridgedDeepLeafOwner = array(binding,
                    "fieldPath").size() > 1
                    && ("CONTAINER_SNAPSHOT:" + selectorBindingId).equals(
                    string(binding, "actualHookSiteId"))
                    && occurrence == integer(binding,
                    "actualHookOccurrence", -2)
                    && string(binding, "materializationSiteId").equals(
                    string(binding, "effectiveMaterializationSiteId"))
                    && occurrence == integer(binding,
                    "effectiveMaterializationOccurrence", -2)
                    && "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_"
                    .concat("EXACT_ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1")
                    .equals(string(binding,
                            "materializationSiteBridgeAuthority"))
                    && selectorBindingId.equals(string(binding,
                    "materializationSiteBridgeBindingId"))
                    && element == longInteger(binding,
                    "materializationSiteBridgeElementObjectToken", 0L)
                    && scope.equals(string(binding,
                    "materializationSiteBridgeObjectTokenScope"));
            return "ARRAY_INDEX".equals(string(selector, "kind"))
                    && bool(selector, "complete", false)
                    && !string(selector, "bindingId").isEmpty()
                    && !string(selector, "containerInputPort").isEmpty()
                    && !string(selector, "containerInputCell").isEmpty()
                    && !string(selector, "containerInputPort").equals(
                    string(binding, "baseInputSymbol"))
                    && "EXACT_ARRAY_INDEX".equals(string(selector,
                    "selectorAuthority"))
                    && integer(selector, "elementIndex", -1) >= 0
                    && integer(selector, "elementOccurrence", -1) > 0
                    && integer(selector, "elementOccurrence", -1)
                    == integer(binding, "materializationOccurrence", -2)
                    && !string(selector,
                    "declaredFieldOwnerClass").isEmpty()
                    && !string(selector, "declaredFieldType").isEmpty()
                    && leaf > 0L && container > 0L && element > 0L
                    && (directLeafOwner || bridgedDeepLeafOwner)
                    && !scope.isEmpty()
                    && scope.equals(string(selector, "objectTokenScope"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(binding, "objectTokenAuthority"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(selector, "objectTokenAuthority"))
                    && ("EXACT_ARRAY_INDEX".equals(resolved)
                    || "DISCOVER_UNIQUE_IDENTITY_INDEX".equals(resolved))
                    && "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                    .concat("ACTIVATION_LOCAL_ELEMENT_IDENTITY").equals(
                            string(selector, "authority"))
                    && !string(binding, "containerBindingId").isEmpty()
                    && string(binding, "containerBindingId").equals(string(
                    selector, "bindingId"))
                    && !string(binding, "containerInputPort").isEmpty()
                    && string(binding, "containerInputPort").equals(string(
                    selector, "containerInputPort"))
                    && !string(binding, "containerInputCell").isEmpty()
                    && string(binding, "containerInputCell").equals(string(
                    selector, "containerInputCell"))
                    && "EXACT_ARRAY_INDEX".equals(string(binding,
                    "selectorAuthority"))
                    && string(binding, "selectorAuthority").equals(string(
                    selector, "selectorAuthority"))
                    && !string(binding,
                    "resolvedFromSelectorAuthority").isEmpty()
                    && string(binding, "resolvedFromSelectorAuthority")
                    .equals(resolved)
                    && integer(binding, "elementIndex", -1) == integer(
                    selector, "elementIndex", -2)
                    && integer(binding, "elementOccurrence", -1) == integer(
                    selector, "elementOccurrence", -2)
                    && !string(binding,
                    "declaredFieldOwnerClass").isEmpty()
                    && string(binding, "declaredFieldOwnerClass").equals(
                    string(selector, "declaredFieldOwnerClass"))
                    && !string(binding, "declaredFieldType").isEmpty()
                    && string(binding, "declaredFieldType").equals(string(
                    selector, "declaredFieldType"));
        }

        private static JsonObject normalizedContainerSelector(
                JsonObject binding) {
            JsonObject source = object(binding, "containerSelector");
            JsonObject result = new JsonObject();
            for (String member : new String[]{"kind", "bindingId",
                    "containerInputPort", "containerInputCell",
                    "selectorAuthority", "elementIndex",
                    "elementOccurrence", "declaredFieldOwnerClass",
                    "declaredFieldType"}) {
                copyMember(source, result, member);
            }
            return result;
        }

        private static boolean completeMapProjectionSelector(
                JsonObject binding) {
            JsonObject selector = object(binding,
                    "mapProjectionSelector");
            int index = integer(selector, "outputIndex", -1);
            int occurrence = integer(selector,
                    "elementOccurrence", -1);
            int count = integer(binding,
                    "entrySnapshotElementCount", -1);
            long leaf = longInteger(binding,
                    "leafOwnerObjectToken", 0L);
            long map = longInteger(selector, "mapObjectToken", 0L);
            long element = longInteger(selector,
                    "elementObjectToken", 0L);
            long output = longInteger(selector,
                    "outputArrayObjectToken", 0L);
            String scope = string(binding, "objectTokenScope");
            JsonArray tokens = array(binding,
                    "entrySnapshotElementObjectTokens");
            JsonArray keys = array(binding,
                    "entrySnapshotMapKeyExpressions");
            String mode = string(binding, "outputValidationMode");
            String outputAuthority = string(selector,
                    "outputVerificationAuthority");
            boolean outputAuthorityValid =
                    "ROOT_RETURN_PROJECTED_FIELD".equals(mode)
                    && "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD"
                    .equals(outputAuthority)
                    || "EXACT_REQUESTED_OUTPUT_CAPTURE".equals(mode)
                    && ("ACTIVE_TOKEN_EXACT_ORIGINAL_CALL_ARGUMENT".equals(
                    outputAuthority)
                    || "ACTIVE_TOKEN_EXACT_POST_INSTANCE_FIELD_ASSIGNMENT"
                    .equals(outputAuthority));
            Set<Long> distinctTokens = new LinkedHashSet<>();
            boolean allTokensValid = tokens.size() == count;
            for (JsonElement tokenElement : tokens) {
                long token = jsonLong(tokenElement, 0L);
                allTokensValid &= token > 0L && distinctTokens.add(token);
            }
            Set<String> distinctKeys = new LinkedHashSet<>();
            boolean allKeysValid = keys.size() == count;
            for (JsonElement keyElement : keys) {
                String stableKey = stableImmutableMapKeySelector(keyElement);
                allKeysValid &= !stableKey.isEmpty()
                        && distinctKeys.add(stableKey);
            }
            return "MAP_OUTPUT_ARRAY_INDEX".equals(string(selector,
                    "kind"))
                    && bool(selector, "complete", false)
                    && !string(selector, "bindingId").isEmpty()
                    && !string(selector, "mapInputPort").isEmpty()
                    && !string(selector, "mapInputCell").isEmpty()
                    && !string(selector, "outputPort").isEmpty()
                    && !string(selector, "outputCell").isEmpty()
                    && ("MAP_VALUES_VIEW".equals(string(selector,
                    "mapProjectionOperation"))
                    || "MAP_KEY_SET_VIEW".equals(string(selector,
                    "mapProjectionOperation")))
                    && index >= 0 && occurrence == index + 1
                    && occurrence == integer(binding,
                    "materializationOccurrence", -2)
                    && !string(selector,
                    "declaredFieldOwnerClass").isEmpty()
                    && !string(selector,
                    "declaredFieldType").isEmpty()
                    && !string(selector,
                    "declaredFieldSignature").isEmpty()
                    && string(binding, "fieldSignature").equals(string(
                    selector, "declaredFieldSignature"))
                    && leaf > 0L && map > 0L && element == leaf
                    && output > 0L
                    && map != element && map != output && element != output
                    && count > 0 && integer(binding,
                    "outputElementCount", -1) == count
                    && allTokensValid && allKeysValid && index < count
                    && jsonLong(tokens.get(index), -1L) == element
                    && selector.get("expectedMapKey") != null
                    && selector.get("expectedMapKey").equals(keys.get(index))
                    && exactImmutableMapKeyExpression(selector.get(
                    "expectedMapKey"))
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(string(selector,
                            "expectedMapKeyAuthority"))
                    && "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_"
                    .concat("SNAPSHOT").equals(string(binding,
                            "entryKeyExpressionAuthority"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                            selector, "sourceOutputIndexAuthority"))
                    && "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                    .concat("POSITIONAL_REFERENCE_EQUALITY").equals(string(
                            binding, "entrySetViewOrderAuthority"))
                    && "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                    .concat("EXACT_OUTPUT_IDENTITY").equals(string(selector,
                            "replaySelectionAuthority"))
                    && !scope.isEmpty()
                    && scope.equals(string(selector, "objectTokenScope"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(binding, "objectTokenAuthority"))
                    && "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN".equals(
                    string(selector, "objectTokenAuthority"))
                    && "NONE".equals(string(selector,
                    "crossExecutionOrdinalAuthority"))
                    && "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                    .concat("EXACT_OUTPUT_IDENTITY")
                    .equals(string(selector, "authority"))
                    && bool(selector, "outputIdentityVerified", false)
                    && outputAuthorityValid;
        }

        private static JsonObject normalizedMapProjectionSelector(
                JsonObject binding) {
            JsonObject source = object(binding,
                    "mapProjectionSelector");
            JsonObject result = new JsonObject();
            for (String member : new String[]{"kind", "bindingId",
                    "mapInputPort", "mapInputCell", "outputPort",
                    "outputCell", "mapProjectionOperation", "outputIndex",
                    "elementOccurrence", "declaredFieldOwnerClass",
                    "declaredFieldType", "declaredFieldSignature",
                    "mapObjectToken", "elementObjectToken",
                    "outputArrayObjectToken", "outputIdentityVerified",
                    "outputVerificationAuthority", "objectTokenAuthority",
                    "objectTokenScope", "crossExecutionOrdinalAuthority",
                    "expectedMapKey", "expectedMapKeyAuthority",
                    "sourceOutputIndexAuthority",
                    "replaySelectionAuthority",
                    "authority", "complete"}) {
                copyMember(source, result, member);
            }
            return result;
        }

        private static long jsonLong(JsonElement element, long fallback) {
            try {
                return element == null || element.isJsonNull()
                        ? fallback : element.getAsLong();
            } catch (RuntimeException malformed) {
                return fallback;
            }
        }

        private static void requireEqualIfPresent(JsonObject assignment,
                                                  JsonObject binding,
                                                  String member)
                throws IOException {
            if (assignment.has(member)
                    && !assignment.get(member).equals(binding.get(member))) {
                throw projectionGap("CROSS_BINDING_SELECTOR:" + member);
            }
        }

        private static JsonObject uniqueAction(JsonObject activation,
                                               String base) {
            JsonObject result = null;
            for (JsonElement element : actionArray(activation)) {
                if (!element.isJsonObject()
                        || !base.equals(string(element.getAsJsonObject(),
                        "symbol"))) continue;
                if (result != null) return null;
                result = element.getAsJsonObject();
            }
            return result;
        }

        private static IOException projectionGap(String reason) {
            return new IOException("DYNAMIC_BINDING_PROJECTION_GAP: "
                    + reason);
        }
    }

    private static boolean exactEngineSymbol(String engine, String symbol) {
        if (engine == null || symbol == null || symbol.isEmpty()) {
            return false;
        }
        if (engine.equals(symbol)) return true;
        if (engine.length() <= 10 || engine.charAt(0) != 'M'
                || engine.charAt(1) != '_'
                || "ZCBSIFJDL".indexOf(engine.charAt(2)) < 0
                || !engine.startsWith("_field_", 3)) {
            return false;
        }
        String payload = engine.substring(10);
        if (payload.equals(symbol)) return true;
        String boundary = symbol + "_";
        return payload.startsWith(boundary)
                && legalVmOwnerSuffix(payload.substring(boundary.length()));
    }

    private static boolean legalVmOwnerSuffix(String suffix) {
        return suffix != null && suffix.matches(
                "[A-Za-z_$][A-Za-z0-9_$]*"
                        + "(?:/[A-Za-z_$][A-Za-z0-9_$]*)*");
    }

    static List<String> materializabilityRefinements(
            JsonObject selectedCase, CaseProjectionRegistry registry,
            String targetKey, List<String> keys, List<String> values,
            List<String> concreteDynamicEntryKeys) throws IOException {
        return materializabilityRefinements(selectedCase, registry,
                targetKey, keys, values, concreteDynamicEntryKeys, "");
    }

    private static List<String> materializabilityRefinements(
            JsonObject selectedCase, CaseProjectionRegistry registry,
            String targetKey, List<String> keys, List<String> values,
            List<String> concreteDynamicEntryKeys, String nameScope)
            throws IOException {
        List<String> result = new ArrayList<>();
        String prefix = firstNonBlank(nameScope).isEmpty()
                ? "replay" : "replay_" + smtName(nameScope);
        String selectedSelector = string(selectedCase,
                "selectorSolverSymbol");
        if (selectedSelector.isEmpty()) {
            throw projectionGap("MISSING_SELECTED_CASE_SELECTOR");
        }
        result.add("(assert (! " + selectedSelector
                + " :named " + prefix + "_selected_case_selector))");
        for (String selector : registry.selectorTerms()) {
            if (selector.equals(selectedSelector)) continue;
            result.add("(assert (! (not " + selector + ") :named " + prefix
                    + "_"
                    + "unselected_case_" + smtName(selector) + "))");
        }
        List<String> nonNull = new ArrayList<>();
        for (String value : values) {
            nonNull.add("(not (= " + value + " nullRef))");
        }
        result.add("(assert (! " + and(nonNull)
                + " :named " + prefix
                + "_materializable_non_null_values))");
        if (values.size() > 1) {
            StringBuilder distinct = new StringBuilder("(distinct");
            for (String value : values) distinct.append(' ').append(value);
            result.add("(assert (! " + distinct.append(')')
                    + " :named " + prefix
                    + "_materializable_distinct_array_values))");
        }
        List<String> intRange = new ArrayList<>();
        intRange.add(intRange(targetKey));
        for (String key : keys) intRange.add(intRange(key));
        result.add("(assert (! " + and(intRange)
                + " :named " + prefix
                + "_materializable_java_int_range))");
        if (!concreteDynamicEntryKeys.isEmpty()) {
            List<String> targetMatchesDynamic = new ArrayList<>();
            for (String key : concreteDynamicEntryKeys) {
                targetMatchesDynamic.add("(= " + targetKey + " " + key
                        + ")");
            }
            result.add("(assert (! " + or(targetMatchesDynamic)
                    + " :named " + prefix
                    + "_target_lookup_key_is_selected_dynamic_"
                    + "entry_key))");
        }
        List<String> absent = new ArrayList<>();
        for (String key : keys) {
            absent.add("(not (= " + targetKey + " " + key + "))");
        }
        result.add("(assert (! " + and(absent)
                + " :named " + prefix
                + "_materializable_target_key_absent))");
        return result;
    }

    private static List<String> lookupKeyMaterializabilityRefinements(
            JsonObject selectedCase, CaseProjectionRegistry registry,
            String targetKey, List<String> keys, List<String> values,
            String lookupKeyProducerTerm, String nameScope)
            throws IOException {
        if (lookupKeyProducerTerm.isEmpty()
                || !keys.contains(lookupKeyProducerTerm)) {
            throw projectionGap("LOOKUP_KEY_PRODUCER_TERM_NOT_MATERIALIZED:"
                    + lookupKeyProducerTerm);
        }
        List<String> result = new ArrayList<>();
        String prefix = "replay_" + smtName(nameScope);
        String selectedSelector = string(selectedCase,
                "selectorSolverSymbol");
        if (selectedSelector.isEmpty()) {
            throw projectionGap("MISSING_SELECTED_CASE_SELECTOR");
        }
        result.add("(assert (! " + selectedSelector + " :named " + prefix
                + "_selected_case_selector))");
        for (String selector : registry.selectorTerms()) {
            if (selector.equals(selectedSelector)) continue;
            result.add("(assert (! (not " + selector + ") :named " + prefix
                    + "_unselected_case_" + smtName(selector) + "))");
        }
        List<String> nonNull = new ArrayList<>();
        for (String value : values) {
            nonNull.add("(not (= " + value + " nullRef))");
        }
        result.add("(assert (! " + and(nonNull) + " :named " + prefix
                + "_materializable_non_null_values))");
        if (values.size() > 1) {
            StringBuilder distinct = new StringBuilder("(distinct");
            for (String value : values) distinct.append(' ').append(value);
            result.add("(assert (! " + distinct.append(')') + " :named "
                    + prefix + "_materializable_distinct_array_values))");
        }
        List<String> ranges = new ArrayList<>();
        ranges.add(intRange(targetKey));
        for (String key : keys) ranges.add(intRange(key));
        result.add("(assert (! " + and(ranges) + " :named " + prefix
                + "_materializable_java_int_range))");
        result.add("(assert (! (= " + targetKey + " "
                + lookupKeyProducerTerm + ") :named " + prefix
                + "_runtime_confirmed_lookup_key_producer_equality))");
        return result;
    }

    private static String intRange(String symbol) {
        return "(and (>= " + symbol + " (- 2147483648)) (<= "
                + symbol + " 2147483647))";
    }

    static JsonObject preMapProducerEvidence(JsonObject summary,
                                             JsonObject activation,
                                             String preMapInput)
            throws IOException {
        Map<String, JsonObject> candidates = new LinkedHashMap<>();
        collectPreMapProducerEvidence(summary, preMapInput, candidates);
        collectPreMapProducerEvidence(activation, preMapInput, candidates);
        List<JsonObject> valid = new ArrayList<>();
        for (JsonObject candidate : candidates.values()) {
            String sourceSummary = string(candidate, "sourceSummaryId");
            String consumerActivation = firstNonBlank(string(candidate,
                    "consumerActivationId"), string(candidate,
                    "activationId"));
            String input = firstNonBlank(string(candidate, "inputPort"),
                    string(candidate, "preMapInput"), string(candidate,
                    "consumerStatePort"));
            String producerState = firstNonBlank(string(candidate,
                    "producerStatePort"), string(candidate,
                    "sourceStatePort"));
            boolean structurallyValid = integer(candidate,
                    "schemaVersion", -1) == 1
                    && "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                    .concat("RELATION").equals(string(candidate, "kind"))
                    && "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                    .concat("RELATION").equals(string(candidate,
                            "authority"))
                    && bool(candidate, "complete", false)
                    && bool(candidate, "runtimeConfirmed", false)
                    && bool(candidate, "existingStateObserved", false)
                    && preMapInput.equals(input)
                    && !producerState.isEmpty()
                    && !string(candidate,
                    "producerRegionInstanceId").isEmpty()
                    && !sourceSummary.isEmpty()
                    && sourceSummary.equals(string(summary, "summaryId"))
                    && !consumerActivation.isEmpty()
                    && (consumerActivation.equals(string(activation,
                    "activationId")) || consumerActivation.equals(string(
                    summary, "activationId")));
            if (structurallyValid) valid.add(candidate);
        }
        if (valid.isEmpty()) {
            Map<String, JsonObject> edgeDerived = new LinkedHashMap<>();
            collectPreMapEdgeBindingEvidence(summary, summary, activation,
                    preMapInput, edgeDerived);
            collectPreMapEdgeBindingEvidence(activation, summary, activation,
                    preMapInput, edgeDerived);
            valid.addAll(edgeDerived.values());
        }
        if (valid.size() != 1) {
            throw new IOException("PRE_MAP_PRODUCER_PROJECTION_GAP: expected "
                    + "one runtime-confirmed existing producer/state relation "
                    + "for " + preMapInput + ", found " + valid.size());
        }
        return valid.get(0).deepCopy();
    }

    /**
     * Production summaries already carry the exact runtime read-from witness
     * in edgeBindings.  Older fixtures used a projector-only
     * preMapProducerRelations member, so consume that member when present but
     * derive the same fail-closed evidence from the production shape when it
     * is absent.
     */
    private static void collectPreMapEdgeBindingEvidence(
            JsonObject source, JsonObject summary, JsonObject activation,
            String preMapInput, Map<String, JsonObject> candidates) {
        String consumerRegion = string(summary, "regionId");
        String consumerInstance = firstNonBlank(string(summary,
                "regionInstanceId"), string(activation,
                "regionInstanceId"));
        for (JsonElement element : array(source, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject edge = element.getAsJsonObject();
            String relation = firstNonBlank(string(edge, "relation"),
                    string(edge, "validatedRelation"));
            String writerSeqName = edge.has("writerEventSeq")
                    ? "writerEventSeq" : edge.has("writeSeq")
                    ? "writeSeq" : "";
            String readerSeqName = edge.has("readerEventSeq")
                    ? "readerEventSeq" : edge.has("readSeq")
                    ? "readSeq" : "";
            String producerPort = string(edge, "fromOutputPort");
            boolean exact = "READ_FROM".equals(relation)
                    && AutomaticRegionEdge
                    .trustedRuntimeReadFromBinding(edge)
                    && preMapInput.equals(string(edge, "toInputPort"))
                    && !consumerRegion.isEmpty()
                    && consumerRegion.equals(string(edge, "toRegion"))
                    && !consumerInstance.isEmpty()
                    && consumerInstance.equals(string(edge,
                    "toRegionInstance"))
                    && !string(edge, "fromRegion").isEmpty()
                    && !string(edge, "fromRegionInstance").isEmpty()
                    && !producerPort.isEmpty()
                    && !writerSeqName.isEmpty()
                    && !readerSeqName.isEmpty()
                    && edge.has("receiverObjectId")
                    && !edge.get("receiverObjectId").isJsonNull()
                    && bool(edge, "orderConfirmed", false)
                    && bool(edge, "objectIdentityConfirmed", false);
            if (!exact) continue;

            JsonObject evidence = new JsonObject();
            evidence.addProperty("schemaVersion", 1);
            evidence.addProperty("kind",
                    "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                            + "RELATION");
            evidence.addProperty("authority",
                    "RUNTIME_CONFIRMED_EXISTING_PRE_MAP_PRODUCER_STATE_"
                            + "RELATION");
            evidence.addProperty("derivationAuthority",
                    "EXACT_RUNTIME_EDGE_BINDING_READ_FROM_WITNESS");
            evidence.addProperty("complete", true);
            evidence.addProperty("runtimeConfirmed", true);
            evidence.addProperty("existingStateObserved", true);
            evidence.addProperty("inputPort", preMapInput);
            evidence.addProperty("producerStatePort", producerPort);
            evidence.addProperty("producerRegion",
                    string(edge, "fromRegion"));
            evidence.addProperty("producerRegionInstanceId",
                    string(edge, "fromRegionInstance"));
            evidence.addProperty("consumerRegion", consumerRegion);
            evidence.addProperty("consumerRegionInstanceId",
                    consumerInstance);
            evidence.addProperty("sourceSummaryId",
                    string(summary, "summaryId"));
            evidence.addProperty("consumerActivationId", firstNonBlank(
                    string(activation, "activationId"),
                    string(summary, "activationId")));
            evidence.addProperty("edgeId", string(edge, "edgeId"));
            evidence.addProperty("relation", "READ_FROM");
            evidence.addProperty("selectionAuthority",
                    "RUNTIME_CONFIRMED_READ_FROM");
            evidence.add("writerEventSeq",
                    edge.get(writerSeqName).deepCopy());
            evidence.add("readerEventSeq",
                    edge.get(readerSeqName).deepCopy());
            evidence.add("receiverObjectId",
                    edge.get("receiverObjectId").deepCopy());
            evidence.addProperty("orderConfirmed", true);
            evidence.addProperty("objectIdentityConfirmed", true);
            candidates.put(GSON.toJson(evidence), evidence);
        }
    }

    private static void collectPreMapProducerEvidence(JsonObject source,
                                                      String preMapInput,
                                                      Map<String, JsonObject>
                                                              candidates) {
        for (String member : new String[]{"preMapProducerRelations",
                "runtimePreMapProducerRelations"}) {
            for (JsonElement element : array(source, member)) {
                if (!element.isJsonObject()) continue;
                JsonObject candidate = element.getAsJsonObject();
                String input = firstNonBlank(string(candidate, "inputPort"),
                        string(candidate, "preMapInput"), string(candidate,
                        "consumerStatePort"));
                if (!preMapInput.equals(input)) continue;
                candidates.put(GSON.toJson(candidate), candidate);
            }
        }
    }

    private static boolean hasHeapEffect(JsonObject summary, String kind) {
        for (JsonElement element : array(summary, "heapEffects")) {
            if (element.isJsonObject() && kind.equals(string(
                    element.getAsJsonObject(), "kind"))) return true;
        }
        return false;
    }

    static String actualTargetLookupTerm(String smt, String targetInput)
            throws IOException {
        String receiver = portName(targetInput);
        Pattern pattern = Pattern.compile("\\(map_(?:has|select)\\s+"
                + Pattern.quote(receiver)
                + "\\s+\\(VInt\\s+([^\\s()]+)\\)\\)");
        Matcher matcher = pattern.matcher(firstNonBlank(smt));
        Set<String> terms = new LinkedHashSet<>();
        while (matcher.find()) terms.add(matcher.group(1));
        if (terms.size() != 1) {
            throw projectionGap("EXPECTED_ONE_ACTUAL_TARGET_LOOKUP_TERM_FOR:"
                    + targetInput + ":found=" + terms);
        }
        return terms.iterator().next();
    }

    private static void validateUniqueMaterializations(JsonArray assignments,
                                                       List<String> terms)
            throws IOException {
        Set<String> controlled = new LinkedHashSet<>();
        for (String term : terms) {
            if (!controlled.add(term)) {
                throw projectionGap("CONTROLLED_SOLVER_TERM_NOT_UNIQUE:"
                        + term);
            }
        }
        Map<String, Integer> assignmentsByTerm = new LinkedHashMap<>();
        Set<String> materializationTargets = new LinkedHashSet<>();
        for (JsonElement element : assignments) {
            if (!element.isJsonObject()) continue;
            JsonObject assignment = element.getAsJsonObject();
            if ("MAP_CLEAR".equals(string(assignment, "modelOperation"))) {
                throw projectionGap("MAP_CLEAR_PROHIBITED_FOR_SELECTED_CASE");
            }
            String solver = string(assignment, "solverSymbol");
            if (!controlled.contains(solver)) continue;
            Integer count = assignmentsByTerm.get(solver);
            assignmentsByTerm.put(solver, count == null ? 1 : count + 1);
            String locator = string(assignment, "inputSymbol") + "\u0000"
                    + GSON.toJson(array(assignment, "materializationPath"))
                    + "\u0000" + (assignment.has("expectedEntryKey")
                    ? GSON.toJson(assignment.get("expectedEntryKey")) : "")
                    + "\u0000" + (assignment.has("containerSelector")
                    ? GSON.toJson(assignment.get("containerSelector")) : "");
            if (!materializationTargets.add(locator)) {
                throw projectionGap("CONTROLLED_MATERIALIZATION_TARGET_NOT_"
                        + "UNIQUE:" + locator);
            }
            if (!bool(assignment, "materializeAtRealDefinition", false)) {
                throw projectionGap("CONTROLLED_TERM_NOT_MATERIALIZED_AT_"
                        + "REAL_DEFINITION:" + solver);
            }
        }
        for (String term : controlled) {
            if (assignmentsByTerm.get(term) == null
                    || assignmentsByTerm.get(term) != 1) {
                throw projectionGap("CONTROLLED_TERM_MATERIALIZATION_COUNT:"
                        + term + ":" + assignmentsByTerm.get(term));
            }
        }
    }

    private static void requireSuccessfulSolver(SolverOutput solver,
                                                String phase)
            throws IOException {
        if (solver.timedOut) {
            throw new IOException("Z3 timed out during " + phase);
        }
        String logicalStatus = firstLine(solver.stdout);
        boolean terminalLogicalStatus = "unsat".equals(logicalStatus)
                || "unknown".equals(logicalStatus);
        if (solver.exitCode != 0 && !terminalLogicalStatus) {
            throw new IOException("Z3 " + phase + " failed (exit "
                    + solver.exitCode + "): " + solver.stderr.trim());
        }
    }

    private static IOException projectionGap(String reason) {
        return new IOException("MODEL_PROJECTION_GAP: " + reason);
    }

    private static String solverInput(String base, List<String> refinements,
                                      List<String> queried) {
        StringBuilder result = new StringBuilder();
        for (String line : firstNonBlank(base).split("\\r?\\n")) {
            String trimmed = line.trim();
            if (trimmed.startsWith("(check-sat")
                    || trimmed.startsWith("(get-value")
                    || trimmed.startsWith("(get-model")
                    || trimmed.startsWith("(exit")) continue;
            result.append(line).append('\n');
        }
        for (String refinement : refinements) {
            result.append(refinement).append('\n');
        }
        result.append("(check-sat)\n(get-value (");
        for (int index = 0; index < queried.size(); index++) {
            if (index > 0) result.append(' ');
            result.append(queried.get(index));
        }
        return result.append("))\n").toString();
    }

    private static TargetMapBinding targetMapInput(JsonObject summary,
                                                   JsonObject fatalQuery,
                                                   JsonObject targetActivation)
            throws IOException {
        String targetInstance = string(fatalQuery, "regionInstanceId");
        Set<String> receiverPorts = new LinkedHashSet<>();
        collectLookupReceiverPorts(fatalQuery.get("constraints"),
                receiverPorts);
        if (receiverPorts.size() != 1) {
            throw projectionGap("EXPECTED_ONE_FATAL_HASHMAP_GET_RECEIVER_"
                    + "PORT:found=" + receiverPorts);
        }
        String receiverPort = receiverPorts.iterator().next();
        Set<String> declaredCells = new LinkedHashSet<>();
        for (JsonElement element : actionArray(targetActivation)) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            if (!receiverPort.equals(string(action, "symbol"))) continue;
            String cell = string(action, "cell");
            Matcher declared = DECLARED_FIELD.matcher(cell);
            if (!declared.matches()
                    || !"java.util.Map".equals(declared.group(2).trim())) {
                continue;
            }
            String exact = "<" + declared.group(1) + ": java.util.Map "
                    + declared.group(3) + ">";
            if (exact.equals(cell)) declaredCells.add(cell);
        }
        if (declaredCells.size() != 1) {
            throw projectionGap("EXPECTED_ONE_TARGET_ACTIVATION_DECLARED_MAP_"
                    + "CELL:receiver=" + receiverPort + ":found="
                    + declaredCells);
        }
        String targetCell = declaredCells.iterator().next();
        List<JsonObject> exact = new ArrayList<>();
        for (JsonElement element : array(summary, "edgeBindings")) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            if (!targetInstance.isEmpty()
                    && !targetInstance.equals(firstNonBlank(
                    string(binding, "toRegionInstance"),
                    string(binding, "consumerRegionInstance")))) continue;
            String input = firstNonBlank(string(binding, "toInputPort"),
                    string(binding, "consumerInputPort"));
            String cell = firstNonBlank(string(binding, "toInputCell"),
                    string(binding, "consumerInputCell"));
            if (receiverPort.equals(input)
                    && targetCell.equals(cell)) {
                exact.add(binding);
            }
        }
        if (exact.size() != 1) {
            throw projectionGap("EXPECTED_ONE_EXACT_TARGET_ALL_KEYS_EDGE_"
                    + "BINDING:receiver=" + receiverPort + ":cell="
                    + targetCell + ":found=" + exact.size());
        }
        return new TargetMapBinding(receiverPort, targetCell);
    }

    private static void collectLookupReceiverPorts(JsonElement element,
                                                   Set<String> result) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectLookupReceiverPorts(child, result);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        if ("MethodExpression".equals(string(object, "_type"))
                && string(object, "_name").endsWith("HashMap get")) {
            JsonArray parameters = array(object, "_param_list");
            if (parameters.size() >= 1) {
                Matcher matcher = REGION_INPUT_PORT.matcher(
                        expressionSymbol(parameters.get(0)));
                Set<String> current = new LinkedHashSet<>();
                while (matcher.find()) current.add(matcher.group());
                result.addAll(current);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectLookupReceiverPorts(entry.getValue(), result);
        }
    }

    private static String targetLookupKey(JsonObject fatalQuery,
                                          String targetInput)
            throws IOException {
        Set<String> keys = new LinkedHashSet<>();
        collectLookupKeys(fatalQuery.get("constraints"), targetInput, keys);
        if (keys.size() != 1) {
            throw new IOException("Expected one target lookup key for "
                    + targetInput + ", found " + keys);
        }
        return keys.iterator().next();
    }

    private static void collectLookupKeys(JsonElement element,
                                          String targetInput,
                                          Set<String> keys) {
        if (element == null || element.isJsonNull()) return;
        if (element.isJsonArray()) {
            for (JsonElement child : element.getAsJsonArray()) {
                collectLookupKeys(child, targetInput, keys);
            }
            return;
        }
        if (!element.isJsonObject()) return;
        JsonObject object = element.getAsJsonObject();
        if ("MethodExpression".equals(string(object, "_type"))
                && string(object, "_name").endsWith("HashMap get")) {
            JsonArray parameters = array(object, "_param_list");
            if (parameters.size() >= 2
                    && expressionSymbol(parameters.get(0)).contains(
                    targetInput)) {
                String key = expressionSymbol(parameters.get(1));
                if (!key.isEmpty()) keys.add(key);
            }
        }
        for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
            collectLookupKeys(entry.getValue(), targetInput, keys);
        }
    }

    private static JsonObject selectUpstreamSummary(List<JsonObject> rows,
                                                    String region,
                                                    String sourceSummaryId)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))
                    || !sourceSummaryId.equals(string(row, "summaryId"))
                    || !bool(row, "valid", false)
                    || !bool(row, "relationallyComplete", false)
                    || array(row, "heapEffects").size() == 0) continue;
            if (selected != null) {
                throw new IOException("More than one complete raw upstream "
                        + "summary matches selected case " + sourceSummaryId);
            }
            selected = row;
        }
        if (selected == null) {
            throw new IOException("No complete raw upstream summary "
                    + sourceSummaryId + " matches selected case in " + region);
        }
        return selected;
    }

    private static JsonObject selectUpstreamActivation(List<JsonObject> rows,
                                                       JsonObject summary,
                                                       String region)
            throws IOException {
        JsonObject selected = null;
        String activation = string(summary, "activationId");
        String instance = string(summary, "regionInstanceId");
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))) continue;
            boolean exactActivation = activation.equals(string(row,
                    "activationId"));
            boolean exactInstance = !instance.isEmpty()
                    && instance.equals(string(row, "regionInstanceId"));
            if (!exactActivation && !exactInstance) continue;
            if (selected != null) {
                throw new IOException("Ambiguous upstream activation for "
                        + region);
            }
            selected = row;
        }
        if (selected == null) {
            throw new IOException("No upstream activation matches summary "
                    + string(summary, "summaryId"));
        }
        return selected;
    }

    private static JsonObject selectTargetActivation(List<JsonObject> rows,
                                                     String activation,
                                                     String region)
            throws IOException {
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))) continue;
            if (!activation.isEmpty()
                    && !activation.equals(string(row, "activationId"))) {
                continue;
            }
            if (selected != null) {
                throw new IOException("Ambiguous target activation for "
                        + region);
            }
            selected = row;
        }
        if (selected == null) {
            throw new IOException("No target activation matches " + region
                    + "/" + activation);
        }
        return selected;
    }

    private static JsonObject selectFatalQuery(List<JsonObject> rows,
                                               JsonObject activation,
                                               String region)
            throws IOException {
        String sourceActivation = string(activation, "activationId");
        String instance = string(activation, "regionInstanceId");
        JsonObject selected = null;
        for (JsonObject row : rows) {
            if (!region.equals(string(row, "regionId"))
                    || !sourceActivation.equals(string(row,
                    "activationId"))
                    || !instance.equals(string(row, "regionInstanceId"))
                    || !bool(row, "readyForSolver", false)) continue;
            if (selected != null) {
                throw new IOException("Ambiguous ready fatal query for "
                        + instance);
            }
            selected = row;
        }
        if (selected == null) {
            throw new IOException("No ready fatal query matches target "
                    + sourceActivation + "/" + instance);
        }
        return selected;
    }

    private static JsonObject action(JsonObject activation, String symbol) {
        for (JsonElement element : actionArray(activation)) {
            if (element.isJsonObject()
                    && symbol.equals(string(element.getAsJsonObject(),
                    "symbol"))) return element.getAsJsonObject();
        }
        return new JsonObject();
    }

    private static JsonArray actionArray(JsonObject activation) {
        JsonArray materializations = array(activation, "materializations");
        return materializations.size() > 0 ? materializations
                : array(activation, "symbolize");
    }

    private static List<String> actionFieldPath(JsonObject action) {
        List<String> result = strings(array(action, "fieldPath"));
        if (!result.isEmpty()) return result;
        String cell = string(action, "cell");
        Matcher declared = DECLARED_FIELD.matcher(cell);
        if (declared.matches()) result.add(declared.group(3).trim());
        Matcher projection = FIELD_PROJECTION.matcher(cell);
        while (projection.find()) result.add(projection.group(1).trim());
        return result;
    }

    private static List<String> projectedFields(String path) {
        List<String> result = new ArrayList<>();
        Matcher matcher = FIELD_PROJECTION.matcher(firstNonBlank(path));
        while (matcher.find()) result.add(matcher.group(1).trim());
        return result;
    }

    private static Integer constantInteger(String raw) {
        String value = firstNonBlank(raw);
        int first = value.indexOf('_');
        int second = first < 0 ? -1 : value.indexOf('_', first + 1);
        value = second < 0 ? value : value.substring(second + 1);
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static boolean exactImmutableMapKeyExpression(
            JsonElement element) {
        if (element == null || !element.isJsonObject()) return false;
        JsonObject expression = element.getAsJsonObject();
        if (!"ConstExpr".equals(string(expression, "_type"))) return false;
        String raw = string(expression, "_exp");
        if (!raw.startsWith("Y_") || raw.length() < 4
                || raw.charAt(3) != '_') return false;
        char kind = raw.charAt(2);
        String type = string(expression, "_java_type").replace('.', '/');
        boolean typeMatches = kind == 'Z'
                && "java/lang/Boolean".equals(type)
                || kind == 'B' && "java/lang/Byte".equals(type)
                || kind == 'C' && "java/lang/Character".equals(type)
                || kind == 'S' && "java/lang/Short".equals(type)
                || kind == 'I' && "java/lang/Integer".equals(type)
                || kind == 'J' && "java/lang/Long".equals(type)
                || kind == 'L' && "java/lang/String".equals(type);
        if (!typeMatches) return false;
        try {
            String value = raw.substring(4);
            if (kind == 'Z') return "0".equals(value)
                    || "1".equals(value);
            if (kind == 'B' || kind == 'C' || kind == 'S'
                    || kind == 'I' || kind == 'J') {
                java.math.BigInteger integer =
                        new java.math.BigInteger(value);
                if (!integer.toString().equals(value)) return false;
                if (kind == 'B') return integer.compareTo(
                        java.math.BigInteger.valueOf(Byte.MIN_VALUE)) >= 0
                        && integer.compareTo(java.math.BigInteger.valueOf(
                        Byte.MAX_VALUE)) <= 0;
                if (kind == 'C') return integer.signum() >= 0
                        && integer.compareTo(java.math.BigInteger.valueOf(
                        Character.MAX_VALUE)) <= 0;
                if (kind == 'S') return integer.compareTo(
                        java.math.BigInteger.valueOf(Short.MIN_VALUE)) >= 0
                        && integer.compareTo(java.math.BigInteger.valueOf(
                        Short.MAX_VALUE)) <= 0;
                if (kind == 'I') return integer.compareTo(
                        java.math.BigInteger.valueOf(Integer.MIN_VALUE)) >= 0
                        && integer.compareTo(java.math.BigInteger.valueOf(
                        Integer.MAX_VALUE)) <= 0;
                return integer.compareTo(java.math.BigInteger.valueOf(
                        Long.MIN_VALUE)) >= 0
                        && integer.compareTo(java.math.BigInteger.valueOf(
                        Long.MAX_VALUE)) <= 0;
            }
            return kind == 'L';
        } catch (RuntimeException malformed) {
            return false;
        }
    }

    private static String stableImmutableMapKeySelector(
            JsonElement element) {
        if (!exactImmutableMapKeyExpression(element)) return "";
        String raw = string(element.getAsJsonObject(), "_exp");
        String value = raw.substring(4);
        return raw.charAt(2) + ":" + value.length() + ":" + value;
    }

    private static String expressionSymbol(JsonElement expression) {
        return expression != null && expression.isJsonObject()
                ? string(expression.getAsJsonObject(), "_exp") : "";
    }

    private static String portName(String port) {
        return "port__" + smtName(port);
    }

    private static String smtName(String value) {
        String normalized = firstNonBlank(value, "anonymous")
                .replaceAll("[^A-Za-z0-9_]", "_");
        if (normalized.isEmpty()) normalized = "anonymous";
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "n_" + normalized;
        }
        return normalized;
    }

    private static String and(List<String> values) {
        if (values.isEmpty()) return "true";
        if (values.size() == 1) return values.get(0);
        StringBuilder result = new StringBuilder("(and");
        for (String value : values) result.append(' ').append(value);
        return result.append(')').toString();
    }

    private static String or(List<String> values) {
        if (values.isEmpty()) return "false";
        if (values.size() == 1) return values.get(0);
        StringBuilder result = new StringBuilder("(or");
        for (String value : values) result.append(' ').append(value);
        return result.append(')').toString();
    }

    private static SolverOutput run(Path executable, String input,
                                    long timeoutMillis)
            throws IOException, InterruptedException {
        Process process = new ProcessBuilder(executable.toString(), "-in",
                "-smt2").start();
        try (OutputStream stream = process.getOutputStream()) {
            stream.write(input.getBytes(StandardCharsets.UTF_8));
        }
        boolean finished = process.waitFor(Math.max(1L, timeoutMillis),
                TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            process.waitFor();
        }
        return new SolverOutput(finished ? process.exitValue() : -1,
                !finished, readAll(process.getInputStream()),
                readAll(process.getErrorStream()));
    }

    private static String readAll(InputStream stream) throws IOException {
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int read;
        while ((read = stream.read(buffer)) >= 0) {
            output.write(buffer, 0, read);
        }
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }

    private static Map<String, String> parseGetValues(
            String output, Set<String> requested) {
        Map<String, String> result = new LinkedHashMap<>();
        int newline = output.indexOf('\n');
        if (newline < 0) return result;
        for (SExpr root : SExpr.parseMany(output.substring(newline + 1))) {
            collectValuePairs(root, requested, result);
        }
        return result;
    }

    private static void collectValuePairs(SExpr expression,
                                          Set<String> requested,
                                          Map<String, String> result) {
        if (expression.children.size() == 2
                && expression.children.get(0).children.isEmpty()) {
            String name = expression.children.get(0).atom;
            if (requested.contains(name)) {
                result.put(name, expression.children.get(1).render());
                return;
            }
        }
        for (SExpr child : expression.children) {
            collectValuePairs(child, requested, result);
        }
    }

    private static String normalizeModelValue(String value) {
        return SmtModelValueCodec.normalizeScalar(value);
    }

    private static String firstLine(String value) {
        String normalized = firstNonBlank(value);
        int newline = normalized.indexOf('\n');
        return newline < 0 ? normalized : normalized.substring(0, newline)
                .trim();
    }

    private static String sha256(String value) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] bytes = digest.digest(firstNonBlank(value)
                    .getBytes(StandardCharsets.UTF_8));
            StringBuilder result = new StringBuilder();
            for (byte item : bytes) {
                result.append(String.format("%02x", item & 0xff));
            }
            return result.toString();
        } catch (NoSuchAlgorithmException impossible) {
            throw new IllegalStateException(impossible);
        }
    }

    private static void require(Path path, String label) throws IOException {
        if (path == null || !Files.isRegularFile(path)) {
            throw new IOException(label + " not found: " + path);
        }
    }

    private static JsonObject readJson(Path path) throws IOException {
        JsonElement parsed = new JsonParser().parse(new String(
                Files.readAllBytes(path), StandardCharsets.UTF_8));
        if (!parsed.isJsonObject()) {
            throw new IOException("Expected JSON object in " + path);
        }
        return parsed.getAsJsonObject();
    }

    private static List<JsonObject> readJsonl(Path path) throws IOException {
        List<JsonObject> result = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                JsonElement parsed = new JsonParser().parse(line);
                if (parsed.isJsonObject()) result.add(parsed.getAsJsonObject());
            }
        }
        return result;
    }

    private static void writeJsonl(Path path, List<JsonObject> rows)
            throws IOException {
        StringBuilder output = new StringBuilder();
        for (JsonObject row : rows) {
            output.append(GSON.toJson(row)).append(System.lineSeparator());
        }
        write(path, output.toString());
    }

    private static void write(Path path, String value) throws IOException {
        Path parent = path.toAbsolutePath().getParent();
        if (parent != null) Files.createDirectories(parent);
        Files.write(path, value.getBytes(StandardCharsets.UTF_8),
                StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING);
    }

    private static JsonArray array(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonArray()
                ? value.getAsJsonArray() : new JsonArray();
    }

    private static JsonObject object(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value != null && value.isJsonObject()
                ? value.getAsJsonObject() : new JsonObject();
    }

    private static String string(JsonObject object, String member) {
        JsonElement value = object == null ? null : object.get(member);
        return value == null || value.isJsonNull() ? "" : value.getAsString();
    }

    private static int integer(JsonObject object, String member,
                               int fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long longInteger(JsonObject object, String member,
                                    long fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsLong();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean bool(JsonObject object, String member,
                                boolean fallback) {
        try {
            JsonElement value = object == null ? null : object.get(member);
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static List<String> strings(JsonArray array) {
        List<String> result = new ArrayList<>();
        for (JsonElement element : array) {
            if (element.isJsonPrimitive()) result.add(element.getAsString());
        }
        return result;
    }

    private static String firstNonBlank(String... values) {
        if (values != null) {
            for (String value : values) {
                if (value != null && !value.trim().isEmpty()) {
                    return value.trim();
                }
            }
        }
        return "";
    }

    static JsonObject selectedCaseProjection(JsonObject composition,
                                             String region,
                                             Map<String, String> values)
            throws IOException {
        return CaseProjectionRegistry.from(composition, region).select(values);
    }

    static final class CaseProjectionRegistry {
        private final List<JsonObject> cases = new ArrayList<>();
        private final Map<String, JsonObject> bySelector =
                new LinkedHashMap<>();

        private static CaseProjectionRegistry from(JsonObject composition,
                                                   String region)
                throws IOException {
            if (!bool(composition, "caseProjectionCatalogComplete", false)) {
                throw projectionGap("CASE_PROJECTION_CATALOG_INCOMPLETE");
            }
            CaseProjectionRegistry result = new CaseProjectionRegistry();
            Set<String> caseIds = new LinkedHashSet<>();
            Set<String> sourceSummaries = new LinkedHashSet<>();
            for (JsonElement element : array(composition,
                    "caseProjectionCatalog")) {
                if (!element.isJsonObject()) {
                    throw projectionGap("NON_OBJECT_CASE_PROJECTION");
                }
                JsonObject pathCase = element.getAsJsonObject();
                if (!region.equals(string(pathCase, "regionId"))) continue;
                String caseId = string(pathCase, "caseId");
                String selector = string(pathCase,
                        "selectorSolverSymbol");
                String sourceSummary = string(pathCase, "sourceSummaryId");
                String sourceActivation = string(pathCase,
                        "sourceActivationId");
                JsonArray mappings = array(pathCase,
                        "rawEngineSymbolMappings");
                JsonArray dynamics = array(pathCase,
                        "dynamicFieldBindings");
                boolean valid = integer(pathCase, "schemaVersion", -1) == 1
                        && "GUARDED_CASE_PROJECTION_CATALOG".equals(string(
                        pathCase, "kind"))
                        && bool(pathCase, "complete", false)
                        && !caseId.isEmpty()
                        && !string(pathCase, "pathKey").isEmpty()
                        && !string(pathCase, "symbolScope").isEmpty()
                        && !selector.isEmpty()
                        && !string(pathCase,
                        "selectorGuardFormula").isEmpty()
                        && !sourceSummary.isEmpty()
                        && !sourceActivation.isEmpty()
                        && "DECLARED_BOOL_EQ_EXACT_CASE_GUARD".equals(string(
                        pathCase, "selectorAuthority"))
                        && "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE".equals(
                        string(pathCase, "rawEngineSymbolMappingAuthority"))
                        && integer(pathCase, "rawEngineSymbolMappingCount", -1)
                        == mappings.size()
                        && integer(pathCase, "dynamicFieldBindingCount", -1)
                        == dynamics.size();
                if (!valid) {
                    throw projectionGap("INCOMPLETE_CASE_PROJECTION:"
                            + caseId);
                }
                Set<String> raws = new LinkedHashSet<>();
                for (JsonElement mappingElement : mappings) {
                    if (!mappingElement.isJsonObject()) {
                        throw projectionGap("NON_OBJECT_CASE_TERM_MAPPING:"
                                + caseId);
                    }
                    JsonObject mapping = mappingElement.getAsJsonObject();
                    String raw = string(mapping, "rawEngineSymbol");
                    if (raw.isEmpty() || !raws.add(raw)
                            || string(mapping, "solverTerm").isEmpty()
                            || string(mapping, "solverSort").isEmpty()
                            || !"EMITTER_ACTUAL_TERM".equals(string(mapping,
                            "authority"))) {
                        throw projectionGap("INCOMPLETE_OR_DUPLICATE_CASE_"
                                + "TERM_MAPPING:" + caseId + ":" + raw);
                    }
                }
                for (JsonElement dynamicElement : dynamics) {
                    if (!dynamicElement.isJsonObject()) {
                        throw projectionGap(
                                "NON_OBJECT_CASE_DYNAMIC_BINDING:" + caseId);
                    }
                    JsonObject binding = dynamicElement.getAsJsonObject();
                    if ((isMapProjectionBinding(binding)
                            || "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING"
                            .equals(string(binding, "kind")))
                            && (!sourceActivation.equals(string(binding,
                            "objectTokenScope"))
                            || !sourceActivation.equals(string(object(binding,
                            isMapProjectionBinding(binding)
                                    ? "mapProjectionSelector"
                                    : "containerSelector"),
                            "objectTokenScope")))) {
                        throw projectionGap(
                                "CASE_DYNAMIC_SCOPE_SOURCE_ACTIVATION_"
                                        + "MISMATCH:" + string(binding,
                                        "dynamicBindingId"));
                    }
                    if (!isMapProjectionBinding(binding)) continue;
                    if (!DynamicProjectionRegistry
                            .completeMapProjectionSelector(binding)
                            || !"EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_"
                            .concat("PC_EXPRESSION").equals(string(binding,
                                    "observationBindingAuthority"))
                            || !"EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_"
                            .concat("PC_EXPRESSION").equals(
                            string(binding, "termBindingAuthority"))
                            || string(binding, "solverTerm").isEmpty()
                            || string(binding,
                            "fieldExpressionRawEngineSymbol").isEmpty()
                            || !string(binding,
                            "fieldExpressionRawEngineSymbol").equals(string(
                                    binding, "dynamicFieldSymbol"))) {
                        throw projectionGap(
                                "INCOMPLETE_CASE_MAP_PROJECTION_SELECTOR:"
                                        + string(binding,
                                        "dynamicBindingId"));
                    }
                }
                if (!caseIds.add(caseId)
                        || result.bySelector.put(selector,
                        pathCase.deepCopy()) != null
                        || !sourceSummaries.add(sourceSummary)) {
                    throw projectionGap("DUPLICATE_CASE_SELECTOR_OR_SOURCE:"
                            + caseId);
                }
                result.cases.add(pathCase.deepCopy());
            }
            if (result.cases.isEmpty()) {
                throw projectionGap("NO_CASE_PROJECTION_FOR_REGION:" + region);
            }
            return result;
        }

        private List<String> selectorTerms() {
            return new ArrayList<>(bySelector.keySet());
        }

        private JsonObject select(Map<String, String> values)
                throws IOException {
            JsonObject selected = null;
            for (Map.Entry<String, JsonObject> entry : bySelector.entrySet()) {
                if (!values.containsKey(entry.getKey())) {
                    throw projectionGap("MISSING_CASE_SELECTOR_MODEL_VALUE:"
                            + entry.getKey());
                }
                String value = normalizeModelValue(values.get(entry.getKey()));
                if (!("true".equals(value) || "false".equals(value))) {
                    throw projectionGap("NON_BOOLEAN_CASE_SELECTOR_MODEL_"
                            + "VALUE:" + entry.getKey() + "=" + value);
                }
                if (!"true".equals(value)) continue;
                if (selected != null) {
                    throw projectionGap("MORE_THAN_ONE_TRUE_CASE_SELECTOR:"
                            + string(selected, "selectorSolverSymbol") + ","
                            + entry.getKey());
                }
                selected = entry.getValue();
            }
            if (selected == null) {
                throw projectionGap("NO_TRUE_CASE_SELECTOR");
            }
            return selected.deepCopy();
        }
    }

    static final class Result {
        final List<JsonObject> activations;
        final JsonObject manifest;

        private Result(List<JsonObject> activations, JsonObject manifest) {
            this.activations = activations;
            this.manifest = manifest;
        }
    }

    static final class Arguments {
        private Path smt;
        private Path compositionManifest;
        private Path upstreamSummaries;
        private Path staticGraph;
        private Path upstreamActivations;
        private Path broadcastActivations;
        private Path producerGroups;
        private Path runtimeEdges;
        private Path targetActivations;
        private Path fatalQueries;
        private Path output;
        private Path manifest;
        private Path z3 = Paths.get("z3");
        private String upstreamRegion;
        private String targetActivationId;
        private int expectedBroadcastCandidates;
        private long timeoutMillis = 20000L;

        static Arguments parse(String[] argv) {
            Map<String, String> values = new LinkedHashMap<>();
            for (int index = 0; index < argv.length; index++) {
                String argument = argv[index];
                if (!argument.startsWith("--") || index + 1 >= argv.length) {
                    throw new IllegalArgumentException("Expected --key value, "
                            + "got " + argument);
                }
                values.put(argument.substring(2), argv[++index]);
            }
            Arguments result = new Arguments();
            result.smt = path(values, "smt", true);
            result.compositionManifest = path(values,
                    "composition-manifest", true);
            result.upstreamSummaries = path(values, "upstream-summaries",
                    true);
            result.staticGraph = path(values, "static-graph", true);
            result.producerGroups = path(values, "producer-groups", false);
            boolean singleGroup = result.producerGroups == null;
            result.runtimeEdges = path(values, "runtime-edges",
                    !singleGroup);
            result.upstreamActivations = path(values,
                    "upstream-activations", singleGroup);
            result.broadcastActivations = path(values,
                    "broadcast-activations", singleGroup);
            result.targetActivations = path(values, "target-activations",
                    true);
            result.fatalQueries = path(values, "fatal-query", true);
            result.output = path(values, "output", true);
            result.manifest = path(values, "manifest", true);
            if (values.containsKey("z3")) result.z3 = Paths.get(
                    values.get("z3"));
            result.upstreamRegion = firstNonBlank(values.get(
                    "upstream-region"));
            result.targetActivationId = firstNonBlank(values.get(
                    "target-activation-id"));
            String expected = firstNonBlank(values.get(
                    "expected-broadcast-candidates"));
            if (singleGroup && expected.isEmpty()) {
                throw new IllegalArgumentException(
                        "Missing --expected-broadcast-candidates");
            }
            if (!expected.isEmpty()) {
                result.expectedBroadcastCandidates = Integer.parseInt(
                        expected);
            }
            if (singleGroup && result.expectedBroadcastCandidates < 1) {
                throw new IllegalArgumentException(
                        "--expected-broadcast-candidates must be positive");
            }
            if (singleGroup && result.upstreamRegion.isEmpty()) {
                throw new IllegalArgumentException(
                        "Missing --upstream-region");
            }
            if (!singleGroup && (!result.upstreamRegion.isEmpty()
                    || result.upstreamActivations != null
                    || result.broadcastActivations != null
                    || !expected.isEmpty())) {
                throw new IllegalArgumentException("--producer-groups cannot "
                        + "be combined with single-group upstream options");
            }
            if (values.containsKey("timeout-ms")) {
                result.timeoutMillis = Long.parseLong(values.get(
                        "timeout-ms"));
            }
            return result;
        }

        private static Path path(Map<String, String> values, String key,
                                 boolean required) {
            String value = values.get(key);
            if ((value == null || value.trim().isEmpty()) && required) {
                throw new IllegalArgumentException("Missing --" + key);
            }
            return value == null || value.trim().isEmpty()
                    ? null : Paths.get(value);
        }
    }

    private static final class ProducerGroupSpec {
        private final String groupId;
        private final String upstreamRegion;
        private final Path upstreamActivations;
        private final Path broadcastActivations;
        private final int expectedBroadcastCandidates;
        private final String projectionRole;
        private final String projectionRoleAuthority;
        private final Map<String, JsonObject> witnessesByCase;

        private ProducerGroupSpec(String groupId, String upstreamRegion,
                                  Path upstreamActivations,
                                  Path broadcastActivations,
                                  int expectedBroadcastCandidates,
                                  String projectionRole,
                                  String projectionRoleAuthority,
                                  Map<String, JsonObject> witnessesByCase) {
            this.groupId = groupId;
            this.upstreamRegion = upstreamRegion;
            this.upstreamActivations = upstreamActivations;
            this.broadcastActivations = broadcastActivations;
            this.expectedBroadcastCandidates = expectedBroadcastCandidates;
            this.projectionRole = projectionRole;
            this.projectionRoleAuthority = projectionRoleAuthority;
            this.witnessesByCase = witnessesByCase;
        }

        private static List<ProducerGroupSpec> read(Path catalog,
                ConcolicProducerGroupPlanner.VerifiedCatalog verified)
                throws IOException {
            JsonElement parsed = new JsonParser().parse(new String(
                    Files.readAllBytes(catalog), StandardCharsets.UTF_8));
            if (!parsed.isJsonObject()) {
                throw projectionGap("PRODUCER_GROUP_CATALOG_NOT_OBJECT");
            }
            JsonObject root = parsed.getAsJsonObject();
            JsonArray rows = array(root, "producerGroups");
            if (integer(root, "schemaVersion", -1) != 2
                    || !ConcolicProducerGroupPlanner.CATALOG_KIND.equals(
                    string(root, "kind"))
                    || !bool(root, "complete", false)
                    || !bool(root, "roleSelectionIsDerived", false)
                    || rows.isEmpty()
                    || integer(root, "producerGroupCount", -1)
                    != rows.size()) {
                throw projectionGap("INCOMPLETE_PRODUCER_GROUP_CATALOG");
            }
            Path base = catalog.toAbsolutePath().getParent();
            List<ProducerGroupSpec> result = new ArrayList<>();
            for (int index = 0; index < rows.size(); index++) {
                JsonElement element = rows.get(index);
                if (!element.isJsonObject()) {
                    throw projectionGap("NON_OBJECT_PRODUCER_GROUP:" + index);
                }
                JsonObject row = element.getAsJsonObject();
                String region = string(row, "upstreamRegion");
                String id = firstNonBlank(string(row, "producerGroupId"),
                        "PRODUCER.GROUP." + region);
                String upstream = string(row, "upstreamActivations");
                String broadcast = string(row, "broadcastActivations");
                String role = string(row, "projectionRole");
                String authority = string(row,
                        "projectionRoleAuthority");
                int expected = integer(row,
                        "expectedBroadcastCandidates", -1);
                if (region.isEmpty() || upstream.isEmpty()
                        || broadcast.isEmpty() || expected < 1
                        || !bool(row, "projectionRoleDerived", false)
                        || !(TARGET_MAP_STATE.equals(role)
                        || LOOKUP_KEY_PRODUCER.equals(role))) {
                    throw projectionGap("INCOMPLETE_PRODUCER_GROUP:" + id);
                }
                String requiredAuthority = TARGET_MAP_STATE.equals(role)
                        ? ConcolicProducerGroupPlanner.TARGET_AUTHORITY
                        : ConcolicProducerGroupPlanner.LOOKUP_AUTHORITY;
                if (!requiredAuthority.equals(authority)) {
                    throw projectionGap("DERIVED_ROLE_AUTHORITY_MISMATCH:"
                            + id);
                }
                Map<String, JsonObject> byCase = new LinkedHashMap<>();
                JsonArray witnessIds = array(row, "witnessIds");
                if (witnessIds.isEmpty() || integer(row, "witnessCount", -1)
                        != witnessIds.size()) {
                    throw projectionGap("GROUP_WITNESS_SET_INCOMPLETE:" + id);
                }
                String requiredKind = TARGET_MAP_STATE.equals(role)
                        ? ConcolicProducerGroupPlanner.TARGET_WITNESS_KIND
                        : ConcolicProducerGroupPlanner.LOOKUP_WITNESS_KIND;
                for (JsonElement witnessIdElement : witnessIds) {
                    if (!witnessIdElement.isJsonPrimitive()) {
                        throw projectionGap("NON_STRING_GROUP_WITNESS:" + id);
                    }
                    String witnessId = witnessIdElement.getAsString();
                    JsonObject witness = verified.witnesses.get(witnessId);
                    String caseId = string(witness, "compositionCaseId");
                    if (witness == null || caseId.isEmpty()
                            || !requiredKind.equals(string(witness, "kind"))
                            || !region.equals(string(witness,
                            "producerRegion"))
                            || byCase.put(caseId, witness.deepCopy()) != null) {
                        throw projectionGap("GROUP_WITNESS_CASE_MISMATCH:"
                                + id + ":" + witnessId);
                    }
                }
                result.add(new ProducerGroupSpec(id, region,
                        resolveCatalogPath(base, upstream),
                        resolveCatalogPath(base, broadcast), expected, role,
                        authority, byCase));
            }
            return result;
        }

        private static Path resolveCatalogPath(Path base, String value) {
            Path path = Paths.get(value);
            return path.isAbsolute() ? path : base.resolve(path).normalize();
        }

        private JsonObject witnessForCase(String caseId) throws IOException {
            JsonObject witness = witnessesByCase.get(caseId);
            if (witness == null) {
                throw projectionGap("NO_VERIFIED_WITNESS_FOR_SELECTED_CASE:"
                        + groupId + ":" + caseId);
            }
            return witness.deepCopy();
        }
    }

    private static final class GroupProjection {
        private final ProducerGroupSpec spec;
        private final CaseProjectionRegistry registry;
        private JsonObject selectedCase;
        private String selectedSourceSummary;
        private JsonObject summary;
        private DynamicProjectionRegistry dynamicBindings;
        private JsonObject upstreamActivation;
        private List<JsonObject> broadcastCandidates;
        private List<EffectProjection> projections;
        private String preMapInput;
        private JsonObject preMapEvidence;
        private List<DynamicTermProjection> dynamicProjections;
        private final List<String> keyNames = new ArrayList<>();
        private final List<String> valueNames = new ArrayList<>();
        private final List<String> dynamicNames = new ArrayList<>();
        private final List<String> dynamicQueryNames = new ArrayList<>();
        private final List<String> dynamicKeys = new ArrayList<>();
        private DynamicTermProjection targetDynamic;
        private String lookupKeyProducerSolverTerm;
        private String lookupKeyProducerEffectId;
        private String lookupKeyProducerRawEngineSymbol;
        private JsonObject lookupKeyProducerWitness = new JsonObject();
        private final JsonArray assignments = new JsonArray();
        private List<String> controlledTerms = new ArrayList<>();
        private String producerSetId;
        private final List<JsonObject> upstreamReplays = new ArrayList<>();
        private JsonObject sourceReplay;

        private GroupProjection(ProducerGroupSpec spec,
                                CaseProjectionRegistry registry) {
            this.spec = spec;
            this.registry = registry;
        }
    }

    private static final class EffectProjection {
        private final String keyRaw;
        private final String keySolverTerm;
        private final String valueRaw;
        private final String valueSolverTerm;
        private final String arrayRaw;
        private final String arraySolverTerm;
        private final String preMapInput;
        private final String inputSymbol;
        private final JsonObject action;
        private final List<String> path;
        private final JsonObject evidence;

        private EffectProjection(String keyRaw, String keySolverTerm,
                                 String valueRaw, String valueSolverTerm,
                                 String arrayRaw, String arraySolverTerm,
                                 String preMapInput, String inputSymbol,
                                 JsonObject action, List<String> path,
                                 JsonObject evidence) {
            this.keyRaw = keyRaw;
            this.keySolverTerm = keySolverTerm;
            this.valueRaw = valueRaw;
            this.valueSolverTerm = valueSolverTerm;
            this.arrayRaw = arrayRaw;
            this.arraySolverTerm = arraySolverTerm;
            this.preMapInput = preMapInput;
            this.inputSymbol = inputSymbol;
            this.action = action;
            this.path = path;
            this.evidence = evidence;
        }
    }

    static final class DynamicTermProjection {
        private final JsonObject binding;
        private final String rawEngineSymbol;
        private final String solverTerm;
        private final String nullnessSolverTerm;
        private final String concreteEntryKey;
        private final JsonObject targetAction;

        DynamicTermProjection(JsonObject binding,
                              String rawEngineSymbol,
                              String solverTerm,
                              String nullnessSolverTerm,
                              String concreteEntryKey,
                              JsonObject targetAction) {
            this.binding = binding;
            this.rawEngineSymbol = rawEngineSymbol;
            this.solverTerm = solverTerm;
            this.nullnessSolverTerm = firstNonBlank(nullnessSolverTerm);
            this.concreteEntryKey = concreteEntryKey;
            this.targetAction = targetAction;
        }
    }

    private static final class TargetMapBinding {
        private final String inputPort;
        private final String inputCell;

        private TargetMapBinding(String inputPort, String inputCell) {
            this.inputPort = inputPort;
            this.inputCell = inputCell;
        }
    }

    private static final class ArrayLoad {
        private final String array;
        private final int index;

        private ArrayLoad(String array, int index) {
            this.array = array;
            this.index = index;
        }
    }

    private static final class StaticField {
        private final String edgeId;
        private final String rawPath;
        private final List<String> path;

        private StaticField(String edgeId, String rawPath,
                            List<String> path) {
            this.edgeId = edgeId;
            this.rawPath = rawPath;
            this.path = path;
        }
    }

    private static final class SolverOutput {
        private final int exitCode;
        private final boolean timedOut;
        private final String stdout;
        private final String stderr;

        private SolverOutput(int exitCode, boolean timedOut, String stdout,
                             String stderr) {
            this.exitCode = exitCode;
            this.timedOut = timedOut;
            this.stdout = stdout;
            this.stderr = stderr;
        }
    }

    private static final class SExpr {
        private final String atom;
        private final List<SExpr> children;

        private SExpr(String atom, List<SExpr> children) {
            this.atom = atom;
            this.children = children;
        }

        private String render() {
            if (children.isEmpty()) return atom;
            StringBuilder result = new StringBuilder("(");
            for (int index = 0; index < children.size(); index++) {
                if (index > 0) result.append(' ');
                result.append(children.get(index).render());
            }
            return result.append(')').toString();
        }

        private static List<SExpr> parseMany(String value) {
            Parser parser = new Parser(firstNonBlank(value));
            List<SExpr> result = new ArrayList<>();
            while (parser.hasNext()) result.add(parser.parse());
            return result;
        }

        private static final class Parser {
            private final String value;
            private int index;

            private Parser(String value) {
                this.value = value;
            }

            private boolean hasNext() {
                skip();
                return index < value.length();
            }

            private SExpr parse() {
                skip();
                if (index >= value.length()) {
                    return new SExpr("", Collections.<SExpr>emptyList());
                }
                if (value.charAt(index) != '(') {
                    return new SExpr(atom(), Collections.<SExpr>emptyList());
                }
                index++;
                List<SExpr> children = new ArrayList<>();
                while (true) {
                    skip();
                    if (index >= value.length()) break;
                    if (value.charAt(index) == ')') {
                        index++;
                        break;
                    }
                    children.add(parse());
                }
                return new SExpr("", children);
            }

            private String atom() {
                int start = index;
                boolean quoted = false;
                while (index < value.length()) {
                    char current = value.charAt(index);
                    if (current == '"') quoted = !quoted;
                    if (!quoted && (Character.isWhitespace(current)
                            || current == '(' || current == ')')) break;
                    index++;
                }
                return value.substring(start, index);
            }

            private void skip() {
                while (index < value.length()
                        && Character.isWhitespace(value.charAt(index))) {
                    index++;
                }
            }
        }
    }
}
