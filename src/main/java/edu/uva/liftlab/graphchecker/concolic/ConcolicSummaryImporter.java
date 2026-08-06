package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.ArtifactIO.sha256;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Converts one VM execution row into one semantic path row.
 *
 * <p>The VM expression graph is the authority for scalars, fields and
 * containers.  Import therefore performs one decode and one admission pass;
 * it does not reconstruct Map entries, array elements or dynamic field
 * selectors from concrete runtime snapshots.</p>
 */
public final class ConcolicSummaryImporter {
    private ConcolicSummaryImporter() {
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> options = parseArgs(args);
        Path results = required(options, "results");
        Path tasks = required(options, "task-plan");
        Path regions = required(options, "regions");
        Path output = Paths.get(firstNonBlank(options.get("output"),
                sibling(results,
                        "concolic_region_summaries.jsonl").toString()));
        Path diagnostics = Paths.get(firstNonBlank(
                options.get("diagnostics"),
                sibling(results,
                        "concolic_import_diagnostics.jsonl").toString()));
        ImportResult imported = importSummaries(results, tasks, regions,
                output, diagnostics);
        if (imported.diagnosticCount > 0) {
            try (BufferedReader reader = Files.newBufferedReader(diagnostics,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    System.err.println("[concolic-import] " + line);
                }
            }
        }
        if (imported.validSummaryCount == 0
                && imported.rawResultCount > 0) {
            System.exit(2);
        }
    }

    public static ImportResult importSummaries(
            Path resultsFile, Path taskPlanFile, Path regionFile,
            Path outputFile, Path diagnosticFile) throws IOException {
        Map<String, ExecutionTask> tasks = taskIndex(
                ArtifactIO.readJsonl(taskPlanFile));
        Set<String> regions = regionIds(ArtifactIO.readJsonl(regionFile));
        List<JsonObject> rawResults = ArtifactIO.readJsonl(resultsFile);
        List<JsonObject> summaries = new ArrayList<>();
        List<JsonObject> diagnostics = new ArrayList<>();
        Set<String> hashes = new LinkedHashSet<>();

        for (int index = 0; index < rawResults.size(); index++) {
            JsonObject raw = rawResults.get(index);
            String taskId = string(raw, "taskId");
            if (!"CONCOLIC_REGION_RESULT".equals(string(raw, "event"))) {
                diagnostics.add(diagnostic(raw, index,
                        "SKIPPED_RUNTIME_EVENT",
                        string(raw, "event")));
                continue;
            }
            ExecutionTask task = tasks.get(taskId);
            if (task == null) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_EXECUTION_TASK", taskId));
                continue;
            }
            if (!regions.contains(task.regionId())) {
                diagnostics.add(diagnostic(raw, index,
                        "UNKNOWN_REGION", task.regionId()));
                continue;
            }
            String exitKind = string(raw, "exitKind");
            if ("CUT".equals(exitKind)
                    || raw.has("pathCut")
                    && !boundedOutputExit(raw, task)) {
                diagnostics.add(diagnostic(raw, index,
                        "LOOP_BOUND_PATH_CUT",
                        object(raw, "pathCut").toString()));
                // A bounded prefix is useful execution diagnostics, but it is
                // neither a normal return nor a workload exception relation.
                // Never let it become a composable region summary.
                continue;
            }
            if ("OUTPUT_BOUNDARY".equals(exitKind)
                    && !exactOutputBoundaryExit(raw, task)) {
                diagnostics.add(diagnostic(raw, index,
                        "INCOMPLETE_OUTPUT_BOUNDARY", taskId));
                continue;
            }

            List<String> issues = new ArrayList<>();
            JsonObject engine = object(raw, "engineSummary");
            if (!bool(engine, "complete", false)
                    || bool(engine, "aborted", false)) {
                issues.add("VM_SUMMARY_INCOMPLETE:"
                        + string(engine, "abortReason"));
            }
            for (JsonElement unresolved : array(raw,
                    "unresolvedInputs")) {
                issues.add("UNRESOLVED_INPUT:" + unresolved);
            }

            SemanticPath path = SemanticPath.from(
                    array(engine, "pathCondition"),
                    array(raw, "branchMappings"));
            JsonArray mappings = branchMappings(raw, task, path, issues);
            String pathSeedMismatch = pathSeedMismatch(raw, task, mappings);
            if (!pathSeedMismatch.isEmpty()) {
                diagnostics.add(diagnostic(raw, index,
                        "PATH_SEED_MISMATCH", pathSeedMismatch));
                continue;
            }
            JsonObject outputs = outputExpressions(raw, task, issues);
            JsonArray symbolicInputs = symbolicInputs(raw);
            JsonObject occurrenceCatalog =
                    task.occurrenceInstantiationCatalog();
            validateOccurrenceCatalog(task, occurrenceCatalog, issues);
            JsonElement replayContract = task.replayContract();

            JsonObject summary = new JsonObject();
            summary.addProperty("schemaVersion", 1);
            summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
            summary.addProperty("goalId", task.goalId());
            summary.addProperty("taskId", task.taskId());
            summary.addProperty("regionId", task.regionId());
            summary.addProperty("regionInstanceId",
                    task.regionInstanceId());
            if (!task.logicalRegionId().isEmpty()) {
                summary.addProperty("logicalRegionId",
                        task.logicalRegionId());
            }
            if (!task.summaryReuseKey().isEmpty()) {
                summary.addProperty("summaryReuseKey",
                        task.summaryReuseKey());
            }
            if (!task.pathSeedKey().isEmpty()) {
                summary.addProperty("pathSeedKey", task.pathSeedKey());
            }
            if (occurrenceCatalog.size() > 0) {
                summary.add(RegionInstancePlan.OCCURRENCE_CATALOG,
                        occurrenceCatalog.deepCopy());
            }
            task.loopBound().writeTo(summary);
            task.goalKind().writeToTask(summary);
            if (task.outputClosure() != null) {
                summary.add(OutputClosureContract.FIELD,
                        task.outputClosure().toJson());
            }
            summary.add("symbolicInputs", symbolicInputs);
            summary.add("edgeBindings", task.edgeBindings());
            summary.add("pathCondition", path.expressions);
            summary.add("branchMappings", mappings);
            summary.add("outputExpressions", outputs);
            boolean boundedExit = "BOUNDED".equals(exitKind)
                    || "OUTPUT_BOUNDARY".equals(exitKind);
            summary.addProperty("normalExit", boundedExit
                    || "NORMAL".equals(exitKind));
            summary.addProperty("boundedExit", boundedExit);
            summary.addProperty("exceptionType",
                    string(raw, "exceptionType"));
            summary.addProperty("relationallyComplete", issues.isEmpty());

            if (replayContract != null && !issues.isEmpty()) {
                diagnostics.add(diagnostic(raw, index,
                        "PATH_REPLAY_ADMISSION_REJECTED",
                        String.join(";", issues)));
                continue;
            }

            JsonObject semantic = summary.deepCopy();
            semantic.remove("taskId");
            String hash = sha256(CanonicalJson.render(semantic));
            if (!hashes.add(hash)) {
                diagnostics.add(diagnostic(raw, index,
                        "DUPLICATE_SUMMARY", hash));
                continue;
            }
            summary.addProperty("summaryId",
                    "SUMMARY." + task.regionId() + "." + hash);
            summaries.add(summary);
            if (!issues.isEmpty()) {
                diagnostics.add(diagnostic(raw, index,
                        "INCOMPLETE_RELATION",
                        String.join(";", issues)));
            }
        }

        ArtifactIO.replaceJsonl(outputFile, summaries);
        ArtifactIO.replaceJsonl(diagnosticFile, diagnostics);
        return new ImportResult(rawResults.size(), summaries.size(),
                diagnostics.size());
    }

    /**
     * Admits a VM row only when it belongs to the canonical bounded path that
     * selected the task.  Cross-run call ids and object identities are not
     * replay addresses: the contract consists solely of static branch sites,
     * activation-local occurrences and outcomes.
     *
     * <p>A seed execution must reproduce the complete branch event set encoded
     * by {@code task.branches}.  A flip execution must reproduce its ordered
     * replay prefix and the requested opposite source outcome; only behavior
     * after that source event may form a newly discovered path.</p>
     */
    private static String pathSeedMismatch(
            JsonObject raw, ExecutionTask task, JsonArray mappings) {
        JsonElement encodedReplay = task.replayContract();
        if (task.pathSeedKey().isEmpty() && encodedReplay == null) {
            // Legacy task rows have no stable seed contract to attest.
            return "";
        }
        if (raw.has("pathSeedKey")
                && !task.pathSeedKey().equals(string(raw,
                "pathSeedKey"))) {
            return "runtime pathSeedKey differs from task pathSeedKey";
        }

        BranchEventCatalog seed = taskSeedEvents(task.branches());
        if (!seed.issue.isEmpty()) {
            return seed.issue;
        }
        BranchEventCatalog observed = observedBranchEvents(mappings);
        if (!observed.issue.isEmpty()) {
            return observed.issue;
        }
        if (encodedReplay == null) {
            return exactSeedMismatch(task.pathSeedKey(), seed.events,
                    observed.events, concreteBranchOutcomes(raw),
                    earlyStopExit(string(raw, "exitKind")));
        }
        if (!encodedReplay.isJsonObject()) {
            return "replayContract is not an object";
        }

        final BranchReplayContract replay;
        try {
            replay = BranchReplayContract.fromJson(
                    encodedReplay.getAsJsonObject());
        } catch (IllegalArgumentException malformed) {
            return "malformed replayContract: " + malformed.getMessage();
        }
        return replayPrefixMismatch(task.pathSeedKey(), seed.events,
                observed.events, replay);
    }

    private static BranchEventCatalog taskSeedEvents(JsonArray branches) {
        BranchEventCatalog result = new BranchEventCatalog();
        int branchIndex = 0;
        for (JsonElement element : branches) {
            if (!element.isJsonObject()) {
                result.issue = "task branch " + branchIndex
                        + " is not an object";
                return result;
            }
            JsonObject branch = element.getAsJsonObject();
            String site = string(branch, "siteId");
            JsonElement encodedOccurrences = branch.get("occurrences");
            if (site.isEmpty() || encodedOccurrences == null
                    || !encodedOccurrences.isJsonArray()) {
                result.issue = "task branch " + branchIndex
                        + " has no stable site/occurrence contract";
                return result;
            }
            for (JsonElement occurrenceElement
                    : encodedOccurrences.getAsJsonArray()) {
                if (!occurrenceElement.isJsonObject()) {
                    result.issue = "task branch occurrence is not an object at "
                            + site;
                    return result;
                }
                JsonObject occurrence = occurrenceElement.getAsJsonObject();
                int ordinal = JsonFields.exactInteger(
                        occurrence, "occurrence", -1);
                Boolean outcome = exactBoolean(occurrence, "outcome");
                if (ordinal < 1 || outcome == null) {
                    result.issue = "task branch occurrence is malformed at "
                            + site;
                    return result;
                }
                BranchEvent event = new BranchEvent(site, ordinal, outcome);
                if (result.byIdentity.put(event.identity, event) != null) {
                    result.issue = "duplicate task branch event "
                            + event.display();
                    return result;
                }
                result.events.add(event);
            }
            branchIndex++;
        }
        return result;
    }

    private static BranchEventCatalog observedBranchEvents(
            JsonArray mappings) {
        BranchEventCatalog result = new BranchEventCatalog();
        int mappingIndex = 0;
        for (JsonElement element : mappings) {
            if (!element.isJsonObject()) {
                result.issue = "runtime branch mapping " + mappingIndex
                        + " is not an object";
                return result;
            }
            final SummaryBranchMapping mapping;
            try {
                mapping = SummaryBranchMapping.fromJson(
                        element.getAsJsonObject());
            } catch (IllegalArgumentException malformed) {
                result.issue = "runtime branch mapping " + mappingIndex
                        + " is malformed: " + malformed.getMessage();
                return result;
            }
            if (mapping.isWitnessed()
                    && mapping.witness().isPcPredicateDecision()) {
                mappingIndex++;
                continue;
            }
            BranchEvent event = new BranchEvent(mapping.siteId(),
                    mapping.occurrence(), mapping.sourceTakenOutcome());
            if (result.byIdentity.put(event.identity, event) != null) {
                result.issue = "duplicate runtime branch event "
                        + event.display();
                return result;
            }
            result.events.add(event);
            mappingIndex++;
        }
        return result;
    }

    /**
     * Attests a seed replay against the recorded branch witnesses.
     *
     * <p>Recording and replay are two executions of the same concurrent
     * workload, so a site repeats as many times as the surrounding
     * environment happens to be wide: a loop over a shared container runs
     * once per element that execution holds.  The demanded slice constrains
     * which way a branch goes, never how many times an environment-sized
     * loop revisits it, so pinning the recorded occurrence ordinals rejects
     * a faithful replay for a fact the failure never depended on.</p>
     *
     * <p>The contract is therefore stated per static site: every outcome the
     * recording witnessed at a site must also be witnessed there by the
     * replay, and the replay may not decide a site the task never planned.
     * A site the replay drives only the other way is a real witness conflict
     * and still fails closed.</p>
     *
     * <p>Coverage is attested by execution, not by solvability.  A branch the
     * replay decided before its symbolic gate opened produces no VM event and
     * therefore no mapping, yet it demonstrably ran; those concrete witnesses
     * satisfy coverage while never entering the path condition.  They cannot
     * make a site unexpected either: a concrete prefix decides branches the
     * demanded slice never planned, and that is ordinary execution.</p>
     *
     * <p>An activation that deliberately stops early — at its reach target,
     * at its output boundary, or at a loop bound — never executes the tail of
     * the recorded region at all.  Demanding coverage of sites the task chose
     * not to reach would reject every bounded summary, so an early stop keeps
     * only the contradiction rules.</p>
     */
    private static String exactSeedMismatch(
            String pathSeedKey, List<BranchEvent> expected,
            List<BranchEvent> observed,
            Map<String, Set<Boolean>> concrete, boolean earlyStop) {
        Map<String, Set<Boolean>> wanted = outcomesBySite(expected);
        Map<String, Set<Boolean>> actual = outcomesBySite(observed);
        for (Map.Entry<String, Set<Boolean>> entry : wanted.entrySet()) {
            Set<Boolean> found = union(actual.get(entry.getKey()),
                    concrete.get(entry.getKey()));
            if (found.isEmpty()) {
                if (earlyStop) continue;
                return seedDetail(pathSeedKey, "missing " + entry.getKey());
            }
            for (Boolean outcome : entry.getValue()) {
                if (!found.contains(outcome)) {
                    return seedDetail(pathSeedKey, "wrong outcome at "
                            + entry.getKey() + ": expected " + outcome
                            + " but observed " + found);
                }
            }
        }
        for (String site : actual.keySet()) {
            if (!wanted.containsKey(site)) {
                return seedDetail(pathSeedKey, "unexpected " + site);
            }
        }
        return "";
    }

    /**
     * Exit kinds where the activation stopped on purpose before the recorded
     * region ended.
     */
    static boolean earlyStopExit(String exitKind) {
        return "TARGET_REACHED".equals(exitKind)
                || "OUTPUT_BOUNDARY".equals(exitKind)
                || "BOUNDED".equals(exitKind);
    }

    /**
     * Indexes the branches an activation executed before its symbolic gate
     * opened.  These rows carry no path condition and no occurrence ordinal,
     * so they can only ever answer "was this site reached, and which way".
     */
    public static Map<String, Set<Boolean>> concreteBranchOutcomes(
            JsonObject raw) {
        Map<String, Set<Boolean>> outcomes = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "concreteBranchWitnesses")) {
            if (!element.isJsonObject()) continue;
            JsonObject witness = element.getAsJsonObject();
            String site = string(witness, "siteId");
            JsonElement outcome = witness.get("sourceTakenOutcome");
            if (site.isEmpty() || outcome == null
                    || !outcome.isJsonPrimitive()
                    || !outcome.getAsJsonPrimitive().isBoolean()) {
                continue;
            }
            Set<Boolean> seen = outcomes.get(site);
            if (seen == null) {
                seen = new LinkedHashSet<>();
                outcomes.put(site, seen);
            }
            seen.add(outcome.getAsBoolean());
        }
        return outcomes;
    }

    private static Set<Boolean> union(Set<Boolean> first, Set<Boolean> second) {
        Set<Boolean> result = new LinkedHashSet<>();
        if (first != null) result.addAll(first);
        if (second != null) result.addAll(second);
        return result;
    }

    private static String replayPrefixMismatch(
            String pathSeedKey, List<BranchEvent> seedEvents,
            List<BranchEvent> observed, BranchReplayContract replay) {
        Map<String, Set<Boolean>> seed = outcomesBySite(seedEvents);
        List<BranchEvent> expected = new ArrayList<>();
        for (BranchWitness witness : replay.orderedPrefix()) {
            if (witness.isPcPredicateDecision()) continue;
            BranchEvent event = new BranchEvent(witness.siteId(),
                    witness.occurrence(), witness.sourceTakenOutcome());
            String inconsistency = replaySeedInconsistency(seed, event);
            if (!inconsistency.isEmpty()) {
                return seedDetail(pathSeedKey, inconsistency);
            }
            expected.add(event);
        }
        BranchWitness source = replay.source();
        if (source.isPcPredicateDecision()) {
            return seedDetail(pathSeedKey,
                    "replay source is not a source-level branch event");
        }
        BranchEvent originalSource = new BranchEvent(source.siteId(),
                source.occurrence(), source.sourceTakenOutcome());
        String inconsistency = replaySeedInconsistency(seed, originalSource);
        if (!inconsistency.isEmpty()) {
            return seedDetail(pathSeedKey, inconsistency);
        }
        expected.add(new BranchEvent(source.siteId(), source.occurrence(),
                replay.requiredTakenOutcome()));

        int next = 0;
        for (BranchEvent actual : observed) {
            if (next == expected.size()) {
                // The flip source has been reached.  Its suffix is precisely
                // the new path that concolic exploration is meant to discover.
                break;
            }
            BranchEvent wanted = expected.get(next);
            if (wanted.identity.equals(actual.identity)) {
                if (wanted.outcome != actual.outcome) {
                    return seedDetail(pathSeedKey, "wrong replay outcome at "
                            + wanted.siteOccurrence() + ": expected "
                            + wanted.outcome + " but observed "
                            + actual.outcome);
                }
                next++;
                continue;
            }
            for (int future = next + 1; future < expected.size(); future++) {
                if (expected.get(future).identity.equals(actual.identity)) {
                    return seedDetail(pathSeedKey, "replay event "
                            + actual.siteOccurrence() + " occurred before "
                            + wanted.siteOccurrence());
                }
            }
            Set<Boolean> original = seed.get(actual.site);
            if (original == null) {
                return seedDetail(pathSeedKey,
                        "unexpected pre-source " + actual.display());
            }
            if (!original.contains(actual.outcome)) {
                return seedDetail(pathSeedKey,
                        "pre-source path diverged at "
                                + actual.siteOccurrence());
            }
        }
        if (next != expected.size()) {
            return seedDetail(pathSeedKey, "missing replay event "
                    + expected.get(next).display());
        }
        return "";
    }

    private static String replaySeedInconsistency(
            Map<String, Set<Boolean>> seed, BranchEvent replayEvent) {
        Set<Boolean> original = seed.get(replayEvent.site);
        if (original == null) {
            return "replay event is absent from task seed: "
                    + replayEvent.siteOccurrence();
        }
        return original.contains(replayEvent.outcome) ? ""
                : "replay event conflicts with task seed at "
                + replayEvent.siteOccurrence();
    }

    private static Map<String, Set<Boolean>> outcomesBySite(
            List<BranchEvent> events) {
        Map<String, Set<Boolean>> result = new LinkedHashMap<>();
        for (BranchEvent event : events) {
            result.computeIfAbsent(event.site,
                    ignored -> new LinkedHashSet<>()).add(event.outcome);
        }
        return result;
    }

    private static Boolean exactBoolean(JsonObject object, String field) {
        JsonElement value = object == null ? null : object.get(field);
        return value != null && value.isJsonPrimitive()
                && value.getAsJsonPrimitive().isBoolean()
                ? value.getAsBoolean() : null;
    }

    private static String seedDetail(String pathSeedKey, String issue) {
        return (pathSeedKey.isEmpty() ? "<replay>" : pathSeedKey)
                + ": " + issue;
    }

    private static final class BranchEventCatalog {
        private final List<BranchEvent> events = new ArrayList<>();
        private final Map<String, BranchEvent> byIdentity =
                new LinkedHashMap<>();
        private String issue = "";
    }

    private static final class BranchEvent {
        private final String site;
        private final int occurrence;
        private final boolean outcome;
        private final String identity;

        private BranchEvent(String site, int occurrence, boolean outcome) {
            this.site = site;
            this.occurrence = occurrence;
            this.outcome = outcome;
            this.identity = site + "\u0000" + occurrence;
        }

        private String siteOccurrence() {
            return site + '#' + occurrence;
        }

        private String display() {
            return siteOccurrence() + '=' + outcome;
        }
    }

    private static void validateOccurrenceCatalog(
            ExecutionTask task, JsonObject catalog, List<String> issues) {
        if (catalog.size() == 0) {
            if (!task.logicalRegionId().isEmpty()) {
                issues.add("MISSING_OCCURRENCE_INSTANTIATION_CATALOG");
            }
            return;
        }
        if (integer(catalog, "schemaVersion", -1) != 1
                || !"LOGICAL_SUMMARY_OCCURRENCE_CATALOG".equals(
                string(catalog, "kind"))
                || !task.logicalRegionId().equals(
                string(catalog, "logicalRegionId"))
                || !task.regionInstanceId().equals(string(catalog,
                "canonicalRegionInstanceId"))
                || !task.summaryReuseKey().equals(
                string(catalog, "summaryReuseKey"))
                || longInteger(task.json(), "rootCallId", -1L) >= 0L
                && longInteger(catalog, "canonicalRootCallId", -1L)
                != longInteger(task.json(), "rootCallId", -1L)) {
            issues.add("MALFORMED_OCCURRENCE_INSTANTIATION_CATALOG");
            return;
        }
        Set<String> canonicalInputs = new LinkedHashSet<>();
        for (JsonElement element : task.inputActions().all()) {
            if (!element.isJsonObject()) continue;
            JsonObject action = element.getAsJsonObject();
            String port = firstNonBlank(string(action, "portId"),
                    string(action, "symbol"));
            if (!port.isEmpty()) canonicalInputs.add(port);
        }
        Set<String> canonicalOutputs = task.outputClosure() == null
                ? new LinkedHashSet<>() : new LinkedHashSet<>(
                task.outputClosure().outputPorts());
        Map<String, List<JsonObject>> bindingsById = new LinkedHashMap<>();
        for (JsonElement element : task.edgeBindings()) {
            if (!element.isJsonObject()) continue;
            JsonObject binding = element.getAsJsonObject();
            String edgeId = string(binding, "edgeId");
            if (!edgeId.isEmpty()) {
                bindingsById.computeIfAbsent(edgeId,
                        ignored -> new ArrayList<>()).add(binding);
            }
        }
        Set<String> instances = new LinkedHashSet<>();
        boolean canonicalFound = false;
        for (JsonElement element : array(catalog, "occurrences")) {
            if (!element.isJsonObject()) {
                issues.add("MALFORMED_SUMMARY_OCCURRENCE");
                continue;
            }
            JsonObject occurrence = element.getAsJsonObject();
            String instance = string(occurrence, "regionInstanceId");
            long rootCall = longInteger(occurrence, "rootCallId", -1L);
            boolean requiresRoot = task.outputClosure() != null
                    || longInteger(task.json(), "rootCallId", -1L) >= 0L;
            boolean inconsistentRoot = (requiresRoot && rootCall < 0L)
                    || (rootCall >= 0L
                    && !instance.endsWith("#call" + rootCall));
            if (instance.isEmpty() || inconsistentRoot
                    || !instances.add(instance)) {
                issues.add("AMBIGUOUS_SUMMARY_OCCURRENCE:" + instance);
                continue;
            }
            canonicalFound |= task.regionInstanceId().equals(instance);
            validatePortMap(occurrence, "inputPortMap", instance,
                    canonicalInputs, issues);
            validatePortMap(occurrence, "outputPortMap", instance,
                    canonicalOutputs, issues);
            Set<String> declaredBindings = new LinkedHashSet<>();
            for (JsonElement id : array(occurrence, "bindingIds")) {
                if (!id.isJsonPrimitive()
                        || !id.getAsJsonPrimitive().isString()
                        || stringValue(id).isEmpty()
                        || !declaredBindings.add(stringValue(id))) {
                    issues.add("MALFORMED_OCCURRENCE_BINDING_ID:"
                            + instance);
                    continue;
                }
                String edgeId = stringValue(id);
                List<JsonObject> bindings = bindingsById.get(edgeId);
                boolean exact = false;
                if (bindings != null) {
                    for (JsonObject binding : bindings) {
                        exact |= instance.equals(string(binding,
                                "fromRegionInstance"))
                                || instance.equals(string(binding,
                                "toRegionInstance"));
                    }
                }
                if (!exact) {
                    issues.add("UNKNOWN_OCCURRENCE_BINDING_ID:"
                            + instance + ":" + edgeId);
                }
            }
            Set<String> touchingBindings = new LinkedHashSet<>();
            for (Map.Entry<String, List<JsonObject>> entry
                    : bindingsById.entrySet()) {
                for (JsonObject binding : entry.getValue()) {
                    if (instance.equals(string(binding,
                            "fromRegionInstance"))
                            || instance.equals(string(binding,
                            "toRegionInstance"))) {
                        touchingBindings.add(entry.getKey());
                    }
                }
            }
            if (!declaredBindings.equals(touchingBindings)) {
                issues.add("INCOMPLETE_OCCURRENCE_BINDING_IDS:"
                        + instance);
            }
        }
        if (!canonicalFound) {
            issues.add("MISSING_CANONICAL_SUMMARY_OCCURRENCE");
        }
    }

    private static void validatePortMap(
            JsonObject occurrence, String field, String instance,
            Set<String> expectedCanonical, List<String> issues) {
        Set<String> canonical = new LinkedHashSet<>();
        Set<String> exact = new LinkedHashSet<>();
        for (JsonElement element : array(occurrence, field)) {
            if (!element.isJsonObject()) {
                issues.add("MALFORMED_OCCURRENCE_PORT_MAP:" + instance
                        + ":" + field);
                continue;
            }
            JsonObject mapping = element.getAsJsonObject();
            String from = string(mapping, "canonicalPort");
            String to = string(mapping, "exactPort");
            if (from.isEmpty() || to.isEmpty()
                    || !canonical.add(from) || !exact.add(to)) {
                issues.add("AMBIGUOUS_OCCURRENCE_PORT_MAP:" + instance
                        + ":" + field);
            }
        }
        if (!canonical.equals(expectedCanonical)) {
            issues.add("INCOMPLETE_OCCURRENCE_PORT_MAP:" + instance
                    + ":" + field);
        }
    }

    private static String stringValue(JsonElement value) {
        return value == null || !value.isJsonPrimitive()
                || !value.getAsJsonPrimitive().isString()
                ? "" : value.getAsString().trim();
    }

    private static boolean boundedOutputExit(JsonObject raw,
                                             ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || !"BOUNDED".equals(string(raw, "exitKind"))) {
            return false;
        }
        JsonObject cut = object(raw, "pathCut");
        return "LOOP_BOUND".equals(string(cut, "kind"))
                && !string(cut, "backedgeId").isEmpty()
                && integer(cut, "maxBackedgeTraversals", -1)
                == task.loopBound().maxBackedgeTraversals();
    }

    /** Admits only a complete, exact producer prefix as a normal relation. */
    private static boolean exactOutputBoundaryExit(
            JsonObject raw, ExecutionTask task) {
        if (!task.goalKind().capturesOutputRelation()
                || task.outputCaptures().isEmpty()) {
            return false;
        }
        JsonArray captures = array(raw, "outputCaptures");
        Set<String> requestedBindings = new LinkedHashSet<>();
        for (OutputCaptureSpec request : task.outputCaptures()) {
            if (!(request.capturesCallArgument()
                    || request.capturesFieldWriteState()
                    || request.capturesMutationState())
                    || !requestedBindings.add(request.captureBindingId())) {
                return false;
            }
            int successfulRows = 0;
            for (JsonElement element : captures) {
                if (!element.isJsonObject()) continue;
                JsonObject capture = element.getAsJsonObject();
                if (!request.captureBindingId().equals(
                        string(capture, "captureBindingId"))) {
                    continue;
                }
                JsonElement expression = capture.get("expression");
                if (expression != null && !expression.isJsonNull()
                        && exactOutputCaptureOccurrence(request, capture)) {
                    successfulRows++;
                }
            }
            // One admitted observation is the relation.  A row that carried
            // no expression is a guarded observation of an occurrence that
            // produced nothing, and a further admitted row is another version
            // of the same relation rather than a second relation.
            if (successfulRows < 1) return false;
        }
        return true;
    }

    private static JsonArray branchMappings(
            JsonObject raw, ExecutionTask task, SemanticPath path,
            List<String> issues) {
        Map<String, SummaryBranchMapping.Policy> policies =
                branchPolicies(task);
        JsonArray result = new JsonArray();
        Set<String> events = new LinkedHashSet<>();
        Set<Integer> decisionPositions = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "branchMappings")) {
            if (!element.isJsonObject()) {
                issues.add("MALFORMED_BRANCH_MAPPING");
                continue;
            }
            JsonObject row = element.getAsJsonObject();
            String site = string(row, "siteId");
            int occurrence = integer(row, "occurrence", -1);
            if (site.isEmpty() || occurrence < 1
                    || !events.add(site + "\u0000" + occurrence)) {
                issues.add("AMBIGUOUS_BRANCH_EVENT:" + site);
                continue;
            }
            SummaryBranchMapping.Policy policy = policies.get(site);
            if (policy == null) {
                policy = SummaryBranchMapping.Policy.PATH_ASSUMPTION;
            }
            try {
                BranchWitness direct = null;
                ExactConcreteBranchObservation concrete = null;
                if (row.has("witness")
                        && row.get("witness").isJsonObject()) {
                    direct = BranchWitness.fromJson(
                            row.getAsJsonObject("witness"));
                    int pcIndex = direct.vmPcIndex();
                    if (pcIndex < 0 || pcIndex >= path.original.size()
                            || !BranchPredicateAlgebra.equivalent(
                            direct.sourceSatisfiedPredicate(),
                            path.original.get(pcIndex))) {
                        issues.add("BRANCH_PC_MISMATCH:" + site);
                        continue;
                    }
                } else if (row.has("concreteObservation")
                        && row.get("concreteObservation").isJsonObject()) {
                    concrete = ExactConcreteBranchObservation.fromJson(
                            row.getAsJsonObject("concreteObservation"));
                } else {
                    // A marker without a VM event is a concrete branch outside
                    // the selected symbolic slice.  It has no guard to retain
                    // or flip, so it is intentionally absent from the summary.
                    continue;
                }

                int baseline = integer(row,
                        "rawPathConditionBaseline", -1);
                int limit = integer(row, "rawPathConditionSize", -1);
                if (baseline < 0 || limit < baseline
                        || limit > path.original.size()
                        || direct != null
                        && (direct.vmPcIndex() < baseline
                        || direct.vmPcIndex() >= limit)) {
                    issues.add("INVALID_BRANCH_PC_WINDOW:" + site);
                    continue;
                }

                if (direct != null) {
                    int summaryPcIndex = path.summaryIndex(
                            direct.vmPcIndex());
                    if (summaryPcIndex < 0) {
                        issues.add("MISSING_BRANCH_PC:" + site);
                        continue;
                    }
                    if (!decisionPositions.add(summaryPcIndex)) {
                        issues.add("AMBIGUOUS_BRANCH_PC:"
                                + summaryPcIndex);
                        continue;
                    }
                    result.add(SummaryBranchMapping.witnessed(
                            direct.atPcIndex(summaryPcIndex),
                            summaryPcIndex, policy).toJson());
                } else if (concrete != null) {
                    result.add(SummaryBranchMapping.concrete(concrete,
                            policy).toJson());
                }
            } catch (IllegalArgumentException malformed) {
                issues.add("MALFORMED_BRANCH_MAPPING:" + site + ":"
                        + malformed.getMessage());
            }
        }
        return result;
    }

    /** True only for a binary VM predicate that would need branch authority. */
    private static boolean pcPredicate(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return false;
        JsonObject object = expression.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))
                || ContainerSmtCodec.handlesFieldBinding(expression)
                || ContainerSmtCodec.handlesAccessConstraint(expression)) {
            return false;
        }
        try {
            BranchPredicateAlgebra.complementOperator(
                    string(object, "_op"));
            return true;
        } catch (IllegalArgumentException unsupported) {
            return false;
        }
    }

    private static Map<String, SummaryBranchMapping.Policy> branchPolicies(
            ExecutionTask task) {
        Map<String, SummaryBranchMapping.Policy> result =
                new LinkedHashMap<>();
        for (JsonElement element : task.branches()) {
            if (!element.isJsonObject()) continue;
            JsonObject branch = element.getAsJsonObject();
            String site = string(branch, "siteId");
            try {
                result.put(site, SummaryBranchMapping.Policy.fromWire(
                        string(branch, "policy")));
            } catch (IllegalArgumentException unsupported) {
                result.put(site, SummaryBranchMapping.Policy.EXPLORE);
            }
        }
        return result;
    }

    private static JsonObject outputExpressions(
            JsonObject raw, ExecutionTask task, List<String> issues) {
        JsonObject result = new JsonObject();
        OutputClosureContract closure = task.outputClosure();
        if (closure == null) return result;

        Map<String, List<JsonObject>> captures = new LinkedHashMap<>();
        for (JsonElement element : array(raw, "outputCaptures")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            JsonElement expression = row.get("expression");
            if (expression != null && !expression.isJsonNull()) {
                captures.computeIfAbsent(string(row, "captureBindingId"),
                        ignored -> new ArrayList<>())
                        .add(row.deepCopy());
            }
        }

        Map<String, List<OutputCaptureSpec>> specsByPort =
                new LinkedHashMap<>();
        for (OutputCaptureSpec spec : task.outputCaptures()) {
            specsByPort.computeIfAbsent(spec.outputPort(),
                    ignored -> new ArrayList<>()).add(spec);
        }
        for (String port : closure.outputPorts()) {
            List<OutputCaptureSpec> specs = specsByPort.get(port);
            List<JsonElement> expressions = new ArrayList<>();
            if (specs != null) {
                for (OutputCaptureSpec spec : specs) {
                    List<JsonObject> values = captures.get(
                            spec.captureBindingId());
                    if (values == null) continue;
                    for (JsonObject value : values) {
                        JsonElement expression = value.get("expression");
                        if (expression == null || expression.isJsonNull()) {
                            // A guarded observation of an occurrence that
                            // produced nothing; another occurrence of the
                            // same site may still carry the relation.
                            continue;
                        }
                        if (!exactOutputCaptureOccurrence(spec, value)) {
                            issues.add("OUTPUT_CAPTURE_OCCURRENCE_MISMATCH:"
                                    + port + ":"
                                    + spec.captureBindingId());
                            continue;
                        }
                        expressions.add(expression.deepCopy());
                    }
                }
            }
            if (expressions.size() == 1) {
                result.add(port, expressions.get(0));
                continue;
            }
            JsonElement root = rootOutputExpression(raw);
            if ((specs == null || specs.isEmpty())
                    && closure.outputPorts().size() == 1
                    && root != null) {
                result.add(port, root);
                continue;
            }
            issues.add("OUTPUT_CAPTURE_COUNT:" + port + ":"
                    + expressions.size());
        }
        return result;
    }

    /**
     * Admits an observation of the recorded output relation.
     *
     * <p>The recorded ordinal is not replay identity: the goal states this
     * relation without one, and a bounded replay reaches the site a different
     * number of times than the recording did.  What must agree is the shape —
     * the same recorded static site, observed inside the bounded replay
     * window.  Which version of the relation a reader sees is settled by the
     * composed versioned channel, not here.</p>
     */
    private static boolean exactOutputCaptureOccurrence(
            OutputCaptureSpec request, JsonObject capture) {
        if (!request.occurrenceScoped()) return true;
        int occurrence = integer(capture, "outputOccurrence", -1);
        return request.outputSiteId().equals(
                string(capture, "outputSiteId"))
                && occurrence >= 1
                && occurrence <= LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
    }

    private static JsonElement rootOutputExpression(JsonObject raw) {
        JsonElement encoded = raw.get("rootOutputExpression");
        if (encoded == null || !encoded.isJsonObject()) return null;
        JsonObject wrapper = encoded.getAsJsonObject();
        JsonElement expression = wrapper.get("expression");
        return expression != null && !expression.isJsonNull()
                ? expression.deepCopy() : null;
    }

    private static JsonArray symbolicInputs(JsonObject raw) {
        JsonArray result = new JsonArray();
        Set<String> unique = new LinkedHashSet<>();
        for (JsonElement element : array(raw, "symbolizedInputs")) {
            if (element.isJsonPrimitive()) {
                String symbol = element.getAsString();
                if (!symbol.isEmpty() && unique.add(symbol)) {
                    result.add(symbol);
                }
            }
        }
        return result;
    }

    private static Map<String, ExecutionTask> taskIndex(
            List<JsonObject> rows) throws IOException {
        Map<String, ExecutionTask> result = new LinkedHashMap<>();
        for (JsonObject row : rows) {
            final ExecutionTask task;
            try {
                task = ExecutionTask.decode(row);
            } catch (IllegalArgumentException malformed) {
                throw new IOException("Malformed execution task: "
                        + malformed.getMessage(), malformed);
            }
            if (result.put(task.taskId(), task) != null) {
                throw new IOException("Duplicate taskId " + task.taskId());
            }
        }
        return result;
    }

    private static Set<String> regionIds(List<JsonObject> rows)
            throws IOException {
        Set<String> result = new LinkedHashSet<>();
        for (JsonObject row : rows) {
            String id = string(row, "regionId");
            if (id.isEmpty() || !result.add(id)) {
                throw new IOException("Missing or duplicate regionId " + id);
            }
        }
        return result;
    }

    private static JsonObject diagnostic(
            JsonObject raw, int index, String code, String detail) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "CONCOLIC_IMPORT_DIAGNOSTIC");
        result.addProperty("code", code);
        result.addProperty("detail", firstNonBlank(detail, "UNKNOWN"));
        result.addProperty("taskId", string(raw, "taskId"));
        result.addProperty("line", index + 1);
        return result;
    }

    /** Removes replay-only container observations and remaps PC ownership. */
    private static final class SemanticPath {
        private final JsonArray original;
        private final JsonArray expressions;
        private final int[] summaryIndices;

        private SemanticPath(JsonArray original, JsonArray expressions,
                             int[] summaryIndices) {
            this.original = original;
            this.expressions = expressions;
            this.summaryIndices = summaryIndices;
        }

        private static SemanticPath from(JsonArray raw,
                                         JsonArray branchMappings) {
            JsonArray original = raw == null
                    ? new JsonArray() : raw.deepCopy();
            JsonArray expressions = new JsonArray();
            int[] indices = new int[original.size()];
            Set<Integer> branchDecisions =
                    witnessedVmPcIndices(branchMappings);
            for (int index = 0; index < original.size(); index++) {
                JsonElement expression = original.get(index);
                boolean witnessed = branchDecisions.contains(index);
                if (!witnessed
                        && (InitialContainerObservation.isConcreteEquality(
                        expression)
                        || pcPredicate(expression))) {
                    indices[index] = -1;
                } else {
                    indices[index] = expressions.size();
                    expressions.add(expression.deepCopy());
                }
            }
            return new SemanticPath(original, expressions, indices);
        }

        private static Set<Integer> witnessedVmPcIndices(
                JsonArray branchMappings) {
            Set<Integer> result = new LinkedHashSet<>();
            for (JsonElement element : branchMappings) {
                if (!element.isJsonObject()) continue;
                JsonObject witness = object(
                        element.getAsJsonObject(), "witness");
                int index = integer(witness, "vmPcIndex", -1);
                if (index >= 0) result.add(index);
            }
            return result;
        }

        private int summaryIndex(int vmIndex) {
            return vmIndex < 0 || vmIndex >= summaryIndices.length
                    ? -1 : summaryIndices[vmIndex];
        }
    }

    private static Map<String, String> parseArgs(String[] args) {
        Map<String, String> result = new LinkedHashMap<>();
        for (int index = 0; index < args.length; index++) {
            String argument = args[index];
            if (!argument.startsWith("--")) {
                throw new IllegalArgumentException(
                        "expected --name value, got " + argument);
            }
            String name = argument.substring(2);
            int equals = name.indexOf('=');
            if (equals >= 0) {
                result.put(name.substring(0, equals),
                        name.substring(equals + 1));
            } else if (index + 1 < args.length) {
                result.put(name, args[++index]);
            } else {
                throw new IllegalArgumentException(
                        "missing value for " + argument);
            }
        }
        return result;
    }

    private static Path required(
            Map<String, String> options, String name) {
        String value = options.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException(
                    "missing required --" + name);
        }
        return Paths.get(value);
    }

    private static Path sibling(Path input, String name) {
        Path parent = input.toAbsolutePath().normalize().getParent();
        return parent == null ? Paths.get(name) : parent.resolve(name);
    }

    public static final class ImportResult {
        public final int rawResultCount;
        public final int validSummaryCount;
        public final int diagnosticCount;

        private ImportResult(int rawResultCount, int validSummaryCount,
                             int diagnosticCount) {
            this.rawResultCount = rawResultCount;
            this.validSummaryCount = validSummaryCount;
            this.diagnosticCount = diagnosticCount;
        }
    }
}
