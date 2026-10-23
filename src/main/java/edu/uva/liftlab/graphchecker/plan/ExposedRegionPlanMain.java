package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.ZkChain;
import edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JsonFields;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class ExposedRegionPlanMain {
    public static final String EXPOSED_REGION = "EXPOSED_REGION";
    public static final String UNPLANNED_INPUT = "UNPLANNED_INPUT";
    public static final String EXPOSED_BY = "EXPOSED_BY:";

    private static final Gson GSON = new Gson();

    private ExposedRegionPlanMain() {
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> values = ConcolicScheduler.parseArgs(args,
                "iteration", "static-scope-map", "plan", "growth", "output",
                "zk-chain", "zk-chain-output");
        Path iteration = ConcolicScheduler.requiredPath(values, "iteration");
        Path scopeMap = ConcolicScheduler.requiredPath(values,
                "static-scope-map");
        Path plan = ConcolicScheduler.requiredPath(values, "plan");
        Path growth = ConcolicScheduler.requiredPath(values, "growth");
        Path output = ConcolicScheduler.requiredPath(values, "output");
        List<JsonObject> rows = ArtifactIO.readJsonl(growth);
        List<JsonObject> generation = grown(ArtifactIO.readJsonl(plan), rows);
        generation.addAll(plan(iteration, scopeMap, rows, generation));
        ZkChain chain = ZkChain.read(values.containsKey("zk-chain")
                ? ConcolicScheduler.requiredPath(values, "zk-chain")
                : null).grown(rows);
        if (values.containsKey("zk-chain-output") && !chain.empty()) {
            keyed(generation, rows, chain);
            chain.write(ConcolicScheduler.requiredPath(values,
                    "zk-chain-output"));
        }
        ArtifactIO.replaceJsonl(output, generation);
    }

    static void keyed(List<JsonObject> generation, List<JsonObject> growth,
                      ZkChain chain) {
        Set<String> edged = new LinkedHashSet<>();
        for (JsonObject row : growth) {
            if (ZkChain.EDGE.equals(optionalString(row, "kind"))) {
                edged.add(optionalString(row, "occurrence"));
            }
        }
        for (JsonObject task : generation) {
            String occurrence = optionalString(task, "occurrenceId");
            JsonArray grown = edged.contains(occurrence)
                    ? chain.contentKeys(occurrence) : new JsonArray();
            if (grown.size() == 0) continue;
            JsonArray keys = task.has(ZkChain.CONTENT_KEYS)
                    ? task.getAsJsonArray(ZkChain.CONTENT_KEYS)
                    : new JsonArray();
            for (JsonElement key : grown) {
                if (!keys.contains(key)) keys.add(key);
            }
            task.add(ZkChain.CONTENT_KEYS, keys);
        }
    }

    static List<JsonObject> grown(List<JsonObject> plan,
                                  List<JsonObject> growth) throws IOException {
        List<JsonObject> rows = new ArrayList<>();
        Map<String, JsonObject> tasks = new LinkedHashMap<>();
        for (JsonObject row : plan) {
            JsonObject copy = row.deepCopy();
            rows.add(copy);
            tasks.put(optionalString(copy, "taskId"), copy);
        }
        for (JsonObject row : growth) {
            if (!UNPLANNED_INPUT.equals(optionalString(row, "kind"))) continue;
            UnplannedInput input = UnplannedInput.of(
                    optionalString(row, "taskId"),
                    optionalString(row, "symbol"),
                    row.has("k") ? row.get("k").getAsInt() : 0);
            JsonObject task = tasks.get(input.taskId());
            JsonArray actions = task == null ? null
                    : task.getAsJsonArray(InputActionCatalog.FIELD);
            JsonObject planned = null;
            boolean present = false;
            for (int index = 0; actions != null && index < actions.size();
                 index++) {
                JsonObject action = actions.get(index).getAsJsonObject();
                String symbol = optionalString(action, "symbol");
                if (symbol.equals(input.symbol())) planned = action;
                present |= symbol.equals(input.grown());
            }
            if (planned == null) {
                throw new IOException("UNPLANNED_INPUT_UNKNOWN: task "
                        + input.taskId() + " plans no input "
                        + input.symbol() + ": " + row);
            }
            if (present) continue;
            JsonObject invocation = planned.deepCopy();
            invocation.addProperty("symbol", input.grown());
            invocation.addProperty("portId", input.grown());
            invocation.addProperty("replayOccurrence", input.k());
            invocation.addProperty("observed", false);
            for (String recorded : RECORDED) invocation.remove(recorded);
            actions.add(InputActionCatalog.stamp(invocation));
        }
        return rows;
    }

    private static final String[] RECORDED = {
        "primitiveValue", "eventSeq", "callId"};

    static List<JsonObject> plan(Path iteration, Path scopeMapFile,
                                 List<JsonObject> growth,
                                 List<JsonObject> planned)
            throws IOException {
        Set<String> tasked = new LinkedHashSet<>();
        for (JsonObject task : planned) {
            tasked.add(optionalString(task, "occurrenceId"));
        }
        // One task per occurrence: an exposure of an occurrence the plan
        // already tasks adds none -- a chain edge's, or a GROW re-run's
        // exposure computed against the plan before an edge of a later
        // generation tasked the same occurrence (solr-adhoc-19, R1: g32's
        // edge then g33's exposure, a duplicate taskId the weave refuses).
        List<JsonObject> exposures = new ArrayList<>();
        for (JsonObject row : growth) {
            String kind = optionalString(row, "kind");
            if ((EXPOSED_REGION.equals(kind) || ZkChain.EDGE.equals(kind))
                    && !tasked.contains(optionalString(row, "occurrence"))) {
                exposures.add(row);
            }
        }
        if (exposures.isEmpty()) return new ArrayList<>();
        // The plan stays within the campaign's task bound, as a planning
        // round's closure stops at its ceiling: an exposure past it is not
        // tasked (solr-adhoc-31, X1: g25 grew past 1024 tasks and the weave
        // refused the plan, ending the campaign).
        int bound = ExecutionTask.maxCampaignTasks();
        int room = bound - planned.size();
        if (room <= 0) {
            pastBound(bound, planned.size(), exposures.size());
            return new ArrayList<>();
        }
        StaticScopeMap scopeMap = StaticScopeMap.read(scopeMapFile);
        if (!scopeMap.stated()) {
            throw new IOException("static scope map states no site: "
                    + scopeMapFile);
        }
        Path skeletonFile = iteration.resolveSibling("seed-skeletons")
                .resolve(StaticScopeMap.REGIONS + ".gz");
        Map<String, StaticProgram.RegionRow> skeletons = new LinkedHashMap<>();
        for (StaticProgram.RegionRow skeleton : StaticProgram.regionRows(
                MapFields.readRows(skeletonFile.toFile()),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, skeletonFile)) {
            skeletons.put(skeleton.regionId, skeleton);
        }
        RuntimePlanArtifact frozen = RuntimePlanArtifact.read(
                iteration.resolve("concolic_region_plan.jsonl"));
        String replayGroupId = replayGroupId(
                iteration.resolve("execution_task_plan.jsonl"));

        List<JsonObject> regionCatalog = frozen.regions();
        List<RegionInstancePlan> regionPlans = new ArrayList<>(
                frozen.regionPlans());
        List<RegionInstancePlan> exposed = new ArrayList<>();
        List<String> exposedBy = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        int past = 0;
        for (JsonObject row : exposures) {
            OccurrenceAddress address = OccurrenceAddress.parse(
                    optionalString(row, "occurrence"));
            String regionId = address.regionId();
            String sessionId = optionalString(row, "sessionId");
            boolean edge = ZkChain.EDGE.equals(optionalString(row, "kind"));
            if (!edge && (!optionalString(row, "regionId").equals(regionId)
                    || !optionalString(row, "node").equals(
                    address.node().render()) || sessionId.isEmpty())) {
                throw new IOException("EXPOSED_REGION row contradicts its "
                        + "occurrence address or names no session: " + row);
            }
            if (!seen.add(address.render())) continue;
            if (exposed.size() >= room) {
                past++;
                continue;
            }
            StaticProgram.RegionRow skeleton = skeletons.get(regionId);
            if (skeleton == null && edge) {
                System.out.println(ZkChain.EDGE + " " + address.render()
                        + ": no candidate skeleton is " + regionId
                        + ", so no task holds it; its path joins the chain");
                continue;
            }
            if (skeleton == null) {
                throw new IOException("EXPOSED_REGION_UNKNOWN: no candidate "
                        + "skeleton is " + regionId + " (" + skeletonFile
                        + ")");
            }
            RegionInstancePlan plan = RegionInstancePlan.decode(
                    GSON.toJsonTree(planRow(skeleton, address, sessionId))
                            .getAsJsonObject());
            regionCatalog.add(GSON.toJsonTree(skeleton.json)
                    .getAsJsonObject());
            regionPlans.add(plan);
            exposed.add(plan);
            exposedBy.add(sessionId);
        }
        if (past > 0) pastBound(bound, planned.size() + exposed.size(), past);
        ConcolicScheduler.SymbolicInputSelection inputs =
                ConcolicScheduler.SymbolicInputSelection.read(scopeMap,
                        regionCatalog);
        LoopBoundPolicy loopBound = ConcolicScheduler.declaredLoopBounds(
                LoopBoundPolicy.declaredDefault(), regionPlans);
        List<JsonObject> rows = new ArrayList<>();
        DoorsOnlyRoots heavy = DoorsOnlyRoots.current();
        for (int index = 0; index < exposed.size(); index++) {
            RegionInstancePlan plan = exposed.get(index);
            RegionInstancePlan.Goal goal = plan.goal();
            Set<String> methods = goal.runtimeDefinitionMethods();
            JsonArray actions = ConcolicScheduler.materializationPlan(goal,
                    ConcolicScheduler.withDeclaredPorts(goal.symbolize(),
                            inputs.declaredSitePorts(plan, scopeMap, methods)),
                    scopeMap, methods);
            JsonArray branchMethods = new JsonArray();
            for (String method : methods) branchMethods.add(method);
            JsonObject task = ConcolicScheduler.regionPathTask(goal, actions,
                    branchMethods, loopBound, inputs).json();
            task.addProperty(ConcolicScheduler.REPLAY_GROUP_ID, replayGroupId);
            task.addProperty(RuntimeSelectedRegionFinalizer.ADMISSION_BASIS,
                    EXPOSED_BY + exposedBy.get(index));
            if (task.has("rootSelector") && heavy.holds(
                    JsonFields.optionalString(task.getAsJsonObject(
                            "rootSelector"), "method"))) {
                task.addProperty(RuntimeSelectedRegionFinalizer.DOORS_ONLY,
                        true);
                task.addProperty(
                        RuntimeSelectedRegionFinalizer.DOORS_ONLY_DECLARED,
                        true);
            }
            rows.add(task);
        }
        return rows;
    }

    private static void pastBound(int bound, int planned, int past) {
        System.out.println(EXPOSED_REGION + ": the plan holds " + planned
                + " of the campaign's " + bound + " tasks, so " + past
                + " exposed occurrence(s) are not tasked: the closure is "
                + "truncated there");
    }

    private static Map<String, Object> planRow(
            StaticProgram.RegionRow skeleton, OccurrenceAddress address,
            String sessionId) {
        String occurrenceId = address.render();
        String sourceKey = address.node().render();
        Map<String, List<Map<String, Object>>> cutPorts =
                RuntimeSelectedRegionFinalizer.cutPortRows(skeleton,
                        Collections.<Map<String, Object>>emptyList());
        Map<String, Object> regionJson = new LinkedHashMap<>(skeleton.json);
        regionJson.put("symbolicInputs", cutPorts.get("IN"));
        regionJson.put("outputs", cutPorts.get("OUT"));
        StaticProgram.RegionRow region = StaticProgram.regionRows(
                Collections.singletonList(regionJson),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                skeleton.regionId).get(0);
        RuntimeRegionPlanner.declareCutPortCells(region);

        Map<String, Object> rootSelector = new LinkedHashMap<>();
        rootSelector.put("method", skeleton.rootMethod);
        rootSelector.put("kind", "GLOBAL_INVOCATION");
        rootSelector.put("causalAnchor", RuntimeRegionPlanner.causalAnchor(
                address.node(), false, "", ""));
        rootSelector.put("invocationOrdinal", 1);

        Map<String, Object> goal = new LinkedHashMap<>();
        goal.put("goalId", "GOAL.REGION_PATH." + UUID.nameUUIDFromBytes(
                occurrenceId.getBytes(StandardCharsets.UTF_8)));
        goal.put("kind", ClosureGoalKind.REGION_PATH_CLOSURE.name());
        goal.put("runtimeDefinitionMethods", new ArrayList<>(skeleton.methods));
        Map<String, Object> admission = new LinkedHashMap<>();
        admission.put("state", "READY");
        admission.put("mode", EXPOSED_REGION);
        admission.put("blockers", Collections.emptyList());
        goal.put("admission", admission);
        goal.put("symbolize", RuntimeRegionPlanner.symbolize(
                region.symbolicInputs, occurrenceId));
        goal.put("branches", Collections.emptyList());

        Map<String, Object> plan = new LinkedHashMap<>();
        plan.put("schemaVersion", 3);
        plan.put("kind", "CONCOLIC_REGION_PLAN");
        plan.put("occurrenceId", occurrenceId);
        plan.put("regionId", skeleton.regionId);
        if (!skeleton.rootAuthority.isEmpty()) {
            plan.put(LoopBoundPolicy.ROOT_AUTHORITY, skeleton.rootAuthority);
        }
        if (skeleton.rootLoop != null) {
            plan.put(LoopBoundPolicy.ROOT_LOOP, skeleton.rootLoop);
        }
        plan.put("activationId", RuntimeRegionPlanner.activationId(
                occurrenceId, rootSelector));
        if (!skeleton.retainedLoops.isEmpty()) {
            plan.put(LoopBoundPolicy.PLAN_FIELD, skeleton.retainedLoops);
        }
        List<Map<String, Object>> handoffs =
                RuntimeRegionPlanner.attachSites(region);
        if (!handoffs.isEmpty()) {
            plan.put(CommunicationHandoffSpec.FIELD, handoffs);
        }
        plan.put("relationKey", RuntimeRegionPlanner.relationKey(
                address.node(), skeleton.regionId));
        plan.put("sourceKey", sourceKey);
        plan.put("rootSelector", rootSelector);
        if (!skeleton.anchorMethod.isEmpty()) {
            plan.put("targetMethod", skeleton.anchorMethod);
        }
        plan.put(RuntimeSelectedRegionFinalizer.ADMISSION_BASIS,
                EXPOSED_BY + sessionId);
        plan.put("closureGoals", Collections.singletonList(goal));
        return plan;
    }

    private static String replayGroupId(Path plan) throws IOException {
        String group = "";
        for (JsonObject task : ArtifactIO.readJsonl(plan)) {
            String named = optionalString(task,
                    ConcolicScheduler.REPLAY_GROUP_ID);
            if (named.isEmpty() || !group.isEmpty() && !group.equals(named)) {
                throw new IOException("the iteration plan names no single "
                        + "replayGroupId: " + plan);
            }
            group = named;
        }
        if (group.isEmpty()) {
            throw new IOException("the iteration plan holds no task: " + plan);
        }
        return group;
    }
}
