package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.runtime.RuntimeRegionPlanner;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.io.IOException;
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
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/** Execution-task rows for occurrences a replay EXPOSED in a region the
 *  recording never planned (DESIGN4 section 3.3b): {@code --iteration <dir>
 *  --growth <growth.jsonl> --output <jsonl>}. Each growth row becomes one
 *  region-path task on that exact address, with static inputs only (cut ports,
 *  declared CALL_RETURN sites), sharing the iteration plan's {@code
 *  replayGroupId}. */
public final class ExposedRegionPlanMain {
    /** The growth row kind this main answers. */
    public static final String EXPOSED_REGION = "EXPOSED_REGION";
    /** Prefix of the admission basis of an exposed occurrence's row. */
    public static final String EXPOSED_BY = "EXPOSED_BY:";

    private static final Gson GSON = new Gson();

    private ExposedRegionPlanMain() {
    }

    public static void main(String[] args) throws Exception {
        Map<String, String> values = ConcolicScheduler.parseArgs(args,
                "iteration", "growth", "output");
        Path iteration = required(values, "iteration");
        Path growth = required(values, "growth");
        Path output = required(values, "output");
        ArtifactIO.replaceJsonl(output, plan(iteration,
                ArtifactIO.readJsonl(growth)));
    }

    static List<JsonObject> plan(Path iteration, List<JsonObject> growth)
            throws IOException {
        JsonObject provenance = object(GSON.fromJson(new String(
                Files.readAllBytes(iteration.resolve(
                        "iteration_manifest.json")), StandardCharsets.UTF_8),
                JsonObject.class), "provenance");
        Path catalog = Paths.get(optionalString(
                object(provenance, "staticCatalog"), "path"));
        Path symbolicInputs = Paths.get(optionalString(
                object(provenance, "symbolicInputs"), "path"));
        StaticScopeMap scopeMap = StaticScopeMap.read(
                catalog.resolveSibling("static_scope_map.jsonl"));
        if (!scopeMap.stated()) {
            throw new IOException("static scope map states no site beside "
                    + catalog);
        }
        Path skeletonFile = iteration.resolveSibling("seed-skeletons")
                .resolve("region_skeletons.jsonl.gz");
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

        // Plan all exposed occurrences before selecting: selection scopes over
        // planned regions.
        List<JsonObject> regionCatalog = frozen.regions();
        List<RegionInstancePlan> regionPlans = new ArrayList<>(
                frozen.regionPlans());
        List<RegionInstancePlan> exposed = new ArrayList<>();
        List<String> exposedBy = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        for (JsonObject row : growth) {
            if (!EXPOSED_REGION.equals(optionalString(row, "kind"))) continue;
            OccurrenceAddress address = OccurrenceAddress.parse(
                    optionalString(row, "occurrence"));
            String regionId = optionalString(row, "regionId");
            String sessionId = optionalString(row, "sessionId");
            if (!regionId.equals(address.regionId())
                    || !optionalString(row, "node").equals(
                    address.node().render()) || sessionId.isEmpty()) {
                throw new IOException("EXPOSED_REGION row contradicts its "
                        + "occurrence address or names no session: " + row);
            }
            if (!seen.add(address.render())) continue;
            StaticProgram.RegionRow skeleton = skeletons.get(regionId);
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
        ConcolicScheduler.SymbolicInputSelection inputs =
                ConcolicScheduler.SymbolicInputSelection.read(symbolicInputs,
                        regionCatalog, regionPlans);
        LoopBoundPolicy loopBound = ConcolicScheduler.declaredLoopBounds(
                LoopBoundPolicy.declaredDefault(), exposed);
        List<JsonObject> rows = new ArrayList<>();
        for (int index = 0; index < exposed.size(); index++) {
            RegionInstancePlan plan = exposed.get(index);
            RegionInstancePlan.Goal goal = plan.goals().get(0);
            Set<String> methods = goal.runtimeDefinitionMethods();
            JsonArray actions = ConcolicScheduler.materializationPlan(goal,
                    ConcolicScheduler.withDeclaredPorts(goal.symbolize(),
                            inputs.declaredSitePorts(plan, scopeMap, methods)),
                    scopeMap, methods);
            JsonArray branchMethods = new JsonArray();
            for (String method : methods) branchMethods.add(method);
            JsonObject task = ConcolicScheduler.regionPathTask(goal, actions,
                    branchMethods, loopBound, inputs).json();
            task.addProperty("replayGroupId", replayGroupId);
            task.addProperty(RuntimeSelectedRegionFinalizer.ADMISSION_BASIS,
                    EXPOSED_BY + exposedBy.get(index));
            rows.add(task);
        }
        return rows;
    }

    /** The region-plan row of an exposed occurrence: RuntimeRegionPlanner's
     *  shape minus recorded facts. */
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

        Map<String, Object> anchor = new LinkedHashMap<>();
        anchor.put("sourceKey", sourceKey);
        anchor.put("kind", RuntimeRegionPlanner.UNREGISTERED_SOURCE.key()
                .equals(sourceKey)
                ? RuntimeRegionPlanner.ANCHOR_UNREGISTERED_SOURCE
                : RuntimeRegionPlanner.ANCHOR_INHERITED_CONTEXT);
        // The selector names root method and anchor node, no receiver class.
        Map<String, Object> rootSelector = new LinkedHashMap<>();
        rootSelector.put("method", skeleton.rootMethod);
        rootSelector.put("kind", "GLOBAL_INVOCATION");
        rootSelector.put("causalAnchor", anchor);
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
                RuntimeRegionPlanner.communicationHandoffSites(region);
        if (!handoffs.isEmpty()) {
            plan.put(CommunicationHandoffSpec.FIELD, handoffs);
        }
        plan.put("relationKey", address.node().node() + "/relation/"
                + skeleton.regionId);
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

    /** The one ledger every task of the iteration's plan names. */
    private static String replayGroupId(Path plan) throws IOException {
        String group = "";
        for (JsonObject task : ArtifactIO.readJsonl(plan)) {
            String named = optionalString(task, "replayGroupId");
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

    private static Path required(Map<String, String> values, String key) {
        String value = values.get(key);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("Missing --" + key);
        }
        return Paths.get(value);
    }
}
