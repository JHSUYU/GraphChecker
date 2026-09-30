package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * One recording, several targets (the pre-screen, tools/adhoc/prescreen.sh):
 * each target is aggregated on its own slice and its own skeletons, and a
 * target the recording does not serve is refused alone.
 *
 * <p>The recording: a SASL handler opens an occurrence and the key lookup
 * folds into it, deciding its guard.  Target {@code lookup} throws below that
 * guard; target {@code other} throws in a method the recording never ran,
 * and its skeletons know the lookup's region as state only -- asked of the
 * weave's union, where {@code lookup} makes that region an exception context,
 * it would have been taken for {@code other}'s own.</p>
 */
public class MultiTargetAggregationTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final String HANDLER =
            "<o.a.h.SaslDataTransferServer: void handle()>";
    private static final String LEAF = "<o.a.h.BlockTokenSecretManager: "
            + "byte[] retrieveDataEncryptionKey(int,byte[])>";
    private static final String OTHER =
            "<o.a.h.BlockTokenSecretManager: void checkAccess()>";
    private static final String HANDLER_REGION = "REGION.handler";
    private static final String LEAF_REGION = "REGION.leaf";
    private static final String OTHER_REGION = "REGION.other";
    private static final String GUARD = LEAF + "#u5";
    private static final String ADDRESS = OccurrenceAddress.of(
            NodeId.parse("wl/dn1#epoch0"), HANDLER_REGION,
            CausalContext.of(Role.of("SASL"), "", 1),
            ExecutionIndex.empty()).render();

    /**
     * Per target: its throw's method, its guard's fatal arm, the region its
     * skeletons call its exception context, and what the recording holds for
     * it.  The recording took the guard's true arm.
     */
    @Test
    public void eachTargetIsAggregatedOnItsOwnSliceAndRefusedAlone()
            throws Exception {
        Object[][] targets = {
                {"lookup", LEAF, true, LEAF_REGION,
                        "ACTIVATED", true, ADDRESS},
                {"lookup-healthy", LEAF, false, LEAF_REGION,
                        "ACTIVATED", false, ADDRESS},
                {"other", OTHER, true, OTHER_REGION,
                        "NOT_IN_WINDOW", false, null},
        };
        List<CausynthTraceRecorder.AggregationTarget> aggregated =
                new ArrayList<>();
        for (Object[] target : targets) {
            aggregated.add(target((String) target[0], (String) target[1],
                    (Boolean) target[2], (String) target[3]));
        }
        Map<String, CausynthTraceRecorder.TargetOutcome> outcomes =
                withLoopBound(() -> CausynthTraceRecorder.aggregateTargets(
                        recording(), aggregated));
        for (Object[] target : targets) {
            CausynthTraceRecorder.TargetOutcome outcome =
                    outcomes.get((String) target[0]);
            assertEquals(target[0] + ": " + outcome.detail, target[4],
                    outcome.state);
            assertEquals(target[0] + " took the fatal arm", target[5],
                    outcome.fatalArmObserved);
            assertEquals(target[0] + "'s target occurrences",
                    target[6] == null ? Collections.emptyList()
                            : Collections.singletonList(target[6]),
                    outcome.occurrences);
        }
        try {
            CausynthTraceRecorder.AggregationTarget.parse("a=graph,map,out");
            fail("a target states its skeletons");
        } catch (IllegalArgumentException refused) {
            // <name>=<candidate-graph>,<static-scope-map>,<skeletons>,<out>
        }
    }

    /** One target's static slice on disk: skeletons in which only its own
     *  throw's region is an exception context, the guard edge, and the scope
     *  map's TARGET_SITE with the guard's fatal arm. */
    private CausynthTraceRecorder.AggregationTarget target(
            String name, String thrower, boolean fatalArm, String context)
            throws Exception {
        File dir = folder.newFolder(name);
        List<Map<String, Object>> skeletons = Arrays.asList(
                skeleton(HANDLER_REGION, HANDLER, context),
                skeleton(LEAF_REGION, LEAF, context),
                skeleton(OTHER_REGION, OTHER, context));
        File skeletonFile = write(new File(dir, "region_skeletons.jsonl"),
                skeletons);
        String guard = thrower + "#u5";
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 3);
        edge.put("kind", "exception_guard");
        edge.put("transferKind", "GUARD");
        edge.put("fromCell", thrower + "::r1");
        edge.put("toCell", guard + "#exception:o.a.h.Invalid");
        edge.put("method", thrower);
        edge.put("siteId", guard);
        edge.put("unitIndex", 5);
        File graph = write(new File(dir, "candidate_dataflow_edges.jsonl"),
                Collections.singletonList(edge));
        Map<String, Object> thrown = new LinkedHashMap<>();
        thrown.put("kind", "exception_throw");
        thrown.put("method", thrower);
        thrown.put("unitIndex", 7);
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", context);
        region.put("methods", Collections.singletonList(thrower));
        StringBuilder map = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(StaticScopeMap.sites(
                Collections.singletonList(thrown),
                Collections.singletonList(region),
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), method -> false,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false),
                site -> Collections.singletonList(
                        new StaticScopeMap.Guard(guard, fatalArm)))) {
            map.append(row).append('\n');
        }
        File scopeMap = new File(dir, StaticScopeMap.FILE);
        Files.write(scopeMap.toPath(),
                map.toString().getBytes(StandardCharsets.UTF_8));
        return new CausynthTraceRecorder.AggregationTarget(name, graph,
                scopeMap, skeletonFile, new File(dir, "runtime"));
    }

    private static Map<String, Object> skeleton(String regionId, String root,
                                                String context) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        row.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        row.put("regionId", regionId);
        row.put("rootMethod", root);
        row.put("rootAuthority", "STATE_WRITER_ENTRY");
        row.put("anchorMethod", root);
        row.put("anchorMethods", Collections.singletonList(root));
        row.put("selection", regionId.equals(context)
                ? "EXCEPTION_CONTEXT" : "STATE_CONTEXT");
        row.put("methods", Collections.singletonList(root));
        return row;
    }

    /** The handler's occurrence, the lookup folded into it, and the guard's
     *  decision there. */
    private static CausynthTraceRecorder.TraceData recording() {
        CausynthTraceRecorder.TraceData trace =
                new CausynthTraceRecorder.TraceData();
        trace.methods.add(entry(10L, HANDLER, 0L, ADDRESS, false));
        trace.methods.add(entry(20L, LEAF, 10L, "", true));
        trace.execution.add(new RuntimeRegionPlanner.RuntimeEvent(5L,
                "BRANCH", LEAF, 20L, 0L, GUARD, "", -1, "", 0, "",
                Boolean.TRUE, null, "IF", ""));
        return trace;
    }

    private static RuntimeRegionPlanner.MethodEvent entry(
            long callId, String method, long parentCallId, String address,
            boolean folded) {
        return new RuntimeRegionPlanner.MethodEvent(callId, "test", "main",
                1L, method, 1, "o.a.h.BlockTokenSecretManager", callId,
                parentCallId, 0L, 1L, 1L, 0L,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true, "", "",
                address, folded);
    }

    private static File write(File file, List<Map<String, Object>> rows)
            throws Exception {
        StringBuilder text = new StringBuilder();
        for (Map<String, Object> row : rows) {
            text.append(new Gson().toJson(row)).append('\n');
        }
        Files.write(file.toPath(), text.toString().getBytes(
                StandardCharsets.UTF_8));
        return file;
    }

    private interface Body<T> {
        T run() throws Exception;
    }

    /** The plan builder refuses to invent the campaign's loop bound; this
     *  fixture declares no loop, so any bound serves. */
    private static <T> T withLoopBound(Body<T> body) throws Exception {
        String bound = System.getProperty("causynth.loop.default.bound");
        System.setProperty("causynth.loop.default.bound", "8");
        try {
            return body.run();
        } finally {
            if (bound == null) {
                System.clearProperty("causynth.loop.default.bound");
            } else {
                System.setProperty("causynth.loop.default.bound", bound);
            }
        }
    }
}
