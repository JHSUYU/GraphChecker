package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.Clock;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRootPolicyTest {

    private static final String NN = "REGION.nn";
    private static final String DN = "REGION.dn";
    private static final Clock WALL_MS = Clock.of(1_000_000L, Clock.WALL);
    private static final String TIMER_NOW =
            "<org.apache.hadoop.util.Timer: long now()>";
    private static final String CLOCK_CELL = TIMER_NOW + ".return";
    private static final String EXPIRE =
            "<C: void removeExpiredKeys()>";
    private static final String KEY_ID = "<org.apache.hadoop.security.token"
            + ".delegation.DelegationKey: int keyId>";
    private static final String ROOT = InputActionCatalog
            .DECLARED_SYMBOLIC_ROOT;
    private static final String GET_NUM = "<S: int getNumSnapshots()>";
    private static final String GET_NUM_LOCAL = GET_NUM + "::$i0";
    private static final String FILE = "<S: org.x.LongFile committed>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void onlyARootMakesAReadSymbolic() throws Exception {
        StaticScopeMap map = map(Arrays.asList(clockRead(EXPIRE)),
                Collections.singletonMap(NN, Collections.singletonList(
                        EXPIRE)), Collections.singletonMap(TIMER_NOW, WALL_MS),
                method -> true);
        assertEquals(Collections.singletonMap(TIMER_NOW, WALL_MS),
                map.clocks());
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(map,
                        catalog());
        JsonArray selected = selection.select(NN, proposals());

        assertTrue("the clock carries the mint marker",
                selected.get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        assertEquals("and the clock's tick, read off its category",
                1_000_000L, selected.get(0).getAsJsonObject()
                        .get(InputActionCatalog.DECLARED_WALL_CLOCK)
                        .getAsLong());
        assertEquals("and the JVM clock it wraps: tick and source are one "
                        + "clock's identity", Clock.WALL,
                member(selected, 0, InputActionCatalog.DECLARED_CLOCK_SOURCE));
        assertEquals("a read no category names is concrete by name",
                "CONCRETE", member(selected, 1, "mode"));
        assertEquals(ConcolicScheduler.SymbolicInputSelection.UNDECLARED,
                member(selected, 1, "symbolicDemand"));
        assertEquals("the fault marker stays symbolic",
                "SYMBOLIC", member(selected, 2, "mode"));
        assertTrue("and is a root: the program's text states it",
                selected.get(2).getAsJsonObject().get(ROOT).getAsBoolean());
        JsonArray actions = proposals();
        actions.add(action("COMMUNICATION_SITE_PORT", "<C: int getKeyId()>#u2",
                "<C: int getKeyId()>.return"));
        JsonObject cut = selection.select(DN, actions).get(3).getAsJsonObject();
        assertEquals("SYMBOLIC", cut.get("mode").getAsString());
        assertFalse("a cut port is not a root", cut.has(ROOT));

        JsonObject port = action("EXTERNAL_CALL_RETURN", GET_NUM + "#u2",
                GET_NUM_LOCAL);
        ConcolicScheduler.SymbolicInputSelection renamed = clockOf(GET_NUM);
        renamed.resolveDeclaredNames(Collections.singletonList(
                copy("SOOT_EXACT_LOCAL_DIRECT_COPY_V1")));
        assertTrue("the proven rename selects the port",
                renamed.select(NN, actions(port)).get(0).getAsJsonObject()
                        .get(ROOT).getAsBoolean());
        ConcolicScheduler.SymbolicInputSelection unproven = clockOf(GET_NUM);
        unproven.resolveDeclaredNames(Collections.singletonList(copy("")));
        assertFalse("an edge Soot did not prove a copy is not a rename",
                unproven.select(NN, actions(port)).get(0).getAsJsonObject()
                        .has(ROOT));
    }

    private static Map<String, Object> read(String cell, int unitIndex,
                                            String local) {
        return edge("{\"kind\":\"field_read\",\"method\":\"" + GET_NUM
                + "\",\"unitIndex\":" + unitIndex + ",\"fromCell\":\""
                + cell + "\",\"toCell\":\"" + GET_NUM + "::" + local
                + "\"}");
    }

    private StaticScopeMap map(List<Map<String, Object>> edges,
                               Map<String, List<String>> regionMethods,
                               Map<String, Clock> clocks,
                               Predicate<String> unwoven)
            throws IOException {
        return map(edges, regionMethods, clocks, unwoven,
                cell -> SharedFieldFlow.TrackedKind.VALUE,
                (demandSite, demandCell) -> null);
    }

    private StaticScopeMap map(List<Map<String, Object>> edges,
                               Map<String, List<String>> regionMethods,
                               Map<String, Clock> clocks,
                               Predicate<String> unwoven,
                               java.util.function.Function<String,
                                       SharedFieldFlow.TrackedKind> kinds,
                               StaticScopeMap.Demand demand)
            throws IOException {
        List<Map<String, Object>> regions = new java.util.ArrayList<>();
        for (Map.Entry<String, List<String>> region
                : regionMethods.entrySet()) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("regionId", region.getKey());
            row.put("methods", region.getValue());
            regions.add(row);
        }
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(StaticScopeMap.sites(edges,
                regions, clocks, (m, u, c) -> null, demand, unwoven,
                kinds, cell -> false, cell -> false),
                null, method -> false)) {
            text.append(row.toString()).append('\n');
        }
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    private ConcolicScheduler.SymbolicInputSelection clockOf(String callee)
            throws IOException {
        return ConcolicScheduler.SymbolicInputSelection.read(map(
                Arrays.asList(clockRead(callee, EXPIRE)),
                Collections.singletonMap(NN, Collections.singletonList(
                        EXPIRE)), Collections.singletonMap(callee, WALL_MS),
                method -> true), catalog());
    }

    private static Map<String, Object> clockRead(String method) {
        return clockRead(TIMER_NOW, method);
    }

    private static Map<String, Object> clockRead(String callee,
                                                 String method) {
        return edge("{\"kind\":\"call_return\",\"method\":\"" + method
                + "\",\"unitIndex\":2,\"invoke\":\"" + callee
                + "\",\"fromCell\":\"" + callee + ".return\",\"toCell\":\""
                + method + "::$l0\"}");
    }

    private static JsonObject copy(String authority) {
        JsonObject edge = json("{\"kind\":\"local_def_use\",\"transferKind\":"
                + "\"VALUE_PASS\",\"fromCell\":\"" + GET_NUM_LOCAL
                + "\",\"toCell\":\"" + GET_NUM + ".return\"}");
        if (!authority.isEmpty()) {
            edge.addProperty("valueFlowAuthority", authority);
        }
        return edge;
    }

    private static Map<String, Object> edge(String row) {
        Map<String, Object> edge = new LinkedHashMap<>();
        for (Map.Entry<String, com.google.gson.JsonElement> member
                : json(row).entrySet()) {
            edge.put(member.getKey(), member.getValue().getAsJsonPrimitive()
                    .isNumber() ? (Object) member.getValue().getAsInt()
                    : member.getValue().getAsString());
        }
        return edge;
    }

    private static List<JsonObject> catalog() {
        return Arrays.asList(json("{\"regionId\":\"" + NN + "\"}"),
                json("{\"regionId\":\"" + DN + "\"}"));
    }

    private static JsonArray proposals() {
        JsonArray actions = new JsonArray();
        JsonObject clock = action("EXTERNAL_CALL_RETURN", EXPIRE + "#u2",
                CLOCK_CELL);
        clock.addProperty("declaredCallee", TIMER_NOW);
        actions.add(clock);
        JsonObject field = action("ACCESSOR_RETURN", "<C: boolean f()>#u9",
                KEY_ID);
        field.addProperty("accessFieldSignature", KEY_ID);
        actions.add(field);
        actions.add(action("EXPLICIT_SYMBOLIC_FAULT",
                "<C: void sendRpcRequest(D)>#u17",
                "<C: void sendRpcRequest(D)>::$z5"));
        return actions;
    }

    private static JsonArray actions(JsonObject action) {
        JsonArray actions = new JsonArray();
        actions.add(action.deepCopy());
        return actions;
    }

    private static JsonObject action(String sourceKind, String siteId,
            String cell) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":\""
                + sourceKind + "\",\"siteId\":\"" + siteId
                + "\",\"portId\":\"port." + siteId + "\",\"symbol\":\"port."
                + siteId + "\",\"cell\":\"" + cell + "\"}");
    }

    private static String member(JsonArray rows, int index, String name) {
        JsonObject row = rows.get(index).getAsJsonObject();
        return row.has(name) ? row.get(name).getAsString() : "";
    }

    private static JsonObject json(String row) {
        return JsonParser.parseString(row).getAsJsonObject();
    }
}
