package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class ScopeGrowthTest {
    private static final String T = ScopeGrowthTest.class.getName();
    private static final String GET = "<" + T + "$Store: long get()>";
    private static final String SHARED = "<" + T + "$Holder: long shared>";

    @Test
    public void theFrontierIsWhereTheSliceStopsNearestFirst() {
        String set = "<" + T + "$Holder: void set(long)>";
        List<Map<String, Object>> edges = Arrays.asList(
                edge("exception_throw", "m::$r9", "m#u9#exception:E", ""),
                edge("local_def_use", "m::$l3", "m::$r9", ""),
                edge("call_return", "<B: java.lang.String say()>.return",
                        "m::$l3", "<B: java.lang.String say()>"),
                edge("exception_guard", "m::$z0", "m#u9#exception:E", ""),
                edge("local_def_use", "m::$l1", "m::$z0", ""),
                edge("local_def_use", "<M: void m(long)>.param0:long",
                        "m::$l1", ""),
                edge("call_return", GET + ".return", "m::$l1", GET),
                edge("field_read", SHARED, "m::$z0", ""),
                edge("field_write", set + ".param0:long", SHARED, ""),
                edge("field_write", "<R: void readFields(java.io.DataInput)>"
                        + ".param0:java.io.DataInput", SHARED, ""),
                edge("call_return", "<C: long now()>.return", "m::$l1",
                        "<C: long now()>"),
                edge("call_return", "<A: long own()>.return", "m::$l1",
                        "<A: long own()>"),
                edge("field_write", "w::$l0", "<W: long far>", ""));
        List<String> found = new ArrayList<>();
        String save = "<" + T + "$Saver: void save(java.io.File)>";
        Map<String, StaticScopeMap.Demanded> demanded = new LinkedHashMap<>();
        demanded.put(set, new StaticScopeMap.Demanded("SCOPE", 3, true));
        demanded.put(SHARED, new StaticScopeMap.Demanded("PRE_WINDOW", 1,
                true));
        demanded.put(save, new StaticScopeMap.Demanded("IO", 5, true));
        for (JsonObject row : ScopeFrontier.rows(edges,
                "<A: long own()>"::equals,
                Collections.singleton("<C: long now()>"), demanded)) {
            found.add(row.get("kind").getAsString() + " "
                    + row.get("signature").getAsString() + " "
                    + row.get("distance").getAsInt()
                    + (row.has("demand") ? " " + row.get("demand")
                    .getAsString() : ""));
        }
        assertEquals(Arrays.asList(
                "FIELD " + SHARED + " 1 PRE_WINDOW",
                "FORMAL " + set + " 3 SCOPE",
                "CALLEE " + save + " 5 IO",
                "CALLEE " + GET + " 2"), found);
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        if (!invoke.isEmpty()) edge.put("invoke", invoke);
        return edge;
    }
}
