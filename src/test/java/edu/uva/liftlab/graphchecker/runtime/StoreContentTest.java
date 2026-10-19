package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Test;

public class StoreContentTest {
    @Test
    public void aDocumentIsItsLeavesByJsonPointer() {
        Map<String, Object> replica = new LinkedHashMap<String, Object>();
        replica.put("state", "active");
        replica.put("leader", "true");
        Map<String, Object> rule = new LinkedHashMap<String, Object>();
        rule.put("expireAt", "1700000000123");
        Map<String, Object> shard = new LinkedHashMap<String, Object>();
        shard.put("replicas", single("core_node2", replica));
        shard.put("routingRules", single("a/b!", rule));
        shard.put("range", Arrays.asList("80000000-ffffffff", 7L));
        List<String> pointers = new ArrayList<String>();
        for (StoreContent.Leaf leaf : StoreContent.leaves("SOLR_ZK",
                "/collections/c/state.json", single("c", single("shards",
                        single("shard1", shard))))) {
            pointers.add(leaf.pointer + "=" + leaf.value + ":"
                    + StoreContent.kindOf(leaf.value));
        }
        assertEquals(Arrays.asList(
                "/c/shards/shard1/replicas/core_node2/state=active:STR",
                "/c/shards/shard1/replicas/core_node2/leader=true:BOOL",
                "/c/shards/shard1/routingRules/a~1b!/expireAt"
                        + "=1700000000123:DEC_LONG",
                "/c/shards/shard1/range/0=80000000-ffffffff:STR",
                "/c/shards/shard1/range/1=7:NUM"), pointers);
    }

    @Test
    public void aDocumentPastItsBoundCrossesTheRestAsConstants() {
        Map<String, Object> wide = new LinkedHashMap<String, Object>();
        for (int at = 0; at < StoreContent.MAX_LEAVES + 5; at++) {
            wide.put("k" + at, "v");
        }
        assertEquals(StoreContent.MAX_LEAVES,
                StoreContent.leaves("T", "/w", wide).size());
        Object deep = "leaf";
        for (int level = 0; level < StoreContent.MAX_DEPTH + 2; level++) {
            deep = single("d", deep);
        }
        assertEquals(0, StoreContent.leaves("T", "/d", deep).size());
    }

    private static Map<String, Object> single(String key, Object value) {
        Map<String, Object> map = new LinkedHashMap<String, Object>();
        map.put(key, value);
        return map;
    }
}
