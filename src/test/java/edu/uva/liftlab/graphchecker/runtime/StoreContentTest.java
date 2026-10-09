package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.Test;

/**
 * A store version's content, leaf by leaf (PIPELINE §8): the leaves a
 * document is walked into, how each crosses, and the value a rendered leaf
 * crosses as.  The VM's export and mint are the smokes'.
 */
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

    /** A leaf's port is a site: no '/' or '@' (contract.Frame). */
    @Test
    public void aLeafsPortIsASite() {
        assertEquals("SOLR_ZK#CONTENT:|aliases.json#|collection_metadata"
                        + "|t|router.start%40x%7Cy",
                StoreContent.port("SOLR_ZK", "/aliases.json",
                        "/collection_metadata/t/router.start@x|y"));
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

    @Test
    public void aLeafCrossesByItsText() {
        Object[][] rows = {
                {"5", StoreContent.Kind.DEC_LONG},
                {"-12", StoreContent.Kind.DEC_LONG},
                {"007", StoreContent.Kind.STR},
                {"99999999999999999999", StoreContent.Kind.STR},
                {"false", StoreContent.Kind.BOOL},
                {"True", StoreContent.Kind.STR},
                {"down", StoreContent.Kind.STR},
                {3L, StoreContent.Kind.NUM},
                {Boolean.TRUE, StoreContent.Kind.NUM},
                {new LinkedHashMap<String, Object>(), null},
        };
        for (Object[] row : rows) {
            assertEquals(String.valueOf(row[0]), row[1],
                    StoreContent.kindOf(row[0]));
        }
    }

    /**
     * A rendered leaf crosses as the value it renders: a lone toString's
     * operand, the text read where the writer held a constant, else the
     * parse of what it held; a boolean computed otherwise crosses as text.
     */
    @Test
    public void aRenderedLeafCrossesAsItsValue() {
        JsonObject clock = symbol("M_J_clock", "J");
        assertEquals(clock, StoreContent.rendered(string("toString", clock),
                StoreContent.Kind.DEC_LONG, "17"));
        JsonObject constant = StoreContent.rendered(text("17"),
                StoreContent.Kind.DEC_LONG, "17");
        assertEquals("Y_J_17", constant.get("_exp").getAsString());
        JsonObject attached = symbol("M_L'String'_h", "java/lang/String");
        JsonObject parse = StoreContent.rendered(attached,
                StoreContent.Kind.DEC_LONG, "17");
        assertEquals("java/lang/Long parseLong",
                parse.get("_name").getAsString());
        assertEquals(attached, parse.getAsJsonArray("_param_list").get(0));
        assertNull(StoreContent.rendered(attached, StoreContent.Kind.BOOL,
                "true"));
    }

    @Test
    public void outsideAReplayNothingIsCaptured() {
        assertFalse(StoreContent.capturing());
        byte[] bytes = new byte[] {'{', '}'};
        StoreContent.written(bytes, single("a", "b"));
        StoreContent.fetched("T", "/x@1", bytes);
        Map<String, Object> tree = single("a", "b");
        StoreContent.parsed(bytes, tree);
        assertEquals("b", tree.get("a"));
        StoreContent.resetForTests();
    }

    private static Map<String, Object> single(String key, Object value) {
        Map<String, Object> map = new LinkedHashMap<String, Object>();
        map.put(key, value);
        return map;
    }

    private static JsonObject symbol(String name, String javaType) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        node.addProperty("_java_type", javaType);
        return node;
    }

    private static JsonObject text(String value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConStringSymbolExp");
        node.addProperty("_exp", "Y_L'String'_" + value);
        node.addProperty("_java_type", "java/lang/String");
        return node;
    }

    private static JsonObject string(String name, JsonObject... params) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "OpStrExpression");
        node.addProperty("_name", name);
        node.addProperty("_is_not", false);
        JsonArray list = new JsonArray();
        for (JsonObject param : params) list.add(param);
        node.add("_param_list", list);
        return node;
    }
}
