package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.WireDeclarations;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.Test;

/**
 * One codec's reading of a message graph (WIRE-CODEC §4.2), one row per
 * shape: which leaves of demanded ports an encode finds, by which slot, what
 * it names instead of guessing, and the slot a decode resolves a path to.
 */
public class CodecWalkerTest {
    private static final String TEST = CodecWalkerTest.class.getName();

    /** An application object whose JSON is its own map (ZkNodeProps). */
    static class Props {
        final Map<String, Object> props = new LinkedHashMap<>();

        Props put(String key, Object value) {
            props.put(key, value);
            return this;
        }

        public Map<String, Object> getProperties() {
            return props;
        }
    }

    /** A subclass the base's view covers (Slice, RoutingRule). */
    static final class Rule extends Props {
    }

    /** Its map plus one extra key (DocCollection's "shards"). */
    static final class Coll extends Props {
        final Map<String, Object> slices = new LinkedHashMap<>();

        public Map<String, Object> getSlices() {
            return slices;
        }
    }

    /** One leaf rendered by an accessor (DocRouter.Range). */
    static final class Range {
        @Override
        public String toString() {
            return new String("80000000-ffffffff");
        }
    }

    /** A flat name/value list (NamedList). */
    static final class Pairs {
        final List<Object> nvPairs = new ArrayList<>();
    }

    /** An object no view declares. */
    static final class Opaque {
    }

    /** Stands for protobuf-java's generated base. */
    abstract static class GeneratedMessageV3 {
    }

    static final class KeyProto extends GeneratedMessageV3 {
        private int bitField0_ = 3;
        private int keyId_;
        private long expiryDate_;

        KeyProto(int keyId, long expiryDate) {
            keyId_ = keyId;
            expiryDate_ = expiryDate;
        }
    }

    static final class KeysProto extends GeneratedMessageV3 {
        private KeyProto currentKey_;
        private List<KeyProto> allKeys_;
        private List<Long> stamps_ = Arrays.asList(5L);
    }

    static final class HeartbeatProto extends GeneratedMessageV3 {
        private int state_ = 1;
    }

    @Test
    public void aWalkFindsTheLeavesOfDemandedPortsBySlot() {
        Rule rule = new Rule();
        rule.put("expireAt", new String("1727")).put("target", "t");
        Rule slice = new Rule();
        slice.put("range", new Range()).put("routingRules",
                singleton("k!", rule));
        Coll coll = new Coll();
        coll.put("router", "compositeId");
        coll.slices.put("S", slice);

        Pairs pairs = new Pairs();
        pairs.nvPairs.addAll(Arrays.<Object>asList("generation", 5L,
                "other", 1L, "generation", 6L));

        Map<String, Object> cyclic = new LinkedHashMap<>();
        cyclic.put("expireAt", "1");
        cyclic.put("self", cyclic);

        KeysProto keys = new KeysProto();
        keys.currentKey_ = new KeyProto(7, 1727L);
        keys.allKeys_ = Arrays.asList(new KeyProto(8, 1L),
                new KeyProto(9, 2L));

        Map<String, Object> nulls = new LinkedHashMap<>();
        nulls.put("expireAt", null);

        Object[][] rows = {
            // name, codec, graph, demanded keys, leaves "path HOLDING key"
            {"views, a subclass's, an extra key, a rendered leaf", "JSON",
                    singleton("C", coll), keys("expireAt", "range"),
                    Arrays.asList(
                            "/C/shards/S/range VIEW range",
                            "/C/shards/S/routingRules/k!/expireAt ENTRY "
                                    + "expireAt")},
            {"an index keeps the key above it", "JSON",
                    singleton("generation", new String[]{"5", "6"}),
                    keys("generation"), Arrays.asList(
                            "/generation[0] ELEMENT generation",
                            "/generation[1] ELEMENT generation")},
            {"an ordered collection's position", "JSON",
                    singleton("generation", new ArrayList<>(
                            Collections.singletonList("5"))),
                    keys("generation"), Collections.singletonList(
                            "/generation[0] POSITION generation")},
            {"a flat name/value list, a repeated name", "JSON", pairs,
                    keys("generation"), Arrays.asList(
                            "/generation POSITION generation",
                            "/generation#1 POSITION generation")},
            {"a graph that reaches itself is walked once", "JSON", cyclic,
                    keys("expireAt"), Collections.singletonList(
                            "/expireAt ENTRY expireAt")},
            {"an undemanded key is no leaf", "JSON", singleton("C", coll),
                    keys("name"), Collections.emptyList()},
            {"a message's fields, nested and repeated", "PB", keys,
                    keys("KeyProto.keyId"), Arrays.asList(
                            "/currentKey/keyId FIELD KeyProto.keyId",
                            "/allKeys[0]/keyId FIELD KeyProto.keyId",
                            "/allKeys[1]/keyId FIELD KeyProto.keyId")},
            {"the graph is one leaf", "NAME", new String("7:user"),
                    keys("NAME"), Collections.singletonList(" ROOT NAME")},
        };
        for (Object[] row : rows) {
            CodecWalker.Walk walk = walker((String) row[1],
                    (Set<String>) row[3]).leaves(row[2]);
            List<String> found = new ArrayList<>();
            for (CodecWalker.Leaf leaf : walk.leaves) {
                found.add(CodecWalker.text(leaf.path) + " " + leaf.holding
                        + " " + leaf.key);
            }
            assertEquals((String) row[0], row[4], found);
            assertTrue(row[0] + ": " + walk.bound, walk.bound.isEmpty());
        }

        // What a walk names instead of guessing.
        Map<String, Object> named = new LinkedHashMap<>();
        named.put("opaque", new Opaque());
        named.put("tags", new HashSet<>(Collections.singletonList("x")));
        named.put("expireAt", null);
        CodecWalker json = walker("JSON", keys("expireAt", "tags"));
        CodecWalker.Walk walk = json.leaves(named);
        assertEquals(Collections.singleton(Opaque.class.getName()),
                walk.viewMissing);
        assertEquals(Collections.singletonList("/tags[0]"),
                walk.unaddressable);
        assertEquals(Collections.singletonList("/expireAt"),
                walk.nullLeaves);
        assertEquals(Collections.singletonList("KeysProto.stamps holds a "
                + "java.util.Arrays$ArrayList"), walker("PB",
                keys("KeysProto.stamps")).leaves(keys).unsupported);
        // A payload whose class reaches no demanded port is not walked.
        assertEquals(0, walker("PB", keys("KeyProto.keyId"))
                .leaves(new HeartbeatProto()).nodes);

        // Bounds are named with the first path they left unvisited.
        Map<String, Object> deep = new LinkedHashMap<>();
        Map<String, Object> at = deep;
        for (int depth = 0; depth < 40; depth++) {
            Map<String, Object> next = new LinkedHashMap<>();
            at.put("d", next);
            at = next;
        }
        String bound = json.leaves(deep).bound;
        assertTrue(bound, bound.startsWith("the path is 32 components deep;"
                + " first unvisited: /d/d"));
        List<Object> wide = new ArrayList<>();
        for (int index = 0; index < CodecWalker.MAX_NODES; index++) {
            wide.add(new ArrayList<>());
        }
        assertTrue(json.leaves(wide).bound.startsWith("the walk visited "
                + CodecWalker.MAX_NODES + " nodes"));
    }

    @Test
    public void aDecodeResolvesAPathToItsSlotAndStoresThroughItsHolder() {
        Map<String, Object> rule = new LinkedHashMap<>();
        rule.put("expireAt", new String("1727"));
        Map<String, Object> graph = singleton("C", singleton("shards",
                singleton("S", singleton("routingRules",
                        singleton("k!", rule)))));
        CodecWalker json = walker("JSON", keys("expireAt"));
        List<Object> path = Arrays.<Object>asList("C", "shards", "S",
                "routingRules", "k!", "expireAt");
        CodecWalker.Leaf leaf = json.resolve(graph, path);
        assertSame(rule, leaf.holder);
        assertEquals(CodecWalker.Holding.ENTRY, leaf.holding);
        assertEquals("expireAt", leaf.key);
        assertNull("an absent path resolves nothing", json.resolve(graph,
                Arrays.<Object>asList("C", "shards", "T", "routingRules")));
        assertTrue(leaf.store("1800"));
        assertEquals("1800", rule.get("expireAt"));

        List<Object> list = new ArrayList<>(Collections.singletonList("5"));
        CodecWalker.Leaf position = json.resolve(singleton("generation",
                list), Arrays.<Object>asList("generation", 0));
        assertTrue(position.store("6"));
        assertEquals("6", list.get(0));
        assertFalse("an immutable holder refuses", json.resolve(
                Collections.singletonMap("expireAt", "1"),
                Collections.<Object>singletonList("expireAt")).store("2"));
        CodecWalker.Leaf root = walker("NAME", keys("NAME")).resolve("7:u",
                Collections.emptyList());
        assertEquals(CodecWalker.Holding.ROOT, root.holding);
        assertFalse("the root is the decoder's to replace",
                root.store("x"));
    }

    // ---- fixtures -------------------------------------------------------

    private static Map<String, Object> singleton(String key, Object value) {
        Map<String, Object> map = new LinkedHashMap<>();
        map.put(key, value);
        return map;
    }

    private static Set<String> keys(String... keys) {
        return new HashSet<>(Arrays.asList(keys));
    }

    /** A walker of one of three codecs, demanding {@code keys}. */
    private static CodecWalker walker(String codec, Set<String> keys) {
        Map<String, JsonObject> rows = new LinkedHashMap<>();
        String[] declared = {
            "{'kind':'CODEC','codec':'JSON','shape':'TREE','space':'kv',"
                    + "'decoders':[{'method':'<o.U: java.lang.Object "
                    + "fromJSON(byte[],int,int)>','encoded':'arg0',"
                    + "'graph':'return'}]}",
            "{'kind':'CODEC','codec':'PB','shape':'PROTOBUF','space':'pb',"
                    + "'decoders':[{'call':'<*: * parseFrom(*)>',"
                    + "'encoded':'arg0','graph':'return'}]}",
            "{'kind':'CODEC','codec':'NAME','shape':'LEAF','space':'leaf',"
                    + "'decoders':[{'method':'<o.S: byte[] key("
                    + "java.lang.String)>','graph':'arg0'}]}",
            "{'kind':'CODEC_VIEW','codec':'JSON','type':'" + TEST
                    + "$Props','map':'getProperties()'}",
            "{'kind':'CODEC_VIEW','codec':'JSON','type':'" + TEST
                    + "$Coll','map':'getProperties()','put':{'shards':"
                    + "'getSlices()'}}",
            "{'kind':'CODEC_VIEW','codec':'JSON','type':'" + TEST
                    + "$Range','leaf':'toString()'}",
            "{'kind':'CODEC_VIEW','codec':'*','type':'" + TEST
                    + "$Pairs','pairs':'nvPairs'}"};
        int line = 0;
        for (String row : declared) {
            JsonObject json = JsonParser.parseString(row.replace('\'', '"'))
                    .getAsJsonObject();
            json.addProperty("schemaVersion", 1);
            rows.put("wire.jsonl:" + (++line), json);
        }
        WireDeclarations wire = WireDeclarations.of(rows);
        WireDeclarations.Codec chosen = wire.codec(codec);
        Set<String> ports = new HashSet<>();
        for (String key : keys) {
            ports.add(CommunicationCatalogContract.codecPortId(
                    chosen.space(), key));
        }
        return new CodecWalker(chosen, wire.views(), ports::contains);
    }
}
