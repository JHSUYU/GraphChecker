package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * THE ZOOKEEPER CAUSAL CHAIN: backward from a target over the recording's
 * store rows, every writer of a chain location (every version), the queue
 * item it applied and that item's writer, and the chain locations'
 * consumers on a chain node -- no other location, no consumer on another
 * node; and the chain's FIELDS, by leaf identity: the pointer the target's
 * leaf was parsed at, the writer's leaf there, the item leaf it serialized
 * from, nothing else of either document.
 */
public class ZkCausalGraphTest {
    private static String at(String node, int k) {
        return "auto0/" + node + "#epoch0/region/REGION.w/ctx:Root:CLIENT/"
                + "suite#1/idx:<a.B: void m()>@" + k;
    }

    private static final String STATE = "SOLR_ZK\n/c/state.json";
    private static final String ITEM = "SOLR_ZK\n/overseer/queue/qn-1";

    @Test
    public void theChainIsEveryWriterOfWhatTheTargetReadAndItsFields() {
        String target = at("node1", 1);
        String sender = at("node0", 2);
        String writer1 = at("node0", 3);
        String writer2 = at("node0", 4);
        String decode = at("node1", 5);
        String elsewhere = at("node2", 6);
        String other = at("node1", 7);
        RecordedStore store = new RecordedStore(Arrays.asList(
                RecordedStore.Event.written("SOLR_ZK", "/overseer/queue/qn-1",
                        0L, sender, 1L),
                RecordedStore.Event.leaves(true, "SOLR_ZK",
                        "/overseer/queue/qn-1", 0L, sender, 2L,
                        new String[]{"|state"}, new int[]{401}),
                RecordedStore.Event.decoded("SOLR_ZK", "/overseer/queue/qn-1",
                        0L, new int[]{50}, writer1, 3L),
                RecordedStore.Event.leaves(false, "SOLR_ZK",
                        "/overseer/queue/qn-1", 0L, writer1, 4L,
                        new String[]{"|state", "|other"},
                        new int[]{201, 301}),
                RecordedStore.Event.written("SOLR_ZK", "/c/state.json", 1L,
                        writer1, 5L),
                RecordedStore.Event.leaves(true, "SOLR_ZK", "/c/state.json",
                        1L, writer1, 6L,
                        new String[]{"|c|shards|s1|state", "|c|router"},
                        new int[]{201, 202}),
                RecordedStore.Event.written("SOLR_ZK", "/c/state.json", 2L,
                        writer2, 7L),
                RecordedStore.Event.decoded("SOLR_ZK", "/c/state.json", 1L,
                        new int[]{60}, decode, 8L),
                RecordedStore.Event.leaves(false, "SOLR_ZK", "/c/state.json",
                        1L, decode, 9L,
                        new String[]{"|c|shards|s1|state", "|c|router"},
                        new int[]{101, 102}),
                RecordedStore.Event.decoded("SOLR_ZK", "/c/state.json", 1L,
                        new int[]{70}, elsewhere, 10L),
                RecordedStore.Event.read("SOLR_ZK", "/other.json", 0L, other,
                        11L)));
        ZkCausalGraph graph = ZkCausalGraph.of(store);
        ZkCausalGraph.Chain chain = graph.chain(
                Collections.singletonList(target),
                Collections.singletonList(STATE),
                occurrence -> occurrence.equals(writer1)
                        ? Collections.singletonList(sender)
                        : Collections.<String>emptyList());
        assertEquals(new LinkedHashSet<>(Arrays.asList(STATE, ITEM)),
                chain.paths.keySet());
        for (String on : new String[]{target, sender, writer1, writer2,
                decode}) {
            assertTrue(on, chain.holds(on));
        }
        assertFalse("a decode on no chain node", chain.holds(elsewhere));
        assertFalse("a read of another location", chain.holds(other));
        assertTrue(graph.zkCarried(other) && !graph.zkCarried(target));

        Map<String, Map<String, Set<String>>> keys = graph.keys(chain,
                Collections.singletonList(101),
                Collections.<String>emptyList());
        assertEquals(Collections.singleton("|c|shards|s1|state"),
                keys.get(decode).get(STATE));
        assertEquals(Collections.singleton("|c|shards|s1|state"),
                keys.get(writer1).get(STATE));
        assertEquals("the item leaf the writer serialized from",
                Collections.singleton("|state"), keys.get(writer1).get(ITEM));
        assertEquals(Collections.singleton("|state"),
                keys.get(sender).get(ITEM));
        // A location a target read decoded objects of is carried whole.
        assertEquals(Collections.singleton(ZkCausalGraph.WHOLE),
                graph.keys(chain, Collections.singletonList(101),
                        Collections.singletonList(STATE))
                        .get(decode).get(STATE));
    }
}
