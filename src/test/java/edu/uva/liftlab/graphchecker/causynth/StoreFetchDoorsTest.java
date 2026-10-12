package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §4.2: a store read's door (a {@code DATA_FLOW} door) is asked
 * only where its fetch lies on the data flow.  The recording states each
 * decode with the occurrence that fetched it ({@link RecordedStore}); PLAN
 * takes the fetch's door to be the data-flow door call that occurrence made
 * last before the decode and after its store event before it, every marker
 * of that one call ({@code RuntimeSelectedRegionFinalizer#fetchDoor}), and
 * states the rest as woven but never asked.  A decode of a version its own
 * occurrence wrote fetched nothing.
 */
public class StoreFetchDoorsTest {
    private static final String MARKER = "<edu.uva.liftlab.graphchecker."
            + "annotation.Debug: boolean makeSymbolicBoolean("
            + "java.lang.String)>";
    private static final String GET = "<z.Client: byte[] getData("
            + "java.lang.String)>";
    private static final String EXISTS = "<z.Client: boolean exists("
            + "java.lang.String)>";
    private static final String SET = "<z.Client: void setData("
            + "java.lang.String)>";

    @Test
    public void aFetchsDoorIsItsOccurrencesLastReadDoorCallBeforeItsDecode()
            throws Exception {
        StaticScopeMap map = scopeMap(
                site(GET + "#u3", "FAULT:ZOOKEEPER:READ:ConnectionLossException"),
                site(GET + "#u6", "FAULT:ZOOKEEPER:READ:SessionExpiredException"),
                site(EXISTS + "#u2",
                        "FAULT:ZOOKEEPER:READ:ConnectionLossException"),
                site(SET + "#u4",
                        "FAULT:ZOOKEEPER:WRITE:ConnectionLossException"));
        Map<String, Object> activation = new LinkedHashMap<>();
        activation.put(DeclaredSiteCapture.PLAN_FIELD, Arrays.asList(
                capture(EXISTS + "#u2", 1, 10), capture(GET + "#u3", 1, 12),
                capture(GET + "#u6", 1, 13), capture(SET + "#u4", 1, 15),
                capture(GET + "#u3", 2, 30), capture(GET + "#u6", 2, 31)));
        // Per decode: the seq of its occurrence's store event before it, its
        // own seq, and the captures its fetch's door made.
        Object[][] rows = {
            {0L, 20L, Arrays.asList(GET + "#u3@1", GET + "#u6@1")},
            {20L, 35L, Arrays.asList(GET + "#u3@2", GET + "#u6@2")},
            {0L, 11L, Collections.singletonList(EXISTS + "#u2@1")},
            {0L, 5L, Collections.<String>emptyList()},
            // The read door before the write served no later decode.
            {14L, 20L, Collections.<String>emptyList()},
        };
        for (Object[] row : rows) {
            List<String> door = new ArrayList<>();
            for (Map<String, Object> capture
                    : RuntimeSelectedRegionFinalizer.fetchDoor(activation, map,
                    (Long) row[0], (Long) row[1])) {
                door.add(capture.get(SiteId.MEMBER) + "@"
                        + capture.get(DeclaredSiteCapture.ORDINAL));
            }
            assertEquals("decoded at " + row[1], row[2], door);
        }

        // The recording's decodes: a fetch's in its occurrence (B's after a
        // write of its own), a provenance site's derived object in none, and
        // C's of the version it wrote itself, no fetch.
        RecordedStore store = new RecordedStore(Arrays.asList(
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 4L,
                        new int[]{8}, "n1/r/B", 40L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 3L,
                        new int[]{7}, "n1/r/A", 20L),
                RecordedStore.Event.written("SOLR_ZK", "/clusterprops.json",
                        2L, "n1/r/B", 30L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 4L,
                        new int[]{9}, "", 41L),
                RecordedStore.Event.written("SOLR_ZK", "/aliases.json", 5L,
                        "n1/r/C", 50L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 5L,
                        new int[]{10}, "n1/r/C", 52L)));
        List<String> fetched = new ArrayList<>();
        for (RecordedStore.Fetch fetch
                : store.fetchesOf(Arrays.asList(8, 9, 10))) {
            fetched.add(fetch.occurrence + "@" + fetch.version);
        }
        for (RecordedStore.Fetch fetch
                : store.fetchesAt("SOLR_ZK\n/aliases.json")) {
            fetched.add(fetch.occurrence + "@" + fetch.since + "-" + fetch.seq);
        }
        assertEquals(Arrays.asList("n1/r/B@4", "n1/r/A@0-20", "n1/r/B@30-40"),
                fetched);
        assertEquals(Collections.singletonMap("SOLR_ZK\n/aliases.json", 5L),
                store.versionsOf(Collections.singletonList(10)));
    }

    /** The fetches a target asks: the one that decoded what it read, and its
     *  node's other fetches of that location up to the version read (a
     *  failed one registers no watch); a later one, or another node's, is on
     *  no flow of the read. */
    @Test
    public void aTargetAsksItsNodesFetchesUpToTheVersionItRead() {
        String node2 = "auto0/node2#epoch0/region/REGION.w/ctx:Root:CLIENT/"
                + "suite#1/idx:<a.B: void m()>@";
        String node3 = "auto0/node3#epoch0/region/REGION.w/ctx:Root:CLIENT/"
                + "suite#1/idx:<a.B: void m()>@";
        RecordedStore store = new RecordedStore(Arrays.asList(
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 1L,
                        new int[]{1}, node2 + "1", 10L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 1L,
                        new int[]{2}, node3 + "1", 11L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 2L,
                        new int[]{3}, node2 + "2", 30L)));
        Object[][] rows = {
            {1, Collections.singletonList(node2 + "1@1 PROVENANCE")},
            {3, Arrays.asList(node2 + "2@2 PROVENANCE",
                    node2 + "1@1 LOCATION")},
        };
        for (Object[] row : rows) {
            List<String> asked = new ArrayList<>();
            for (Map.Entry<RecordedStore.Fetch, String> fetch
                    : RuntimeSelectedRegionFinalizer.dataFlowFetches(store,
                    Collections.singletonList((Integer) row[0]),
                    NodeId.parse("auto0/node2#epoch0")).entrySet()) {
                asked.add(fetch.getKey().occurrence + "@"
                        + fetch.getKey().version + " " + fetch.getValue());
            }
            assertEquals("read object " + row[0], row[1], asked);
        }
    }

    /** A planned occurrence whose final basis is a door's -- a control
     *  producer's or a store fetch's -- is doors-only; one a value rule
     *  moved, or a target, is not. */
    @Test
    public void aDoorOccurrenceIsPlannedDoorsOnly() {
        Map<String, Map<String, Object>> instances = new LinkedHashMap<>();
        String[][] rows = {{"cp", "CONTROL_PRODUCER_V1"},
                {"fetch", "STORE_FETCH_V1"},
                {"writer", "SHARED_LOCATION_DEMAND_V1"},
                {"root", "ROOT_RELEVANT_V1"}, {"target", ""}};
        for (String[] row : rows) {
            Map<String, Object> activation = new LinkedHashMap<>();
            if (!row[1].isEmpty()) {
                activation.put(RuntimeSelectedRegionFinalizer.ADMISSION_BASIS,
                        row[1]);
            }
            instances.put(row[0], activation);
        }
        assertEquals(2, RuntimeSelectedRegionFinalizer.stateDoorsOnly(
                instances, instances.keySet()));
        for (String[] row : rows) {
            assertEquals(row[0], row[1].endsWith("PRODUCER_V1")
                    || row[1].startsWith("STORE_FETCH"), instances.get(row[0])
                    .containsKey(RuntimeSelectedRegionFinalizer.DOORS_ONLY));
        }
    }

    private static Map<String, Object> capture(String siteId, int ordinal,
                                               long seq) {
        Map<String, Object> capture = new LinkedHashMap<>();
        capture.put(SiteId.MEMBER, siteId);
        capture.put(DeclaredSiteCapture.DECLARED_CALLEE, MARKER);
        capture.put(DeclaredSiteCapture.ORDINAL, ordinal);
        capture.put(DeclaredSiteCapture.EVENT_SEQ, seq);
        return capture;
    }

    private static JsonObject site(String siteId, String marker) {
        JsonObject site = new JsonObject();
        site.addProperty("kind", "STATIC_SCOPE_SITE");
        site.addProperty("role", "DECLARED_SITE");
        site.addProperty("regionId", "REGION.fetch");
        site.addProperty("siteId", siteId);
        site.addProperty("cell", MARKER + ".return");
        site.addProperty("declaredCallee", MARKER);
        site.addProperty("declaredKind", "CALL_RETURN");
        site.addProperty("dependencyCell", siteId + "::$fault");
        site.addProperty("javaType", "boolean");
        site.addProperty("inputKind", "FAULT");
        site.addProperty("marker", marker);
        return site;
    }

    private static StaticScopeMap scopeMap(JsonObject... sites)
            throws Exception {
        Path file = Files.createTempFile("scope", ".jsonl");
        StringBuilder text = new StringBuilder();
        for (JsonObject site : sites) text.append(site).append('\n');
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        try {
            return StaticScopeMap.read(file);
        } finally {
            Files.delete(file);
        }
    }
}
