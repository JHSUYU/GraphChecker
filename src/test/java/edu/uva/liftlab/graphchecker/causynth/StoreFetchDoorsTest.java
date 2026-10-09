package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
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
 * last before the decode, every marker of that one call ({@code
 * RuntimeSelectedRegionFinalizer#fetchDoor}), and states the rest as woven
 * but never asked.
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
        // Per decode seq: the captures its fetch's door made.
        Object[][] rows = {
            {20L, Arrays.asList(GET + "#u3@1", GET + "#u6@1")},
            {35L, Arrays.asList(GET + "#u3@2", GET + "#u6@2")},
            {11L, Collections.singletonList(EXISTS + "#u2@1")},
            {5L, Collections.<String>emptyList()},
        };
        for (Object[] row : rows) {
            List<String> door = new ArrayList<>();
            for (Map<String, Object> capture
                    : RuntimeSelectedRegionFinalizer.fetchDoor(activation, map,
                    (Long) row[0])) {
                door.add(capture.get(SiteId.MEMBER) + "@"
                        + capture.get(DeclaredSiteCapture.ORDINAL));
            }
            assertEquals("decoded at " + row[0], row[1], door);
        }

        // The recording's decodes: a fetch's in its occurrence, a
        // provenance site's derived object in none.
        RecordedStore store = new RecordedStore(Arrays.asList(
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 3L,
                        new int[]{7}, "n1/r/A", 20L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 4L,
                        new int[]{8}, "n1/r/B", 40L),
                RecordedStore.Event.decoded("SOLR_ZK", "/aliases.json", 4L,
                        new int[]{9}, "", 41L)));
        List<String> fetched = new ArrayList<>();
        for (RecordedStore.Fetch fetch : store.fetchesOf(Arrays.asList(8, 9))) {
            fetched.add(fetch.occurrence + "@" + fetch.version);
        }
        for (RecordedStore.Fetch fetch
                : store.fetchesAt("SOLR_ZK\n/aliases.json")) {
            fetched.add(fetch.occurrence + "@" + fetch.seq);
        }
        assertEquals(Arrays.asList("n1/r/B@4", "n1/r/A@20", "n1/r/B@40"),
                fetched);
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
