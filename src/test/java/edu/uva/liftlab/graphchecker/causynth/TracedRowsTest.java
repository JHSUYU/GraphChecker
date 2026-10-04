package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/** The recording writes a call, argument or exit row exactly where SEED's
 *  aggregation reads one. */
public class TracedRowsTest {
    private static final String M = "<a.B: int m(int)>";
    private static final String GET = "<a.C: int get()>";
    private static final String SEND = "<a.D: void send(int)>";
    private static final String RECV = "<a.D: int recv()>";
    private static final String NAME = "<a.E: java.lang.String name()>";
    private static final String PUT = "<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>";

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void tracesTheRowsAReaderTakesAndNoOther() throws Exception {
        TracedRows traced = new TracedRows(skeletons(), scopeMap(), graph());
        Object[][] rows = {
            // kind, site or method, callee, index, traced
            {"call", M + "#u3", GET, -1, true},      // a declared site
            {"call", M + "#u3", NAME, -1, false},    // its site, another callee
            {"call", M + "#u5", NAME, -1, true},     // an accessor's field
            {"call", M + "#u6", PUT, -1, true},      // a mutation through a field
            {"call", M + "#u7", RECV, -1, true},     // a call-return port
            {"call", M + "#u8", SEND, -1, true},     // a call-argument port
            {"argument", M + "#u8", SEND, 0, true},
            {"argument", M + "#u8", SEND, 1, false},
            {"argument", M + "#u3", GET, 0, false},
            {"call", M + "#u9", GET, -1, false},     // read by nothing
            {"parameter", M, "", 0, true},           // a parameter port
            {"parameter", M, "", 1, false},
            {"exit", M, "", -1, true},               // a method-return port
            {"exit", GET, "", -1, false},
        };
        for (Object[] row : rows) {
            String kind = (String) row[0];
            String where = (String) row[1];
            int index = (Integer) row[3];
            boolean actual = "call".equals(kind)
                    ? traced.callSite(where, (String) row[2])
                    : "argument".equals(kind)
                    ? traced.callArgument(where, (String) row[2], index)
                    : "parameter".equals(kind)
                    ? traced.methodArgument(where, index)
                    : traced.methodExit(where);
            assertEquals(Arrays.toString(row), row[4], actual);
        }
    }

    private StaticScopeMap scopeMap() throws Exception {
        String rows = String.join("\n",
                "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                        + "\"role\":\"DECLARED_SITE\",\"regionId\":\"R\","
                        + "\"siteId\":\"" + M + "#u3\",\"cell\":\"<a.C: int f>\","
                        + "\"declaredCallee\":\"" + GET + "\","
                        + "\"declaredKind\":\"ACCESSOR_RETURN\",\"edgeId\":\"DF.1\","
                        + "\"dependencyCell\":\"" + M + "::$i0\",\"javaType\":\"int\","
                        + "\"implementationMethod\":\"" + GET + "\",\"guards\":[]}",
                "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                        + "\"role\":\"WRITE_SITE\",\"regionId\":\"R\","
                        + "\"siteId\":\"" + M + "#u6\",\"cell\":\"<a.B: java.util.Map m>\","
                        + "\"carrier\":\"<a.B: java.util.Map m>.state\","
                        + "\"declaredCallee\":\"" + PUT + "\",\"guards\":[]}");
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, (rows + "\n").getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    private static List<Map<String, Object>> graph() {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", "accessor_field_return");
        edge.put("siteId", M + "#u5");
        edge.put("fromCell", "<a.E: java.lang.String name>");
        return Collections.singletonList(edge);
    }

    private static List<StaticProgram.RegionRow> skeletons() {
        Map<String, Object> skeleton = new LinkedHashMap<>();
        skeleton.put("schemaVersion", 3);
        skeleton.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        skeleton.put("regionId", "R");
        skeleton.put("rootMethod", M);
        skeleton.put("anchorMethod", M);
        skeleton.put("methods", Collections.singletonList(M));
        skeleton.put("communicationPorts", Arrays.asList(
                port("IN", "CALL_RETURN", 7, RECV, -1),
                port("OUT", "CALL_ARGUMENT", 8, SEND, 0),
                port("IN", "METHOD_PARAMETER", -1, "", 0),
                port("OUT", "METHOD_RETURN", -1, "", -1)));
        return StaticProgram.regionRows(Collections.singletonList(skeleton),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    private static Map<String, Object> port(String side, String capture,
                                            int unit, String callee,
                                            int index) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("portId", "P." + capture);
        port.put("regionPortSide", side);
        port.put("outputCaptureKind", capture);
        port.put("definitionMethod", M);
        port.put("definitionUnitIndex", unit);
        port.put("declaredCallee", callee);
        port.put("argumentIndex", index);
        return port;
    }
}
