package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import org.apache.hadoop.ipc.CausynthMessagePropagation;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * What binds a codec's entries to the message that carries them
 * (WIRE-CODEC §4.4-§4.5), never the thread, one row per binding; the
 * envelope they travel in; and the template a leaf's expression is cut into
 * and read back by.
 */
public class CodecMessagesTest {
    private static final String ZK = "SOLR_ZK";

    @Before
    @After
    public void reset() {
        CodecMessages.clear();
        RowRuntime.resetForTests();
    }

    @Test
    public void entriesTravelWithTheirMessageNeverTheThread() {
        List<CodecMessages.Entry> item = Collections.singletonList(
                entry("JSON", 0, 0, "expireAt"));

        // Identity: the queue's response node is created first, from an
        // empty array; the request node's array is the encode's.
        byte[] request = new byte[]{1};
        byte[] response = new byte[0];
        assertEquals(0, CodecMessages.encoded(request, "JSON", item));
        assertTrue("the response node carries nothing",
                CodecMessages.written(response).isEmpty());
        assertSame(item, CodecMessages.written(request));

        // N readers of one version, and one array decoded twice: each read
        // binds its own array to the one message, which no decode consumes.
        CodecMessages.Message stored = CodecMessages.stored(ZK,
                "/queue/qn-0001@0", item).message;
        assertEquals("SOLR_ZK /queue/qn-0001@0", stored.key);
        assertEquals("/queue/qn-0001@0", stored.storeKey);
        byte[] overseer = new byte[]{1};
        byte[] leader = new byte[]{1};
        CodecMessages.fetched(ZK, "/queue/qn-0001@0", overseer);
        CodecMessages.fetched(ZK, "/queue/qn-0001@0", leader);
        for (byte[] read : Arrays.asList(overseer, leader, overseer)) {
            assertSame(stored, CodecMessages.delivered(read));
        }
        assertNull("local data is bound to no message",
                CodecMessages.delivered(new byte[]{1}));

        // A path keeps its last versions; a read of a dropped one says so.
        for (int version = 1; version <= 10; version++) {
            CodecMessages.stored(ZK, "/state.json@" + version, item);
        }
        CodecMessages.Fetch dropped = CodecMessages.fetched(ZK,
                "/state.json@2", new byte[0]);
        assertNull(dropped.message);
        assertTrue(dropped.dropped);
        assertFalse(CodecMessages.fetched(ZK, "/state.json@11",
                new byte[0]).dropped);
        assertTrue(CodecMessages.fetched(ZK, "/state.json@3", new byte[0])
                .message != null);
        // The paths are bounded too, the least recently used dropped.
        String first = "";
        for (int path = 0; path <= CodecMessages.MAX_PATHS; path++) {
            String pushed = CodecMessages.stored(ZK, "/p" + path + "@0",
                    item).dropped;
            if (first.isEmpty()) first = pushed;
        }
        assertEquals("SOLR_ZK /queue/qn-0001", first);

        // A bracket: its encodes are drained by the next door of its
        // transport; what is left at its close is unsent.
        long outer = CodecMessages.beginExchange("SOLR_HTTP");
        CodecMessages.Bracket bracket = CodecMessages.innermost();
        assertEquals(0, bracket.nextOrdinal("PARAMS"));
        assertEquals(1, bracket.nextOrdinal("PARAMS"));
        bracket.staged.add(entry("PARAMS", 0, 0, "generation"));
        assertTrue(CodecMessages.drain("HDFS_SASL").isEmpty());
        assertEquals(1, CodecMessages.drain("SOLR_HTTP").size());
        assertTrue("drained once", CodecMessages.drain("SOLR_HTTP")
                .isEmpty());
        CodecMessages.beginExchange("SOLR_HTTP");
        CodecMessages.innermost().staged.add(entry("PARAMS", 1, 0,
                "generation"));
        CodecMessages.endExchange(outer);
        assertNull("closing the outer bracket closed the inner one",
                CodecMessages.innermost());
        CodecMessages.unsent("PARAMS");
        assertEquals(Long.valueOf(2L),
                CodecMessages.unsentCounts().get("PARAMS"));
    }

    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    /** Named as Hadoop's IPC request wrapper is, with no payload field. */
    static final class RpcProtobufRequest {
    }

    /**
     * A door names what it cannot carry: a symbolic header segment of no
     * scheme, a payload its adapter cannot unwrap.
     */
    @Test
    public void theDoorsNameWhatTheyCannotCarry() throws Exception {
        Path root = iteration.getRoot().toPath().resolve("iteration-0000");
        Path results = root.resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
        MessageDoors.inbound(null, "not-an-envelope", "SOLR_HTTP", "c1", "1",
                MessageDoors.REQUEST, null, false);
        MessageDoors.endInbound();
        CausynthMessagePropagation.outbound("HADOOP_IPC", "c2", "0",
                MessageDoors.REQUEST, null, null, new RpcProtobufRequest());
        RowRuntime.closeSession();
        List<String> named = new ArrayList<>();
        for (GapRow gap : RowCodec.readAll(SessionDir.of(root,
                RowRuntime.sessionId()).gaps(), RowCodec::readGap)) {
            named.add(gap.kind() + " " + gap.subject() + " " + gap.detail());
        }
        assertTrue(named.toString(), named.stream().anyMatch(gap ->
                gap.startsWith("MESSAGE_CONTEXT_REFUSED inbound symbolic")));
        assertTrue(named.toString(), named.stream().anyMatch(gap ->
                gap.startsWith("UNSTATED_VALUE HADOOP_IPC")
                        && gap.contains("RpcProtobufRequest")));
    }

    @Test
    public void theEnvelopeCarriesTheProducerAndIsBounded() {
        List<CodecMessages.Entry> entries = Arrays.asList(
                entry("JSON", 0, 0, "expireAt"),
                entry("JSON", 0, 1, "expireAt"));
        CodecEnvelope.Written written = CodecEnvelope.write("m", entries,
                Integer.MAX_VALUE);
        assertTrue(written.wire.startsWith("CSE6;"));
        List<CodecMessages.Entry> read = CodecEnvelope.read(written.wire);
        assertEquals(2, read.size());
        for (int index = 0; index < 2; index++) {
            CodecMessages.Entry sent = entries.get(index);
            CodecMessages.Entry got = read.get(index);
            assertEquals(sent.producer, got.producer);
            assertEquals(sent.contractHole(), got.contractHole());
            assertEquals(sent.recorded, got.recorded);
            assertEquals(sent.text, got.text);
            assertEquals(sent.exportSeq, got.exportSeq);
            assertEquals(sent.template.wire(), got.template.wire());
        }
        CodecEnvelope.Written capped = CodecEnvelope.write("m", entries,
                written.wire.length() - 1);
        assertEquals("a byte bound keeps what fits", 1,
                capped.carried.size());
        assertEquals("a header already full carries no hole", "",
                CodecEnvelope.write("m", entries, 0).wire);
        assertTrue("a malformed envelope installs nothing",
                CodecEnvelope.read("CSE6;%%%").isEmpty());
    }

    @Test
    public void aLeafIsCutIntoTheTemplateBothSidesRead() {
        String n = "{`_type`:`SymbolExpression`,`_java_type`:`J`,"
                + "`_exp`:`M_J_field_SRC.n`}";
        String i = "{`_type`:`SymbolExpression`,`_java_type`:`I`,"
                + "`_exp`:`M_I_field_SRC.i`}";
        String s = "{`_type`:`SymbolExpression`,"
                + "`_java_type`:`java/lang/String`,`_exp`:`M_L_s`}";
        Object[][] rows = {
            // expression, leaf text, template, hole texts (null: none)
            {concat(literal("k-"), toString(n)), "k-1727",
                    "[k-, DEC_LONG]", Collections.singletonList("1727")},
            {toString(i), "42", "[DEC_INT]",
                    Collections.singletonList("42")},
            {concat(toString(i), literal(":"), s), "42:abc",
                    "[DEC_INT, :, STR]", Arrays.asList("42", "abc")},
            {concat(toString(n), s), "1727abc", "[STR]",
                    Collections.singletonList("1727abc")},
            {concat(s, literal(":"), s), "a:b:c", "[STR, :, STR]", null},
            {literal("1727"), "1727", "[DEC_INT]",
                    Collections.singletonList("1727")},
            {literal("17270000000000"), "17270000000000", "[DEC_LONG]",
                    Collections.singletonList("17270000000000")},
            {literal("true"), "true", "[BOOL]",
                    Collections.singletonList("true")},
            {literal("80000000-ffffffff"), "80000000-ffffffff", "[STR]",
                    Collections.singletonList("80000000-ffffffff")},
            {concat(literal("k-"), toString(n)), "x-1727",
                    "[k-, DEC_LONG]", null},
            // A decimal before a literal that could end it: two readings.
            {concat(toString(i), literal("0"), s), "1000x",
                    "[DEC_INT, 0, STR]", null},
        };
        for (Object[] row : rows) {
            CodecExport.Template template = CodecExport.cut(json(
                    (String) row[0]), false, "Ljava/lang/String;",
                    (String) row[1]);
            assertEquals(row[0].toString(), row[2], shape(template));
            List<String> texts = template.match((String) row[1]);
            assertEquals(row[0].toString(), row[3], texts);
            if (texts != null) {
                assertEquals(row[1], template.render(texts));
                assertEquals("the wire keeps the shape", row[2], shape(
                        CodecExport.Template.fromWire(template.wire())));
            }
        }
        // A decoded leaf is read against its producer's template: minted
        // only as the value the producer recorded; one whole-leaf hole only
        // when the producer's template was one; else it stays concrete.
        CodecExport.Template pair = CodecExport.cut(json(concat(toString(i),
                literal(":"), s)), false, "Ljava/lang/String;", "42:abc");
        CodecExport.Template whole = CodecExport.cut(json(n), true, "J",
                "1727");
        Object[][] readings = {
            // producer's template, decoded leaf, recorded, shape or mismatch
            {pair, "42:abc", "42:abc", "[DEC_INT, :, STR]"},
            {pair, "42:abd", "42:abc", "VALUE_MISMATCH"},
            {pair, 42L, "42:abc", "VALUE_MISMATCH"},
            {whole, "1727", "1727", "[STR]"},
            {whole, 1727L, "1727", "[NUM]"},
            {CodecExport.cut(json(concat(toString(i), literal("0"), s)),
                    false, "Ljava/lang/String;", "1000x"), "1000x",
                    "1000x", "TEMPLATE_MISMATCH"},
        };
        for (Object[] row : readings) {
            CodecExport.Reading reading = CodecExport.Reading.of(
                    (CodecExport.Template) row[0], row[1], (String) row[2]);
            assertEquals(row[1] + " against " + row[2], row[3],
                    reading.mismatch.isEmpty() ? shape(reading.template)
                            : reading.mismatch);
        }

        CodecExport.Template box = CodecExport.cut(json(n), true, "J",
                "1727");
        assertTrue(box.numeric());
        assertEquals(Collections.singletonList("1727"), box.match("1727"));
        assertEquals("{\"parts\":[{\"literal\":\"k-\"},{\"hole\":\"DEC_LONG\","
                        + "\"label\":\"HOFF.a\",\"text\":\"9\"}]}",
                CodecExport.cut(json(concat(literal("k-"), toString(n))),
                        false, "Ljava/lang/String;", "k-9").mintJson(
                        Collections.singletonList("HOFF.a"),
                        Collections.singletonList("9")));
    }

    // ---- fixtures -------------------------------------------------------

    private static String shape(CodecExport.Template template) {
        StringBuilder shape = new StringBuilder("[");
        for (CodecExport.Part part : template.parts) {
            if (shape.length() > 1) shape.append(", ");
            shape.append(part.hole() ? part.kind.name() : part.literal);
        }
        return shape.append("]").toString();
    }

    private static JsonObject json(String text) {
        return JsonParser.parseString(text.replace('`', '"'))
                .getAsJsonObject();
    }

    private static String literal(String text) {
        return "{`_type`:`ConStringSymbolExp`,`_java_type`:`java/lang/String`,"
                + "`_exp`:`Y_L'String'_" + text + "`}";
    }

    private static String toString(String operand) {
        return "{`_type`:`OpStrExpression`,`_name`:`toString`,`_is_not`:false,"
                + "`_param_list`:[" + operand + "]}";
    }

    private static String concat(String... operands) {
        return "{`_type`:`OpStrExpression`,`_name`:`concat`,`_is_not`:false,"
                + "`_param_list`:[" + String.join(",", operands) + "]}";
    }

    private static CodecMessages.Entry entry(String codec, int ordinal,
                                             int hole, String key) {
        OccurrenceAddress occurrence = OccurrenceAddress.of(
                NodeId.of("node0", 0), "REGION.migrate",
                CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of("MigrateCmd#call", 0))));
        Endpoint producer = Endpoint.of(occurrence, "XCH.wire.kv:" + key,
                ExecutionIndex.of(Collections.singletonList(Frame.of(
                        CodecRuntime.frameSite("XCH.wire.kv:" + key, "",
                                Collections.<Object>singletonList(key), hole),
                        0))),
                0);
        // "42:abc": a DEC_INT hole, a literal, an STR hole.
        CodecExport.Template template = CodecExport.cut(json(concat(
                toString("{`_type`:`SymbolExpression`,`_java_type`:`I`,"
                        + "`_exp`:`M_I_field_SRC.i`}"), literal(":"),
                "{`_type`:`SymbolExpression`,`_java_type`:"
                        + "`java/lang/String`,`_exp`:`M_L_s`}")), false,
                "Ljava/lang/String;", "42:abc");
        return new CodecMessages.Entry(codec, ordinal,
                Collections.<Object>singletonList(key), hole, template,
                producer, 40L + hole, "42:abc", hole == 0 ? "42" : "abc",
                null, hole == 0 ? "I" : "Ljava/lang/String;");
    }
}
