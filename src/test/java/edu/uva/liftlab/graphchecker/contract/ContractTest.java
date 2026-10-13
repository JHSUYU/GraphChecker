package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.Arms;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The contract, checked where two modules would otherwise disagree:
 * what an occurrence is called, what makes two occurrences the same one across
 * replays, what a case declaration selects, and what a row looks like on disk.
 */
public class ContractTest {
    private static final NodeId DN0 = NodeId.of("hdfs-17897/dn0", 0);
    private static final NodeId NN0 = NodeId.of("hdfs-17897/nn0", 0);
    private static final String REGION =
            "REGION.53092d3e-263d-3a18-b7a5-ae5b437d96de";
    private static final String RPC =
            "ClientNamenodeProtocol#getBlockKeys";
    private static final String PRODUCER_ID = "9f2c1a3b4c5d6e7f";
    private static final String PORT = "XCH.53092d3e.resp.block-key-id";
    private static final String BLOCK_KEY =
            "Lorg/apache/hadoop/hdfs/security/token/block/BlockKey;";

    /** The three frames from the scope root to the region entry. */
    private static final String RUN = "o.a.h.h.s.d.DataXceiver#run#12";
    private static final String CHECKSUM =
            "o.a.h.h.s.d.DataXceiver#blockChecksum#48";
    private static final String COMPUTE =
            "o.a.h.h.s.d.BlockChecksumHelper#compute#7";

    /** A case declaration naming the request that reached the region. */
    private static final String V1_WITH_API =
            "hdfs-17897/dn0#epoch0/region/" + REGION
                    + "@hdfs-17897/client#epoch0/striped-file-checksum#1";
    /** A case declaration under no request at all. */
    private static final String V1_BARE =
            "hdfs-17899/dn0#epoch0/region/" + REGION + "#2";
    private static final String DECLARED_API =
            "hdfs-17897/client#epoch0/striped-file-checksum";

    @Rule
    public TemporaryFolder iteration = new TemporaryFolder();

    /** A session's expressions are logged as the DAG they are: a chain
     *  whose every node names the one below twice is 2^64 nodes as a tree (a
     *  File.getParent chain left finalize-gs a8's table unwritable).  A ref
     *  is the content's, whatever the objects and their member order. */
    /**
     * What a read node returned, as its row spells it: no String content
     * reads as a number, an identity or null, and an identity states none.
     */
    @Test
    public void aReadRowSpellsWhatItsReadReturned() {
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "Y_J_1003");
        Object[][] cases = {
                {constant, "1003", null},
                {new com.google.gson.JsonPrimitive("N"), "\"N\"", "N"},
                {new com.google.gson.JsonPrimitive("Y_I_2 \"q\""),
                        "\"Y_I_2 \\\"q\\\"\"", "Y_I_2 \"q\""},
                {com.google.gson.JsonNull.INSTANCE, "N", null},
                {symbol("M_L'java/util/HashMap'_12"),
                        "M_L'java/util/HashMap'_12", null},
                {truncated(), null, null},
                {null, null, null}};
        for (Object[] each : cases) {
            JsonObject node = new JsonObject();
            if (each[0] != null) {
                node.add("concreteValue", (com.google.gson.JsonElement) each[0]);
            }
            String spelled = ReadRow.returned(node);
            assertEquals(String.valueOf(each[0]), each[1], spelled);
            assertEquals(each[2], ReadRow.stringContent(spelled));
        }
        // A node that states nothing: an exact read returned its version's
        // leaf (a reference cell's INITIAL null), an inexact one or a
        // symbolic version nothing.
        Object[][] observed = {
                {symbol("N"), true, "N"},
                {symbol("M_L'java/util/HashMap'_12"), true,
                        "M_L'java/util/HashMap'_12"},
                {constant, true, "1003"},
                {symbol("N"), false, null},
                {symbol("S_J_clock"), true, null}};
        for (Object[] each : observed) {
            JsonObject version = new JsonObject();
            version.add("expression", (JsonObject) each[0]);
            JsonObject node = new JsonObject();
            node.addProperty("observedExact", (Boolean) each[1]);
            node.add("observedVersion", version);
            assertEquals(java.util.Arrays.toString(each), each[2],
                    ReadRow.returned(node));
        }
    }

    /** A String the VM cut past its bound: its length, and no content. */
    private static JsonObject truncated() {
        JsonObject value = new JsonObject();
        value.addProperty("_type", "TruncatedValue");
        value.addProperty("length", 5000);
        return value;
    }

    @Test
    public void aSessionLogHoldsTheDagAndRefsNameContent()
            throws IOException {
        Path file = iteration.getRoot().toPath().resolve(
                SessionDir.EXPRESSIONS);
        JsonObject chain = new JsonObject();
        chain.addProperty("_type", "ConstExpr");
        chain.addProperty("_exp", "C_I_1");
        chain.addProperty("_java_type", "I");
        for (int depth = 0; depth < 64; depth++) {
            JsonObject sum = new JsonObject();
            sum.addProperty("_type", "BinaryExpression");
            sum.addProperty("_op", "+");
            sum.add("_left", chain);
            sum.add("_right", chain);
            chain = sum;
        }
        Map<String, JsonObject> expressions =
                new LinkedHashMap<String, JsonObject>();
        expressions.put("EXPR.0000000000000001", chain);
        RowCodec.writeExpressions(file, ExpressionTable.of(expressions));
        assertTrue(Files.size(file) < 64 * 1024);
        JsonObject read = SessionExpressionLog.read(file, new RowPool())
                .expression("EXPR.0000000000000001");
        assertSame(read.get("_left"), read.get("_right"));
        assertEquals(new ExpressionRefs().ref(chain),
                new ExpressionRefs().ref(read));

        JsonObject reordered = new JsonObject();
        reordered.addProperty("_java_type", "I");
        reordered.addProperty("_exp", "C_I_1");
        reordered.addProperty("_type", "ConstExpr");
        JsonObject constant = new JsonObject();
        constant.addProperty("_type", "ConstExpr");
        constant.addProperty("_exp", "C_I_1");
        constant.addProperty("_java_type", "I");
        assertEquals(new ExpressionRefs().ref(constant),
                new ExpressionRefs().ref(reordered));
        constant.addProperty("_exp", "C_I_2");
        assertNotEquals(new ExpressionRefs().ref(constant),
                new ExpressionRefs().ref(reordered));

        // A log the session never published is refused, never the empty
        // table every ref then misses (hdfs-17960's offline compose read
        // UNSTATED_VALUE and hid the missing file): IMPORT and COMPOSE
        // refuse the session SESSION_INCOMPLETE.
        Files.write(file, new byte[0]);
        SessionDir bare = SessionDir.of(iteration.getRoot().toPath(),
                "s-no-log").create();
        for (Path unpublished : new Path[] {file, bare.expressions()}) {
            try {
                SessionExpressionLog.read(unpublished, new RowPool());
                fail("read " + unpublished + " as a table");
            } catch (IllegalArgumentException refused) {
                assertTrue(refused.getMessage(), refused.getMessage()
                        .contains(unpublished.toString()));
            }
        }
        assertTrue(SessionReader.read(bare).incomplete()
                .startsWith(SessionDir.EXPRESSIONS + " could not be read"));
    }

    /**
     * A VM chain is imported and judged once per node and to its end: one
     * whose nodes name the one below twice is 2^64 paths as a tree, and one
     * 100000 deep overflowed the import's recursion (the publication thread
     * was given a 512 MB stack for it) and passed the gate's depth-64 cap
     * unjudged.
     */
    @Test(timeout = 120_000L)
    public void aDeepSharedChainIsImportedAndJudgedToItsEnd()
            throws IOException {
        for (int depth : new int[]{64, 100_000}) {
            boolean doubled = depth == 64;
            // The VM's own encoding: node k names node k-1 by its id.
            JsonArray definitions = new JsonArray();
            definitions.add(vmDefinition(1, binary("!=",
                    symbol("M_Z_marker"), literal("Y_Z_0"))));
            for (int id = 2; id <= depth; id++) {
                definitions.add(vmDefinition(id, binary("==",
                        vmReference(id - 1), doubled ? vmReference(id - 1)
                                : literal("Y_Z_1"))));
            }
            JsonObject table = new JsonObject();
            table.addProperty("schemaVersion", 1);
            table.addProperty("kind", VmExpressionTable.KIND);
            table.addProperty("authority", VmExpressionTable.AUTHORITY);
            table.addProperty("sessionId", 1L);
            table.addProperty("definitionCount", depth);
            table.add("definitions", definitions);
            JsonObject envelope = new JsonObject();
            envelope.add(VmExpressionTable.FIELD, table);
            envelope.add("expression", vmReference(depth));
            JsonObject chain = new VmExpressionTable.Store(owner -> false)
                    .importEnvelope(envelope).getAsJsonObject("expression");
            if (doubled) assertSame(chain.get("_left"), chain.get("_right"));
            Set<String> symbols = new LinkedHashSet<>();
            Arms.symbolsIn(chain, symbols);
            assertTrue(depth + ": " + symbols, symbols.contains("M_Z_marker"));

            // True at the marker the session minted, so outcome=false is
            // the complement of what the term held.
            Rows flipped = clean();
            flipped.expressions.put("EXPR.0000000000000001", chain);
            flipped.decisions.set(0, DecisionRow.of("s-gate", 12L,
                    flipped.anchor, "Guard#u8", 1, false,
                    "EXPR.0000000000000001",
                    Collections.<String, Long>emptyMap()));
            assertInvariant(6, GapClass.BLOCKING, "field=outcome", flipped);
        }
    }

    /**
     * A JVM's store keeps each VM node's expansion, not its definition: a
     * node another envelope names again is the same object, two nodes'
     * equal strings are one value, and a node defined again otherwise is
     * refused.
     */
    @Test
    public void aVmNodeIsKeptOnceAndDefinedAlike() {
        VmExpressionTable.Store store = new VmExpressionTable.Store(owner -> false);
        JsonObject first = store.importEnvelope(vmEnvelope(
                vmReference(1), vmDefinition(1, symbol("M_I_site"))))
                .getAsJsonObject("expression");
        JsonObject twice = store.importEnvelope(vmEnvelope(vmReference(2),
                vmDefinition(1, symbol("M_I_site")),
                vmDefinition(2, binary("==", vmReference(1),
                        symbol("M_I_site"))))).getAsJsonObject("expression");
        assertSame(first, twice.get("_left"));
        assertSame(first.get("_exp"),
                twice.getAsJsonObject("_right").get("_exp"));
        try {
            store.importEnvelope(vmEnvelope(vmReference(1),
                    vmDefinition(1, symbol("M_I_other"))));
            fail("node 1 defined again otherwise");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("conflicting"));
        }
    }

    /**
     * The engine's own plumbing is never program state: a read a generated
     * message's code (or the engine's) made is imported as the value of the
     * version it observed, so no row and no HELD value can stand on it
     * (hdfs-11741 AR1: the woven read-back of a wire carrier's leaf); a read
     * the program made stays a read.
     */
    @Test
    public void aReadThePlumbingMadeIsTheValueItObserved() {
        String message = "o/a/h/HdfsServerProtos$BlockKeyProto";
        VmExpressionTable.Store store = new VmExpressionTable.Store(
                message::equals);
        for (String site : new String[]{message, "o/a/h/PBHelper"}) {
            JsonObject read = new JsonObject();
            read.addProperty("_type", "ReadFromExpression");
            JsonObject at = new JsonObject();
            at.addProperty("className", site);
            read.add("site", at);
            JsonObject observed = new JsonObject();
            observed.add("expression", vmReference(1));
            read.add("observedVersion", observed);
            JsonObject imported = store.importEnvelope(vmEnvelope(
                    vmReference(2), vmDefinition(1, symbol("M_I_keyId")),
                    vmDefinition(2, read))).getAsJsonObject("expression");
            assertEquals(site, message.equals(site) ? "SymbolExpression"
                            : "ReadFromExpression",
                    imported.get("_type").getAsString());
            store = new VmExpressionTable.Store(message::equals);
        }
    }

    /**
     * A paged read-out is read one record at a time against the page's own
     * table, which comes after its records: each record is expanded and
     * handed on in page order, sharing the nodes the table shares (and the
     * store's earlier pages'), the header states the rest and the count, an
     * unadmitted page hands on nothing, and a record naming a node the
     * table lacks is refused.
     */
    @Test
    public void aPagedReadOutIsReadOneRecordAtATime() {
        VmExpressionTable.Store store = new VmExpressionTable.Store(owner -> false);
        JsonObject earlier = store.importEnvelope(vmEnvelope(vmReference(1),
                vmDefinition(1, symbol("M_I_site"))))
                .getAsJsonObject("expression");
        JsonObject first = new JsonObject();
        first.add("value", vmReference(2));
        JsonObject second = new JsonObject();
        second.add("value", vmReference(1));
        JsonObject page = vmPage(new JsonObject[] {first, second},
                vmDefinition(1, symbol("M_I_site")), vmDefinition(2,
                        binary("==", vmReference(1), symbol("M_I_site"))));
        List<JsonObject> read = new ArrayList<>();
        JsonObject header = store.importRecords(page.toString(), "records",
                stated -> true, record -> read.add(record.getAsJsonObject()));
        assertEquals(2, read.size());
        JsonObject value = read.get(1).getAsJsonObject("value");
        assertSame(earlier, value);
        assertSame(value, read.get(0).getAsJsonObject("value").get("_left"));
        assertEquals("PAGE", header.get("kind").getAsString());
        assertEquals(2, header.get(VmExpressionTable.RECORD_COUNT).getAsInt());
        assertFalse(header.has("records")
                || header.has(VmExpressionTable.FIELD));
        read.clear();
        store.importRecords(page.toString(), "records", stated -> false,
                record -> read.add(record.getAsJsonObject()));
        assertTrue("an unadmitted page hands on no record", read.isEmpty());
        // A node the store expanded is not read again: its expansion
        // answers, whatever the envelope repeats of it.
        store.importRecords(vmPage(new JsonObject[] {second},
                vmDefinition(1, symbol("M_I_other"))).toString(), "records",
                stated -> true, record -> read.add(record.getAsJsonObject()));
        assertSame(earlier, read.get(0).getAsJsonObject("value"));
        // A record is consumed outside the store's lock: another thread
        // imports meanwhile.
        final JsonObject[] meanwhile = new JsonObject[1];
        store.importRecords(page.toString(), "records", stated -> true,
                record -> {
                    Thread other = new Thread(() -> meanwhile[0] =
                            store.importEnvelope(vmEnvelope(vmReference(3),
                                    vmDefinition(3, symbol("M_I_next")))));
                    other.start();
                    try {
                        other.join(10_000L);
                    } catch (InterruptedException interrupted) {
                        Thread.currentThread().interrupt();
                    }
                });
        assertNotNull("a page's consumer holds no lock", meanwhile[0]);
        // Read off the text alike (a branch window too): blanks between
        // members, strings holding quotes, backslashes and brackets, a
        // member before the records whose string holds a brace.
        String compact = page.toString();
        String table = compact.substring(compact.indexOf(
                ",\"" + VmExpressionTable.FIELD + "\""));
        String spelled = "{ \"kind\" : \"PA}GE ]\" ,\n \"records\" : [ "
                + "{ \"value\" : " + vmReference(2) + " , \"note\" : "
                + "\"a \\\"q\\\" } ] \\\\\" } ,\n"
                + "{\"value\":" + vmReference(1) + "}\t]" + table;
        read.clear();
        header = store.importRecords(spelled, "records", stated -> true,
                record -> read.add(record.getAsJsonObject()));
        assertEquals("PA}GE ]", header.get("kind").getAsString());
        assertEquals(2, header.get(VmExpressionTable.RECORD_COUNT).getAsInt());
        assertEquals("a \"q\" } ] \\", read.get(0).get("note").getAsString());
        assertSame(earlier, read.get(1).getAsJsonObject("value"));
        int[] decodes = {0};
        for (int pass = 0; pass < 2; pass++) {
            store.importRepeatedRecords(spelled, "records", stated -> true,
                    JsonObject.class, record -> {
                        decodes[0]++;
                        return record.getAsJsonObject();
                    }, record -> { });
        }
        assertEquals("read again, held", 2, decodes[0]);
        // Refused, never read past: a record naming a node the table lacks;
        // a row spelled otherwise than the VM does (no row start the reader
        // knows: it stays in the row before it, which then holds two); a
        // count the rows do not meet; a table that does not close the page.
        JsonObject dangling = new JsonObject();
        dangling.add("value", vmReference(9));
        String twoRows = vmPage(new JsonObject[] {first},
                vmDefinition(1, symbol("M_I_site")), vmDefinition(2,
                        binary("==", vmReference(1), symbol("M_I_site"))))
                .toString();
        JsonObject tableFirst = new JsonObject();
        tableFirst.add(VmExpressionTable.FIELD,
                page.get(VmExpressionTable.FIELD));
        tableFirst.add("records", page.get("records"));
        String[][] refusals = {
            {vmPage(new JsonObject[] {dangling}, vmDefinition(1,
                    symbol("M_I_site"))).toString(), "missing"},
            {twoRows.replace(",{\"_type\":\"VmExpressionDefinition\","
                    + "\"sessionId\":1,\"expressionId\":2,",
                    ",{\"sessionId\":1,\"_type\":\"VmExpressionDefinition\","
                            + "\"expressionId\":2,"), "more than one row"},
            {twoRows.replace("\"definitionCount\":2",
                    "\"definitionCount\":3"), "count"},
            {tableFirst.toString(), "close"},
        };
        for (String[] refused : refusals) {
            try {
                new VmExpressionTable.Store(owner -> false).importRecords(refused[0],
                        "records", stated -> true, record -> { });
                fail("read: " + refused[0]);
            } catch (IllegalArgumentException refusal) {
                assertTrue(refusal.getMessage(),
                        refusal.getMessage().contains(refused[1]));
            }
        }
    }

    /**
     * A record a read-out states again unchanged is decoded once: the store
     * hands on the decoding its first reading had, in page order, and a
     * page whose every record it holds reads no table (here a broken one,
     * which a page with a record to decode is refused for).  A record
     * changed by one member is decoded again and held from then on.
     */
    @Test
    public void aRepeatedRecordIsDecodedOnce() {
        VmExpressionTable.Store store =
                new VmExpressionTable.Store(owner -> false);
        JsonObject first = new JsonObject();
        first.add("value", vmReference(2));
        JsonObject second = new JsonObject();
        second.add("value", vmReference(1));
        JsonObject[] definitions = {vmDefinition(1, symbol("M_I_site")),
                vmDefinition(2, binary("==", vmReference(1),
                        symbol("M_I_site")))};
        String page = vmPage(new JsonObject[] {first, second}, definitions)
                .toString();
        int[] decodes = {0};
        List<JsonObject> read = new ArrayList<>();
        java.util.function.Function<com.google.gson.JsonElement, JsonObject>
                decode = record -> {
                    decodes[0]++;
                    return record.getAsJsonObject();
                };
        JsonObject header = store.importRepeatedRecords(page, "records",
                stated -> true, JsonObject.class, decode, read::add);
        assertEquals(2, decodes[0]);
        assertEquals(2, header.get(VmExpressionTable.RECORD_COUNT).getAsInt());
        List<JsonObject> again = new ArrayList<>();
        String broken = page.replace("\"definitionCount\":2",
                "\"definitionCount\":3");
        header = store.importRepeatedRecords(broken, "records",
                stated -> true, JsonObject.class, decode, again::add);
        assertEquals("held: decoded no more", 2, decodes[0]);
        assertEquals(2, header.get(VmExpressionTable.RECORD_COUNT).getAsInt());
        assertSame(read.get(0), again.get(0));
        assertSame(read.get(1), again.get(1));
        JsonObject changed = second.deepCopy();
        changed.addProperty("readEventId", 7L);
        String moved = vmPage(new JsonObject[] {first, changed},
                definitions).toString();
        try {
            store.importRepeatedRecords(moved.replace(
                    "\"definitionCount\":2", "\"definitionCount\":3"),
                    "records", stated -> true, JsonObject.class, decode,
                    record -> { });
            fail("a page with a record to decode reads its table");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("count"));
        }
        again.clear();
        store.importRepeatedRecords(moved, "records", stated -> true,
                JsonObject.class, decode, again::add);
        assertEquals("only the changed record is decoded", 3, decodes[0]);
        assertSame(read.get(0), again.get(0));
        assertEquals(7L, again.get(1).get("readEventId").getAsLong());
        assertSame(read.get(0).get("value"), again.get(0).get("value"));
        store.importRepeatedRecords(moved, "records", stated -> true,
                JsonObject.class, decode, record -> { });
        assertEquals(3, decodes[0]);
    }

    /** A read-out page: its records, then its table, as the VM writes it. */
    private static JsonObject vmPage(JsonObject[] records,
                                     JsonObject... definitions) {
        JsonObject page = new JsonObject();
        page.addProperty("kind", "PAGE");
        JsonArray held = new JsonArray();
        for (JsonObject record : records) held.add(record);
        page.add("records", held);
        page.add(VmExpressionTable.FIELD, vmEnvelope(new JsonObject(),
                definitions).get(VmExpressionTable.FIELD));
        return page;
    }

    private static JsonObject vmEnvelope(JsonObject expression,
                                         JsonObject... definitions) {
        JsonArray rows = new JsonArray();
        for (JsonObject definition : definitions) rows.add(definition);
        JsonObject table = new JsonObject();
        table.addProperty("schemaVersion", 1);
        table.addProperty("kind", VmExpressionTable.KIND);
        table.addProperty("authority", VmExpressionTable.AUTHORITY);
        table.addProperty("sessionId", 1L);
        table.addProperty("definitionCount", rows.size());
        table.add("definitions", rows);
        JsonObject envelope = new JsonObject();
        envelope.add(VmExpressionTable.FIELD, table);
        envelope.add("expression", expression);
        return envelope;
    }

    private static JsonObject vmReference(long id) {
        JsonObject reference = new JsonObject();
        reference.addProperty("_type", VmExpressionTable.REFERENCE_TYPE);
        reference.addProperty("sessionId", 1L);
        reference.addProperty("expressionId", id);
        return reference;
    }

    private static JsonObject vmDefinition(long id, JsonObject expression) {
        JsonObject definition = vmReference(id);
        definition.addProperty("_type", VmExpressionTable.DEFINITION_TYPE);
        definition.add("expression", expression);
        return definition;
    }

    /**
     * An integral configuration's domain joins the c - 1, c, c + 1 of every
     * literal a recorded decision compared it with (minReplication against a
     * live replica count of 1: [1, 1] becomes [0, 2]) and never leaves what
     * its own validation admits ({@code minR <= 0} throws: [1, 2]); the
     * case's declaration still wins, and no other root widens.
     */
    @Test
    public void aComparedLiteralWidensAConfigurationWithinItsValidity() {
        OccurrenceAddress at = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0)));
        Map<String, RootDomain> declared = new LinkedHashMap<>();
        declared.put("CASE.K", RootDomain.of("CASE.K", RootKind.INTEGRAL, "",
                "-1", "+1"));
        Validity positive = Validity.of(java.math.BigInteger.ONE, null,
                "<B: int init(C)>#u3");
        Object[][] rows = {
            // root, category, validity, compared, domain
            {"CONFIG:min", RootCategory.CONFIG, Validity.ANY, "1",
                "[0, 2]"},
            {"CONFIG:min", RootCategory.CONFIG, positive, "1", "[1, 2]"},
            {"CONFIG:min", RootCategory.CONFIG, positive, "", "[1, 1]"},
            // a validation the recorded reading (1) fails clips nothing
            {"CONFIG:min", RootCategory.CONFIG, Validity.of(java.math
                    .BigInteger.valueOf(2), null, "<B: int init(C)>#u5"),
                "1", "[0, 2]"},
            {"CONFIG:min", RootCategory.CONFIG, Validity.ANY, "1 512",
                "[0, 513]"},
            {"CASE.K", RootCategory.CONFIG, Validity.ANY, "9", "[0, 2]"},
            {"HOOK.K", RootCategory.HOOK, Validity.ANY, "9", "[1, 1]"}};
        for (Object[] row : rows) {
            java.util.List<java.math.BigInteger> compared =
                    new java.util.ArrayList<>();
            for (String literal : ((String) row[3]).split(" ")) {
                if (!literal.isEmpty()) {
                    compared.add(new java.math.BigInteger(literal));
                }
            }
            RootDomain domain = RootDomain.resolved(RootMintRow.of("s", 1L,
                    at, (String) row[0], "sym", RootKind.INTEGRAL,
                    (RootCategory) row[1], "1", "1", "1", true, null, 0L)
                    .validated((Validity) row[2]), declared, compared);
            assertEquals(java.util.Arrays.toString(row), row[4],
                    "[" + domain.min() + ", " + domain.max() + "]");
        }
        JsonObject stated = new JsonObject();
        positive.write(stated);
        assertEquals("a row states it whole", positive,
                Validity.read(stated));
        assertEquals("two validations at once", Validity.of(
                java.math.BigInteger.ONE, java.math.BigInteger.TEN,
                "<B: int init(C)>#u3,x"), positive.and(Validity.of(null,
                java.math.BigInteger.TEN, "x")));
        assertEquals("either writer's: no bound one leaves open",
                Validity.ANY, positive.or(Validity.of(null,
                java.math.BigInteger.TEN, "x")));
    }

    /**
     * A root row's bounds are absolute: a configuration whose default is -1
     * states {@code domainMin "-2"}, minus two.  Only a case's declaration
     * (root-domains.jsonl) spells {@code +k}/{@code -k} off the reading.
     */
    @Test
    public void aRootRowsBoundsAreAbsoluteAndOnlyADeclarationIsRelative() {
        OccurrenceAddress at = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0)));
        Map<String, RootDomain> declared = new LinkedHashMap<>();
        declared.put("CASE.K", RootDomain.of("CASE.K", RootKind.INTEGRAL, "",
                "-2", "+3"));
        Object[][] rows = {
            {"a row's negative bound is a value", "CONFIG:k", "-2", "5",
                "[-2, 5]"},
            {"a declaration's -k is off the reading", "CASE.K", "-2", "5",
                "[98, 103]"},
            {"no bound is pinned", "CONFIG:k", null, null, "[null, null]"},
            {"a bound that is no integer is none", "CONFIG:k", "x", "5",
                "[null, 5]"}};
        for (Object[] row : rows) {
            RootDomain domain = RootDomain.resolved(RootMintRow.of("s", 1L,
                    at, (String) row[1], "sym", RootKind.INTEGRAL,
                    RootCategory.CONFIG, "100", (String) row[2],
                    (String) row[3], true, null, 0L), declared,
                    Collections.<java.math.BigInteger>emptyList());
            assertEquals((String) row[0], row[4],
                    "[" + domain.min() + ", " + domain.max() + "]");
        }
    }

    @Test
    public void rendersAndParsesEveryCausalContextAndIndex() {
        OccurrenceAddress anchored = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC),
                index(frame(RUN, 0), frame(CHECKSUM, 2), frame(COMPUTE, 0)));
        assertEquals(DN0.render() + "/region/" + REGION
                        + "/ctx:Anchor:" + PRODUCER_ID + "@" + RPC
                        + "/idx:" + RUN + "@0/" + CHECKSUM + "@2/"
                        + COMPUTE + "@0",
                anchored.render());
        assertEquals(anchored, OccurrenceAddress.parse(anchored.render()));
        assertEquals(anchored.id(),
                OccurrenceAddress.parse(anchored.render()).id());
        assertEquals(16, anchored.id().length());
        assertFalse(anchored.lineageLost());
        assertEquals(3, anchored.index().frames().size());

        // A daemon tick has no incoming message, only its role and the k-th
        // tick of that role inside the window.
        OccurrenceAddress tick = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", 3),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
        assertEquals(NN0.render() + "/region/REGION.a1b2"
                        + "/ctx:Root:KEY_MANAGER_TICK#3"
                        + "/idx:o.a.h.h.s.b.KeyManager#run#9@0",
                tick.render());
        assertEquals(tick, OccurrenceAddress.parse(tick.render()));

        // A scope nobody could attribute degrades to its role and says so in
        // the id itself, rather than in a flag beside it.
        OccurrenceAddress lost = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.UNKNOWN), ExecutionIndex.empty());
        assertEquals(NN0.render()
                + "/region/REGION.a1b2/ctx:Lost:UNKNOWN/idx:", lost.render());
        assertEquals(lost, OccurrenceAddress.parse(lost.render()));
        assertTrue(lost.lineageLost());
        assertEquals(16, ExecutionIndex.empty().hash().length());
        assertEquals(anchored.index(),
                ExecutionIndex.parse(anchored.index().render()));
    }

    @Test
    public void theSameControlPathIsTheSameOccurrence() {
        List<Frame> path = Arrays.asList(frame(RUN, 0), frame(CHECKSUM, 2),
                frame(COMPUTE, 0));
        CausalContext started = CausalContext.of(PRODUCER_ID, RPC);
        OccurrenceAddress recorded =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(path));
        // The replay ran an unrelated extra invocation elsewhere: nothing on
        // the path to the region moved, so it is the same occurrence -- which
        // is the whole reason the index replaced the k-th-activation ordinal.
        OccurrenceAddress replayed =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(Arrays.asList(frame(RUN, 0),
                                frame(CHECKSUM, 2), frame(COMPUTE, 0))));
        assertEquals(recorded, replayed);
        assertEquals(recorded.id(), replayed.id());
        // One more turn of a loop ON the path is a different occurrence, and
        // so is the same path reached for another reason.
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                started, index(frame(RUN, 0), frame(CHECKSUM, 3),
                        frame(COMPUTE, 0))).id());
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.of(path)).id());

        // Same port, same consumer: only the producer endpoint tells two
        // deliveries apart, so only the interaction is a usable family key.
        ExecutionIndex site = index(frame("o.a.h.h.p.PBHelper#convert#31", 0));
        Endpoint attach = Endpoint.of(recorded, PORT, site, 0);
        Endpoint first = Endpoint.of(tick(1), PORT, site, 0);
        Endpoint second = Endpoint.of(tick(2), PORT, site, 0);
        Endpoint retried = Endpoint.of(tick(1), PORT, site, 1);
        assertNotEquals(first.id(), second.id());
        assertNotEquals(first.id(), retried.id());
        assertNotEquals(first.id(), Endpoint.of(tick(1), PORT,
                index(frame("o.a.h.h.p.PBHelper#convert#31", 1)), 0).id());
        Interaction delivered = Interaction.of(InteractionKind.WIRE, first,
                attach);
        assertNotEquals(delivered.id(), Interaction.of(InteractionKind.WIRE,
                second, attach).id());
        assertNotEquals(delivered.id(), Interaction.of(InteractionKind.STATE,
                first, attach).id());
        assertFalse(delivered.producer().occurrence().lineageLost());
        assertTrue(Interaction.of(InteractionKind.WIRE,
                Endpoint.of(OccurrenceAddress.of(NN0, "REGION.a1b2",
                        CausalContext.of(Role.UNKNOWN), site), PORT, site, 0),
                attach).producer().occurrence().lineageLost());

        // A store's re-delivery of one version to one watcher is its own
        // activation (MessageDoors#fetched: KIND.n from the second on), and
        // how many a run takes is the store's timing: every delivery is
        // addressed alike for CONFIRM (anyDelivery), and nothing else is.
        String[][] deliveries = {
                {"SOLR_ZK.ZKSTATEREADER$STATEWATCHER.2/OVERSEER_STATE_UPDATE",
                        "SOLR_ZK.ZKSTATEREADER$STATEWATCHER/OVERSEER_STATE_UPDATE"},
                {"SOLR_ZK.ZKSTATEREADER$STATEWATCHER/OVERSEER_STATE_UPDATE",
                        null},
                {"SOLR_HTTP/.update", null},
                {"HADOOP_IPC/ping.2", null}};
        for (String[] row : deliveries) {
            OccurrenceAddress notified = OccurrenceAddress.of(DN0, REGION,
                    CausalContext.of(PRODUCER_ID, row[0]),
                    ExecutionIndex.of(path));
            assertEquals(row[0], row[1] == null ? notified
                    : OccurrenceAddress.of(DN0, REGION, CausalContext.of(
                    PRODUCER_ID, row[1]), ExecutionIndex.of(path)),
                    notified.anyDelivery());
        }

        // ONE owner spelling, the one the runtime writes: the VM's
        // symbolic rid of the object whose state this is.  A join is per
        // session, and inside one run two rids are two objects.  The
        // allocation-endpoint owner this asked for is deleted -- no main
        // code produced it, and the gate that admitted only it refused
        // every row of both corpora.
        LocationId expiry = LocationId.of(LocationKind.INSTANCE, "12",
                "expiryDate");
        assertEquals("12", expiry.owner());
        assertNotEquals(expiry, LocationId.of(LocationKind.INSTANCE, "13",
                "expiryDate"));
        assertEquals("INSTANCE 12.expiryDate", expiry.toString());
    }

    @Test
    public void selectorsReadTheV1CaseDeclarations() {
        Selector declared = OccurrenceAddress.parseSelector(V1_WITH_API);
        assertEquals(DN0, declared.node());
        assertEquals(REGION, declared.regionId());
        assertEquals(DECLARED_API, declared.api());
        assertEquals(1, declared.k());
        assertEquals(V1_WITH_API, declared.render());
        Selector elsewhere = OccurrenceAddress.parseSelector(V1_BARE);
        assertEquals(NodeId.of("hdfs-17899/dn0", 0), elsewhere.node());
        assertEquals(REGION, elsewhere.regionId());
        assertNull(elsewhere.api());
        assertEquals(2, elsewhere.k());

        OccurrenceAddress anchored = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0)));
        // The same region on another component is another case: the node the
        // declaration names is part of what selects.
        assertFalse(elsewhere.matches(anchored, null));
        // Region only, on this component: every occurrence of that region is a
        // candidate, and k among them is the scheduler's business.
        Selector here = OccurrenceAddress.parseSelector(
                DN0.render() + "/region/" + REGION + "#2");
        assertTrue(here.matches(anchored, null));
        assertTrue(declared.matches(anchored, DECLARED_API));
        assertFalse(declared.matches(anchored, "hdfs-17897/client#epoch0/x"));
        assertFalse(here.matches(OccurrenceAddress.of(DN0, "REGION.other",
                CausalContext.of(PRODUCER_ID, RPC), index(frame(RUN, 0))),
                null));
        // A selector that names an api matches nothing no message started.
        assertFalse(declared.matches(tick(1), DECLARED_API));
        // A declaration with no component selects on every component, and
        // round-trips through its own rendering.
        Selector anywhere = Selector.of(REGION, null, 1, null);
        assertTrue(anywhere.matches(anchored, null));
        assertEquals(anywhere, OccurrenceAddress.parseSelector(
                anywhere.render()));
    }

    @Test
    public void everyRowKindSurvivesItsFileInTheSessionLayout()
            throws IOException {
        Path root = iteration.getRoot().toPath();
        SessionDir session = SessionDir.of(root, "s-17897-1").create();
        assertEquals(root.resolve("sessions").resolve("s-17897-1")
                .resolve(SessionDir.ACTIVATIONS), session.activations());

        OccurrenceAddress anchor = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(PRODUCER_ID, RPC),
                index(frame(RUN, 0), frame(CHECKSUM, 2), frame(COMPUTE, 0)));
        OccurrenceAddress producer = OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.UNKNOWN),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
        ExecutionIndex site = index(frame("o.a.h.h.p.PBHelper#convert#31", 0));
        Endpoint attach = Endpoint.of(anchor, PORT, site, 1);
        Endpoint export = Endpoint.of(producer, PORT, site, 0);
        LocationId keys = LocationId.of(LocationKind.MAP,
                "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys");
        Map<String, Long> clocks = new LinkedHashMap<>();
        clocks.put("clock_dn0", 1757700000000L);

        // The sender its anchor names rides along, so a reader follows the
        // causal chain past the anchor.
        ActivationRow activation = ActivationRow.of("s-17897-1", anchor,
                "task-1", true, true, "DataXceiver-7#41",
                ActivationRow.ClaimKind.NONE, export);
        // The session's own event order: export, attach, write, decision,
        // read, anchor -- the numbers a producer's condition is cut at.
        DecisionRow decision = DecisionRow.of("s-17897-1", 12L, anchor,
                "BlockTokenSecretManager#retrieve#61", 1, false,
                "(= v_H_key_id 3)", clocks);
        ExportRow exported = ExportRow.of("s-17897-1", 4L, export,
                "EXPR.v1.9f2c", "I", 41L, "3");
        AttachRow attached = AttachRow.of("s-17897-1", 9L, attach,
                "v_H_key_id", "I", "3", true, "4", export, "xch-53092d3e",
                "HANDLE");
        WriteRow written = WriteRow.of("s-17897-1", 10L,
                Endpoint.of(anchor, Endpoint.stateSite(
                        "BlockTokenSecretManager", "addKeys", 12, true), site,
                        0), keys, 7L, "EXPR.v1.7ab1", BLOCK_KEY);
        ReadRow read = ReadRow.of("s-17897-1", 14L,
                Endpoint.of(anchor, Endpoint.stateSite(
                        "BlockTokenSecretManager", "retrieve", 61, false),
                        site, 0), keys, 7L, "state_allKeys_7", BLOCK_KEY,
                null);
        RootMintRow minted = RootMintRow.of("s-17897-1", 2L, producer,
                "SERIAL_NO", "root_serial_no", RootKind.INTEGRAL,
                RootCategory.HOOK, "3", "3", "6", true, null, 0L);
        TargetRow target = TargetRow.of("s-17897-1", 15L, anchor,
                "BlockTokenSecretManager#retrieve#61", "(= key nil)", true,
                true);
        GapRow gap = GapRow.of("s-17897-1", GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, export.id(),
                "the exporter ran outside any attributable scope");

        assertEquals(activation, RowCodec.readActivation(
                reline(RowCodec.writeActivation(activation)), new RowPool()));
        // A claimed task states its claim's kind: how an order holds it.
        ActivationRow handed = ActivationRow.of("s-17897-1", anchor,
                "task-1", true, true, ActivationRow.CLAIMED + "s|k",
                ActivationRow.ClaimKind.HANDOFF_TASK, null);
        assertEquals(handed, RowCodec.readActivation(
                reline(RowCodec.writeActivation(handed)), new RowPool()));
        assertTrue(handed.heldWhereItRuns(Collections.<String>emptySet()));
        assertFalse("a hand-off task that served a queue",
                handed.heldWhereItRuns(Collections.singleton(
                        handed.threadKey())));
        // A claimed row from before claimKind reads as NONE and keeps the
        // send rule.
        JsonObject legacy = RowCodec.writeActivation(handed);
        legacy.remove("claimKind");
        ActivationRow old = RowCodec.readActivation(reline(legacy),
                new RowPool());
        assertEquals(ActivationRow.ClaimKind.NONE, old.claimKind());
        assertFalse(old.heldWhereItRuns(Collections.<String>emptySet()));
        // Claimed work is keyed by its claimed start, never by its thread.
        try {
            ActivationRow.of("s-17897-1", anchor, "task-1", true, true,
                    "pool-1-thread-1#20", ActivationRow.ClaimKind.ITEM, null);
            fail("an item keyed by its thread");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("claimed start"));
        }
        // An activation a lightweight entry hook published carries no thread
        // starter, and says the region was never instrumented -- so a reader
        // that finds no decisions for it knows why.
        ActivationRow ambient = ActivationRow.of("s-17897-1", producer, "",
                false, false, "KeyManager-1#13");
        ActivationRow ambientBack = RowCodec.readActivation(
                reline(RowCodec.writeActivation(ambient)), new RowPool());
        assertEquals(ambient, ambientBack);
        assertFalse(ambientBack.instrumented());
        assertEquals("KeyManager-1#13", ambientBack.threadKey());
        assertEquals(decision, RowCodec.readDecision(
                reline(RowCodec.writeDecision(decision)), new RowPool()));
        assertEquals(exported, RowCodec.readExport(
                reline(RowCodec.writeExport(exported)), new RowPool()));
        assertEquals(attached, RowCodec.readAttach(
                reline(RowCodec.writeAttach(attached)), new RowPool()));
        assertEquals(written, RowCodec.readWrite(
                reline(RowCodec.writeWrite(written)), new RowPool()));
        // A reference write states its container's state, or why not.
        LocationId map = LocationId.of(LocationKind.MAP, "42", "-3");
        for (WriteRow reference : Arrays.asList(
                WriteRow.of("s-17897-1", 11L, written.endpoint(),
                        LocationId.of(LocationKind.INSTANCE, "8", "16"), 9L,
                        "EXPR.v1.7ab1", "L", WriteRow.Referent.of(map, 7L),
                        null),
                WriteRow.of("s-17897-1", 11L, written.endpoint(),
                        LocationId.of(LocationKind.INSTANCE, "8", "16"), 9L,
                        "EXPR.v1.7ab1", "L", null, "RESIZING"))) {
            assertEquals(reference, RowCodec.readWrite(
                    reline(RowCodec.writeWrite(reference)), new RowPool()));
        }
        assertFalse(RowCodec.writeWrite(written).has("referentState"));
        assertEquals(read, RowCodec.readRead(
                reline(RowCodec.writeRead(read)), new RowPool()));
        // A placeholder's mint version is part of the row it round-trips as.
        ReadRow placeholder = ReadRow.of("s-17897-1", 14L, read.endpoint(),
                keys, 7L, "state_allKeys_7", BLOCK_KEY, null, 9L);
        assertEquals(placeholder, RowCodec.readRead(
                reline(RowCodec.writeRead(placeholder)), new RowPool()));
        assertFalse("a stated mint version is not the unknown one",
                placeholder.equals(read));
        // So is an unnamed writer: the read joins, alternatives not.
        ReadRow partial = ReadRow.of("s-17897-1", 14L, read.endpoint(),
                keys, 7L, "state_allKeys_7", BLOCK_KEY, null,
                ReadRow.UNKNOWN_VERSION, true);
        assertEquals(partial, RowCodec.readRead(
                reline(RowCodec.writeRead(partial)), new RowPool()));
        assertFalse(partial.equals(read));
        assertFalse(RowCodec.writeRead(read).has("unnamedWriter"));
        assertEquals(minted, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(minted))));
        // A clock states the instant its node's clock ran it at and how far
        // that ran off the host's reading, the reading a skew is off; a
        // reading at the host's own instant states no skew.
        RootMintRow ranOn = RootMintRow.of("s-17897-1", 16067L, producer,
                "CLOCK.nn0", "M_J_clock", RootKind.CLOCK, RootCategory.CLOCK,
                "1790775789773", null, null, true,
                Clock.of(1_000_000L, Clock.WALL), 3_600_000L);
        assertEquals(ranOn, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(ranOn))));
        assertEquals("1790772189773", ranOn.hostReading());
        assertFalse(RowCodec.writeRootMint(minted).has(
                RootMintRow.CLOCK_SKEW));
        assertEquals(target, RowCodec.readTarget(
                reline(RowCodec.writeTarget(target))));
        // A FORCED run's rows (PIPELINE §7.10): a decision states the arm
        // its operands decided, a target its forcing, which observed no
        // fatal; a row of any other run states neither.
        DecisionRow forcedDecision = decision.forced(true);
        TargetRow forcedTarget = target.forced();
        assertEquals(forcedDecision, RowCodec.readDecision(
                reline(RowCodec.writeDecision(forcedDecision)),
                new RowPool()));
        assertEquals(forcedTarget, RowCodec.readTarget(
                reline(RowCodec.writeTarget(forcedTarget))));
        assertTrue(forcedDecision.isForced()
                && forcedDecision.concreteOutcome()
                && !forcedDecision.outcome());
        assertTrue(forcedTarget.isForced() && !forcedTarget.observedFatal());
        assertFalse(RowCodec.writeDecision(decision).has("forced")
                || RowCodec.writeTarget(target).has("forced"));
        assertEquals(gap, RowCodec.readGap(reline(RowCodec.writeGap(gap))));
        // The parts a reader joins on survive the line form: the context, the
        // index, the site index, the session order and the declared sorts.
        AttachRow back = RowCodec.readAttach(
                reline(RowCodec.writeAttach(attached)), new RowPool());
        assertEquals(attach.id(), back.endpoint().id());
        assertEquals(site, back.endpoint().siteIndex());
        assertEquals(9L, back.seq());
        assertEquals("I", back.javaType());
        assertEquals(3, back.endpoint().occurrence().index().frames().size());
        assertTrue(RowCodec.readRootMint(reline(RowCodec.writeRootMint(minted)))
                .occurrence().lineageLost());
        assertEquals(2L, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(minted))).seq());
        assertEquals(GapKind.SOLVER_TIMEOUT, RowCodec.readGap(reline(
                RowCodec.writeGap(GapRow.of("s-17897-1",
                        GapKind.SOLVER_TIMEOUT, GapClass.BLOCKING,
                        anchor.id(), "z3 gave no answer in 900s")))).kind());
        // A nullable field that was null comes back null, not "" or "null".
        assertNull(RowCodec.readRead(reline(RowCodec.writeRead(read)),
                new RowPool()).concreteValue());

        RowCodec.writeAll(session.attaches(), Arrays.asList(attached,
                AttachRow.of("s-17897-1", 11L, Endpoint.of(anchor, PORT,
                        index(frame("o.a.h.h.p.PBHelper#convert#31", 1)), 0),
                        "v_H_key_id_2", "I", "5", false, null, null,
                        "xch-53092d3e", "")), RowCodec::writeAttach);
        List<AttachRow> rows = RowCodec.readAll(session.attaches(),
                json -> RowCodec.readAttach(json, new RowPool()));
        assertEquals(2, rows.size());
        assertEquals(attached, rows.get(0));
        // WHICH key paired it survives the round trip, and a blank one is
        // UNSTATED rather than a third spelling: the unpaired row already
        // says so with a null producer.
        assertEquals("HANDLE", rows.get(0).pairedBy());
        assertNull(rows.get(1).pairedBy());
        assertNull(rows.get(1).producer());
        // Reading one kind never touches another kind's file.
        assertTrue(RowCodec.readAll(session.reads(),
                json -> RowCodec.readRead(json, new RowPool())).isEmpty());

        JsonObject expression = new JsonObject();
        expression.addProperty("op", "SYMBOL");
        expression.addProperty("name", "root_serial_no");
        Map<String, JsonObject> expressions = new LinkedHashMap<>();
        expressions.put("EXPR.v1.9f2c", expression);
        RowCodec.writeExpressions(session.expressions(),
                ExpressionTable.of(expressions));
        assertEquals(ExpressionTable.of(expressions),
                SessionExpressionLog.read(session.expressions(),
                        new RowPool()));
        assertEquals(Collections.singletonList(session),
                SessionDir.sessionsIn(root));

        // ---- the row contract as a GATE (RowInvariants) ----------------
        //
        // One table, one row per rule: what a recording has to state, and
        // what it is told when it does not.  This is the shape of the fix
        // 17960 needed twice -- a decision whose outcome was the complement
        // of its term's truth value, and a focused session whose expression
        // table was empty -- so each rule is checked where every row passes
        // through rather than in the stage that happened to trip over it.
        assertTrue("a recording that states everything states no violation: "
                        + names(gate(clean())),
                gate(clean()).isEmpty());
        // 1: exactly one seed session per epoch, and every row's occurrence
        // ran in its own session.
        Rows second = clean();
        second.id = "s-two";
        assertInvariant(1, GapClass.BLOCKING, "epoch/sessions",
                clean(), second);
        Rows unactivated = clean();
        unactivated.activations.clear();
        assertInvariant(1, GapClass.BLOCKING, "field=occurrence",
                unactivated);
        // 2: never neither -- a read states a version or a value.
        Rows neither = clean();
        neither.reads.set(0, ReadRow.of("s-gate", 14L, neither.readAt, keys,
                -1L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(2, GapClass.BLOCKING, "field=observedVersion",
                neither);
        // An attach is paired by the handle or by correlation+port; no
        // stated key is unstated, not unpaired; any other key is refused.
        for (Object[] pairing : new Object[][] {
                {AttachRow.HANDLE, true, ""},
                {AttachRow.CORRELATION_PORT, true, ""},
                {null, false, ""},
                {"ENVELOPE", true, "names a third key"}}) {
            Rows paired = clean();
            paired.attaches.add(AttachRow.of("s-gate", 18L, paired.readAt,
                    "M_J_field_HOFF.1", "J", "1727", false, null,
                    (Boolean) pairing[1] ? paired.writeAt : null,
                    "corr-1", (String) pairing[0]));
            String refusal = (String) pairing[2];
            if (refusal.isEmpty()) {
                assertTrue(names(gate(paired)).toString(),
                        noViolation(gate(paired), 2));
            } else {
                assertInvariant(2, GapClass.BLOCKING, refusal, paired);
            }
        }
        // 3: a reference a row cites exists in its OWN session's table, and
        // no other reference spelling appears.
        Rows empty = clean();
        empty.expressions.clear();
        assertInvariant(3, GapClass.BLOCKING, "field=term", empty);
        Rows spelled = clean();
        spelled.decisions.set(0, DecisionRow.of("s-gate", 12L,
                spelled.anchor, "Guard#u8", 1, true, "EXPR.v1.9f2c", clocks));
        assertInvariant(3, GapClass.BLOCKING, "EXPR.v1.9f2c", spelled);
        // 4: one row per event; an endpoint two events share is the site
        // index's failure and is recorded, not refused.
        Rows twice = clean();
        twice.reads.add(twice.reads.get(0));
        assertInvariant(4, GapClass.BLOCKING, "field=seq/location", twice);
        Rows collided = clean();
        collided.reads.add(ReadRow.of("s-gate", 20L, collided.readAt, keys,
                7L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(4, GapClass.DIAGNOSTIC, "site index missing",
                collided);
        // A target row that did not reach its anchor states no event, so
        // two occurrences that both ran without reaching it are two rows;
        // two rows at one reached event are still one event twice.
        Rows unreached = clean();
        OccurrenceAddress other = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                index(frame(RUN, 0)));
        unreached.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42"));
        unreached.targets.add(TargetRow.of("s-gate", 0L, unreached.anchor,
                "Guard#u8", "", false, false));
        unreached.targets.add(TargetRow.of("s-gate", 0L, other, "Guard#u8",
                "", false, false));
        assertTrue("an unreached anchor is one row per occurrence: "
                + names(gate(unreached)), noViolation(gate(unreached), 4));
        // Nor does a concrete decision: it stands after the last VM event,
        // which two occurrences can share.
        Rows decided = clean();
        decided.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42"));
        decided.targets.add(TargetRow.of("s-gate",
                decided.targets.get(0).seq(), other, "Guard#u8", "", false,
                true));
        assertTrue("two occurrences deciding concretely after one event: "
                + names(gate(decided)), noViolation(gate(decided), 4));
        // A store read is one reader's read of one version: two nodes'
        // readers (or two versions) at one shared JVM event are two reads.
        LocationId stateJson = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/c/state.json");
        for (Object[] each : new Object[][] {
                {"another reader", other, 4L, true},
                {"another version", null, 5L, true},
                {"the same read", null, 4L, false}}) {
            Rows stored = clean();
            stored.activations.add(ActivationRow.of("s-gate", other, "t",
                    false, true, "DataXceiver-8#42"));
            Endpoint first = Endpoint.of(stored.anchor, "Guard#u3:READ",
                    stored.readAt.siteIndex(), 0);
            Endpoint reader = each[1] == null ? first
                    : Endpoint.of((OccurrenceAddress) each[1], first.site(),
                    first.siteIndex(), 0);
            stored.reads.add(ReadRow.of("s-gate", 22L, first,
                    stateJson, 4L, "S_v4", "[B", null));
            stored.reads.add(ReadRow.of("s-gate", 22L, reader, stateJson,
                    (Long) each[2], "S_v" + each[2], "[B", null));
            if ((Boolean) each[3]) {
                assertTrue(each[0] + ": " + names(gate(stored)),
                        noViolation(gate(stored), 4));
            } else {
                assertInvariant(4, GapClass.BLOCKING,
                        "field=occurrence/seq/location/version", stored);
            }
        }
        Rows reachedTwice = clean();
        reachedTwice.targets.add(reachedTwice.targets.get(0));
        assertInvariant(4, GapClass.BLOCKING,
                "field=occurrence/seq/anchorSiteId", reachedTwice);
        // A node's view of a store path is its version, as the store's own
        // write is: two decodes of two versions with no VM event between
        // them are two events; one version stated twice is one.
        LocationId view = LocationId.of(LocationKind.VIEW,
                "SOLR_ZK@auto0/node0#epoch0", "/aliases.json");
        Rows decodes = clean();
        decodes.writes.add(WriteRow.of("s-gate", 30L, decodes.writeAt, view,
                3L, "EXPR.0000000000000001", "J"));
        decodes.writes.add(WriteRow.of("s-gate", 30L, decodes.writeAt, view,
                4L, "EXPR.0000000000000001", "J"));
        for (GapRow decode : gate(decodes)) {
            assertFalse("two decodes of two versions at one event: "
                    + decode.subject(), decode.detail().contains(
                    "invariant 4 (") && decode.cls() == GapClass.BLOCKING);
        }
        decodes.writes.add(decodes.writes.get(decodes.writes.size() - 1));
        assertInvariant(4, GapClass.BLOCKING, "field=seq/location/version",
                decodes);
        // 5: one name, one spelled sort, and a placeholder read's sort is the
        // one its own row declares.
        Rows mixed = clean();
        mixed.reads.add(ReadRow.of("s-gate", 21L, mixed.placeholderAt, keys,
                7L, "M_Z_field_" + REGION + ".in.a1", "I", "2"));
        assertInvariant(5, GapClass.BLOCKING, "field=symbol/javaType", mixed);
        // 6: outcome says whether the published term HELD.
        Rows flipped = clean();
        flipped.decisions.set(0, DecisionRow.of("s-gate", 12L,
                flipped.anchor, "Guard#u8", 1, false, "EXPR.0000000000000001",
                clocks));
        assertInvariant(6, GapClass.BLOCKING, "field=outcome", flipped);
        // 7: a version some row of the session states, and never a write
        // whose whole expression is a placeholder's own symbol.
        Rows unstated = clean();
        unstated.writes.clear();
        // and the mint states a different version, so nothing states v7
        unstated.reads.set(1, ReadRow.of("s-gate", 16L,
                unstated.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2", 99L));
        assertInvariant(7, GapClass.DIAGNOSTIC, "field=observedVersion",
                unstated);
        // The mint's own store published as a write: the version the
        // placeholder minted, whatever expression the row carries.
        Rows fabricated = clean();
        fabricated.writes.add(WriteRow.of("s-gate", 11L,
                fabricated.writeAt, keys, 8L, "EXPR.0000000000000002",
                BLOCK_KEY));
        assertInvariant(7, GapClass.BLOCKING, "field=version", fabricated);
        // A legitimate copy: a later version of the cell assigned the minted
        // symbol is a write of its own, whole expression that symbol or not.
        Rows copied = clean();
        copied.writes.add(WriteRow.of("s-gate", 11L, copied.writeAt, keys,
                9L, "EXPR.0000000000000002", BLOCK_KEY));
        assertTrue("a write of another version that carries the minted "
                        + "symbol is no fabricated write: "
                        + names(gate(copied)),
                noViolation(gate(copied), 7));
        // Contract v2.4: a placeholder read states the version it mints, so
        // a version no write carries is stated all the same -- and a
        // placeholder that states none is refused, once the recording
        // publishes the field at all.
        // The mint's own version is NOT the version it observed: laneA5's
        // placeholder observed 77 and minted 177, and keying the mint by the
        // observed version refused a row whose field was right there in it.
        Rows mintStated = clean();
        mintStated.reads.set(1, ReadRow.of("s-gate", 16L,
                mintStated.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2", 177L));
        mintStated.reads.add(ReadRow.of("s-gate", 17L, mintStated.readAt,
                keys, 177L, "state_allKeys_177", BLOCK_KEY, null));
        assertTrue("the mint states 177 and a later read observes it, so "
                        + "neither is unstated: " + names(gate(mintStated)),
                noViolation(gate(mintStated), 7));
        Rows unminted = clean();
        unminted.reads.set(1, ReadRow.of("s-gate", 16L,
                unminted.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2"));
        assertInvariant(7, GapClass.BLOCKING, "field=mintVersion", unminted);
        // 8: a RootMintRow is published for a declared root, and its reading
        // is spelled the way its kind is read back.
        Rows undeclared = clean();
        undeclared.roots.set(0, RootMintRow.of("s-gate", 2L,
                undeclared.anchor, "CASE.MARKER", "M_Z_marker",
                RootKind.MARKER, RootCategory.FAULT, "true", null, null, false,
                null, 0L));
        assertInvariant(8, GapClass.BLOCKING, "field=declared", undeclared);
        Rows unspelled = clean();
        unspelled.roots.set(0, RootMintRow.of("s-gate", 2L, unspelled.anchor,
                "CASE.MARKER", "M_Z_marker", RootKind.MARKER, RootCategory.FAULT,
                "1", null, null, true, null, 0L));
        assertInvariant(8, GapClass.BLOCKING, "field=recordedValue",
                unspelled);
        // 9: a reached anchor states phi in the FATAL polarity -- a term, or
        // for a concrete fatal condition the constant of the arm it took
        // (SOLR-18413 r9: the deleted target's lookup) -- and phi holds
        // exactly on the fatal arm at the session's own root values (the
        // marker ran true, so EXPR.1 holds).  {phi, observedFatal, class}.
        Object[][] nine = {
                {"", true, GapClass.BLOCKING},
                {"", false, GapClass.DIAGNOSTIC},
                {"true", true, null},
                {"false", false, null},
                {"false", true, GapClass.BLOCKING},
                {"true", false, GapClass.BLOCKING},
                {"EXPR.0000000000000001", false, GapClass.BLOCKING},
                {"(not EXPR.0000000000000001)", false, null}};
        for (Object[] row : nine) {
            Rows stated = clean();
            stated.targets.set(0, TargetRow.of("s-gate", 15L, stated.anchor,
                    "Guard#u8", (String) row[0], (Boolean) row[1], true));
            if (row[2] == null) {
                assertTrue("phi " + row[0] + " on the " + (Boolean.TRUE.equals(
                                row[1]) ? "fatal" : "healthy") + " arm: "
                                + names(gate(stated)),
                        noViolation(gate(stated), 9));
            } else {
                assertInvariant(9, (GapClass) row[2], "field=phiTerm",
                        stated);
            }
        }
        // 11 (R4): a root symbol without its RootMintRow.  WHICH quantities
        // are roots is a fact about the SET -- CASE.MARKER is a root because
        // some session of the epoch minted a row naming it -- and a session
        // that NAMES that root's symbol while publishing no mint row of its
        // own carries a quantity nothing of it attributes.  That is 11741
        // campaign #4: the symbol reached the expressions out of an
        // activation the run abandoned, and the composer met it as an arm it
        // could not guard.
        Rows unattributed = clean();
        unattributed.id = "s-abandoned";
        unattributed.roots.clear();
        assertInvariant(11, GapClass.BLOCKING, "CASE.MARKER",
                clean(), unattributed);
        assertEquals("one row per (session, root), naming both: "
                        + names(gate(clean(), unattributed)),
                1, stating(gate(clean(), unattributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
        // And the same corpus with the mint row present states none.
        Rows attributed = clean();
        attributed.id = "s-abandoned";
        assertEquals("a session that states the mint row is not refused: "
                        + names(gate(clean(), attributed)),
                0, stating(gate(clean(), attributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
        // Gated a session at a time, an epoch states exactly what one gate
        // over all of it states, each row once: the later gate judges its
        // own session, and the rules over the set (1, 11) against the one
        // gated before -- which it reads again only for a root the later
        // one brings (the mint second) -- and a gate of sessions the ledger
        // holds judges nothing.
        for (boolean mintFirst : new boolean[] {true, false}) {
            Path epoch = iteration.newFolder().toPath();
            clean().read(epoch);
            unattributed.read(epoch);
            Path whole = epoch.resolve("whole.jsonl");
            ImportGateMain.gate(epoch, Collections.<String>emptyList(), null,
                    whole, "e");
            Path ledger = epoch.resolve("gated.txt");
            Path stepped = epoch.resolve("stepped.jsonl");
            ImportGateMain.gate(epoch, Collections.singletonList(
                    mintFirst ? "s-gate" : "s-abandoned"), ledger, stepped,
                    "e");
            ImportGateMain.gate(epoch, Collections.<String>emptyList(),
                    ledger, stepped, "e");
            JsonObject again = ImportGateMain.gate(epoch,
                    Arrays.asList("s-gate", "s-abandoned"), ledger, stepped,
                    "e");
            List<String> filed = Files.readAllLines(stepped);
            assertEquals("mint first: " + mintFirst,
                    new LinkedHashSet<>(Files.readAllLines(whole)),
                    new LinkedHashSet<>(filed));
            assertEquals("invariants 1 and 11, each once: " + filed, 2,
                    filed.size());
            assertEquals(0, again.get("sessions").getAsInt());
        }
        // 12: a reference write's container state is an older write of the
        // session (v7); a version no row states (the placeholder's minted
        // v8) is evidence lost, not a malformed row; one not older than the
        // store (v9) is.
        for (long named : new long[] {7L, 8L, 9L}) {
            Rows referring = clean();
            referring.writes.add(WriteRow.of("s-gate", 13L,
                    referring.writeAt, LocationId.of(LocationKind.INSTANCE,
                            "5", "16"), 9L, "EXPR.0000000000000001", "L",
                    WriteRow.Referent.of(referring.writes.get(0).location(),
                            named), null));
            if (named == 7L) {
                assertTrue(names(gate(referring)).toString(),
                        noViolation(gate(referring), 12));
            } else {
                assertInvariant(12, named == 8L ? GapClass.DIAGNOSTIC
                        : GapClass.BLOCKING, "field=referentState", referring);
            }
        }
    }

    /** How many rows of one kind and class a gate stated. */
    private static int stating(List<GapRow> gaps, GapKind kind,
                               GapClass cls) {
        int count = 0;
        for (GapRow gap : gaps) {
            if (gap.kind() == kind && gap.cls() == cls) count++;
        }
        return count;
    }

    /** No violation of that rule at all, whatever its class. */
    private static boolean noViolation(List<GapRow> gaps, int rule) {
        for (GapRow gap : gaps) {
            if (gap.detail().contains("invariant " + rule)) return false;
        }
        return true;
    }

    /** One session's rows, as a recording a table row can bend. */
    private final class Rows {
        private String id = "s-gate";

        private OccurrenceAddress anchor;
        private Endpoint readAt;
        private Endpoint writeAt;
        private Endpoint placeholderAt;
        private final List<ActivationRow> activations =
                new java.util.ArrayList<>();
        private final List<DecisionRow> decisions = new java.util.ArrayList<>();
        private final List<ReadRow> reads = new java.util.ArrayList<>();
        private final List<WriteRow> writes = new java.util.ArrayList<>();
        private final List<RootMintRow> roots = new java.util.ArrayList<>();
        private final List<TargetRow> targets = new java.util.ArrayList<>();
        private final List<ExportRow> exports = new java.util.ArrayList<>();
        private final List<AttachRow> attaches = new java.util.ArrayList<>();
        private final Map<String, JsonObject> expressions =
                new LinkedHashMap<>();

        private SessionReader read(Path root) throws IOException {
            SessionDir dir = SessionDir.of(root, id).create();
            RowCodec.writeAll(dir.activations(), activations,
                    RowCodec::writeActivation);
            RowCodec.writeAll(dir.decisions(), decisions,
                    RowCodec::writeDecision);
            RowCodec.writeAll(dir.reads(), reads, RowCodec::writeRead);
            RowCodec.writeAll(dir.writes(), writes, RowCodec::writeWrite);
            RowCodec.writeAll(dir.roots(), roots, RowCodec::writeRootMint);
            RowCodec.writeAll(dir.targets(), targets, RowCodec::writeTarget);
            RowCodec.writeAll(dir.exports(), exports, RowCodec::writeExport);
            RowCodec.writeAll(dir.attaches(), attaches,
                    RowCodec::writeAttach);
            RowCodec.writeExpressions(dir.expressions(),
                    ExpressionTable.of(expressions));
            // The fixture STATES the role, as a campaign's own session
            // manifest does.
            boolean focused = false;
            for (ActivationRow activation : activations) {
                if (activation.focused()) focused = true;
            }
            RowCodec.writeManifest(dir.manifest(),
                    SessionManifest.of(id,
                            focused ? SessionManifest.Role.FOCUSED
                                    : SessionManifest.Role.SEED,
                            focused ? java.util.Collections.singletonList(
                                    "OBL." + id)
                                    : java.util.Collections
                                            .<String>emptyList()));
            return SessionReader.read(dir);
        }
    }

    /** A recording that states everything the contract asks of one. */
    private Rows clean() {
        Rows rows = new Rows();
        rows.anchor = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 1),
                index(frame(RUN, 0)));
        ExecutionIndex site = index(frame(COMPUTE, 0));
        rows.readAt = Endpoint.of(rows.anchor, Endpoint.stateSite(
                "BlockTokenSecretManager", "retrieve", 61, false), site, 0);
        rows.writeAt = Endpoint.of(rows.anchor, Endpoint.stateSite(
                "BlockTokenSecretManager", "addKeys", 12, true), site, 0);
        rows.placeholderAt = Endpoint.of(rows.anchor,
                "INSTANCE_FIELD/2#24" + RowInvariants.PLACEHOLDER + "0:READ",
                site, 0);
        rows.activations.add(ActivationRow.of("s-gate", rows.anchor, "t", false,
                true, "DataXceiver-7#41"));
        // A marker the session minted true, and a term that is true at it.
        rows.roots.add(RootMintRow.of("s-gate", 2L, rows.anchor,
                "CASE.MARKER", "M_Z_marker", RootKind.MARKER, RootCategory.FAULT,
                "true", null, null, true, null, 0L));
        rows.expressions.put("EXPR.0000000000000001",
                binary("!=", symbol("M_Z_marker"), literal("Y_Z_0")));
        rows.expressions.put("EXPR.0000000000000002",
                symbol("M_I_field_" + REGION + ".in.a1"));
        rows.decisions.add(DecisionRow.of("s-gate", 12L, rows.anchor,
                "Guard#u8", 1, true, "EXPR.0000000000000001",
                Collections.<String, Long>emptyMap()));
        rows.writes.add(WriteRow.of("s-gate", 10L, rows.writeAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "EXPR.0000000000000001", BLOCK_KEY));
        rows.reads.add(ReadRow.of("s-gate", 14L, rows.readAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "state_allKeys_7", BLOCK_KEY, null));
        // The declared region input, as a placeholder read: the only row
        // that mints it, so a write whose whole expression IS its symbol
        // would be a value the two of them fabricated between them.
        rows.reads.add(ReadRow.of("s-gate", 16L, rows.placeholderAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "M_I_field_" + REGION + ".in.a1", "I", "2", 8L));
        rows.targets.add(TargetRow.of("s-gate", 15L, rows.anchor, "Guard#u8",
                "EXPR.0000000000000001", true, true));
        return rows;
    }

    /** The violations one set of sessions states. */
    private List<GapRow> gate(Rows... sessions) throws IOException {
        Path root = iteration.newFolder().toPath();
        for (Rows rows : sessions) rows.read(root);
        return RowInvariants.check(Collections.<SessionDir>emptyList(),
                SessionDir.sessionsIn(root),
                Collections.<String, List<JsonObject>>emptyMap());
    }

    /** That rule, that class, that subject -- and nothing silent. */
    private void assertInvariant(int rule, GapClass cls, String subject,
                                 Rows... sessions) throws IOException {
        List<GapRow> gaps = gate(sessions);
        for (GapRow gap : gaps) {
            if (gap.cls() != cls) continue;
            if (!gap.detail().contains("invariant " + rule)) continue;
            if (gap.subject().contains(subject)
                    || gap.detail().contains(subject)) {
                return;
            }
        }
        throw new AssertionError("invariant " + rule + " did not state " + cls
                + " over " + subject + "; it stated " + names(gaps));
    }

    private static List<String> names(List<GapRow> gaps) {
        List<String> named = new java.util.ArrayList<>();
        for (GapRow gap : gaps) {
            named.add(gap.cls() + " " + gap.subject());
        }
        return named;
    }

    private static JsonObject symbol(String name) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        return node;
    }

    private static JsonObject literal(String value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_exp", value);
        return node;
    }

    private static JsonObject binary(String op, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", op);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    private static Frame frame(String callSite, int iteration) {
        return Frame.of(callSite, iteration);
    }

    private static ExecutionIndex index(Frame... frames) {
        return ExecutionIndex.of(Arrays.asList(frames));
    }

    /** The w-th key-manager tick of the name node. */
    private static OccurrenceAddress tick(int windowIndex) {
        return OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", windowIndex),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
    }

    /** One row through the line form it is stored in and back. */
    private static JsonObject reline(JsonObject row) {
        return RowCodec.fromLine(RowCodec.toLine(row));
    }
}
