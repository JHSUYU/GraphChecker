package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
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

    private static final String RUN = "o.a.h.h.s.d.DataXceiver#run#12";
    private static final String CHECKSUM =
            "o.a.h.h.s.d.DataXceiver#blockChecksum#48";
    private static final String COMPUTE =
            "o.a.h.h.s.d.BlockChecksumHelper#compute#7";

    @Rule
    public TemporaryFolder iteration = new TemporaryFolder();

    @Test
    public void aGzipRowFileReadsAsFarAsItWasWritten() throws IOException {
        Path dir = iteration.getRoot().toPath();
        List<GapRow> rows = new ArrayList<GapRow>();
        StringBuilder text = new StringBuilder();
        for (int at = 0; at < 3; at++) {
            rows.add(GapRow.of("s", GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, "row " + at, "the " + at + "th"));
            text.append(RowCodec.toLine(RowCodec.writeGap(rows.get(at))))
                    .append('\n');
        }
        Path open = dir.resolve("open" + SessionDir.GAPS);
        java.io.Writer out = new java.io.OutputStreamWriter(
                ArtifactIO.appending(open), StandardCharsets.UTF_8);
        long[] flushedAt = new long[rows.size()];
        for (int at = 0; at < rows.size(); at++) {
            out.write(RowCodec.toLine(RowCodec.writeGap(rows.get(at))));
            out.write('\n');
            out.flush();
            flushedAt[at] = Files.size(open);
        }
        assertEquals("unfinished: every flushed row", rows,
                RowCodec.readAll(open, RowCodec::readGap));
        assertEquals(text.length(), ArtifactIO.decodedSize(open));
        byte[] unfinished = Files.readAllBytes(open);
        out.close();
        assertTrue(Files.size(open) > unfinished.length);
        assertEquals("finished", rows,
                RowCodec.readAll(open, RowCodec::readGap));
        assertEquals("its trailer's count", text.length(),
                ArtifactIO.decodedSize(open));

        Path cut = dir.resolve("cut" + SessionDir.GAPS);
        Files.write(cut, Arrays.copyOf(unfinished,
                (int) (flushedAt[1] + flushedAt[2]) / 2));
        List<String> lines = new ArrayList<String>();
        RowCodec.eachLine(cut, lines::add);
        assertTrue(lines.toString(), lines.size() >= 2);
        assertEquals(text.substring(0, text.indexOf("\n",
                text.indexOf("\n") + 1)), String.join("\n",
                lines.subList(0, 2)));
        assertTrue(text.toString().startsWith(String.join("\n", lines)));

        Path empty = dir.resolve("empty" + SessionDir.GAPS);
        Files.write(empty, new byte[0]);
        assertTrue(RowCodec.readAll(empty, RowCodec::readGap).isEmpty());
        assertEquals(0L, ArtifactIO.decodedSize(empty));

        List<GapRow> many = new ArrayList<GapRow>();
        for (int at = 0; at < 2500; at++) {
            many.add(GapRow.of("s", GapKind.UNSTATED_VALUE,
                    GapClass.DIAGNOSTIC, "row " + at, "many"));
        }
        Path members = dir.resolve("members.jsonl.gz");
        RowCodec.writeAll(members, many, RowCodec::writeGap);
        assertEquals(many, RowCodec.readAll(members, RowCodec::readGap));
        RowCodec.writeAll(members, Collections.<GapRow>emptyList(),
                RowCodec::writeGap);
        assertTrue(RowCodec.readAll(members, RowCodec::readGap).isEmpty());
        assertTrue("an empty member, whole", Files.size(members) >= 20);

        Path damaged = dir.resolve("damaged" + SessionDir.GAPS);
        Files.write(damaged, "{\"no\": \"gzip\"}\n".getBytes(
                StandardCharsets.UTF_8));
        try {
            RowCodec.readAll(damaged, RowCodec::readGap);
            fail("read a file that holds no gzip stream");
        } catch (java.io.UncheckedIOException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains(damaged.toString()));
        }
    }

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

    @Test
    public void anEnvelopeOfRecordsIsReadOneRecordAtATime() {
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
        store.importRecords(vmPage(new JsonObject[] {second},
                vmDefinition(1, symbol("M_I_other"))).toString(), "records",
                stated -> true, record -> read.add(record.getAsJsonObject()));
        assertSame(earlier, read.get(0).getAsJsonObject("value"));
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

    @Test
    public void aReadOutPageIsItsChannelsNextTable() throws Exception {
        java.util.concurrent.ExecutorService helpers =
                java.util.concurrent.Executors.newFixedThreadPool(3);
        try {
            VmExpressionTable.Store store =
                    new VmExpressionTable.Store(owner -> false);
            int[] decodes = {0};
            java.util.function.Function<com.google.gson.JsonElement,
                    JsonObject> decode = record -> {
                        synchronized (decodes) {
                            decodes[0]++;
                        }
                        return record.getAsJsonObject();
                    };
            JsonObject first = record("first", vmReference(2));
            JsonObject second = record("second", vmReference(1));
            String one = channelPage(1L, new JsonObject[] {first, second},
                    vmDefinition(1, symbol("M_I_site")), vmDefinition(2,
                            binary("==", vmReference(1), symbol("M_I_site"))));
            List<JsonObject> read = new ArrayList<>();
            assertFalse(store.truncationMarked());
            JsonObject header = store.importReadOutPage(one, "records",
                    stated -> true, JsonObject.class, decode, read::add,
                    helpers, 3);
            assertEquals(2, header.get(VmExpressionTable.RECORD_COUNT)
                    .getAsInt());
            assertEquals(2, decodes[0]);
            JsonObject site = read.get(1).getAsJsonObject("value");
            assertSame(site, read.get(0).getAsJsonObject("value")
                    .get("_left"));
            read.clear();
            store.importReadOutPage(channelPage(2L, new JsonObject[] {
                    record("third", vmReference(3))}, vmDefinition(3,
                    binary("+", vmReference(2), vmReference(1)))), "records",
                    stated -> true, JsonObject.class, decode, read::add,
                    helpers, 3);
            assertSame(site, read.get(0).getAsJsonObject("value")
                    .getAsJsonObject("_left").get("_left"));
            store.importReadOutPage(channelPage(3L, new JsonObject[] {
                    record("withheld", vmReference(4))}, vmDefinition(4,
                    symbol("M_I_late"))), "records", stated -> false,
                    JsonObject.class, decode, read::add, helpers, 3);
            assertEquals("a withheld page hands on nothing", 1, read.size());
            store.importReadOutPage(channelPage(4L, new JsonObject[] {
                    record("late", vmReference(4))}), "records",
                    stated -> true, JsonObject.class, decode, read::add,
                    helpers, 3);
            assertEquals("M_I_late", read.get(1).getAsJsonObject("value")
                    .get("_exp").getAsString());
            int before = decodes[0];
            read.clear();
            store.importReadOutPage(channelPage(5L, new JsonObject[] {first,
                    second}), "records", stated -> true, JsonObject.class,
                    decode, read::add, helpers, 3);
            assertEquals("held: decoded no more", before, decodes[0]);
            assertEquals(2, read.size());
            JsonObject[] many = new JsonObject[40];
            for (int index = 0; index < many.length; index++) {
                many[index] = record("many" + index, vmReference(
                        index == 17 ? 20 : 1 + index % 4));
            }
            read.clear();
            assertTrue(store.readOutLosses().isEmpty());
            try {
                store.importReadOutPage(channelPage(9L, many, vmDefinition(
                        20, binary("+", vmReference(7), vmReference(1))),
                        vmDefinition(21, symbol("M_I_kept"))), "records",
                        stated -> true, JsonObject.class, decode, read::add,
                        helpers, 3);
                fail("a node only a lost table defined");
            } catch (IllegalArgumentException missing) {
            }
            assertFalse(store.readOutLosses().isEmpty());
            assertEquals("handed on in page order up to the failure", 17,
                    read.size());
            for (int index = 0; index < read.size(); index++) {
                assertEquals("many" + index,
                        read.get(index).get("name").getAsString());
            }
            read.clear();
            store.importReadOutPage(channelPage(10L, new JsonObject[] {
                    record("kept", vmReference(21))}), "records",
                    stated -> true, JsonObject.class, decode, read::add,
                    helpers, 3);
            assertEquals("M_I_kept", read.get(0).getAsJsonObject("value")
                    .get("_exp").getAsString());
            String[] refusals = {
                channelPage(10L, new JsonObject[0]),
                channelPage(11L, new JsonObject[0]).replace(
                        "\"sessionId\":1,\"sequence\"",
                        "\"sessionId\":2,\"sequence\""),
                vmPage(new JsonObject[0]).toString(),
                "{\"records\":[]}",
                channelPage(11L, new JsonObject[0], vmDefinition(5,
                        symbol("M_I_x"))).replace("\"definitionCount\":1",
                        "\"definitionCount\":2"),
            };
            for (String refused : refusals) {
                try {
                    store.importReadOutPage(refused, "records",
                            stated -> true, JsonObject.class, decode,
                            record -> { }, helpers, 3);
                    fail("read: " + refused);
                } catch (IllegalArgumentException expected) {
                }
            }
            assertFalse(store.truncationMarked());
            JsonObject truncated = new JsonObject();
            truncated.addProperty("_type", "TruncatedExpression");
            truncated.addProperty("expressionAuthority",
                    "VM_SERIALIZATION_TRUNCATION_V1");
            JsonObject wrapped = binary("==", vmReference(1), truncated);
            store.importReadOutPage(channelPage(12L, new JsonObject[] {
                    record("cut", vmReference(6))}, vmDefinition(6,
                    wrapped)), "records", stated -> true, JsonObject.class,
                    decode, record -> { }, helpers, 3);
            assertTrue("a definition holding the marker",
                    store.truncationMarked());
            VmExpressionTable.Store fresh =
                    new VmExpressionTable.Store(owner -> false);
            fresh.importReadOutPage(channelPage(1L, new JsonObject[] {
                    record("cut", truncated)}), "records", stated -> true,
                    JsonObject.class, decode, record -> { }, null, 0);
            assertTrue("a record holding the marker",
                    fresh.truncationMarked());
        } finally {
            helpers.shutdownNow();
        }
    }

    private static JsonObject record(String name, JsonObject value) {
        JsonObject record = new JsonObject();
        record.addProperty("name", name);
        record.add("value", value);
        return record;
    }

    private static String channelPage(long sequence, JsonObject[] records,
                                      JsonObject... definitions) {
        JsonObject page = vmPage(records, definitions);
        JsonObject table = page.getAsJsonObject(VmExpressionTable.FIELD);
        JsonObject channel = new JsonObject();
        for (Map.Entry<String, com.google.gson.JsonElement> member
                : table.entrySet()) {
            if ("definitionCount".equals(member.getKey())) {
                channel.addProperty("sequence", sequence);
            }
            channel.add(member.getKey(), member.getValue());
        }
        channel.addProperty("authority",
                VmExpressionTable.READ_OUT_AUTHORITY);
        page.add(VmExpressionTable.FIELD, channel);
        return page.toString();
    }

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
            {"CONFIG:min", RootCategory.CONFIG, Validity.ANY, "1",
                "[0, 2]"},
            {"CONFIG:min", RootCategory.CONFIG, positive, "1", "[1, 2]"},
            {"CONFIG:min", RootCategory.CONFIG, positive, "", "[1, 1]"},
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

    @Test
    public void theSameControlPathIsTheSameOccurrence() {
        List<Frame> path = Arrays.asList(frame(RUN, 0), frame(CHECKSUM, 2),
                frame(COMPUTE, 0));
        CausalContext started = CausalContext.of(PRODUCER_ID, RPC);
        OccurrenceAddress recorded =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(path));
        OccurrenceAddress replayed =
                OccurrenceAddress.of(DN0, REGION, started,
                        ExecutionIndex.of(Arrays.asList(frame(RUN, 0),
                                frame(CHECKSUM, 2), frame(COMPUTE, 0))));
        assertEquals(recorded, replayed);
        assertEquals(recorded.id(), replayed.id());
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                started, index(frame(RUN, 0), frame(CHECKSUM, 3),
                        frame(COMPUTE, 0))).id());
        assertNotEquals(recorded.id(), OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.CLIENT, "", 1),
                ExecutionIndex.of(path)).id());

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

        LocationId expiry = LocationId.of(LocationKind.INSTANCE, "12",
                "expiryDate");
        assertEquals("12", expiry.owner());
        assertNotEquals(expiry, LocationId.of(LocationKind.INSTANCE, "13",
                "expiryDate"));
        assertEquals("INSTANCE 12.expiryDate", expiry.toString());
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

        ActivationRow activation = ActivationRow.of("s-17897-1", anchor,
                "task-1", true, true, "DataXceiver-7#41",
                ActivationRow.ClaimKind.NONE, export);
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
                true, null);
        GapRow gap = GapRow.of("s-17897-1", GapKind.LINEAGE_LOST,
                GapClass.DIAGNOSTIC, export.id(),
                "the exporter ran outside any attributable scope");

        assertEquals(activation, RowCodec.readActivation(
                reline(RowCodec.writeActivation(activation)), new RowPool()));
        ActivationRow handed = ActivationRow.of("s-17897-1", anchor,
                "task-1", true, true, ActivationRow.CLAIMED + "s|k",
                ActivationRow.ClaimKind.HANDOFF_TASK, null);
        assertEquals(handed, RowCodec.readActivation(
                reline(RowCodec.writeActivation(handed)), new RowPool()));
        assertTrue(handed.heldWhereItRuns(Collections.<String>emptySet()));
        assertFalse("a hand-off task that served a queue",
                handed.heldWhereItRuns(Collections.singleton(
                        handed.threadKey())));
        JsonObject legacy = RowCodec.writeActivation(handed);
        legacy.remove("claimKind");
        ActivationRow old = RowCodec.readActivation(reline(legacy),
                new RowPool());
        assertEquals(ActivationRow.ClaimKind.NONE, old.claimKind());
        assertFalse(old.heldWhereItRuns(Collections.<String>emptySet()));
        try {
            ActivationRow.of("s-17897-1", anchor, "task-1", true, true,
                    "pool-1-thread-1#20", ActivationRow.ClaimKind.ITEM, null);
            fail("an item keyed by its thread");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains("claimed start"));
        }
        ActivationRow ambient = ActivationRow.of("s-17897-1", producer, "",
                false, false, "KeyManager-1#13", ActivationRow.ClaimKind.NONE, null);
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
        ReadRow placeholder = ReadRow.of("s-17897-1", 14L, read.endpoint(),
                keys, 7L, "state_allKeys_7", BLOCK_KEY, null, 9L);
        assertEquals(placeholder, RowCodec.readRead(
                reline(RowCodec.writeRead(placeholder)), new RowPool()));
        assertFalse("a stated mint version is not the unknown one",
                placeholder.equals(read));
        ReadRow partial = ReadRow.of("s-17897-1", 14L, read.endpoint(),
                keys, 7L, "state_allKeys_7", BLOCK_KEY, null,
                ReadRow.UNKNOWN_VERSION, true);
        assertEquals(partial, RowCodec.readRead(
                reline(RowCodec.writeRead(partial)), new RowPool()));
        assertFalse(partial.equals(read));
        assertFalse(RowCodec.writeRead(read).has("unnamedWriter"));
        assertEquals(minted, RowCodec.readRootMint(
                reline(RowCodec.writeRootMint(minted))));
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
        assertEquals("HANDLE", rows.get(0).pairedBy());
        assertNull(rows.get(1).pairedBy());
        assertNull(rows.get(1).producer());
        assertTrue(RowCodec.readAll(session.reads(),
                json -> RowCodec.readRead(json, new RowPool())).isEmpty());

        JsonObject expression = new JsonObject();
        expression.addProperty("op", "SYMBOL");
        expression.addProperty("name", "root_serial_no");
        Map<String, JsonObject> expressions = new LinkedHashMap<>();
        expressions.put("EXPR.v1.9f2c", expression);
        ExpressionLogs.write(session.expressions(), expressions);
        assertEquals(expressions, SessionExpressionLog.read(
                session.expressions(), new RowPool()).expressions());
        assertEquals(Collections.singletonList(session),
                SessionDir.sessionsIn(root));

        assertTrue("a recording that states everything states no violation: "
                        + names(gate(clean())),
                gate(clean()).isEmpty());
        Rows second = clean();
        second.id = "s-two";
        assertInvariant(1, GapClass.BLOCKING, "epoch/sessions",
                clean(), second);
        Rows unactivated = clean();
        unactivated.activations.clear();
        assertInvariant(1, GapClass.BLOCKING, "field=occurrence",
                unactivated);
        Rows neither = clean();
        neither.reads.set(0, ReadRow.of("s-gate", 14L, neither.readAt, keys,
                -1L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(2, GapClass.BLOCKING, "field=observedVersion",
                neither);
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
        Rows empty = clean();
        empty.expressions.clear();
        assertInvariant(3, GapClass.BLOCKING, "field=term", empty);
        Rows spelled = clean();
        spelled.decisions.set(0, DecisionRow.of("s-gate", 12L,
                spelled.anchor, "Guard#u8", 1, true, "EXPR.v1.9f2c", clocks));
        assertInvariant(3, GapClass.BLOCKING, "EXPR.v1.9f2c", spelled);
        Rows twice = clean();
        twice.reads.add(twice.reads.get(0));
        assertInvariant(4, GapClass.BLOCKING, "field=seq/location", twice);
        Rows collided = clean();
        collided.reads.add(ReadRow.of("s-gate", 20L, collided.readAt, keys,
                7L, "state_allKeys_7", BLOCK_KEY, null));
        assertInvariant(4, GapClass.DIAGNOSTIC, "site index missing",
                collided);
        Rows unreached = clean();
        OccurrenceAddress other = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                index(frame(RUN, 0)));
        unreached.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42", ActivationRow.ClaimKind.NONE, null));
        unreached.targets.add(TargetRow.of("s-gate", 0L, unreached.anchor,
                "Guard#u8", "", false, false, null));
        unreached.targets.add(TargetRow.of("s-gate", 0L, other, "Guard#u8",
                "", false, false, null));
        assertTrue("an unreached anchor is one row per occurrence: "
                + names(gate(unreached)), noViolation(gate(unreached), 4));
        Rows decided = clean();
        decided.activations.add(ActivationRow.of("s-gate", other, "t",
                false, true, "DataXceiver-8#42", ActivationRow.ClaimKind.NONE, null));
        decided.targets.add(TargetRow.of("s-gate",
                decided.targets.get(0).seq(), other, "Guard#u8", "", false,
                true, null));
        assertTrue("two occurrences deciding concretely after one event: "
                + names(gate(decided)), noViolation(gate(decided), 4));
        LocationId stateJson = LocationId.of(LocationKind.STORE, "SOLR_ZK",
                "/collections/c/state.json");
        for (Object[] each : new Object[][] {
                {"another reader", other, 4L, true},
                {"another version", null, 5L, true},
                {"the same read", null, 4L, false}}) {
            Rows stored = clean();
            stored.activations.add(ActivationRow.of("s-gate", other, "t",
                    false, true, "DataXceiver-8#42", ActivationRow.ClaimKind.NONE, null));
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
        Rows mixed = clean();
        mixed.reads.add(ReadRow.of("s-gate", 21L, mixed.placeholderAt, keys,
                7L, "M_Z_field_" + REGION + ".in.a1", "I", "2"));
        assertInvariant(5, GapClass.BLOCKING, "field=symbol/javaType", mixed);
        Rows flipped = clean();
        flipped.decisions.set(0, DecisionRow.of("s-gate", 12L,
                flipped.anchor, "Guard#u8", 1, false, "EXPR.0000000000000001",
                clocks));
        assertInvariant(6, GapClass.BLOCKING, "field=outcome", flipped);
        Rows unstated = clean();
        unstated.writes.clear();
        unstated.reads.set(1, ReadRow.of("s-gate", 16L,
                unstated.placeholderAt, keys, 7L,
                "M_I_field_" + REGION + ".in.a1", "I", "2", 99L));
        assertInvariant(7, GapClass.DIAGNOSTIC, "field=observedVersion",
                unstated);
        Rows fabricated = clean();
        fabricated.writes.add(WriteRow.of("s-gate", 11L,
                fabricated.writeAt, keys, 8L, "EXPR.0000000000000002",
                BLOCK_KEY));
        assertInvariant(7, GapClass.BLOCKING, "field=version", fabricated);
        Rows copied = clean();
        copied.writes.add(WriteRow.of("s-gate", 11L, copied.writeAt, keys,
                9L, "EXPR.0000000000000002", BLOCK_KEY));
        assertTrue("a write of another version that carries the minted "
                        + "symbol is no fabricated write: "
                        + names(gate(copied)),
                noViolation(gate(copied), 7));
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
                    "Guard#u8", (String) row[0], (Boolean) row[1], true, null));
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
        Rows unattributed = clean();
        unattributed.id = "s-abandoned";
        unattributed.roots.clear();
        assertInvariant(11, GapClass.BLOCKING, "CASE.MARKER",
                clean(), unattributed);
        assertEquals("one row per (session, root), naming both: "
                        + names(gate(clean(), unattributed)),
                1, stating(gate(clean(), unattributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
        Rows attributed = clean();
        attributed.id = "s-abandoned";
        assertEquals("a session that states the mint row is not refused: "
                        + names(gate(clean(), attributed)),
                0, stating(gate(clean(), attributed),
                        GapKind.MINT_UNATTRIBUTED, GapClass.BLOCKING));
        for (boolean mintFirst : new boolean[] {true, false}) {
            Path epoch = iteration.newFolder().toPath();
            clean().read(epoch);
            unattributed.read(epoch);
            Path whole = epoch.resolve("whole.jsonl");
            ImportGateMain.gate(epoch, gates(epoch, "s-gate", "s-abandoned"),
                    Collections.<String>emptySet(), null, whole, "e");
            Path ledger = epoch.resolve("gated");
            Path stepped = epoch.resolve("stepped.jsonl");
            String first = mintFirst ? "s-gate" : "s-abandoned";
            String later = mintFirst ? "s-abandoned" : "s-gate";
            ImportGateMain.gate(epoch, gates(epoch, first),
                    Collections.<String>emptySet(), ledger, stepped, "e");
            Path staged = epoch.resolve("worker/sessions/" + later);
            Files.createDirectories(staged.getParent());
            Files.move(SessionDir.of(epoch, later).dir(), staged);
            for (Path file : Files.newDirectoryStream(
                    SessionDir.of(epoch, first).dir())) {
                Files.delete(file);
            }
            List<Path> none = Collections.<Path>emptyList();
            ImportGateMain.gate(epoch, Collections.singletonList(
                    new ImportGateMain.Gate(staged, none)),
                    Collections.<String>emptySet(), ledger, stepped, "e");
            JsonObject again = ImportGateMain.gate(epoch, Arrays.asList(
                    new ImportGateMain.Gate(staged, none),
                    new ImportGateMain.Gate(SessionDir.of(epoch, first).dir(),
                            none)), Collections.<String>emptySet(), ledger,
                    stepped, "e");
            List<String> filed = Files.readAllLines(stepped);
            assertEquals("mint first: " + mintFirst,
                    new LinkedHashSet<>(Files.readAllLines(whole)),
                    new LinkedHashSet<>(filed));
            assertEquals("invariants 1 and 11, each once: " + filed, 2,
                    filed.size());
            assertEquals(0, again.get("sessions").getAsInt());
            Set<String> replaced = Collections.<String>emptySet();
            if (mintFirst) {
                Files.write(epoch.resolve(SessionDir.WITHDRAWN),
                        Collections.singletonList(first));
            } else {
                replaced = Collections.singleton(first);
            }
            Path late = epoch.resolve("late.jsonl");
            Rows another = clean();
            another.id = "s-late";
            another.read(epoch);
            ImportGateMain.gate(epoch, gates(epoch, "s-late"), replaced,
                    ledger, late, "e");
            assertEquals("the epoch without " + first + ": "
                            + Files.readAllLines(late),
                    1L, Files.readAllLines(late).stream()
                            .filter(line -> line.contains(
                                    "2 of 2 sessions state role SEED"))
                            .count());
        }
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

    @Test
    public void aSessionStatesEveryFlipItWasHeldToAtItsOccurrence()
            throws IOException {
        OccurrenceAddress other = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("DATA_XCEIVER"), "", 2),
                index(frame(RUN, 0)));
        String guard = "Guard#u8#1 -> true at occurrence ";
        Object[][] worlds = {
                {"own", "", ""},
                {"other", "", guard + "OWN"},
                {"own", "Guard#u8@other", guard + "OTHER"},
                {"own", "PAIRING:reader@other", ""}};
        for (Object[] world : worlds) {
            Rows rows = clean();
            rows.activations.add(ActivationRow.of("s-gate", other, "t",
                    false, true, "DataXceiver-8#42",
                    ActivationRow.ClaimKind.NONE, null));
            if (world[0].equals("other")) {
                rows.decisions.set(0, DecisionRow.of("s-gate", 12L, other,
                        "Guard#u8", 1, true, "EXPR.0000000000000001",
                        Collections.<String, Long>emptyMap()));
            }
            JsonObject focus = new JsonObject();
            focus.addProperty("focusedOccurrenceId", rows.anchor.id());
            JsonObject flip = new JsonObject();
            flip.addProperty("siteId", "Guard#u8");
            flip.addProperty("ordinal", 1);
            flip.addProperty("outcome", true);
            focus.add("flip", flip);
            JsonArray inherited = new JsonArray();
            String carried = (String) world[1];
            if (!carried.isEmpty()) {
                JsonObject one = new JsonObject();
                one.addProperty("focusedOccurrenceId",
                        carried.endsWith("@other") ? other.id()
                                : rows.anchor.id());
                one.addProperty("siteId", carried.substring(0,
                        carried.indexOf('@')));
                one.addProperty("ordinal", 1);
                one.addProperty("outcome", true);
                inherited.add(one);
            }
            focus.add("inheritedFlips", inherited);
            Path epoch = iteration.newFolder().toPath();
            rows.read(epoch);
            Path worker = epoch.resolve("obligations-0000").resolve("w");
            Files.createDirectories(worker);
            Files.write(worker.resolve(ObligationDir.FOCUSED_TASK),
                    Collections.singletonList(focus.toString()));
            Files.write(worker.resolve(ObligationDir.RESULT),
                    Collections.singletonList(RowCodec.toLine(
                            RowCodec.writeObligationResult(ObligationResult
                                    .of("OBL.s-gate", Verdict.ADMITTED,
                                            "s-gate", "fixture")))));
            Path ledger = epoch.resolve("gated");
            Path filed = epoch.resolve("gaps.jsonl");
            ImportGateMain.gate(epoch, Collections.singletonList(
                    new ImportGateMain.Gate(SessionDir.of(epoch, "s-gate")
                            .dir(), Collections.singletonList(worker))),
                    Collections.<String>emptySet(), ledger, filed, "e");
            JsonArray recorded = com.google.gson.JsonParser.parseString(
                    new String(Files.readAllBytes(ledger.resolve("s-gate"
                            + ImportGateMain.RECORD)), StandardCharsets.UTF_8))
                    .getAsJsonObject().getAsJsonArray("unstated");
            String want = ((String) world[2]).replace("OWN",
                    rows.anchor.id()).replace("OTHER", other.id());
            List<String> said = new ArrayList<String>();
            for (int at = 0; at < recorded.size(); at++) {
                said.add(recorded.get(at).getAsString());
            }
            assertEquals(Arrays.toString(world), want.isEmpty()
                    ? Collections.<String>emptyList()
                    : Collections.singletonList(want), said);
            long tenth = Files.exists(filed) ? Files.readAllLines(filed)
                    .stream().filter(line -> line.contains("invariant 10"))
                    .count() : 0L;
            assertEquals(Arrays.toString(world), said.size(), tenth);
        }
    }

    @Test
    public void aTimedWaitTurnIsNamedByItsFamily() {
        StableEventNames names = new StableEventNames();
        assertEquals(names.context("n0|Root:WAKE/peek#3|<A: void a()>@2"),
                names.context("n0|Root:WAKE/peek#7|<A: void a()>@5"));
        assertEquals("n0|Root:WAKE/peek#*|<A: void a()>",
                names.context("n0|Root:WAKE/peek#3|<A: void a()>@2"));
        assertEquals("n0|Root:TASK#3|<A: void a()>",
                names.context("n0|Root:TASK#3|<A: void a()>@2"));
        OccurrenceAddress third = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.WAKE, "peek", 3), ExecutionIndex.empty());
        OccurrenceAddress seventh = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.WAKE, "peek", 7), ExecutionIndex.empty());
        OccurrenceAddress task = OccurrenceAddress.of(DN0, REGION,
                CausalContext.of(Role.of("TASK"), "", 3),
                ExecutionIndex.empty());
        assertEquals(third.anyTurn().id(), seventh.anyTurn().id());
        assertEquals(task.id(), task.anyTurn().id());
    }
    private static int stating(List<GapRow> gaps, GapKind kind,
                               GapClass cls) {
        int count = 0;
        for (GapRow gap : gaps) {
            if (gap.kind() == kind && gap.cls() == cls) count++;
        }
        return count;
    }

    private static boolean noViolation(List<GapRow> gaps, int rule) {
        for (GapRow gap : gaps) {
            if (gap.detail().contains("invariant " + rule)) return false;
        }
        return true;
    }

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
            ExpressionLogs.write(dir.expressions(), expressions);
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
                true, "DataXceiver-7#41", ActivationRow.ClaimKind.NONE, null));
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
        rows.reads.add(ReadRow.of("s-gate", 16L, rows.placeholderAt,
                LocationId.of(LocationKind.MAP,
                        "o.a.h.h.s.t.b.BlockTokenSecretManager", "allKeys"),
                7L, "M_I_field_" + REGION + ".in.a1", "I", "2", 8L));
        rows.targets.add(TargetRow.of("s-gate", 15L, rows.anchor, "Guard#u8",
                "EXPR.0000000000000001", true, true, null));
        return rows;
    }

    private static List<ImportGateMain.Gate> gates(Path epoch, String... ids) {
        List<ImportGateMain.Gate> gates = new ArrayList<>();
        for (String id : ids) {
            gates.add(new ImportGateMain.Gate(SessionDir.of(epoch, id).dir(),
                    Collections.<Path>emptyList()));
        }
        return gates;
    }

    private List<GapRow> gate(Rows... sessions) throws IOException {
        Path root = iteration.newFolder().toPath();
        for (Rows rows : sessions) rows.read(root);
        return RowInvariants.check(
                Collections.<RowInvariants.Gated>emptyList(),
                SessionDir.sessionsIn(root),
                Collections.<String, List<JsonObject>>emptyMap()).gaps;
    }

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

    private static OccurrenceAddress tick(int windowIndex) {
        return OccurrenceAddress.of(NN0, "REGION.a1b2",
                CausalContext.of(Role.of("KEY_MANAGER_TICK"), "", windowIndex),
                index(frame("o.a.h.h.s.b.KeyManager#run#9", 0)));
    }

    private static JsonObject reline(JsonObject row) {
        return RowCodec.fromLine(RowCodec.toLine(row));
    }

    @Test
    public void aFileAnotherHostReplacedWhileItWasReadIsReadAgain()
            throws IOException {
        Path file = iteration.newFile("obligation_result.jsonl").toPath();
        Files.write(file, "{}\n".getBytes(StandardCharsets.UTF_8));
        int[] opens = {0};
        assertEquals("the replaced file, opened afresh", "{}", new String(
                RowCodec.reopened(file, () -> {
                    if (++opens[0] == 1) {
                        throw new IOException("Stale file handle");
                    }
                    return Files.readAllBytes(file);
                }), StandardCharsets.UTF_8).trim());
        assertEquals(2, opens[0]);
        opens[0] = 0;
        try {
            RowCodec.reopened(file, () -> {
                opens[0]++;
                throw new IOException("Stale file handle");
            });
            fail("stale on every open");
        } catch (IOException stale) {
            assertTrue(stale.getMessage(), stale.getMessage().startsWith(
                    file + ": Stale file handle on each of 3 fresh opens"));
        }
        assertEquals(3, opens[0]);
        opens[0] = 0;
        try {
            RowCodec.reopened(file, () -> {
                opens[0]++;
                throw new IOException("Input/output error");
            });
            fail("another failure");
        } catch (IOException other) {
            assertEquals("Input/output error", other.getMessage());
        }
        assertEquals("any other failure is not read again", 1, opens[0]);
    }
}
