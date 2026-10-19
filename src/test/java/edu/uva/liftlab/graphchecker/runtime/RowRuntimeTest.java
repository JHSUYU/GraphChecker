package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.runtime.Fixtures.call;
import static edu.uva.liftlab.graphchecker.runtime.Fixtures.json;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.rules.TemporaryFolder;

@RunWith(FreshStatics.class)
public class RowRuntimeTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final SourceRef NN =
            new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0", 0);

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
    }

    @After
    public void clear() {
        MessageDoors.endInbound();
        RuntimeTraceContext.resetForTests();
        Fixtures.set(ConcolicTaskPlan.class, "plan", null);
        Fixtures.set(MessageDoors.class, "chain", null);
    }

    private void openSession() throws Exception {
        Fixtures.openSession(iteration.getRoot().toPath());
    }

    private SessionDir session() {
        return Fixtures.session(iteration.getRoot().toPath());
    }

    private List<GapRow> gaps() throws Exception {
        return Fixtures.gaps(iteration.getRoot().toPath());
    }

    private static void run(Thread thread) {
        thread.start();
        try {
            thread.join();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
        }
    }

    private static Thread poolThreadCreatedOutsideAnyScope(Runnable work) {
        AtomicReference<Thread> created = new AtomicReference<>();
        run(new Thread(() -> created.set(new Thread(work))));
        return created.get();
    }

    private static OccurrenceAddress address(String nodeKey, String regionId,
                                             CausalContext context,
                                             ExecutionIndex index) {
        return OccurrenceAddress.of(NodeId.parse(nodeKey), regionId, context,
                index);
    }

    private static OccurrenceAddress targetDn() {
        return address("hdfs-17899/target-dn#epoch0", "REGION.53092d3e",
                CausalContext.of("producer-endpoint-id", "HDFS_SASL#replace"),
                ExecutionIndex.parse("DataXceiver.run()#u9@0"));
    }

    @Test
    public void aCarriedScopeReachesTheThreadThatRunsTheWork()
            throws Exception {
        RuntimeTraceContext.registerSource(new Object(), NN);
        long request = RuntimeTraceContext.beginRequest(NN, "balance-block");
        assertEquals("Root:CLIENT/balance-block#1", rootContext());
        assertEquals(Role.CLIENT, Lineage.role());
        Object carried = RuntimeTraceContext.captureScope();
        AtomicReference<String> onHandler = new AtomicReference<>("");
        run(poolThreadCreatedOutsideAnyScope(() -> {
            long scope = RuntimeTraceContext.enterCarriedScope(carried,
                    "IPC_HANDLER", "balance-block");
            onHandler.set(rootContext() + "/" + Lineage.role());
            RuntimeTraceContext.exitCarriedScope(scope);
        }));
        assertEquals("Root:CLIENT/balance-block#1/IPC_HANDLER",
                onHandler.get());
        Object task = new Object();
        Identity.startWork("<a.Pool: void submit()>#u1", task, null);
        AtomicReference<String> onWorker = new AtomicReference<>("");
        run(poolThreadCreatedOutsideAnyScope(() -> {
            Identity.claimStart(task);
            onWorker.set(rootContext() + "/" + Lineage.role());
            RuntimeTraceContext.releaseCarried();
        }));
        assertEquals("Root:CLIENT/balance-block#1/EXECUTOR_TASK",
                onWorker.get());
        RuntimeTraceContext.endRequest(request);
        assertFalse("the request's scope ended with it", Lineage.named());
    }

    @Test
    public void aClosedSessionIsNotWrittenAgain() throws Exception {
        GapRow late = GapRow.of("s", GapKind.UNSTATED_VALUE,
                GapClass.BLOCKING, "late", "filed after the run ended");
        SessionDir ended = SessionDir.of(iteration.getRoot().toPath(),
                "ended");
        SessionPublisher closed = SessionPublisher.at(ended);
        closed.close();
        closed.gap(late);
        assertEquals(0L, Files.size(ended.gaps()));
        SessionDir layout = SessionDir.of(iteration.getRoot().toPath(),
                "withdrawn");
        SessionPublisher session = SessionPublisher.at(layout);
        Files.move(layout.dir(), iteration.getRoot().toPath().resolve("aside"));
        session.gap(late);
        assertFalse(Files.exists(layout.dir()));
    }

    @Test(timeout = 60000L)
    public void aReadOutDecodesBesideThePublications() throws Exception {
        java.util.concurrent.CountDownLatch decoding =
                new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch release =
                new java.util.concurrent.CountDownLatch(1);
        String[] ran = new String[1];
        assertTrue(ConcolicResultPublisher.decodeInOrder(1L, () -> {
            ran[0] = Thread.currentThread().getName();
            decoding.countDown();
            try {
                release.await();
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
            }
        }));
        decoding.await();
        java.util.concurrent.CountDownLatch published =
                new java.util.concurrent.CountDownLatch(1);
        ((java.util.concurrent.Executor) Fixtures.get(
                ConcolicResultPublisher.class,
                "RESULT_PUBLICATION_EXECUTOR")).execute(published::countDown);
        assertTrue(published.await(30L, TimeUnit.SECONDS));
        release.countDown();
        assertTrue(ran[0], ran[0].startsWith("causynth-read-out-decode-"));
        SharedStateCapture.SharedStateReadOut readOut =
                new SharedStateCapture.SharedStateReadOut();
        assertTrue((Boolean) call(readOut, "decodeLater", new Class<?>[] {
                String.class, ActiveRegion.class}, "{}", null));
        readOut.awaitDecoded();
        assertEquals(1, ((List<?>) Fixtures.get(readOut, "refusals")).size());
    }

    @Test(timeout = 60000L)
    public void aRowIsWrittenWholeUnderTheSessionLock() throws Exception {
        GapRow row = GapRow.of("s", GapKind.UNSTATED_VALUE,
                GapClass.DIAGNOSTIC, "held", "stated while the lock is held");
        SessionDir layout = SessionDir.of(iteration.getRoot().toPath(),
                "locked");
        SessionPublisher session = SessionPublisher.at(layout);
        Thread stating = new Thread(() -> session.gap(row));
        synchronized (Fixtures.get(SessionPublisher.class, "LOCK")) {
            stating.start();
            while (stating.getState() != Thread.State.BLOCKED) {
                Thread.yield();
            }
            assertEquals(0L, Files.size(layout.gaps()));
        }
        stating.join();
        StringBuilder written = new StringBuilder();
        try (java.io.BufferedReader in = ArtifactIO.lines(layout.gaps())) {
            for (int c; (c = in.read()) >= 0; ) written.append((char) c);
        }
        assertEquals(RowCodec.toLine(RowCodec.writeGap(row))
                + System.lineSeparator(), written.toString());
    }

    private static String rootContext() {
        return CausalContext.of(Lineage.rootRole(), Lineage.rootApi(),
                Lineage.rootWindowIndex()).render();
    }

    @Test
    public void anUnplannedExportNamesTheRegionItRanIn() throws Exception {
        Fixtures.set(ConcolicTaskPlan.class, "plan", new ConcolicTaskPlan(
                null, Collections.<ConcolicTaskPlan.RuntimeTask>emptyList()));
        openSession();
        Lineage.resetForTests();
        Object nameNode = new Object();
        RuntimeTraceContext.registerSource(nameNode, NN);
        Identity.scopeStart(Identity.Hop.SCOPE_ROOT);
        String convert = "<o.a.h.PBHelper: o.a.h.NNHAStatusHeartbeatProto"
                + " convert(o.a.h.NNHAStatusHeartbeat)>";
        long frame = Identity.enterFrame(convert + "#u0", null);
        long entry = ConcolicRegionRuntime.enterRegionEntry(
                "REGION.b9bd09cd", convert, nameNode);
        OccurrenceAddress here;
        try {
            here = Identity.currentOccurrence(NN.key());
            WireExport.exportLeaf("XCH.53d59f95-3ee5-385f-a674-a07d58f5b75b"
                    + ".wire.auto:NNHAStatusHeartbeatProto.Txid",
                    new ConcolicRegionRuntime.HandoffLeafCarrier(), "j", "J",
                    null);
        } finally {
            ConcolicRegionRuntime.exitRegionEntry(entry);
            Identity.exitFrame(frame);
        }
        RowRuntime.closeSession();
        assertEquals("REGION.b9bd09cd", here.regionId());
        assertFalse("a region, which the closure can grow", here.role());
        GapRow refused = null;
        for (GapRow gap : gaps()) {
            assertTrue("no plan declares an export: " + gap.detail(),
                    gap.kind() != GapKind.DECLARATION_MISSING);
            if (gap.kind() == GapKind.UNSTATED_VALUE) refused = gap;
        }
        assertNotNull("the refused export is named", refused);
        assertEquals("at the occurrence it ran in", here.render(),
                refused.subject());
        List<ActivationRow> activations =
                SessionReader.read(session()).activations();
        assertEquals("that occurrence is stated, unselected", here,
                activations.get(0).occurrence());
        assertFalse(activations.get(0).instrumented());
    }

    @Test
    public void phiIsPublishedInTheFatalPolarityForBothObservedArms()
            throws Exception {
        openSession();
        OccurrenceAddress occurrence = targetDn();
        JsonObject condition = json("{'_type':'BinaryExpression','_exp':"
                + "'allKeys.get(id) == null'}");
        String site = "retrieveDataEncryptionKey#u8";
        RowRuntime.target(occurrence, 8L, site, condition, true, true, true);
        RowRuntime.target(occurrence, 9L, site, condition, false, false, true);
        RowRuntime.target(occurrence, 10L, site, null, true, true, true);
        RowRuntime.target(occurrence, 11L, site, null, false, false, true);
        RowRuntime.target(occurrence, 0L, site, null, false, false, false);
        RowRuntime.closeSession();
        List<TargetRow> rows = RowCodec.readAll(session().targets(),
                RowCodec::readTarget);
        assertEquals(5, rows.size());
        String ref = rows.get(0).phiTerm();
        assertTrue(ref.startsWith("EXPR."));
        assertTrue(rows.get(0).observedFatal());
        assertEquals("(not " + ref + ")", rows.get(1).phiTerm());
        assertFalse(rows.get(1).observedFatal());
        assertEquals("true", rows.get(2).phiTerm());
        assertEquals("false", rows.get(3).phiTerm());
        assertEquals("", rows.get(4).phiTerm());
    }

    @Test
    public void aDisjunctiveGuardIsTheOrOfItsTestsFatalArms() {
        JsonObject a = predicate("a");
        JsonObject c = predicate("c");
        String refA = RowRuntime.expressionRef(a);
        String refC = RowRuntime.expressionRef(c);
        Map<String, Boolean> guards = new LinkedHashMap<>();
        guards.put("G#u1", true);
        guards.put("G#u2", true);
        guards.put("G#u3", false);
        Object[][] rows = {
            {decided("G#u1", false, a), decided("G#u2", false, null),
                decided("G#u3", true, c), false,
                Arrays.asList("(not " + refA + ")", "(not " + refC + ")")},
            {decided("G#u1", false, a), decided("G#u2", true, null), null,
                true, Collections.singletonList("true")},
            {decided("G#u1", true, a), null, null, true,
                Collections.singletonList(refA)}};
        for (Object[] row : rows) {
            List<JsonObject> mappings = new ArrayList<>();
            mappings.add(decided("G#u2", true, null));
            mappings.get(0).addProperty("occurrence", 0);
            for (int index = 0; index < 3; index++) {
                if (row[index] != null) mappings.add((JsonObject) row[index]);
            }
            List<String> arms = new ArrayList<>();
            assertEquals(row[3], RowPublication.disjunction(mappings, guards,
                    "G#u1", 1, arms));
            assertEquals(row[4], arms);
        }
        List<String> arms = new ArrayList<>();
        assertTrue(RowPublication.disjunction(Collections.singletonList(
                decided("G#u3", false, c)), guards, "G#u3", 1, arms));
        assertEquals(Collections.singletonList(refC), arms);
    }

    private static List<JsonObject> mappings(Object[][] decisions) {
        List<JsonObject> mappings = new ArrayList<>();
        for (Object[] each : decisions) {
            JsonObject mapping = decided((String) each[0],
                    (Boolean) each[2], (JsonObject) each[3]);
            mapping.addProperty("vmEventId", (Long) each[1]);
            mapping.addProperty("occurrence", (Integer) each[4]);
            mappings.add(mapping);
        }
        return mappings;
    }

    private static JsonObject predicate(String name) {
        return json("{'_exp':'" + name + "'}");
    }

    private static JsonObject decided(String site, boolean outcome,
                                      JsonObject satisfied) {
        JsonObject mapping = json("{'siteId':'" + site + "','occurrence':1,"
                + "'outcome':" + outcome + ",'witness':{}}");
        if (satisfied != null) {
            mapping.getAsJsonObject("witness").add("sourceSatisfiedPredicate",
                    satisfied);
        }
        return mapping;
    }
}
