package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * A MINT STORE IS NO WRITE, IN ANY ACTIVATION.
 *
 * <p>A mint installs its symbol into a field the VM versions, and that
 * version is suppressed: nobody stored it, the mint made it.  The
 * suppression used to be a question about ONE activation's own mint rows,
 * and {@code RowPublication#writes} skips the version BEFORE it claims the
 * write event -- so a second activation that merely read the same VM record
 * out published the mint's store as a WriteRow and won the claim.</p>
 *
 * <p>On hdfs-11741 campaign #5b that is 284 clock mint stores published as
 * writes at {@code sun.reflect.NativeMethodAccessorImpl#invoke}, and 593 of
 * 877 unbox reads bound by accident off them.  In the campaign #5b seed
 * session, 11 WriteRows have a whole expression that IS a declared root's
 * symbol.</p>
 */
public class DeclaredMintOwesItsPlaceholderReadTest {
    @Rule
    public final TemporaryFolder iteration = new TemporaryFolder();

    private static final String METHOD = "<a.B: void run()>";
    private static final String REGION = "REGION.ba3902cd";
    private static final String NODE = "hdfs-11741/dn1#epoch0";
    private static final String OCCURRENCE =
            NODE + "/region/" + REGION + "#1";
    /** The cell the woven clock mint allocates and symbolizes. */
    private static final String CLOCK_CELL = "INSTANCE_FIELD/217#24";
    /** The version that mint installed: the one the unbox read observes. */
    private static final long MINT_VERSION = 1155L;
    /** The VM's own name for what it installed there. */
    private static final String CLOCK_SYMBOL =
            "M_J_field_REGION.ba3902cd.in.559a1724.occ.e36a3c48_java/lang/Long";
    private static final String INSTANT = "1789965233929";

    private final List<Long> opened = new ArrayList<Long>();

    @Before
    public void reset() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void clear() {
        for (Long token : opened) {
            ConcolicRegionRuntime.ACTIVE.remove(token);
        }
        opened.clear();
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    /**
     * The activation that never minted publishes first, and states no write.
     *
     * <p>It knows nothing about the mint: it is the MINTING activation's own
     * registration, filed where the mint RAN rather than where its rows are
     * published, that answers for it.  The control write of the same cell --
     * a bare symbol that no declared input minted -- is published, so the
     * suppression is the mint's and not the location's.</p>
     */
    @Test
    public void noActivationPublishesAMintStoreAsAWrite() throws Exception {
        RowRuntime.configure(sessionFile());
        OccurrenceAddress at = address(OCCURRENCE);
        ActiveRegion minting = region(at);
        clockMint(minting);

        // The VM record as EVERY activation reads it out: the mint's store,
        // and one real write of the same cell by the same performer.
        RowRuntime.journalRegion(900L, at);
        JsonObject shared = record(CLOCK_CELL,
                loggedAt(version(MINT_VERSION,
                        symbolExpression(CLOCK_SYMBOL, "J"))));
        array(shared, "versions").add(loggedAt(version(MINT_VERSION + 1L,
                symbolExpression("M_J_field_HOFF.9f1c_a/Carrier", "J"))));

        ActiveRegion bystander = region(address(
                NODE + "/region/REGION.16ba41cf#1"));
        bystander.sharedStateRecords.put(CLOCK_CELL, shared);
        writes(bystander);
        minting.sharedStateRecords.put(CLOCK_CELL, shared);
        writes(minting);
        RowRuntime.closeSession();

        List<WriteRow> writes = writes();
        assertEquals("the cell's one real write is published", 1,
                writes.size());
        assertEquals(MINT_VERSION + 1L, writes.get(0).version());
        for (WriteRow write : writes) {
            assertFalse("and no activation states the mint's own store as a"
                            + " write of it",
                    write.version() == MINT_VERSION);
        }
    }

    // ------------------------------------------------------------------
    // The fixture.
    // ------------------------------------------------------------------

    /** One declared CLOCK mint, through the runtime's own recorder. */
    private void clockMint(ActiveRegion active) {
        active.recordManualSymbolization(
                new SymbolizeAction(clockAction()), "PORT.now",
                Collections.<String>emptyList(),
                "<org.apache.hadoop.util.Timer: long now()>.return",
                symbolExpression(CLOCK_SYMBOL, "J"), true, false, INSTANT);
    }

    /** {@code RowPublication#writes}, the one publisher of WriteRows. */
    private static void writes(ActiveRegion active) throws Exception {
        java.lang.reflect.Method publish = RowPublication.class
                .getDeclaredMethod("writes", ActiveRegion.class);
        publish.setAccessible(true);
        publish.invoke(null, active);
    }

    private ActiveRegion region(OccurrenceAddress at) throws Exception {
        long token = 880001L + opened.size();
        ActiveRegion active = new ActiveRegion(token,
                new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(task())),
                null, Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        opened.add(Long.valueOf(token));
        active.d3Address = at;
        return active;
    }

    private static OccurrenceAddress address(String occurrence) {
        return OccurrenceAddress.of(NodeId.parse(NODE),
                occurrence.substring(occurrence.indexOf("/region/") + 8,
                        occurrence.lastIndexOf('#')),
                CausalContext.of("5c6bd4ac", "HADOOP_IPC/refresh-block-keys"),
                ExecutionIndex.parse("a.B.run()#u1@0"));
    }

    /** One VM write-log record, as an activation reads one out. */
    private static JsonObject record(String locationKey, JsonObject first) {
        JsonObject envelope = new JsonObject();
        JsonArray versions = new JsonArray();
        versions.add(first);
        envelope.add("versions", versions);
        JsonObject record = new JsonObject();
        record.addProperty("locationKey", locationKey);
        record.add("envelope", envelope);
        return record;
    }

    private static JsonArray array(JsonObject record, String member) {
        return record.getAsJsonObject("envelope").getAsJsonArray(member);
    }

    private static JsonObject version(long id, JsonObject expression) {
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", id);
        version.add("expression", expression);
        return version;
    }

    /** The same version, with the site and activation the VM logs on it. */
    private static JsonObject loggedAt(JsonObject version) {
        JsonObject site = new JsonObject();
        site.addProperty("className", "sun/reflect/NativeMethodAccessorImpl");
        site.addProperty("methodName", "invoke");
        site.addProperty("methodDescriptor",
                "(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;");
        site.addProperty("bci", 100);
        version.add("site", site);
        version.addProperty("regionEnterEventId", 900L);
        return version;
    }

    private static JsonObject symbolExpression(String symbol, String type) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", type);
        expression.addProperty("_exp", symbol);
        return expression;
    }

    /** One frozen SYMBOLIC action declaring a wall-clock read. */
    private static JsonObject clockAction() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "PORT.now");
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        encoded.addProperty("cell",
                "<org.apache.hadoop.util.Timer: long now()>.return");
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("clock", true);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", INSTANT);
        encoded.addProperty("eventSeq", 7L);
        return encoded;
    }

    /** One executable task row, as the plan carries it. */
    private static JsonObject task() {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", NODE);
        encoded.addProperty("occurrenceId", OCCURRENCE);
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", METHOD);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", NODE);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branchMethods", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("defaultBackedgeTraversals", 8);
        encoded.add("loopBound", loopBound);
        return encoded;
    }

    private List<WriteRow> writes() throws Exception {
        return RowCodec.readAll(session().writes(), RowCodec::readWrite);
    }

    private Path sessionFile() throws Exception {
        Path results = iteration.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        Files.createDirectories(results.getParent());
        return results;
    }

    private SessionDir session() {
        return SessionDir.of(iteration.getRoot().toPath()
                .resolve("iteration-0000"), RowRuntime.sessionId());
    }
}
