package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.io.IOException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The region graph joins on an address, and refuses anything else.
 *
 * <p>String equality on {@code occurrenceId} merges two activations the
 * moment one carries an {@code #a<n>} suffix, and that merge is invisible.
 * The graph only scopes: it never decides what matters, picks an arm, or
 * names a writer.</p>
 */
public class RegionGraphOccurrenceKeyTest {
    /** One planned occurrence, as identity v3 addresses it. */
    private static final String PLANNED =
            "hdfs-17960/nn0#epoch1/region/"
                    + "REGION.9492ec77-0f65-34ba-a3af-14753ac7347d"
                    + "/ctx:Root:KEY_MANAGER_TICK#1"
                    + "/idx:o.a.h.h.s.n.FSNamesystem#saveNamespace#12@0";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    /**
     * A planned address keys as itself: the migration is byte-neutral.  An
     * absent id is still absent, so the callers' early returns stand.  A
     * per-activation id, and anything that does not spell an address at all,
     * is refused rather than merged onto the address it resembles.
     */
    @Test
    public void aPlannedAddressKeysAsItselfAndAnythingElseIsRefused() {
        assertEquals(PLANNED,
                RuntimeSelectedRegionFinalizer.occurrenceKey(PLANNED));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(null));
        assertEquals("", RuntimeSelectedRegionFinalizer.occurrenceKey(""));
        for (String unreadable : new String[] {
                PLANNED + "#a1",
                "REGION.9492ec77",
                "hdfs-17960/nn0#epoch1/region/REGION.1",
                "hdfs-17960/nn0#epoch1/region/REGION.1#0"}) {
            refuses(unreadable);
        }
    }

    private static void refuses(String occurrenceId) {
        try {
            RuntimeSelectedRegionFinalizer.occurrenceKey(occurrenceId);
            fail("expected a refusal for " + occurrenceId);
        } catch (IllegalArgumentException refused) {
            assertEquals(true, refused.getMessage().contains(occurrenceId));
        }
    }

    /**
     * What names a recorded exchange edge across two recordings of one workload.
     *
     * <p>The wire transaction is minted fresh in every run, so the name is
     * the producing and consuming occurrence, the port, the direction and
     * an ordinal over that tuple.</p>
     */
    @Test
    public void aRecordedExchangeEdgeIsNamedFromContentNotTheWire()
            throws Exception {
        assertNotEquals("the wire transactions of two recordings are "
                        + "expected to differ",
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0",
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

        // The one transaction of one exchange site is exchange number one,
        // whichever transaction the recording happened to mint.
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0"));
        assertEquals(1, RuntimeSelectedRegionFinalizer.exchangeOrdinal(
                new LinkedHashMap<>(), SITE,
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0"));

        // A request-control edge is named by the response edge, not the wire:
        // the response edge already names the exchange from content, and it
        // names it more exactly than the transaction does, because each retry
        // of one logical request has its own response edge.
        String first = controlEdgeId(
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0");
        String second = controlEdgeId(
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");
        assertEquals("two recordings of one request fault must publish one "
                + "control edge name", first, second);
    }

    private static final String SITE =
            "hdfs-17899/nn0#epoch0/region/REGION.a#1\n"
                    + "hdfs-17899/source-dn#epoch0/region/REGION.b#1\n"
                    + "REGION.b.in.port\nREQUEST";

    @SuppressWarnings("unchecked")
    private static String controlEdgeId(String transaction) throws Exception {
        Method edge = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("requestFaultControlEdge", Map.class,
                        Map.class, Map.class, Map.class, Map.class,
                        String.class, String.class, long.class, long.class,
                        long.class, long.class, long.class);
        edge.setAccessible(true);
        Map<String, Object> result = (Map<String, Object>) edge.invoke(null,
                row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.f/ctx:Root:KEY_MANAGER_TICK#1/idx:o.a.h.h.s.n.FSNamesystem#saveNamespace#12@0",
                        "regionId", "REGION.f", "rootCallId", 11L),
                row("occurrenceId", "hdfs-17899/nn0#epoch0/region/REGION.c/ctx:Root:KEY_MANAGER_TICK#1/idx:o.a.h.h.s.n.FSNamesystem#saveNamespace#12@0",
                        "regionId", "REGION.c", "rootCallId", 12L),
                row("portId", "REGION.c.in.port", "symbolicName", "S1"),
                row("edgeId", "RPC.request", "requestKey", "rk",
                        "attemptId", "a1"),
                row("edgeId", "RPC.response"),
                transaction, "hdfs-17899/nn0#epoch0",
                1L, 2L, 3L, 4L, 5L);
        return String.valueOf(result.get("edgeId"));
    }

    /**
     * The care set is the intersection of the two conditions: a field must
     * appear on the backward slice AND be forward-reachable from a symbolic
     * root.  A field the slice names but no root reaches is a constant for
     * this failure and stays out.  An explicit fault marker and a wire attach
     * point are symbolic roots of the same standing.
     *
     * <p>Then what the slice PUBLISHES about those cells (CLOSURE-V2 SS4):
     * every write site of a cell it names, under the innermost region that
     * would run it, with the guard set post-dominance gives that site -- and
     * the guard set is where a may-reach guard and a control-dependence guard
     * differ, which is the difference between finding 17960's marker flip and
     * not finding it.</p>
     */
    @Test
    public void careSetKeepsOnlySliceFieldsASymbolicRootReaches()
            throws IOException {
        List<Map<String, Object>> graph = Arrays.asList(
                // The fault symbol enters at the wire and flows to a cell
                // that reads the rolled key.
                row("kind", "explicit_symbolic_fault",
                        "explicitSymbolicFault", true,
                        "fromCell", "cell.fault", "toCell", "cell.request"),
                row("kind", "field_read", "fromCell", "cell.request",
                        "toCell", "cell.key",
                        "declaredFieldSignature",
                        "<example.Owner: example.Key currentKey>"),
                // On the slice, but nothing symbolic reaches it: a harness
                // setter writing its own island.
                row("kind", "field_write", "fromCell", "cell.harness",
                        "toCell", "cell.interval",
                        "declaredFieldSignature",
                        "<example.Owner: long keyUpdateInterval>"));

        Set<String> cared = RuntimeSelectedRegionFinalizer
                .caredSharedLocations(graph);
        assertTrue(cared.contains("example.Owner#currentKey"));
        assertFalse(cared.contains("example.Owner#keyUpdateInterval"));

        List<Map<String, Object>> handoff = Arrays.asList(
                row("kind", "wire_handoff", "fromCell", "cell.send",
                        "toCell", "cell.receive"),
                row("kind", "field_write", "fromCell", "cell.receive",
                        "toCell", "cell.keys",
                        "fieldPathDeclarations", Collections.singletonList(
                                "<example.Owner: java.util.Map allKeys>")));
        assertTrue(RuntimeSelectedRegionFinalizer.caredSharedLocations(handoff)
                .contains("example.Owner#allKeys"));

        theSliceNamesEveryWriteSiteOfACellItNames();
        theGuardSetIsPostDominanceAndNotMayReach();
    }

    /**
     * 17960's shape: one counter, two writers, and the writer the seed never
     * ran is in the map exactly like the one it did.
     */
    private void theSliceNamesEveryWriteSiteOfACellItNames()
            throws IOException {
        String increment = "<example.Manager: java.lang.String create()>";
        String decrement = "<example.Manager: void delete(int,long)>";
        String saver = "<example.Saver: void save(java.io.OutputStream)>";
        String carrier =
                "<example.Manager: java.util.concurrent.atomic.AtomicInteger"
                        + " count>";
        List<Map<String, Object>> edges = Arrays.asList(
                row("kind", "field_mutation", "method", increment,
                        "unitIndex", 27, "toCell", carrier,
                        "invoke", "<java.util.concurrent.atomic."
                                + "AtomicInteger: int getAndIncrement()>"),
                row("kind", "field_mutation", "method", decrement,
                        "unitIndex", 35, "toCell", carrier,
                        "invoke", "<java.util.concurrent.atomic."
                                + "AtomicInteger: int getAndDecrement()>"),
                row("kind", "exception_throw", "method", saver,
                        "unitIndex", 64, "toCell", saver
                                + "#u64#exception:java.lang.IllegalState"),
                // A local-held container mutation names no shared location,
                // so it is no candidate writer of one.
                row("kind", "container_mutation_argument", "method", decrement,
                        "unitIndex", 12, "toCell", decrement + "::$r5"));
        Map<String, Object> port = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, saver,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        List<Map<String, Object>> regions = Arrays.asList(
                // The enclosing request region holds every method below it.
                row("regionId", "REGION.request", "methods", Arrays.asList(
                        "<example.Rpc: void handle()>", increment, decrement)),
                row("regionId", "REGION.delete", "methods",
                        Collections.singletonList(decrement)),
                row("regionId", "REGION.create", "methods",
                        Collections.singletonList(increment)),
                row("regionId", "REGION.save", "methods",
                        Collections.singletonList(saver),
                        "communicationPorts",
                        Collections.singletonList(port)));

        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(edges, regions);
        Path file = tree.newFolder("scope-map").toPath()
                .resolve(StaticScopeMap.FILE);
        StringBuilder text = new StringBuilder();
        for (JsonObject written : StaticScopeMap.rows(sites,
                siteId -> siteId.endsWith("#u35")
                        ? Arrays.asList(
                        new StaticScopeMap.Guard(decrement + "#u7", true),
                        new StaticScopeMap.Guard(decrement + "#u15", false))
                        : Collections.<StaticScopeMap.Guard>emptyList())) {
            text.append(written.toString()).append('\n');
        }
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        // The counter's carrier is found from the site the recording DID
        // write at, spelled the way the VM spells an endpoint site.
        Set<String> carriers = map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "I");
        assertEquals(Collections.singleton(carrier), carriers);
        // A write row of another type at that method is not that cell.
        assertTrue(map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "Z")
                .isEmpty());
        List<String> writers = new ArrayList<>();
        for (StaticScopeMap.Site site : map.writersOf(carrier)) {
            writers.add(site.regionId + " " + site.siteId);
        }
        assertEquals("the writer the seed never ran is in the map, under the "
                        + "innermost region that would run it: " + writers,
                Arrays.asList("REGION.create " + increment + "#u27",
                        "REGION.delete " + decrement + "#u35"), writers);
        List<String> guards = new ArrayList<>();
        List<Boolean> arms = new ArrayList<>();
        for (StaticScopeMap.Site site : map.writersOf(carrier)) {
            assertEquals("<java.util.concurrent.atomic.AtomicInteger: int"
                    + " value>", site.cell);
            if (site.siteId.equals(decrement + "#u35")) {
                guards.addAll(site.guards);
                arms.addAll(site.guardOutcomes);
            }
        }
        assertEquals("the write site carries its post-dominance guard set",
                Arrays.asList(decrement + "#u7", decrement + "#u15"), guards);
        assertEquals("and the arm of each guard that reaches it",
                Arrays.asList(Boolean.TRUE, Boolean.FALSE), arms);
        // The port's producer side, and the annotated target.
        assertEquals(1, map.exportsOf("XCH.a.resp.count").size());
        assertEquals("REGION.save",
                map.exportsOf("XCH.a.resp.count").get(0).regionId);
        assertEquals(1, map.targetSites().size());
        assertEquals(saver + "#u64", map.targetSites().get(0).siteId);
        assertEquals("example.Saver#save(Ljava/io/OutputStream;)V",
                map.targetSites().get(0).vmSite);
    }

    /**
     * The guard set of a write is post-dominance, not may-reach: the branch
     * BOTH of whose arms can reach the write still decides it, because on one
     * arm the write is unavoidable and on the other it is not.  That branch is
     * 17960's ordered-deletion marker.
     */
    private void theGuardSetIsPostDominanceAndNotMayReach() {
        G.reset();
        SootClass owner = new SootClass("example.Guarded");
        owner.setApplicationClass();
        Scene.v().addClass(owner);
        SootMethod method = new SootMethod("delete",
                Collections.<soot.Type>emptyList(), VoidType.v(),
                Modifier.PUBLIC);
        owner.addMethod(method);
        JimpleBody body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local marker = Jimple.v().newLocal("i0", IntType.v());
        Local earliest = Jimple.v().newLocal("i1", IntType.v());
        Local count = Jimple.v().newLocal("i2", IntType.v());
        body.getLocals().addAll(Arrays.asList(marker, earliest, count));
        Unit u0 = Jimple.v().newAssignStmt(marker, IntConstant.v(0));
        Unit u1 = Jimple.v().newAssignStmt(earliest, IntConstant.v(0));
        Unit u2 = Jimple.v().newAssignStmt(count, IntConstant.v(0));
        Unit write = Jimple.v().newAssignStmt(count, IntConstant.v(1));
        Unit assertFirst = Jimple.v().newNopStmt();
        IfStmt ordered = Jimple.v().newIfStmt(Jimple.v().newEqExpr(marker,
                IntConstant.v(0)), write);
        IfStmt first = Jimple.v().newIfStmt(Jimple.v().newEqExpr(earliest,
                IntConstant.v(0)), assertFirst);
        Unit deferred = Jimple.v().newReturnVoidStmt();
        Unit done = Jimple.v().newReturnVoidStmt();
        for (Unit unit : Arrays.asList(u0, u1, u2, ordered, first, deferred,
                assertFirst, write, done)) {
            body.getUnits().add(unit);
        }
        String decrement = SiteId.of(method.getSignature(), 7);
        List<String> expected = Arrays.asList(
                SiteId.of(method.getSignature(), 3),
                SiteId.of(method.getSignature(), 4));
        assertEquals(expected, guardSites(SiteControlDependence.over(
                Collections.singletonList(decrement)).of(decrement)));
        // Each kept branch also NAMES the arm that makes the write
        // unavoidable: that is the site's fatal polarity, and it is stated
        // once, here, instead of derived by a second rule downstream.
        assertEquals(Arrays.asList(Boolean.TRUE, Boolean.TRUE),
                guardArms(SiteControlDependence.over(
                        Collections.singletonList(decrement)).of(decrement)));
        // Both arms of the marker branch CAN reach the write, which is why
        // the graph's may-reach guard rule drops it.
        assertEquals(2, new soot.toolkits.graph.BriefUnitGraph(body)
                .getSuccsOf(ordered).size());

        // And after INSTRUMENT has woven a hook into the same body, the guard
        // ids are STILL the ids the branches were planned and woven under: a
        // published site id is in the ORIGINAL numbering, and reading the
        // guards off positions in a woven body shifted every one of them past
        // the first hook (the whole of G1's "0 of the 27 installed guard ids
        // is decided anywhere in the session").
        CausynthPipeline.tagOriginalUnits(new ArrayList<Unit>(
                body.getUnits()));
        Unit hook = Jimple.v().newAssignStmt(count, IntConstant.v(7));
        body.getUnits().insertBefore(hook, ordered);
        assertEquals("the hook shifted the positions", 8,
                new ArrayList<Unit>(body.getUnits()).indexOf(write));
        assertEquals(expected, guardSites(SiteControlDependence.over(
                Collections.singletonList(decrement)).of(decrement)));
    }

    private static List<String> guardSites(
            List<StaticScopeMap.Guard> guards) {
        List<String> sites = new ArrayList<>();
        for (StaticScopeMap.Guard guard : guards) sites.add(guard.siteId());
        return sites;
    }

    private static List<Boolean> guardArms(
            List<StaticScopeMap.Guard> guards) {
        List<Boolean> arms = new ArrayList<>();
        for (StaticScopeMap.Guard guard : guards) arms.add(guard.outcome());
        return arms;
    }



    private static Map<String, Object> row(Object... fields) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < fields.length; index += 2) {
            result.put((String) fields[index], fields[index + 1]);
        }
        return result;
    }
}
