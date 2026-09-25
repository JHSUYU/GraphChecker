package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.DeclaredSiteCapture;
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

/**
 * The region graph joins on an address.  It only scopes: it never decides
 * what matters, picks an arm, or names a writer.
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
     * An address two activations landed on STATES ITS CLASS, which is
     * whether the kept closure holds its region: inside it a task addresses
     * the occurrence and the ambiguity withholds, outside it no plan row, no
     * task and no session row names the occurrence and the row is telemetry.
     * All three rows of the reviewed hdfs-17960 run were the second case --
     * {@code FSDirectory$InitQuotaTask} ForkJoin siblings, whose regions the
     * closure drops -- and they were published with no class at all, which
     * the campaign reads as blocking.
     */
    @Test
    public void aSharedAddressStatesItsClass() throws Exception {
        assertEquals("BLOCKING", sharedAddressClass("REGION.kept"));
        assertEquals("DIAGNOSTIC", sharedAddressClass("REGION.dropped"));
    }

    /** The class the finalizer states for one shared address. */
    private static String sharedAddressClass(String regionId)
            throws Exception {
        StaticProgram program = new StaticProgram();
        Map<String, Object> kept = new LinkedHashMap<String, Object>();
        kept.put("regionId", "REGION.kept");
        program.regions.add(kept);
        Map<String, Object> shared = new LinkedHashMap<String, Object>();
        shared.put("occurrenceId", PLANNED);
        shared.put("regionId", regionId);
        shared.put(RuntimeSelectedRegionFinalizer.SHARED_ADDRESS_ROOT_CALLS,
                Arrays.asList(26744L, 26745L));
        Method rule = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("stateSharedAddressClasses",
                        StaticProgram.class, List.class);
        rule.setAccessible(true);
        rule.invoke(null, program,
                Collections.singletonList(shared));
        assertEquals(1, program.planGaps.size());
        Map<String, Object> row = program.planGaps.get(0);
        assertEquals("OCCURRENCE_ADDRESS_SHARED", row.get("kind"));
        // The detail says WHICH rule answered, so a reader is not left to
        // infer the class from the code.
        assertTrue(String.valueOf(row.get("detail")),
                String.valueOf(row.get("detail"))
                        .contains(row.get("cls") + ": " + regionId));
        return String.valueOf(row.get("cls"));
    }

    /**
     * What names a declared wire attach across two recordings of one
     * workload.
     *
     * <p>The wire transaction is minted fresh in every run, so nothing in
     * the plan may be named from it.  The offline exchange pairing that used
     * to mint an ordinal over (producer occurrence, consumer occurrence,
     * port, direction), and the request-control edge that used to be named
     * from a response edge, are both gone -- rows are the pairing authority.
     * What decides that an activation holds a declared attach is the
     * DECLARATION (the region's own cut port, with the call site and callee
     * the case's communication mapping names) joined with the RECORDING (a
     * capture at that site), and nothing else: a frame that converted
     * nothing states no capture and is not admitted, whatever the wire
     * called the transaction.</p>
     */
    @Test
    public void aDeclaredAttachIsNamedByTheDeclarationNotTheWire()
            throws Exception {
        assertNotEquals("the wire transactions of two recordings are "
                        + "expected to differ",
                "hadoop-ipc-f76d5ada8a274fd1ac95a5db23edeaa4-21\n0",
                "hadoop-ipc-9c8bc11a624f4ee1ad1374fe269fe5ca-21\n0");

        String frame = "<example.Helper: example.Keys convert("
                + "example.KeysProto)>";
        String site = "<example.Helper: example.Key convert("
                + "example.KeyProto)>#u2";
        String callee = "<example.KeyProto: int getKeyId()>";
        StaticProgram.RegionRow skeleton = skeleton(frame, site, callee);

        assertTrue("the recording states a capture at the declared site",
                attached(skeleton, capture(site, callee)));
        assertFalse("a frame that converted nothing states none",
                attached(skeleton, capture("", "")));
        assertFalse("a capture at some other call is not this attach",
                attached(skeleton, capture(site,
                        "<example.KeyProto: long getExpiryDate()>")));
    }

    /** One region skeleton declaring one IN cut port of a wire mapping. */
    private static StaticProgram.RegionRow skeleton(String frame,
                                                    String site,
                                                    String callee) {
        Map<String, Object> port = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.key-id",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                CommunicationCatalogContract.CALL_SITE_ID, site,
                CommunicationCatalogContract.DECLARED_CALLEE, callee);
        Map<String, Object> region = row(
                "schemaVersion", 3,
                "kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "regionId", "REGION.frame",
                "rootMethod", frame,
                "anchorMethod", frame,
                "methods", Collections.singletonList(frame),
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                Collections.singletonList(port));
        return StaticProgram.regionRows(Collections.singletonList(region),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "test").get(0);
    }

    /** One activation stating one recorded declared-site capture. */
    private static Map<String, Object> capture(String site, String callee) {
        if (site.isEmpty()) return row("regionId", "REGION.frame");
        return row("regionId", "REGION.frame",
                DeclaredSiteCapture.PLAN_FIELD, Collections.singletonList(
                        row(SiteId.MEMBER, site,
                                DeclaredSiteCapture.DECLARED_CALLEE, callee,
                                DeclaredSiteCapture.ORDINAL, 1)));
    }

    private static boolean attached(StaticProgram.RegionRow skeleton,
                                    Map<String, Object> activation)
            throws Exception {
        Method rule = RuntimeSelectedRegionFinalizer.class
                .getDeclaredMethod("attachedADeclaredPort",
                        StaticProgram.RegionRow.class, Map.class);
        rule.setAccessible(true);
        return (Boolean) rule.invoke(null, skeleton, activation);
    }

    /**
     * What the slice PUBLISHES about the cells it names (CLOSURE-V2 SS4):
     * every write site of such a cell, under the innermost region that would
     * run it, with the guard set post-dominance gives that site -- and the
     * guard set is where a may-reach guard and a control-dependence guard
     * differ, which is the difference between finding 17960's marker flip and
     * not finding it.
     *
     * <p>That is the whole of what the static side contributes to the demand
     * walk.  {@code writerRegionsByCell} is the join the region finalizer
     * crosses on: one location, the REGIONS whose text stores into it, under
     * both names a read can reach it by -- the leaf the VM versions and the
     * declared field that owns it.  It names no activation and no writer: a
     * region the recording never entered contributes no occurrence, and WHICH
     * of the entered ones wrote the value the VM's own expression decides.</p>
     */
    @Test
    public void theMapScopesTheDemandWalkAndNamesNoWriter()
            throws IOException {
        theSliceNamesEveryWriteSiteOfACellItNames();
        theGuardSetIsPostDominanceAndNotMayReach();
    }

    /**
     * 17960's shape: one counter, two writers, and the writer the seed never
     * ran is in the map exactly like the one it did.
     */
    private void theSliceNamesEveryWriteSiteOfACellItNames()
            throws IOException {
        String leaf = "<java.util.concurrent.atomic.AtomicInteger: int value>";
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

        // The join the demand walk crosses on: both names of the location
        // answer with the same two sites, each naming the region AND the
        // method an activation has to have entered to have written there.
        Map<String, List<StaticScopeMap.Site>> writeSites =
                map.writeSitesByCell();
        assertEquals("the leaf the VM keeps versions of",
                Arrays.asList("REGION.create " + increment + "#u27",
                        "REGION.delete " + decrement + "#u35"),
                scoped(writeSites.get(leaf)));
        assertEquals("and the declared field that owns it",
                scoped(writeSites.get(leaf)),
                scoped(writeSites.get(carrier)));
        assertEquals("the storing method is what the recording is joined on",
                Arrays.asList(increment, decrement),
                methodsOf(writeSites.get(leaf)));
        assertFalse("a local-held container mutation names no shared "
                        + "location, so it scopes no writer",
                writeSites.containsKey(decrement + "::$r5"));
        assertFalse("the annotated target is not a write site",
                writeSites.containsKey(saver
                        + "#u64#exception:java.lang.IllegalState"));
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

    private static List<String> scoped(List<StaticScopeMap.Site> sites) {
        List<String> scopes = new ArrayList<>();
        for (StaticScopeMap.Site site : sites) {
            scopes.add(site.regionId + " " + site.siteId);
        }
        return scopes;
    }

    private static List<String> methodsOf(List<StaticScopeMap.Site> sites) {
        List<String> methods = new ArrayList<>();
        for (StaticScopeMap.Site site : sites) {
            methods.add(SiteId.methodOf(site.siteId));
        }
        return methods;
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
