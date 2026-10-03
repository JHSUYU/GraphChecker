package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
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
import soot.ArrayType;
import soot.DoubleType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
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
     * whether the kept closure retains that occurrence: then a task
     * addresses it and the ambiguity withholds; otherwise no plan row, no
     * task and no session row names it and the row is telemetry, whatever
     * else of its region is planned.  All three rows of the reviewed
     * hdfs-17960 run were the second case -- {@code FSDirectory$InitQuotaTask}
     * ForkJoin siblings, whose regions the closure drops -- and they were
     * published with no class at all, which the campaign reads as blocking.
     */
    @Test
    public void aSharedAddressStatesItsClass() throws Exception {
        assertEquals("BLOCKING", sharedAddressClass(PLANNED));
        assertEquals("DIAGNOSTIC", sharedAddressClass(
                PLANNED.replace("TICK#1", "TICK#2")));
    }

    /** The class the finalizer states for one shared address of the kept
     *  region, the closure retaining {@code retained} of it. */
    private static String sharedAddressClass(String retained)
            throws Exception {
        String regionId = "REGION.kept";
        StaticProgram program = new StaticProgram();
        Map<String, Object> kept = new LinkedHashMap<String, Object>();
        kept.put("regionId", regionId);
        kept.put("runtimeOccurrenceIds", Collections.singletonList(retained));
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
                        .contains(row.get("cls") + ": the closure"));
        return String.valueOf(row.get("cls"));
    }

    /**
     * WHAT THE RECORDING HELD decides where the failure's demand crosses
     * (SYMBOL-SCOPE §4.4).  A stored field is one object's: of the
     * occurrences on the reader's node that ran its storing method, the walk
     * plans those the recording saw access it on the object the reader read
     * it on, or on no object (a store on an arm it did not take), never one
     * that held other objects only, nor one on another node.  A message is
     * one exchange leg: an attach whose value reaches what is demanded plans
     * the occurrence that exported it on that leg, never an export of the
     * same port on another leg -- the unconditional admission of every
     * capture planned 2673 occurrences for one ad-hoc check (a40h-5).
     */
    @Test
    public void theWalkCrossesWhatTheRecordingHeld() throws Exception {
        Object[][] activations = {
                // name, node, region, owners of EPOCH, attach leg, export leg
                {"target", "wl/nn0#epoch0", "REGION.check", 7, "", ""},
                {"same-object", "wl/nn0#epoch0", "REGION.bump", 7, "L1", ""},
                {"other-object", "wl/nn0#epoch0", "REGION.bump", 8, "L2", ""},
                {"no-access", "wl/nn0#epoch0", "REGION.bump", 0, "", ""},
                {"other-node", "wl/dn0#epoch0", "REGION.bump", 7, "", ""},
                {"paired-export", "wl/dn0#epoch0", "REGION.send", 0, "", "L1"},
                {"other-leg", "wl/dn0#epoch0", "REGION.send", 0, "", "L2"},
        };
        List<Map<String, Object>> instances = new ArrayList<>();
        Map<String, String> addresses = new LinkedHashMap<>();
        for (int index = 0; index < activations.length; index++) {
            Object[] row = activations[index];
            String address = OccurrenceAddress.of(
                    NodeId.parse((String) row[1]), (String) row[2],
                    CausalContext.of(Role.of("CLIENT"), "", index + 1),
                    ExecutionIndex.empty()).render();
            addresses.put((String) row[0], address);
            String method = "REGION.check".equals(row[2]) ? CHECK
                    : "REGION.bump".equals(row[2]) ? BUMP : SEND;
            Map<String, Object> activation = row(
                    "kind", "RUNTIME_REGION_ACTIVATION",
                    "regionId", row[2],
                    "rootCallId", (long) index + 1,
                    "occurrenceAddress", address,
                    "selection", "REGION.check".equals(row[2])
                            ? "EXCEPTION_CONTEXT" : "STATE_CONTEXT",
                    "callIds", Collections.singletonList((long) index + 1),
                    "observedMethods", Collections.singletonList(method));
            if ((Integer) row[3] != 0) {
                activation.put(RuntimeSelectedRegionFinalizer.FIELD_OWNERS,
                        Collections.singletonMap(EPOCH,
                                Collections.singleton(row[3])));
            }
            List<Map<String, Object>> captures = new ArrayList<>();
            if (!((String) row[4]).isEmpty()) {
                captures.add(row("side", "IN", "portId", PORT,
                        "exchangeLeg", row[4]));
            }
            if (!((String) row[5]).isEmpty()) {
                captures.add(row("side", "OUT", "portId", PORT,
                        "exchangeLeg", row[5]));
            }
            activation.put(RuntimeSelectedRegionFinalizer
                    .OBSERVED_COMMUNICATION_CAPTURES, captures);
            instances.add(activation);
        }
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(walkGraph(),
                        walkSkeletons(), "test", Arrays.asList(CHECK, BUMP,
                                SEND), instances,
                        Collections.singletonList(row("kind", "BRANCH",
                                "eventSeq", 5L, "method", CHECK,
                                "callId", 1L, "siteId", CHECK + "#u5",
                                "outcome", Boolean.TRUE)),
                        walkScopeMap(), RuntimeWorkflowDiscovery.FIRST,
                        Collections.<ScheduleEvent>emptyList());
        List<String> planned = new ArrayList<>();
        for (Map<String, Object> region : closure.regions) {
            for (Object occurrence
                    : (List<?>) region.get("runtimeOccurrenceIds")) {
                for (Map.Entry<String, String> named : addresses.entrySet()) {
                    if (named.getValue().equals(occurrence)) {
                        planned.add(named.getKey());
                    }
                }
            }
        }
        Collections.sort(planned);
        assertEquals(Arrays.asList("no-access", "paired-export",
                "same-object", "target"), planned);
    }

    private static final String CHECK = "<ex.Server: void check()>";
    private static final String BUMP = "<ex.State: void bump(ex.Proto)>";
    private static final String SEND = "<ex.Client: ex.Proto send()>";
    private static final String EPOCH = "<ex.State: int epoch>";
    private static final String GET = "<ex.Proto: int getEpoch()>";
    private static final String SET =
            "<ex.Proto$Builder: ex.Proto$Builder setEpoch(int)>";
    private static final String PORT = "XCH.ex.wire.epoch";

    /** The target reads EPOCH into its fatal guard; bump stores what it
     *  attached into EPOCH; send exports it. */
    private static List<Map<String, Object>> walkGraph() {
        return Arrays.asList(
                row("kind", "exception_guard", "transferKind", "GUARD",
                        "fromCell", CHECK + "::$i0",
                        "toCell", CHECK + "#u5#exception:ex.Fail",
                        "method", CHECK, "siteId", CHECK + "#u5",
                        "unitIndex", 5),
                row("kind", "field_read", "fromCell", EPOCH,
                        "toCell", CHECK + "::$i0", "method", CHECK,
                        "siteId", CHECK + "#u3", "unitIndex", 3),
                row("kind", "call_return", "fromCell", GET + ".return",
                        "toCell", BUMP + "::$i1", "method", BUMP,
                        "siteId", BUMP + "#u1", "unitIndex", 1),
                row("kind", "field_write", "fromCell", BUMP + "::$i1",
                        "toCell", EPOCH, "method", BUMP,
                        "siteId", BUMP + "#u2", "unitIndex", 2),
                row("kind", "wire_capture_argument",
                        "fromCell", SEND + "::$i2",
                        "toCell", SET + ".param0:int", "method", SEND,
                        "siteId", SEND + "#u4", "unitIndex", 4));
    }

    private static List<StaticProgram.RegionRow> walkSkeletons() {
        Map<String, Object> attach = row("portId", PORT,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN,
                CommunicationCatalogContract.CALL_SITE_ID, BUMP + "#u1",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, BUMP,
                CommunicationCatalogContract.DECLARED_CALLEE, GET,
                "javaType", "int");
        Map<String, Object> export = row("portId", PORT,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_ARGUMENT,
                CommunicationCatalogContract.CALL_SITE_ID, SEND + "#u4",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, SEND,
                CommunicationCatalogContract.DECLARED_CALLEE, SET,
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX, 0,
                "javaType", "int");
        return StaticProgram.regionRows(Arrays.asList(
                walkSkeleton("REGION.check", CHECK, "EXCEPTION_CONTEXT",
                        Collections.<Map<String, Object>>emptyList()),
                walkSkeleton("REGION.bump", BUMP, "STATE_CONTEXT",
                        Collections.singletonList(attach)),
                walkSkeleton("REGION.send", SEND, "COMMUNICATION_CONTEXT",
                        Collections.singletonList(export))),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    private static Map<String, Object> walkSkeleton(
            String regionId, String method, String selection,
            List<Map<String, Object>> ports) {
        return row("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION,
                "kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "regionId", regionId, "rootMethod", method,
                "rootAuthority", "STATE_WRITER_ENTRY",
                "anchorMethod", method,
                "anchorMethods", Collections.singletonList(method),
                "selection", selection,
                "methods", Collections.singletonList(method),
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS, ports);
    }

    /** The guard that decides the throw, and bump's store of EPOCH. */
    private StaticScopeMap walkScopeMap() throws IOException {
        JsonObject target = new JsonObject();
        target.addProperty("kind", "STATIC_SCOPE_SITE");
        target.addProperty("role", "TARGET_SITE");
        target.addProperty("regionId", "REGION.check");
        target.addProperty("siteId", CHECK + "#u7");
        JsonArray guards = new JsonArray();
        guards.add(CHECK + "#u5");
        target.add("guards", guards);
        JsonArray outcomes = new JsonArray();
        outcomes.add(true);
        target.add("guardOutcomes", outcomes);
        JsonObject write = new JsonObject();
        write.addProperty("kind", "STATIC_SCOPE_SITE");
        write.addProperty("role", "WRITE_SITE");
        write.addProperty("regionId", "REGION.bump");
        write.addProperty("siteId", BUMP + "#u2");
        write.addProperty("cell", EPOCH);
        write.addProperty("carrier", EPOCH);
        Path file = tree.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, (target + "\n" + write + "\n")
                .getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    /**
     * What the slice PUBLISHES about the cells it names (SYMBOL-SCOPE §3):
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
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, saver,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        // The same port's attach defines nothing: no export site.
        Map<String, Object> attach = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                decrement,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 3);
        List<Map<String, Object>> regions = Arrays.asList(
                // The enclosing request region holds every method below it.
                row("regionId", "REGION.request", "methods", Arrays.asList(
                        "<example.Rpc: void handle()>", increment, decrement)),
                row("regionId", "REGION.delete", "methods",
                        Collections.singletonList(decrement),
                        "communicationPorts",
                        Collections.singletonList(attach)),
                row("regionId", "REGION.create", "methods",
                        Collections.singletonList(increment)),
                row("regionId", "REGION.save", "methods",
                        Collections.singletonList(saver),
                        "communicationPorts",
                        Collections.singletonList(port)));

        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(edges, regions,
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null, StaticScopeMap.NO_DEMAND, method -> false,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false);
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
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "I",
                LocationKind.INSTANCE);
        assertEquals(Collections.singleton(carrier), carriers);
        // A write row of another type at that method is not that cell.
        assertTrue(map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "Z",
                LocationKind.INSTANCE)
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
        // The port's producer side only, and the declared target.
        assertEquals("the attach in REGION.delete is no export", 1,
                map.exportsOf("XCH.a.resp.count").size());
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
        assertFalse("the declared target is not a write site",
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
        // the first hook ("0 of the 27 installed guard ids is decided
        // anywhere in the session").
        CausynthPipeline.tagOriginalUnits(new ArrayList<Unit>(
                body.getUnits()));
        Unit hook = Jimple.v().newAssignStmt(count, IntConstant.v(7));
        body.getUnits().insertBefore(hook, ordered);
        assertEquals("the hook shifted the positions", 8,
                new ArrayList<Unit>(body.getUnits()).indexOf(write));
        assertEquals(expected, guardSites(SiteControlDependence.over(
                Collections.singletonList(decrement)).of(decrement)));
    }

    /**
     * SYMBOL-SCOPE F2: a field is tracked by what it holds.  An integral
     * instance field, boxed or not, is a VALUE; a field a store re-points
     * holding any other object, an array or a static one included, is a
     * REFERENCE; a final one, a String, a float and a static value are
     * none.  A wrapper-typed field is a value cell as its primitive is
     * (solr-18413's {@code RoutingRule.expireAt}, a Long): its {@code
     * getfield} is the READ_SITE a branch decides on through the unboxing,
     * observed like its {@code putfield}; the box's own {@code value} is no
     * tracked cell; and a write row stating the value's type ({@code J}),
     * or a null ({@code L}), names the field as its carrier.  A static
     * reference cell is observed too, as {@code static} (on its class's
     * mirror).
     */
    @Test
    public void aWrapperFieldIsAValueCell() throws IOException {
        G.reset();
        SootClass rule = new SootClass("example.Rule");
        rule.setApplicationClass();
        Scene.v().addClass(rule);
        SootClass box = new SootClass("java.lang.Long");
        box.addField(new SootField("value", LongType.v(), Modifier.FINAL));
        Scene.v().addClass(box);
        SharedFieldFlow.TrackedKind held = SharedFieldFlow.TrackedKind.VALUE;
        SharedFieldFlow.TrackedKind reference =
                SharedFieldFlow.TrackedKind.REFERENCE;
        SharedFieldFlow.TrackedKind none = SharedFieldFlow.TrackedKind.NONE;
        Object[][] fields = {
                {LongType.v(), 0, held},
                {RefType.v("java.lang.Long"), 0, held},
                {RefType.v("java.lang.Boolean"), 0, held},
                {RefType.v("java.lang.Long"), Modifier.STATIC, none},
                {RefType.v("java.lang.Double"), 0, none},
                {DoubleType.v(), 0, none},
                {RefType.v("java.lang.String"), 0, none},
                {RefType.v("java.util.Map"), Modifier.VOLATILE, reference},
                {RefType.v("java.util.Map"), Modifier.FINAL, none},
                {RefType.v("java.util.Map"), Modifier.STATIC, reference},
                {ArrayType.v(LongType.v(), 1), 0, reference}};
        for (int index = 0; index < fields.length; index++) {
            SootField field = new SootField("f" + index,
                    (soot.Type) fields[index][0], (Integer) fields[index][1]);
            rule.addField(field);
            assertEquals(field.getSignature(), fields[index][2],
                    CausynthStaticFacts.trackedKind(field.getSignature()));
            assertEquals(field.getSignature(),
                    ((Integer) fields[index][1] & Modifier.STATIC) != 0,
                    CausynthStaticFacts.staticField(field.getSignature()));
        }
        assertTrue("Boolean's unboxing passes its receiver's value on",
                JavaPrimitiveBoxing.unboxing(
                        "<java.lang.Boolean: boolean booleanValue()>"));

        String init = "<example.Rule: void <init>(java.util.Map)>";
        String expired = "<example.Rule: boolean isExpired()>";
        String expireAt = "<example.Rule: java.lang.Long f1>";
        String value = "<java.lang.Long: long value>";
        String unbox = "<java.lang.Long: long longValue()>";
        String registry = "<example.Rule: java.util.Map f9>";
        List<Map<String, Object>> edges = Arrays.asList(
                row("kind", "field_write", "method", init, "unitIndex", 34,
                        "fromCell", init + "::$r16", "toCell", expireAt),
                row("kind", "field_write", "method", init, "unitIndex", 40,
                        "fromCell", init + "::$r20", "toCell", registry),
                row("kind", "field_read", "method", expired, "unitIndex", 8,
                        "fromCell", registry, "toCell", expired + "::$r3",
                        "declaredFieldSignature", registry),
                row("kind", "guard_dependency", "method", expired,
                        "unitIndex", 9, "fromCell", expired + "::$r3",
                        "toCell", expired + "#u9"),
                row("kind", "field_read", "method", expired, "unitIndex", 1,
                        "fromCell", expireAt, "toCell", expired + "::$r1",
                        "declaredFieldSignature", expireAt),
                row("kind", "local_def_use", "method", expired,
                        "unitIndex", 2, "fromCell", expired + "::$r1",
                        "toCell", expired + "::$l0", "invoke", unbox),
                row("kind", "accessor_field_return", "method", expired,
                        "unitIndex", 2, "fromCell", value,
                        "toCell", expired + "::$l0", "invoke", unbox,
                        "declaredFieldSignature", value,
                        "accessorImplementationMethod", unbox),
                row("kind", "guard_dependency", "method", expired,
                        "unitIndex", 6, "fromCell", expired + "::$l0",
                        "toCell", expired + "#u6"));
        List<Map<String, Object>> regions = Arrays.asList(
                row("regionId", "REGION.update", "methods",
                        Collections.singletonList(expired)),
                row("regionId", "REGION.overseer", "methods",
                        Collections.singletonList(init)));
        StringBuilder text = new StringBuilder();
        for (JsonObject written : StaticScopeMap.rows(StaticScopeMap.sites(
                edges, regions, Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null, StaticScopeMap.NO_DEMAND,
                method -> !method.startsWith("<example."),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField), null)) {
            text.append(written.toString()).append('\n');
        }
        Path file = tree.newFolder("wrapper").toPath()
                .resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        Map<String, String> observed = new LinkedHashMap<>();
        for (int index = 0; index < map.observedSites().size(); index++) {
            JsonObject site = map.observedSites().get(index)
                    .getAsJsonObject();
            observed.put(site.get("siteId").getAsString(),
                    site.get("cell").getAsString()
                            + (site.has("static") ? " static" : ""));
        }
        Map<String, String> expected = new LinkedHashMap<>();
        expected.put(init + "#u34", expireAt);
        expected.put(expired + "#u1", expireAt);
        expected.put(init + "#u40", registry + " static");
        expected.put(expired + "#u8", registry + " static");
        assertEquals("the wrapper's putfield and getfield, not the box's"
                + " value, and the static map's store and read", expected,
                observed);
        assertEquals(Collections.singleton("REGION.update"),
                map.trackedRegions());
        String store = "example.Rule#<init>(Ljava/util/Map;)V#376:WRITE";
        for (String javaType : new String[]{"J", "L"}) {
            assertEquals(javaType, Collections.singleton(expireAt),
                    map.carriersAt(store, javaType, LocationKind.INSTANCE));
        }
        assertTrue(map.carriersAt(store, "I", LocationKind.INSTANCE)
                .isEmpty());
        assertEquals("a class's location joins the static map, never an"
                        + " object's field", Collections.singleton(registry),
                map.carriersAt(store, "L", LocationKind.STATIC));
        assertEquals("a read's INITIAL names it too",
                Collections.singleton(expireAt),
                map.carriersAt("example.Rule#isExpired()Z#30:READ", "J",
                        LocationKind.INSTANCE));
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
