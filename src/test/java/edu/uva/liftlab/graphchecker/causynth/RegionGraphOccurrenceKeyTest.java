package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import java.io.IOException;
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
import static org.junit.Assert.assertTrue;

public class RegionGraphOccurrenceKeyTest {
    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void theMapScopesTheDemandWalkAndNamesNoWriter()
            throws IOException {
        theSliceNamesEveryWriteSiteOfACellItNames();
        theGuardSetIsPostDominanceAndNotMayReach();
    }

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
                row("kind", "container_mutation_argument", "method", decrement,
                        "unitIndex", 12, "toCell", decrement + "::$r5"));
        Map<String, Object> port = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD, saver,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 9);
        Map<String, Object> attach = row(
                CommunicationCatalogContract.PORT_ID, "XCH.a.resp.count",
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                decrement,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, 3);
        List<Map<String, Object>> regions = Arrays.asList(
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
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null, (demandSite, demandCell) -> null, method -> false,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false,
                cell -> false);
        Path file = tree.newFolder("scope-map").toPath()
                .resolve(StaticScopeMap.FILE);
        StringBuilder text = new StringBuilder();
        for (JsonObject written : StaticScopeMap.rows(sites,
                siteId -> siteId.endsWith("#u35")
                        ? Arrays.asList(
                        new StaticScopeMap.Guard(decrement + "#u7", true),
                        new StaticScopeMap.Guard(decrement + "#u15", false))
                        : Collections.<StaticScopeMap.Guard>emptyList(),
                method -> false)) {
            text.append(written.toString()).append('\n');
        }
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        Set<String> carriers = map.carriersAt(
                "example.Manager#create()Ljava/lang/String;#621:WRITE", "I",
                LocationKind.INSTANCE);
        assertEquals(Collections.singleton(carrier), carriers);
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
        assertEquals("the attach in REGION.delete is no export", 1,
                map.exportsOf("XCH.a.resp.count").size());
        assertEquals("REGION.save",
                map.exportsOf("XCH.a.resp.count").get(0).regionId);
        assertEquals(1, map.targetSites().size());
        assertEquals(saver + "#u64", map.targetSites().get(0).siteId);
        assertEquals("example.Saver#save(Ljava/io/OutputStream;)V",
                map.targetSites().get(0).vmSite);

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
        assertEquals(Arrays.asList(Boolean.TRUE, Boolean.TRUE),
                guardArms(SiteControlDependence.over(
                        Collections.singletonList(decrement)).of(decrement)));
        assertEquals(2, new soot.toolkits.graph.BriefUnitGraph(body)
                .getSuccsOf(ordered).size());

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
