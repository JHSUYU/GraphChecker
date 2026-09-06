package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

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

import static org.junit.Assert.assertEquals;

/**
 * {@code K_L}, from the campaign that declares it to the retained-loop row
 * that states it.
 *
 * <p>Every case here is about one rule: a bound is a declaration, so the
 * planner may publish exactly what a campaign stated for a loop it really
 * retained, and must refuse everything else by name rather than let a loop
 * inherit a prefix nobody asked for.</p>
 */
public class DeclaredLoopBodyBoundTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private final Map<String, Body> bodies = new LinkedHashMap<>();
    private final Map<String, SootMethod> methods = new LinkedHashMap<>();

    @Before
    public void resetBefore() {
        soot.G.reset();
        bodies.clear();
        methods.clear();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    /**
     * The declared bound reaches the row of the loop it names, and no other
     * row acquires one.
     */
    @Test
    public void aRetainedLoopCarriesTheBoundItsCampaignDeclared()
            throws Exception {
        SootMethod client = clientWithLoopAroundCut();
        String loopSite = CommunicationCatalogContract.siteId(
                client.getSignature(), 2);

        CommunicationCatalogPlanner.Result result = plan(client,
                declarations("{\"loopSiteId\": \"" + loopSite + "\","
                        + " \"loopBodyBound\": 32,"
                        + " \"reason\": \"bounded experiment rationale\"}"));

        Map<String, Object> loop = loop(result, loopSite);
        assertEquals(Collections.singletonList(loopSite),
                loop.get(LoopBoundPolicy.LOOP_CONTROL_SITE_IDS));
        assertEquals(32, loop.get(LoopBoundPolicy.LOOP_BODY_BOUND));
    }

                                // ------------------------------------------------------------------
    // Fixture
    // ------------------------------------------------------------------

    private CommunicationCatalogPlanner.Result plan(
            SootMethod client, DeclaredLoopBodyBounds bounds) {
        return CommunicationCatalogPlanner.plan(
                Collections.singletonList(client.getSignature()),
                bodies::get,
                Collections.<WireFlowCatalog.WireFlow>emptyList(), bounds);
    }

    private DeclaredLoopBodyBounds declarations(String... rows)
            throws IOException {
        return DeclaredLoopBodyBounds.read(file(rows));
    }

    private Path file(String... rows) throws IOException {
        Path path = folder.newFile("loop-bounds-" + rows.length + "-"
                + Math.abs(Arrays.hashCode(rows)) + ".jsonl").toPath();
        List<String> lines = new ArrayList<>();
        lines.add("# K_L declarations for this campaign.");
        lines.addAll(Arrays.asList(rows));
        Files.write(path, lines, StandardCharsets.UTF_8);
        return path;
    }

    /**
     * <pre>
     * u0 proto := @parameter0
     * u1 i = 0
     * u2 if i &gt;= 3 goto u5     // loop control: continues to u3, exits to u5
     * u3 i = i + 1
     * u4 goto u2
     * u5 proto.call(i)          // the cut
     * u6 if i &gt;= 0 goto u8
     * u7 return
     * u8 return
     * </pre>
     */
    private SootMethod clientWithLoopAroundCut() {
        SootClass object = libraryClass("java.lang.Object");
        SootClass protocol = protocolInterface(object);
        SootMethod declared = protocol.getMethodByName("call");
        SootClass owner = applicationClass("example.LoopClient", object);
        SootMethod method = new SootMethod("run",
                Collections.<soot.Type>singletonList(
                        RefType.v(protocol.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        methods.put(method.getSignature(), method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local proto = local(body, "proto", RefType.v(protocol.getName()));
        Local counter = local(body, "i", IntType.v());
        Unit cut = Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(proto, declared.makeRef(),
                        counter));
        Unit loopHead = Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(counter, IntConstant.v(3)), cut);
        Unit exit = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIdentityStmt(proto,
                Jimple.v().newParameterRef(proto.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(counter,
                IntConstant.v(0)));
        body.getUnits().add(loopHead);
        body.getUnits().add(Jimple.v().newAssignStmt(counter,
                Jimple.v().newAddExpr(counter, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newGotoStmt(loopHead));
        body.getUnits().add(cut);
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(counter, IntConstant.v(0)), exit));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        body.getUnits().add(exit);
        bodies.put(method.getSignature(), body);
        return method;
    }

    private SootClass protocolInterface(SootClass object) {
        SootClass protocol = Scene.v().containsClass("example.Proto")
                ? Scene.v().getSootClass("example.Proto") : null;
        if (protocol != null) {
            return protocol;
        }
        protocol = new SootClass("example.Proto",
                Modifier.PUBLIC | Modifier.INTERFACE | Modifier.ABSTRACT);
        protocol.setSuperclass(object);
        Scene.v().addClass(protocol);
        protocol.setApplicationClass();
        SootMethod call = new SootMethod("call",
                Collections.<soot.Type>singletonList(IntType.v()),
                VoidType.v(), Modifier.PUBLIC | Modifier.ABSTRACT);
        protocol.addMethod(call);
        methods.put(call.getSignature(), call);
        return protocol;
    }

    private SootClass applicationClass(String name, SootClass parent) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        sootClass.setSuperclass(parent);
        Scene.v().addClass(sootClass);
        sootClass.setApplicationClass();
        return sootClass;
    }

    private static SootClass libraryClass(String name) {
        if (Scene.v().containsClass(name)) {
            return Scene.v().getSootClass(name);
        }
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        Scene.v().addClass(sootClass);
        sootClass.setLibraryClass();
        return sootClass;
    }

    private static Local local(Body body, String name, soot.Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }

    private static Map<String, Object> loop(
            CommunicationCatalogPlanner.Result result, String loopSiteId) {
        for (Map<String, Object> row : result.loops) {
            if (loopSiteId.equals(row.get(LoopBoundPolicy.LOOP_SITE_ID))) {
                return row;
            }
        }
        throw new AssertionError("no retained loop " + loopSiteId
                + " was published; loops=" + result.loops);
    }

}
