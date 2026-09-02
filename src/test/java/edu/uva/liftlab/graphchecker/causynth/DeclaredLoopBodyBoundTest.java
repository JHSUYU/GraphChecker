package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.concolic.BoundedLoopComposition;
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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

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

    /**
     * A retained loop that declares nothing omits the field.
     *
     * <p>Writing the inherited value instead would hand a loop that declared
     * nothing the {@link LoopBoundPolicy#BOUND_FROM_DECLARATION} authority of
     * one that did, which is exactly what README {@code LOOP-1} refuses: an
     * absent field declares no {@code K_L} and carries no authority at
     * all.</p>
     */
    @Test
    public void aRetainedLoopThatDeclaresNothingOmitsTheFieldEntirely()
            throws Exception {
        SootMethod client = clientWithLoopAroundCut();
        String loopSite = CommunicationCatalogContract.siteId(
                client.getSignature(), 2);

        Map<String, Object> undeclared = loop(
                plan(client, DeclaredLoopBodyBounds.none()), loopSite);
        Map<String, Object> declared = loop(
                plan(client, declarations("{\"loopSiteId\": \"" + loopSite
                        + "\", \"loopBodyBound\": 16}")), loopSite);

        assertFalse(String.valueOf(undeclared), undeclared.containsKey(
                LoopBoundPolicy.LOOP_BODY_BOUND));
        assertEquals(LoopBoundPolicy.NO_DECLARED_BOUND,
                LoopBoundPolicy.bodyBound(undeclared.get(
                        LoopBoundPolicy.LOOP_BODY_BOUND)));
        // The declared row is the undeclared row plus exactly one key, at the
        // end: nothing else about the artifact moved.
        List<String> declaredKeys = new ArrayList<>(declared.keySet());
        List<String> undeclaredKeys = new ArrayList<>(undeclared.keySet());
        assertEquals(undeclaredKeys.size() + 1, declaredKeys.size());
        assertEquals(LoopBoundPolicy.LOOP_BODY_BOUND,
                declaredKeys.get(declaredKeys.size() - 1));
        assertEquals(undeclaredKeys,
                declaredKeys.subList(0, undeclaredKeys.size()));
        for (String key : undeclaredKeys) {
            assertEquals(key, String.valueOf(undeclared.get(key)),
                    String.valueOf(declared.get(key)));
        }
    }

    /**
     * One composite nest site has one prefix: members that state different
     * bounds are refused, naming both.
     */
    @Test
    public void aNestWhoseMembersDisagreeIsRefusedNamingBoth()
            throws Exception {
        String outer = "<example.Client: int call()>#u2";
        String inner = "<example.Client: int call()>#u4";
        DeclaredLoopBodyBounds bounds = declarations(
                "{\"loopSiteId\": \"" + outer + "\","
                        + " \"loopBodyBound\": 32}",
                "{\"loopSiteId\": \"" + inner + "\","
                        + " \"loopBodyBound\": 16}");
        try {
            bounds.bound(Arrays.asList(outer, inner));
            fail("a nest with two prefixes must be refused");
        } catch (IllegalArgumentException refused) {
            String message = refused.getMessage();
            assertTrue(message, message.startsWith(
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES));
            assertTrue(message, message.contains(
                    DeclaredLoopBodyBounds.KEY_PREFIX + outer + "=32"));
            assertTrue(message, message.contains(
                    DeclaredLoopBodyBounds.KEY_PREFIX + inner + "=16"));
            // The refusal names the model site the nest is stated over.
            assertTrue(message, message.contains(
                    LoopBoundPolicy.loopSiteId(Arrays.asList(outer, inner))));
        }
    }

    /**
     * A nest member that declares nothing inherits, which is a second prefix
     * for one loop.  Refused rather than resolved by taking the stated one.
     */
    @Test
    public void aNestMemberThatDeclaresNothingIsRefused() throws Exception {
        String outer = "<example.Client: int call()>#u2";
        String inner = "<example.Client: int call()>#u4";
        DeclaredLoopBodyBounds bounds = declarations(
                "{\"loopSiteId\": \"" + inner + "\","
                        + " \"loopBodyBound\": 24}");
        try {
            bounds.bound(Arrays.asList(outer, inner));
            fail("a partly declared nest must be refused");
        } catch (IllegalArgumentException refused) {
            String message = refused.getMessage();
            assertTrue(message, message.startsWith(
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES));
            assertTrue(message, message.contains("absent, inheriting "
                    + LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS));
        }
    }

    /**
     * A bound above the per-loop ceiling has no executor to be translated to.
     * Mint time refuses it anyway; refusing at emission names the key and the
     * file that stated it, which is the only place a person can fix it.
     */
    @Test
    public void aBoundOutsideTheCeilingIsRefusedNamingTheConfigKey()
            throws Exception {
        SootMethod client = clientWithLoopAroundCut();
        String loopSite = CommunicationCatalogContract.siteId(
                client.getSignature(), 2);
        int beyond = LoopBoundPolicy.MAX_DECLARED_LOOP_BODY_ITERATIONS + 1;
        Path file = file("{\"loopSiteId\": \"" + loopSite
                + "\", \"loopBodyBound\": " + beyond + "}");

        try {
            plan(client, DeclaredLoopBodyBounds.read(file));
            fail("a bound above the ceiling must be refused");
        } catch (IllegalArgumentException refused) {
            String message = refused.getMessage();
            assertTrue(message, message.startsWith(
                    LoopBoundPolicy.DECLARED_BOUND_OUT_OF_RANGE));
            assertTrue(message, message.contains(
                    DeclaredLoopBodyBounds.KEY_PREFIX + loopSite + "="
                            + beyond));
            assertTrue(message, message.contains(file.toString()));
        }
    }

    /**
     * A key that names no retained loop is a typo, a stale unit index, or a
     * loop this slice does not retain.  All three would leave the loop the
     * author meant inheriting the default, so the campaign is refused rather
     * than the key ignored.
     */
    @Test
    public void aKeyThatNamesNoRetainedLoopIsRefusedRatherThanIgnored()
            throws Exception {
        SootMethod client = clientWithLoopAroundCut();
        // Unit 3 is the loop body, not its control branch: exactly the shape
        // a recompiled workload produces when indices shift.
        String stale = CommunicationCatalogContract.siteId(
                client.getSignature(), 3);
        DeclaredLoopBodyBounds bounds = declarations(
                "{\"loopSiteId\": \"" + stale + "\", \"loopBodyBound\": 32}");

        CommunicationCatalogPlanner.Result result = plan(client, bounds);

        assertFalse(result.loops.isEmpty());
        for (Map<String, Object> row : result.loops) {
            assertFalse(String.valueOf(row), row.containsKey(
                    LoopBoundPolicy.LOOP_BODY_BOUND));
        }
        try {
            bounds.refuseUnclaimed();
            fail("a declaration no retained loop claims must be refused");
        } catch (IllegalStateException refused) {
            String message = refused.getMessage();
            assertTrue(message, message.startsWith(
                    LoopBoundPolicy.DECLARED_BOUND_SITE_UNDECLARED));
            assertTrue(message, message.contains(
                    DeclaredLoopBodyBounds.KEY_PREFIX + stale));
        }
    }

    /** A declaration naming a field this schema has no meaning for. */
    @Test
    public void anUnknownDeclarationFieldIsRefused() throws Exception {
        try {
            declarations("{\"loopSiteId\": \"<a.B: void c()>#u1\","
                    + " \"loopBodyBounds\": 32}");
            fail("an unknown declaration field must be refused");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    DeclaredLoopBodyBounds.FIELD_UNKNOWN));
        }
    }

    /** One loop has one prefix, so one loop has one declaration. */
    @Test
    public void oneLoopDeclaredTwiceIsRefused() throws Exception {
        try {
            declarations(
                    "{\"loopSiteId\": \"<a.B: void c()>#u1\","
                            + " \"loopBodyBound\": 32}",
                    "{\"loopSiteId\": \"<a.B: void c()>#u1\","
                            + " \"loopBodyBound\": 32}");
            fail("one loop declared twice must be refused");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().startsWith(
                    BoundedLoopComposition.LOOP_BODY_BOUND_DISAGREES));
        }
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
