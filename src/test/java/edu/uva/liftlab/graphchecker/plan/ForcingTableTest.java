package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonArray;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.SiteControlDependence;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.Body;
import soot.BooleanType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.options.Options;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.Assert.assertEquals;

/**
 * The declared throw's forcing table (PIPELINE §2): each guard at its fatal
 * arm, each chain guard at its arm toward the guard it controls, a helper's
 * deciding arm whose verdict the guard wants (else its open arm, nested
 * deciders alike, each with the method that calls its helper); a switch
 * guard and a fault call (no arm) are not forced.  SEED writes it on the
 * TARGET_SITE row, the map reads each row's back, and a task takes its own
 * target's.
 */
public class ForcingTableTest {
    private static final String M = "<a.T: void check(int)>";
    private static final String H = "<a.T: boolean expired()>";
    private static final String N = "<a.T: int age()>";
    private static final String CALLER = "<a.T: void run(int)>";
    /** A branchless helper between {@link #H}'s test and {@link #N}: N's
     *  deciders are called from it, not from H. */
    private static final String X = "<a.T: boolean aged()>";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @Test
    public void theTableNamesTheArmOfEveryBranchOnTheWayToTheThrow()
            throws IOException {
        // check: u3 a switch, u5 a fault call,
        // u8 `if (!expired())` deciding the throw at u9; expired(): u1 tests
        // age(), whose u2 decides; run: u4 calls check.
        String row = "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                + "\"siteId\":\"" + M + "#u9\",\"vmSite\":\"\","
                + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                + "\"guards\":[\"" + M + "#u8\",\"" + M + "#u5\"],"
                + "\"guardOutcomes\":[false,null],"
                + "\"guardDeciders\":{\"" + M + "#u8\":["
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":true,"
                + "\"verdict\":true,\"via\":\"" + M + "\"},"
                + "{\"siteId\":\"" + H + "#u1\",\"outcome\":false,"
                + "\"via\":\"" + M + "\","
                + "\"deciders\":[{\"siteId\":\"" + N + "#u2\","
                + "\"outcome\":true,\"verdict\":false,\"via\":\"" + X
                + "\"},{\"siteId\":\"" + N + "#u2\",\"outcome\":false,"
                + "\"via\":\"" + X + "\"}]}]},"
                + "\"chain\":[{\"siteId\":\"" + M + "#u3\",\"outcome\":null},"
                + "{\"siteId\":\"" + CALLER + "#u4\",\"outcome\":true}]}";
        StaticScopeMap.Site target = read(row).targetSites().get(0);
        Map<String, ForcingTable.Arm> table = ForcingTable.read(
                ForcingTable.of(target, Collections.<String>emptySet()));
        Object[][] rows = {
                {"the guard, at its fatal arm", M + "#u8", "=false"},
                {"the helper's decider at the arm whose verdict the guard "
                        + "wants (false: expired() returns false)",
                        H + "#u1", "=false via " + M},
                {"under that open arm, the nested decider at the arm whose "
                        + "verdict it wants; its other arm is open, so "
                        + "neither leaves the way: passable; via as SEED "
                        + "stated it (its helper is called from X, not from "
                        + "H, whose branch it decides)", N + "#u2",
                        "=true via " + X + " passable"},
                {"a chain switch: never forced", M + "#u3", null},
                {"a caller's chain guard", CALLER + "#u4", "=true"},
                {"a fault call: no arm to force", M + "#u5", null}};
        for (Object[] expected : rows) {
            ForcingTable.Arm arm = table.get((String) expected[1]);
            assertEquals((String) expected[0], expected[2], arm == null ? null
                    : arm.toString().substring(((String) expected[1])
                    .length()));
        }
        assertEquals("one arm per site", 4, table.size());

        // Stated on the row, read back by the map whole, under its site.
        JsonArray force = ForcingTable.of(target,
                Collections.<String>emptySet());
        assertEquals(force, read(row.substring(0, row.length() - 1)
                + ",\"force\":" + force + "}").forcing(M + "#u9"));
        assertEquals("no target, no table", new JsonArray(),
                StaticScopeMap.empty().forcing(M + "#u9"));
    }

    /** Two throws, two tables that disagree on a shared branch: each
     *  TARGET_SITE keeps its own, and a task takes the one whose guards
     *  name its target branch -- never the other's arms. */
    @Test
    public void eachThrowKeepsItsOwnTable() throws IOException {
        String first = target(M + "#u9", M + "#u8",
                "[{\"siteId\":\"" + M + "#u8\",\"arm\":false},"
                        + "{\"siteId\":\"" + CALLER + "#u4\",\"arm\":true}]");
        String second = target(N + "#u9", N + "#u2",
                "[{\"siteId\":\"" + N + "#u2\",\"arm\":true},"
                        + "{\"siteId\":\"" + CALLER + "#u4\",\"arm\":false}]");
        StaticScopeMap map = read(first + "\n" + second);
        Object[][] rows = {
                // {target branch, its throw, the shared caller guard's arm}
                {M + "#u8", M + "#u9", true},
                {N + "#u2", N + "#u9", false}};
        for (Object[] row : rows) {
            StaticScopeMap.Site own = map.ownTarget((String) row[0]);
            assertEquals((String) row[0], row[1], own.siteId);
            Map<String, ForcingTable.Arm> table = ForcingTable.read(
                    map.forcing(own.siteId));
            assertEquals((String) row[0], 2, table.size());
            assertEquals((String) row[0], row[2],
                    table.get(CALLER + "#u4").arm);
        }
        assertEquals("every forced site, for the count of seed flips at "
                + "them", 3, map.forcedSites().size());
    }

    private static String target(String site, String guard, String force) {
        return "{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                + "\"siteId\":\"" + site + "\",\"vmSite\":\"\","
                + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                + "\"guards\":[\"" + guard + "\"],\"guardOutcomes\":[true],"
                + "\"force\":" + force + "}";
    }

    /** An occurrence that entered the throw's method is forced by its own
     *  branches and the deciders only; one that never did, by its callers'
     *  guards too. */
    @Test
    public void anOccurrenceInsideTheThrowsMethodLeavesItsCallersGuards() {
        JsonArray table = JsonParser.parseString("[{\"siteId\":\"" + M
                + "#u8\",\"arm\":false},{\"siteId\":\"" + CALLER
                + "#u4\",\"arm\":true},{\"siteId\":\"" + H
                + "#u1\",\"arm\":false,\"via\":\"" + M + "\"}]")
                .getAsJsonArray();
        Set<String> throwing = Collections.singleton(M);
        Object[][] rows = {
                {"it decided a branch of the throw's method",
                        Collections.singleton(M + "#u3"), 2},
                {"it never entered it", Collections.singleton(
                        CALLER + "#u2"), 3},
                {"it decided nothing", Collections.<String>emptySet(), 3}};
        for (Object[] row : rows) {
            @SuppressWarnings("unchecked")
            Set<String> observed = (Set<String>) row[1];
            Map<String, ForcingTable.Arm> kept = ForcingTable.read(
                    ForcingTable.forOccurrence(table, throwing, observed));
            assertEquals((String) row[0], row[2], kept.size());
            assertEquals((String) row[0], (Integer) row[2] == 3,
                    kept.containsKey(CALLER + "#u4"));
        }
    }

    /**
     * An {@code assert} before the throw: its {@code $assertionsDisabled}
     * test (u2) is a chain guard on its skip arm, yet its other arm reaches
     * the throw too, through the assert's own test (u3): it is passable,
     * never forced, so a forced world with assertions on states no {@code
     * false} for it (solr-adhoc-07 F2P2: ZkController.register's two
     * asserts).  The assert's test is forced at its arm.  Of the throw's own
     * guards, {@code if (x > 5 || x < -5)}, u5's healthy arm reaches the
     * throw through u6: passable too, left to its operands, and a FORCE run
     * goes on to u6 when it takes that arm (runtime.ForcedArms#reachedTarget;
     * solr-18406 F2V3: getAndSaveCommitPoint's u11); u6, at its fatal arm,
     * is forced.  check(int x): u1 z0 = $assertionsDisabled; u2 if z0 goto
     * u5; u3 if x != 0 goto u5; u4 return; u5 if x > 5 goto u7; u6 if x >= -5
     * goto u9; u7 r1 = new X (the throw); u8 throw r1; u9 return.
     */
    @Test
    public void aBranchBothOfWhoseArmsReachTheThrowIsNeverForced()
            throws IOException {
        String check = "<a.A: void check(int)>";
        String thrown = check + "#u7";
        try {
            assertBody();
            StaticScopeMap.Site target = read("{\"schemaVersion\":1,"
                    + "\"kind\":\"STATIC_SCOPE_SITE\","
                    + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                    + "\"siteId\":\"" + thrown + "\",\"vmSite\":\"\","
                    + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\"}")
                    .targetSites().get(0);
            JsonArray force = StaticScopeMap.rows(
                    Collections.singletonList(target),
                    SiteControlDependence.over(Collections.singleton(thrown)),
                    method -> false).get(0).getAsJsonArray("force");
            Map<String, ForcingTable.Arm> table = ForcingTable.read(force);
            Object[][] rows = {
                    {"$assertionsDisabled: both arms reach the throw",
                            check + "#u2", "=true passable"},
                    {"the assert's own test: its other arm returns",
                            check + "#u3", "=true"},
                    {"the throw's own first test: its healthy arm reaches"
                            + " the throw through u6", check + "#u5",
                            "=true passable"},
                    {"the throw's other guard, at its fatal arm",
                            check + "#u6", "=false"}};
            for (Object[] expected : rows) {
                ForcingTable.Arm arm = table.get((String) expected[1]);
                assertEquals((String) expected[0], expected[2], arm == null
                        ? null : arm.toString().substring(
                        ((String) expected[1]).length()));
            }
            assertEquals("a passable branch is no forced site",
                    new java.util.LinkedHashSet<String>(Arrays.asList(
                            check + "#u6", check + "#u3")),
                    read("{\"schemaVersion\":1,\"kind\":\"STATIC_SCOPE_SITE\","
                            + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                            + "\"siteId\":\"" + thrown + "\",\"vmSite\":\"\","
                            + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\","
                            + "\"force\":" + force + "}").forcedSites());
        } finally {
            G.reset();
        }
    }

    /** {@link #aBranchBothOfWhoseArmsReachTheThrowIsNeverForced}'s body. */
    private static void assertBody() {
        Options.v().set_allow_phantom_refs(true);
        SootClass owner = new SootClass("a.A", Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField disabled = new SootField("$assertionsDisabled",
                BooleanType.v(), Modifier.STATIC | Modifier.FINAL);
        owner.addField(disabled);
        SootMethod check = new SootMethod("check",
                Collections.<Type>singletonList(IntType.v()), VoidType.v(),
                Modifier.PUBLIC);
        owner.addMethod(check);
        Jimple j = Jimple.v();
        Body body = j.newBody(check);
        check.setActiveBody(body);
        Local x = j.newLocal("i0", IntType.v());
        Local z = j.newLocal("z0", BooleanType.v());
        RefType thrown = RefType.v("a.X");
        Local r = j.newLocal("r1", thrown);
        body.getLocals().addAll(Arrays.asList(x, z, r));
        Unit end = j.newReturnVoidStmt();
        Unit throwing = j.newAssignStmt(r, j.newNewExpr(thrown));
        Unit afterAssert = j.newIfStmt(j.newGtExpr(x, IntConstant.v(5)),
                throwing);
        body.getUnits().addAll(Arrays.asList(
                j.newIdentityStmt(x, j.newParameterRef(IntType.v(), 0)),
                j.newAssignStmt(z, j.newStaticFieldRef(disabled.makeRef())),
                j.newIfStmt(j.newNeExpr(z, IntConstant.v(0)), afterAssert),
                j.newIfStmt(j.newNeExpr(x, IntConstant.v(0)), afterAssert),
                j.newReturnVoidStmt(),
                afterAssert,
                j.newIfStmt(j.newGeExpr(x, IntConstant.v(-5)), end),
                throwing,
                j.newThrowStmt(r),
                end));
    }

    /**
     * Passable is reachability within ONE iteration: a backedge (the loop's
     * header) is a barrier.  scan(int i): u1 if i >= 10 goto u12 (the loop's
     * test); u2 z1 = first; u3 if z1 == 0 goto u6; u4 z2 = active; u5 if z2
     * == 0 goto u10 (continue); u6 z3 = leader; u7 if z3 == 0 goto u10
     * (continue); u8 r1 = new X (the throw); u9 throw r1; u10 i = i + 1; u11
     * goto u1; u12 return; u13 r2 := @caughtexception (the handler of a
     * trap over u4-u5); u14 if z1 == 0 goto u1 (a {@code continue} straight
     * to the header); u15 goto u6.  The catch block is a head of the CFG,
     * which has no exception edges, so the header dominates no latch: the
     * loop is found from the entry, through the trap's handler
     * (solr-adhoc-07's ZkController$1.command).  isActive's continue arm
     * (u5) comes back to the throw only through the header, in a turn where
     * {@code first} is false: it leaves the way in this one, so it is
     * forced; so is the catch block's u14; {@code first} (u3) leads to u6
     * either way within the turn, so it is passable.
     */
    @Test
    public void aGuardWhoseArmComesBackOnlyInTheNextIterationIsForced()
            throws IOException {
        String scan = "<a.L: void scan(int)>";
        String thrown = scan + "#u8";
        try {
            loopBody();
            StaticScopeMap.Site target = read("{\"schemaVersion\":1,"
                    + "\"kind\":\"STATIC_SCOPE_SITE\","
                    + "\"role\":\"TARGET_SITE\",\"regionId\":\"R\","
                    + "\"siteId\":\"" + thrown + "\",\"vmSite\":\"\","
                    + "\"cell\":\"\",\"carrier\":\"\",\"portId\":\"\"}")
                    .targetSites().get(0);
            Map<String, ForcingTable.Arm> table = ForcingTable.read(
                    StaticScopeMap.rows(Collections.singletonList(target),
                            SiteControlDependence.over(
                                    Collections.singleton(thrown)),
                            method -> false).get(0).getAsJsonArray("force"));
            Object[][] rows = {
                    {"isLeader, the throw's guard, at its fatal arm",
                            scan + "#u7", "=false"},
                    {"isActive: its continue arm leaves the way in this turn",
                            scan + "#u5", "=false"},
                    {"first: both arms reach isLeader within the turn",
                            scan + "#u3", "=true passable"},
                    {"the loop's test: its exit returns", scan + "#u1",
                            "=false"},
                    {"the catch block's continue to the header leaves the"
                            + " way in this turn", scan + "#u14", "=false"}};
            for (Object[] expected : rows) {
                ForcingTable.Arm arm = table.get((String) expected[1]);
                assertEquals((String) expected[0], expected[2], arm == null
                        ? null : arm.toString().substring(
                        ((String) expected[1]).length()));
            }
        } finally {
            G.reset();
        }
    }

    /** {@link #aGuardWhoseArmComesBackOnlyInTheNextIterationIsForced}'s
     *  body. */
    private static void loopBody() {
        Options.v().set_allow_phantom_refs(true);
        SootClass owner = new SootClass("a.L", Modifier.PUBLIC);
        Scene.v().addClass(owner);
        owner.setApplicationClass();
        SootField[] flags = new SootField[3];
        String[] names = {"first", "active", "leader"};
        for (int index = 0; index < flags.length; index++) {
            flags[index] = new SootField(names[index], BooleanType.v(),
                    Modifier.STATIC);
            owner.addField(flags[index]);
        }
        SootMethod scan = new SootMethod("scan",
                Collections.<Type>singletonList(IntType.v()), VoidType.v(),
                Modifier.PUBLIC);
        owner.addMethod(scan);
        Jimple j = Jimple.v();
        Body body = j.newBody(scan);
        scan.setActiveBody(body);
        Local i = j.newLocal("i0", IntType.v());
        Local[] z = {j.newLocal("z1", BooleanType.v()),
                j.newLocal("z2", BooleanType.v()),
                j.newLocal("z3", BooleanType.v())};
        RefType thrown = RefType.v("a.X");
        Local r = j.newLocal("r1", thrown);
        Local caught = j.newLocal("r2", RefType.v("java.lang.Throwable"));
        body.getLocals().addAll(Arrays.asList(i, z[0], z[1], z[2], r,
                caught));
        Unit end = j.newReturnVoidStmt();
        Unit latch = j.newAssignStmt(i, j.newAddExpr(i, IntConstant.v(1)));
        Unit leader = j.newAssignStmt(z[2],
                j.newStaticFieldRef(flags[2].makeRef()));
        Unit head = j.newIfStmt(j.newGeExpr(i, IntConstant.v(10)), end);
        body.getUnits().addAll(Arrays.asList(
                j.newIdentityStmt(i, j.newParameterRef(IntType.v(), 0)),
                head,
                j.newAssignStmt(z[0], j.newStaticFieldRef(flags[0].makeRef())),
                j.newIfStmt(j.newEqExpr(z[0], IntConstant.v(0)), leader),
                j.newAssignStmt(z[1], j.newStaticFieldRef(flags[1].makeRef())),
                j.newIfStmt(j.newEqExpr(z[1], IntConstant.v(0)), latch),
                leader,
                j.newIfStmt(j.newEqExpr(z[2], IntConstant.v(0)), latch),
                j.newAssignStmt(r, j.newNewExpr(thrown)),
                j.newThrowStmt(r),
                latch,
                j.newGotoStmt(head),
                end));
        Unit handler = j.newIdentityStmt(caught, j.newCaughtExceptionRef());
        body.getUnits().addAll(Arrays.asList(handler,
                j.newIfStmt(j.newEqExpr(z[0], IntConstant.v(0)), head),
                j.newGotoStmt(leader)));
        List<Unit> units = new java.util.ArrayList<Unit>(body.getUnits());
        SootClass throwable = new SootClass("java.lang.Throwable",
                Modifier.PUBLIC);
        Scene.v().addClass(throwable);
        body.getTraps().add(j.newTrap(throwable, units.get(4), units.get(6),
                handler));
    }

    @Test
    public void aTableIsReadByItsArms() {
        JsonArray json = JsonParser.parseString("[{\"siteId\":\"a#u1\","
                + "\"arm\":true},{\"siteId\":\"a#u3\",\"arm\":false,"
                + "\"via\":\"<m>\"},{\"siteId\":\"a#u1\",\"arm\":false},"
                + "{\"siteId\":\"\"},{\"siteId\":\"a#u4\"}]")
                .getAsJsonArray();
        Map<String, ForcingTable.Arm> table = ForcingTable.read(json);
        Object[][] rows = {
                {"a#u1", true, ""},
                {"a#u3", false, "<m>"}};
        for (Object[] row : rows) {
            ForcingTable.Arm arm = table.get((String) row[0]);
            assertEquals((String) row[0] + " arm", row[1], arm.arm);
            assertEquals((String) row[0] + " via", row[2], arm.via);
        }
        assertEquals("the first arm of a site, none without an arm", 2,
                table.size());
    }

    private StaticScopeMap read(String row) throws IOException {
        Path file = tree.newFile().toPath();
        Files.write(file, (row + "\n").getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }
}
