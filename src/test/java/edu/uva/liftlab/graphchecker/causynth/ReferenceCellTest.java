package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.BooleanType;
import soot.G;
import soot.Local;
import soot.LongType;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LongConstant;
import soot.jimple.NullConstant;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

/**
 * R3-REFCONT WP1: reference cells, containers by interface, JDK atomics.
 * The scene is solr-18406's shape: {@code update} builds a fresh map, puts
 * a commit under {@code !deleted}, and stores the map into the re-pointable
 * {@code known}; {@code check} throws on {@code known.get(g)}, on {@code
 * latest}'s generation, on an {@code AtomicBoolean} and on a final
 * {@code ConcurrentHashMap}'s {@code getOrDefault}.
 */
public class ReferenceCellTest {
    private static final String CHM = "java.util.concurrent.ConcurrentHashMap";
    private static final String BOOL = "java.util.concurrent.atomic.AtomicBoolean";
    private static final String POLICY = "s.Policy";
    private static final String UPDATE = "<s.Policy: void update(s.Commit)>";
    private static final String CHECK =
            "<s.Policy: void check(java.lang.Object)>";
    private static final String KNOWN = "<s.Policy: java.util.Map known>";
    private static final String LATEST = "<s.Policy: s.Commit latest>";
    private static final String VALUE = "<" + BOOL + ": int value>";
    private static final String PUT = "<java.util.Map: java.lang.Object"
            + " put(java.lang.Object,java.lang.Object)>";

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    /** The contracts are the interfaces': a class's own, its supertypes',
     *  or the fixed list's when no hierarchy is at hand. */
    @Test
    public void aContainerCallIsItsInterfacesContract() {
        Function<String, Collection<String>> none =
                name -> Collections.<String>emptySet();
        Function<String, Collection<String>> mine = name -> Arrays.asList(
                "a.MyMap", "java.util.AbstractMap", "java.util.Map");
        Object[][] rows = {
                {"CHM's keySet, whatever view it returns", true,
                        JavaContainerTypes.query("<" + CHM + ": " + CHM
                                + "$KeySetView keySet()>", null)},
                {"CHM's getOrDefault", true, JavaContainerTypes.query("<"
                        + CHM + ": java.lang.Object getOrDefault("
                        + "java.lang.Object,java.lang.Object)>", none)},
                {"a TreeMap's floorKey", true, JavaContainerTypes.query(
                        "<java.util.TreeMap: java.lang.Object floorKey("
                                + "java.lang.Object)>", null)},
                {"a view's removeIf writes its map", true,
                        JavaContainerTypes.mutation("<java.util.Set: boolean"
                                + " removeIf(java.util.function.Predicate)>",
                                null)},
                {"CHM's merge writes", true, JavaContainerTypes.mutation("<"
                        + CHM + ": java.lang.Object merge(java.lang.Object,"
                        + "java.lang.Object,java.util.function.BiFunction)>",
                        null)},
                {"an ArrayDeque's push writes", true,
                        JavaContainerTypes.mutation("<java.util.ArrayDeque:"
                                + " void push(java.lang.Object)>", null)},
                {"a list states no poll", false, JavaContainerTypes.query(
                        "<java.util.List: java.lang.Object poll()>", null)},
                {"an application class states nothing by name", false,
                        JavaContainerTypes.mutation("<a.App: void put("
                                + "java.lang.Object,java.lang.Object)>",
                                none)},
                {"a class reaching Map is a map", true,
                        JavaContainerTypes.query("<a.MyMap: java.lang.Object"
                                + " get(java.lang.Object)>", mine)},
                {"CHM is associative", JavaContainerTypes.Shape.ASSOCIATIVE,
                        JavaContainerTypes.shape("L" + CHM.replace('.', '/')
                                + ";")},
                {"LinkedList is indexed", JavaContainerTypes.Shape.INDEXED,
                        JavaContainerTypes.shape("java.util.LinkedList")},
                {"an array is indexed", JavaContainerTypes.Shape.INDEXED,
                        JavaContainerTypes.shape("[J")},
                {"any other class is none", JavaContainerTypes.Shape.NONE,
                        JavaContainerTypes.shape("a.Foo")},
                {"an atomic's CAS writes its value", true,
                        SharedFieldFlow.atomicWrite("<java.util.concurrent"
                                + ".atomic.AtomicReference: boolean"
                                + " compareAndSet(java.lang.Object,"
                                + "java.lang.Object)>")},
                {"AtomicBoolean.get() reads its int value", VALUE,
                        SharedFieldFlow.atomicRead("<" + BOOL
                                + ": boolean get()>")},
                {"an AtomicLong's set stores its value",
                        "<java.util.concurrent.atomic.AtomicLong: long value>",
                        SharedFieldFlow.atomicValueField("<a.X: java.util"
                                + ".concurrent.atomic.AtomicLong n>",
                                "<java.util.concurrent.atomic.AtomicLong:"
                                        + " void set(long)>")},
                {"of the atomic the carrier holds only", "",
                        SharedFieldFlow.atomicValueField("<a.X: java.util"
                                + ".concurrent.atomic.AtomicInteger n>",
                                "<java.util.concurrent.atomic.AtomicLong:"
                                        + " void set(long)>")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * SYMBOL-SCOPE F2 on the scene: a map built in a local and stored into
     * {@code known} makes its guarded {@code put} a write site of {@code
     * known} (P2b), whose guard is the store's construction guard (D5);
     * {@code known} and {@code latest} are REFERENCE cells, read through a
     * query and a projection (D1: a read's object is a use of it); the
     * atomic's {@code get()} is its value (P6); a CHM query depends on its
     * receiver (P1); the final map is no cell.
     */
    @Test
    public void aReferenceCellIsReadStoredAndConstructed() throws Exception {
        StaticProgram program = new SeedBackwardStaticAnalyzer(scene())
                .analyze();
        Object[][] edges = {
                {"the put publishes into known, from the local",
                        "container_publication " + UPDATE + "::$r2 -> "
                                + KNOWN + " $r2",
                        edge(program, "container_publication", UPDATE, 6)},
                {"a CHM query depends on its receiver",
                        "container_receiver " + CHECK + "::$r7 -> " + CHECK
                                + "::$r8 ",
                        edge(program, "container_receiver", CHECK, 9)},
                {"the atomic's get() reads its value",
                        "accessor_field_return " + VALUE + " -> " + CHECK
                                + "::$z1 ",
                        edge(program, "accessor_field_return", CHECK, 7)},
                {"latest's projection is a use of latest's read",
                        "local_def_use " + CHECK + "::$r4 -> " + CHECK
                                + "::$l0 ",
                        edge(program, "local_def_use", CHECK, 5)}};
        for (Object[] row : edges) {
            assertEquals((String) row[0], row[1], row[2]);
        }

        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(program.edges,
                Collections.<Map<String, Object>>singletonList(region()),
                Collections.<String, Long>emptyMap(),
                method -> !method.startsWith("<s."),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField);
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(sites,
                SiteControlDependence.over(StaticScopeMap.siteIds(sites)))) {
            text.append(row).append('\n');
        }
        Path file = tree.newFolder("map").toPath()
                .resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);

        Set<String> reads = new LinkedHashSet<>();
        for (StaticScopeMap.Site site : sites) {
            if (StaticScopeMap.READ_SITE.equals(site.role)) {
                reads.add(site.siteId + " " + site.cell + " "
                        + site.trackedKind);
            }
        }
        Set<String> writes = new LinkedHashSet<>();
        for (String carrier : Arrays.asList(KNOWN, LATEST,
                "<s.Policy: " + BOOL + " enabled>")) {
            for (StaticScopeMap.Site site : map.writersOf(carrier)) {
                writes.add(site.siteId + " " + site.cell + " "
                        + site.publishedFrom + " " + site.guards);
            }
        }
        String store = "s.Policy#update(Ls/Commit;)V#12:WRITE";
        Object[][] rows = {
                {"the reads: two references and the atomic's value",
                        new LinkedHashSet<>(Arrays.asList(
                                CHECK + "#u2 " + KNOWN + " REFERENCE",
                                CHECK + "#u4 " + LATEST + " REFERENCE",
                                CHECK + "#u7 " + VALUE + " VALUE")), reads},
                {"known's store, its guarded put, latest's, the atomic's",
                        new LinkedHashSet<>(Arrays.asList(
                                UPDATE + "#u7 " + KNOWN + "  []",
                                UPDATE + "#u6 " + KNOWN + " $r2 ["
                                        + UPDATE + "#u5]",
                                "<s.Policy: void setLatest(s.Commit)>#u2 "
                                        + LATEST + "  []",
                                "<s.Policy: void enable()>#u2 " + VALUE
                                        + "  []")), writes},
                {"the put's guard, on the arm that puts, is known's"
                        + " construction guard", Collections.singletonList(
                        UPDATE + "#u5=false"),
                        guards(map.constructionGuards(store, KNOWN))},
                {"the put builds no other carrier",
                        Collections.<String>emptyList(),
                        guards(map.constructionGuards(store, LATEST))},
                {"known's store joins known holding a CHM, the put joins"
                        + " it as the map's state, and no element joins it",
                        Arrays.asList("INSTANCE java/util/concurrent/"
                                        + "ConcurrentHashMap [" + KNOWN + "]",
                                "MAP L [" + KNOWN + "]", "ARRAY L []"),
                        carriers(map, store, "INSTANCE java/util/concurrent/"
                                + "ConcurrentHashMap", "MAP L", "ARRAY L")},
                {"every access is observed with its kind, the put before"
                        + " its publication is not",
                        new LinkedHashSet<>(Arrays.asList(
                                UPDATE + "#u7 REFERENCE",
                                CHECK + "#u2 REFERENCE",
                                "<s.Policy: void setLatest(s.Commit)>#u2"
                                        + " REFERENCE",
                                CHECK + "#u4 REFERENCE",
                                "<s.Policy: void enable()>#u2 VALUE",
                                CHECK + "#u7 VALUE")),
                        observed(map.observedSites())},
                {"an accessor answering another type declares no input",
                        Collections.<StaticScopeMap.Site>emptyList(),
                        map.declaredSites()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static String edge(StaticProgram program, String kind,
                               String method, int unit) {
        for (Map<String, Object> edge : program.edges) {
            if (kind.equals(edge.get("kind"))
                    && method.equals(edge.get("method"))
                    && Integer.valueOf(unit).equals(edge.get("unitIndex"))) {
                return kind + " " + edge.get("fromCell") + " -> "
                        + edge.get("toCell") + " " + MapFields.text(
                        edge.get("publishedFrom"));
            }
        }
        return "";
    }

    /** Each "location kind, type" a write states, and the carriers one
     *  recorded site joins it to. */
    private static List<String> carriers(StaticScopeMap map, String site,
                                         String... written) {
        List<String> found = new ArrayList<>();
        for (String write : written) {
            String[] kindAndType = write.split(" ", 2);
            found.add(write + " " + map.carriersAt(site, kindAndType[1],
                    LocationKind.valueOf(kindAndType[0])));
        }
        return found;
    }

    /**
     * A recorded write joins a carrier of its method by the kind of location
     * the site stores -- a field store a field, a mutator call the
     * container's state, nothing an array element -- and by what the cell's
     * declared class may hold: a map field any map or a class no sort names;
     * a String or box field only its own class, both being final; a field of
     * a class no sort names anything.
     */
    @Test
    public void aWriteJoinsTheCarrierItsLocationAndClassMayBe()
            throws Exception {
        String method = "<s.Holder: void set()>";
        String[][] sites = {
                // cell, the mutator it calls
                {"<s.Holder: java.util.Map map>", ""},
                {"<s.Holder: java.util.Map map>", PUT},
                {"<s.Holder: java.lang.String name>", ""},
                {"<s.Holder: java.lang.Long stamp>", ""},
                {"<s.Holder: s.Commit latest>", ""}};
        StringBuilder text = new StringBuilder();
        for (int index = 0; index < sites.length; index++) {
            JsonObject row = new JsonObject();
            row.addProperty("kind", StaticScopeMap.SITE_KIND);
            row.addProperty("role", StaticScopeMap.WRITE_SITE);
            row.addProperty("regionId", "REGION.holder");
            row.addProperty("siteId", method + "#u" + index);
            row.addProperty("vmSite", "s.Holder#set()V");
            row.addProperty("cell", sites[index][0]);
            row.addProperty("carrier", sites[index][0]);
            row.addProperty("declaredCallee", sites[index][1]);
            row.add("guards", new JsonArray());
            text.append(row).append('\n');
        }
        Path file = tree.newFolder("holder").toPath()
                .resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        StaticScopeMap map = StaticScopeMap.read(file);
        String mapField = sites[0][0];
        String name = sites[2][0];
        String stamp = sites[3][0];
        String latest = sites[4][0];
        Object[][] rows = {
                {"INSTANCE java/util/concurrent/ConcurrentHashMap",
                        Arrays.asList(mapField, latest)},
                {"INSTANCE s/Other", Arrays.asList(mapField, latest)},
                {"INSTANCE java/lang/String", Arrays.asList(name, latest)},
                {"INSTANCE J", Collections.singletonList(stamp)},
                {"INSTANCE L", Arrays.asList(mapField, name, stamp, latest)},
                {"MAP L", Collections.singletonList(mapField)},
                {"ARRAY s/Other", Collections.<String>emptyList()}};
        for (Object[] row : rows) {
            String[] kindAndType = ((String) row[0]).split(" ", 2);
            assertEquals((String) row[0], row[1],
                    new ArrayList<>(map.carriersAt("s.Holder#set()V#9:WRITE",
                            kindAndType[1],
                            LocationKind.valueOf(kindAndType[0]))));
        }
    }

    private static List<String> guards(List<StaticScopeMap.Guard> guards) {
        List<String> found = new ArrayList<>();
        for (StaticScopeMap.Guard guard : guards) found.add(guard.toString());
        return found;
    }

    private static Set<String> observed(JsonArray sites) {
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement site : sites) {
            JsonObject row = site.getAsJsonObject();
            found.add(row.get("siteId").getAsString() + " "
                    + row.get("trackedKind").getAsString());
        }
        return found;
    }

    private static Map<String, Object> region() {
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", "REGION.policy");
        List<String> methods = new ArrayList<>();
        for (SootMethod method : Scene.v().getSootClass(POLICY)
                .getMethods()) {
            methods.add(method.getSignature());
        }
        region.put("methods", methods);
        return region;
    }

    /** The scene, and the declared throw in {@code check}. */
    private static CausynthTargetContext scene() {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        SootClass map = library("java.util.Map", null,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        SootClass chm = library(CHM, object, 0);
        chm.addInterface(map);
        SootClass atomic = library(BOOL, object, 0);
        atomic.addField(new SootField("value", soot.IntType.v(),
                Modifier.PRIVATE | Modifier.VOLATILE));
        library("java.lang.IllegalStateException", object, 0);
        RefType objectType = object.getType();
        SootMethod put = method(map, "put", Arrays.<Type>asList(objectType,
                objectType), objectType, Modifier.ABSTRACT);
        SootMethod get = method(map, "get", Collections.<Type>singletonList(
                objectType), objectType, Modifier.ABSTRACT);
        SootMethod init = method(chm, "<init>", Collections.<Type>emptyList(),
                VoidType.v(), 0);
        SootMethod orDefault = method(chm, "getOrDefault", Arrays.<Type>asList(
                objectType, objectType), objectType, 0);
        SootMethod atomicGet = method(atomic, "get",
                Collections.<Type>emptyList(), BooleanType.v(), 0);
        SootMethod atomicSet = method(atomic, "set",
                Collections.<Type>singletonList(BooleanType.v()),
                VoidType.v(), 0);

        SootClass commit = application("s.Commit", object);
        SootField deleted = new SootField("deleted", BooleanType.v(), 0);
        SootField gen = new SootField("gen", LongType.v(), 0);
        commit.addField(deleted);
        commit.addField(gen);
        SootClass policy = application(POLICY, object);
        SootField known = new SootField("known", map.getType(),
                Modifier.VOLATILE);
        SootField latest = new SootField("latest", commit.getType(), 0);
        SootField reserves = new SootField("reserves", chm.getType(),
                Modifier.FINAL);
        SootField enabled = new SootField("enabled", atomic.getType(),
                Modifier.FINAL);
        for (SootField field : Arrays.asList(known, latest, reserves,
                enabled)) {
            policy.addField(field);
        }
        RefType self = policy.getType();
        RefType commitType = commit.getType();

        SootMethod update = method(policy, "update",
                Collections.<Type>singletonList(commitType), VoidType.v(), 0);
        Local u0 = local(update, "r0", self);
        Local u1 = local(update, "r1", commitType);
        Local built = local(update, "$r2", chm.getType());
        Local gone = local(update, "$z0", BooleanType.v());
        Unit publish = Jimple.v().newAssignStmt(Jimple.v()
                .newInstanceFieldRef(u0, known.makeRef()), built);
        body(update, Jimple.v().newIdentityStmt(u0,
                        Jimple.v().newThisRef(self)),
                Jimple.v().newIdentityStmt(u1,
                        Jimple.v().newParameterRef(commitType, 0)),
                Jimple.v().newAssignStmt(built,
                        Jimple.v().newNewExpr(chm.getType())),
                Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(
                        built, init.makeRef())),
                Jimple.v().newAssignStmt(gone, Jimple.v()
                        .newInstanceFieldRef(u1, deleted.makeRef())),
                Jimple.v().newIfStmt(Jimple.v().newNeExpr(gone,
                        IntConstant.v(0)), publish),
                Jimple.v().newInvokeStmt(Jimple.v().newInterfaceInvokeExpr(
                        built, put.makeRef(), Arrays.<Value>asList(u1, u1))),
                publish,
                Jimple.v().newReturnVoidStmt());

        SootMethod setLatest = method(policy, "setLatest",
                Collections.<Type>singletonList(commitType), VoidType.v(), 0);
        Local s0 = local(setLatest, "r0", self);
        Local s1 = local(setLatest, "r1", commitType);
        body(setLatest, Jimple.v().newIdentityStmt(s0,
                        Jimple.v().newThisRef(self)),
                Jimple.v().newIdentityStmt(s1,
                        Jimple.v().newParameterRef(commitType, 0)),
                Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(s0,
                        latest.makeRef()), s1),
                Jimple.v().newReturnVoidStmt());

        SootMethod enable = method(policy, "enable",
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local e0 = local(enable, "r0", self);
        Local flag = local(enable, "$r1", atomic.getType());
        body(enable, Jimple.v().newIdentityStmt(e0,
                        Jimple.v().newThisRef(self)),
                Jimple.v().newAssignStmt(flag, Jimple.v()
                        .newInstanceFieldRef(e0, enabled.makeRef())),
                Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(
                        flag, atomicSet.makeRef(), IntConstant.v(1))),
                Jimple.v().newReturnVoidStmt());

        SootMethod check = method(policy, "check",
                Collections.<Type>singletonList(objectType), VoidType.v(), 0);
        Local c0 = local(check, "r0", self);
        Local key = local(check, "r1", objectType);
        Local held = local(check, "$r2", map.getType());
        Local found = local(check, "$r3", objectType);
        Local last = local(check, "$r4", commitType);
        Local generation = local(check, "$l0", LongType.v());
        Local on = local(check, "$r5", atomic.getType());
        Local enabledNow = local(check, "$z1", BooleanType.v());
        Local reserved = local(check, "$r7", chm.getType());
        Local until = local(check, "$r8", objectType);
        Local order = local(check, "$b0", soot.ByteType.v());
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(check, "$r6", failure);
        Unit done = Jimple.v().newReturnVoidStmt();
        body(check, Jimple.v().newIdentityStmt(c0,
                        Jimple.v().newThisRef(self)),
                Jimple.v().newIdentityStmt(key,
                        Jimple.v().newParameterRef(objectType, 0)),
                Jimple.v().newAssignStmt(held, Jimple.v()
                        .newInstanceFieldRef(c0, known.makeRef())),
                Jimple.v().newAssignStmt(found, Jimple.v()
                        .newInterfaceInvokeExpr(held, get.makeRef(), key)),
                Jimple.v().newAssignStmt(last, Jimple.v()
                        .newInstanceFieldRef(c0, latest.makeRef())),
                Jimple.v().newAssignStmt(generation, Jimple.v()
                        .newInstanceFieldRef(last, gen.makeRef())),
                Jimple.v().newAssignStmt(on, Jimple.v()
                        .newInstanceFieldRef(c0, enabled.makeRef())),
                Jimple.v().newAssignStmt(enabledNow, Jimple.v()
                        .newVirtualInvokeExpr(on, atomicGet.makeRef())),
                Jimple.v().newAssignStmt(reserved, Jimple.v()
                        .newInstanceFieldRef(c0, reserves.makeRef())),
                Jimple.v().newAssignStmt(until, Jimple.v()
                        .newVirtualInvokeExpr(reserved, orDefault.makeRef(),
                                key, key)),
                Jimple.v().newIfStmt(Jimple.v().newNeExpr(found,
                        NullConstant.v()), done),
                Jimple.v().newAssignStmt(order, Jimple.v().newCmpExpr(
                        generation, LongConstant.v(5L))),
                Jimple.v().newIfStmt(Jimple.v().newLeExpr(order,
                        IntConstant.v(0)), done),
                Jimple.v().newIfStmt(Jimple.v().newEqExpr(enabledNow,
                        IntConstant.v(0)), done),
                Jimple.v().newIfStmt(Jimple.v().newEqExpr(until,
                        NullConstant.v()), done),
                Jimple.v().newAssignStmt(thrown,
                        Jimple.v().newNewExpr(failure)),
                Jimple.v().newThrowStmt(thrown),
                done);
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", POLICY, "check",
                        "(Ljava/lang/Object;)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }

    private static SootClass application(String name, SootClass parent) {
        SootClass type = library(name, parent, 0);
        type.setApplicationClass();
        return type;
    }

    private static SootClass library(String name, SootClass parent,
                                     int modifiers) {
        SootClass type = new SootClass(name, Modifier.PUBLIC | modifiers);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returned,
                                     int modifiers) {
        SootMethod method = new SootMethod(name, parameters, returned,
                Modifier.PUBLIC | modifiers);
        owner.addMethod(method);
        if ((modifiers & Modifier.ABSTRACT) == 0) {
            method.setActiveBody(Jimple.v().newBody(method));
        }
        return method;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = Jimple.v().newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }

    private static void body(SootMethod method, Unit... units) {
        method.getActiveBody().getUnits().addAll(Arrays.asList(units));
    }
}
