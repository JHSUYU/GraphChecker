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
import soot.G;
import soot.Scene;
import soot.SootMethod;

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
        System.clearProperty(LibraryReceivers.ROOTS);
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
                {"a list hands its state to a stream", true,
                        JavaContainerTypes.query("<java.util.List: java.util"
                                + ".stream.Stream stream()>", null)},
                {"a map view's stream, through Collection", true,
                        JavaContainerTypes.query("<java.util.Collection:"
                                + " java.util.stream.Stream stream()>", null)},
                {"every stream call is a query", true,
                        JavaContainerTypes.query("<java.util.stream.Stream:"
                                + " java.util.stream.Stream limit(long)>",
                                null)},
                {"a Collectors factory too", true, JavaContainerTypes.query(
                        "<java.util.stream.Collectors: java.util.stream"
                                + ".Collector toList()>", null)},
                {"an Iterable's forEach reads it", true,
                        JavaContainerTypes.query("<java.lang.Iterable: void"
                                + " forEach(java.util.function.Consumer)>",
                                null)},
                {"a stream is no container shape", JavaContainerTypes.Shape
                        .NONE, JavaContainerTypes.shape("java.util.stream"
                        + ".Stream")},
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
     * receiver (P1); the final map is a CONTAINER cell, read for its
     * contents.
     */
    @Test
    public void aReferenceCellIsReadStoredAndConstructed() throws Exception {
        // The system's own roots hold none of the scene's library classes.
        System.setProperty(LibraryReceivers.ROOTS,
                tree.newFolder("roots").getPath());
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

        String reserves = "<" + POLICY + ": " + CHM + " reserves>";
        // The root demand chose the final map's read (a CONTAINER read is a
        // read site only where it did, SYMBOL-SCOPE §5.1).
        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(program.edges,
                Collections.<Map<String, Object>>singletonList(region()),
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), (m, u, c) -> null,
                (demandSite, demandCell) -> reserves.equals(demandCell)
                        ? new StaticScopeMap.Demanded("TRACK_CONTAINER", 1,
                        true) : null,
                method -> !method.startsWith("<s."),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField,
                CausynthStaticFacts::constructionOnly);
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(sites,
                SiteControlDependence.over(StaticScopeMap.siteIds(sites)),
                method -> false)) {
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
        Set<String> constructionOnly = new LinkedHashSet<>();
        for (String carrier : Arrays.asList(KNOWN, LATEST, reserves)) {
            for (StaticScopeMap.Site site : map.writersOf(carrier)) {
                if (site.constructionOnly) {
                    constructionOnly.add(site.siteId + " " + site.cell);
                }
            }
        }
        String store = "s.Policy#update(Ls/Commit;)V#12:WRITE";
        Object[][] rows = {
                {"the reads: two references, the atomic's value and the"
                        + " final map's contents",
                        new LinkedHashSet<>(Arrays.asList(
                                CHECK + "#u2 " + KNOWN + " REFERENCE",
                                CHECK + "#u4 " + LATEST + " REFERENCE",
                                CHECK + "#u7 " + VALUE + " VALUE",
                                CHECK + "#u8 " + reserves + " CONTAINER")),
                        reads},
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
                {"every access is observed with its kind, a map's read by"
                        + " its field and its container, the final map's by"
                        + " its container alone, its constructor's store and"
                        + " the put before its publication not at all",
                        new LinkedHashSet<>(Arrays.asList(
                                UPDATE + "#u7 REFERENCE field",
                                CHECK + "#u2 REFERENCE field container",
                                "<s.Policy: void setLatest(s.Commit)>#u2"
                                        + " REFERENCE field",
                                CHECK + "#u4 REFERENCE field",
                                "<s.Policy: void enable()>#u2 VALUE field",
                                CHECK + "#u7 VALUE field",
                                CHECK + "#u8 CONTAINER container")),
                        observed(map.observedSites())},
                {"the weave takes them off the map, once for the"
                        + " campaign: a plan's task states none",
                        siteIds(map.observedSites()),
                        woven(ConcolicInstrumentationSelections
                                .ConcolicMaterializationSelection.observed(
                                        map.observedSites()))},
                {"only the final map's store, by its constructor, is"
                        + " construction-only (no guarded store)",
                        Collections.singleton("<" + POLICY + ": void <init>()>"
                                + "#u3 " + reserves), constructionOnly},
                {"an accessor answering another type declares no input",
                        Collections.<StaticScopeMap.Site>emptyList(),
                        map.declaredSites()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * A functional argument of a stream call contributes its functional
     * method's return: {@code choose} filters its list by a lambda that
     * captured {@code excluded} and throws on an empty result; the slice
     * enters the lambda's {@code test} (through which its captured cell is
     * read) and reaches {@code excluded} at the creation site, through the
     * lambda's factory and constructor.
     */
    @Test
    public void aFunctionalArgumentIsEnteredAndItsCaptureReachesTheCreation()
            throws Exception {
        System.setProperty(LibraryReceivers.ROOTS,
                tree.newFolder("roots").getPath());
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                functionalScene()).analyze();
        String choose = "<s.Chooser: void choose(java.util.List)>";
        String lambda = "s.Chooser$lambda_choose_0__1";
        Object[][] rows = {
                {"the filter's predicate contributes its test's return",
                        "functional_return <" + lambda + ": boolean test("
                                + "java.lang.Object)>.return -> " + choose
                                + "::$r3 ", edge(program,
                        "functional_return", choose, 5)},
                {"a stream call reads its receiver",
                        "container_receiver " + choose + "::$r4 -> " + choose
                                + "::$r5 ", edge(program,
                        "container_receiver", choose, 5)},
                {"the lambda's capture is read in test",
                        "field_read <" + lambda + ": java.util.Set cap0> -> <"
                                + lambda + ": boolean test(java.lang.Object)>"
                                + "::$r1 ", edge(program, "field_read",
                        "<" + lambda + ": boolean test(java.lang.Object)>",
                        2)},
                {"the captured cell is read at the creation site",
                        "field_read <s.Chooser: java.util.Set excluded> -> "
                                + choose + "::$r2 ", edge(program,
                        "field_read", choose, 2)}};
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

    private static Set<String> siteIds(JsonArray sites) {
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement site : sites) {
            found.add(site.getAsJsonObject().get("siteId").getAsString());
        }
        return found;
    }

    private static Set<String> woven(ConcolicInstrumentationSelections
            .ConcolicMaterializationSelection selection) {
        Set<String> found = new LinkedHashSet<>();
        for (ConcolicInstrumentationSelections.ObservedSite site
                : selection.observedSites()) {
            found.add(site.siteId);
        }
        return found;
    }

    private static Set<String> observed(JsonArray sites) {
        Set<String> found = new LinkedHashSet<>();
        for (JsonElement site : sites) {
            JsonObject row = site.getAsJsonObject();
            found.add(row.get("siteId").getAsString() + " "
                    + row.get("trackedKind").getAsString()
                    + (row.get("field").getAsBoolean() ? " field" : "")
                    + (row.get("container").getAsBoolean()
                            ? " container" : ""));
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
        String policy = "s.Policy";
        JimpleScene.load(JimpleScene.OBJECT,
                "public abstract interface java.util.Map {"
                        + " public abstract java.lang.Object put("
                        + "java.lang.Object, java.lang.Object);"
                        + " public abstract java.lang.Object get("
                        + "java.lang.Object); }",
                "public class " + CHM + " extends java.lang.Object"
                        + " implements java.util.Map {"
                        + " public void <init>() { }"
                        + " public java.lang.Object getOrDefault("
                        + "java.lang.Object, java.lang.Object) { } }",
                "public class " + BOOL + " extends java.lang.Object {"
                        + " private volatile int value;"
                        + " public boolean get() { }"
                        + " public void set(boolean) { } }",
                JimpleScene.FAILURE,
                "application public class s.Commit extends java.lang.Object"
                        + " { boolean deleted; long gen; }",
                "application public class s.Policy extends java.lang.Object"
                        + " { volatile java.util.Map known; s.Commit latest;"
                        + " final " + CHM + " reserves;"
                        + " final " + BOOL + " enabled;"
                        + " public void update(s.Commit) {"
                        + " s.Policy r0; s.Commit r1; " + CHM + " $r2;"
                        + " boolean $z0;"
                        + " r0 := @this: s.Policy;"
                        + " r1 := @parameter0: s.Commit;"
                        + " $r2 = new " + CHM + ";"
                        + " specialinvoke $r2.<" + CHM + ": void <init>()>();"
                        + " $z0 = r1.<s.Commit: boolean deleted>;"
                        + " if $z0 != 0 goto label1;"
                        + " interfaceinvoke $r2." + PUT + "(r1, r1);"
                        + " label1: r0." + KNOWN + " = $r2; return; }"
                        // The final map, stored once, by the constructor.
                        + " public void <init>() { s.Policy r0; " + CHM
                        + " $r1; r0 := @this: s.Policy;"
                        + " $r1 = new " + CHM + ";"
                        + " specialinvoke $r1.<" + CHM + ": void <init>()>();"
                        + " r0.<s.Policy: " + CHM + " reserves> = $r1;"
                        + " return; }"
                        + " public void setLatest(s.Commit) { s.Policy r0;"
                        + " s.Commit r1; r0 := @this: s.Policy;"
                        + " r1 := @parameter0: s.Commit;"
                        + " r0." + LATEST + " = r1; return; }"
                        + " public void enable() { s.Policy r0; " + BOOL
                        + " $r1; r0 := @this: s.Policy;"
                        + " $r1 = r0.<s.Policy: " + BOOL + " enabled>;"
                        + " virtualinvoke $r1.<" + BOOL + ": void set("
                        + "boolean)>(1); return; }"
                        + " public void check(java.lang.Object) {"
                        + " s.Policy r0; java.lang.Object r1;"
                        + " java.util.Map $r2; java.lang.Object $r3;"
                        + " s.Commit $r4; long $l0; " + BOOL + " $r5;"
                        + " boolean $z1; " + CHM + " $r7;"
                        + " java.lang.Object $r8; byte $b0;"
                        + " java.lang.IllegalStateException $r6;"
                        + " r0 := @this: s.Policy;"
                        + " r1 := @parameter0: java.lang.Object;"
                        + " $r2 = r0." + KNOWN + ";"
                        + " $r3 = interfaceinvoke $r2.<java.util.Map:"
                        + " java.lang.Object get(java.lang.Object)>(r1);"
                        + " $r4 = r0." + LATEST + ";"
                        + " $l0 = $r4.<s.Commit: long gen>;"
                        + " $r5 = r0.<s.Policy: " + BOOL + " enabled>;"
                        + " $z1 = virtualinvoke $r5.<" + BOOL
                        + ": boolean get()>();"
                        + " $r7 = r0.<s.Policy: " + CHM + " reserves>;"
                        + " $r8 = virtualinvoke $r7.<" + CHM
                        + ": java.lang.Object getOrDefault(java.lang.Object,"
                        + "java.lang.Object)>(r1, r1);"
                        + " if $r3 != null goto label1;"
                        + " $b0 = $l0 cmp 5L; if $b0 <= 0 goto label1;"
                        + " if $z1 == 0 goto label1;"
                        + " if $r8 == null goto label1;"
                        + " $r6 = new java.lang.IllegalStateException;"
                        + " throw $r6; label1: return; } }");
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", policy, "check",
                        "(Ljava/lang/Object;)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }

    /** {@code s.Chooser.choose}: {@code if (list.stream().filter(v ->
     *  excluded.contains(v)).collect(toList()).size() < 1) throw}, with the
     *  lambda as Soot desugars it (a class, its {@code bootstrap$}). */
    private static CausynthTargetContext functionalScene() {
        String lambda = "s.Chooser$lambda_choose_0__1";
        String stream = "java.util.stream.Stream";
        String predicate = "java.util.function.Predicate";
        String collector = "java.util.stream.Collector";
        JimpleScene.load("public class java.lang.Object {"
                        + " public void <init>() { } }",
                "public abstract interface java.util.Set {"
                        + " public abstract boolean contains("
                        + "java.lang.Object); }",
                "public abstract interface java.util.List {"
                        + " public abstract " + stream + " stream();"
                        + " public abstract int size(); }",
                "public abstract interface " + stream + " {"
                        + " public abstract " + stream + " filter("
                        + predicate + "); public abstract java.lang.Object"
                        + " collect(" + collector + "); }",
                "public abstract interface " + collector + " { }",
                "public class java.util.stream.Collectors extends"
                        + " java.lang.Object { public static " + collector
                        + " toList() { } }",
                "public abstract interface " + predicate + " {"
                        + " public abstract boolean test(java.lang.Object);"
                        + " }",
                JimpleScene.FAILURE,
                "application public class s.Chooser extends java.lang.Object"
                        + " { java.util.Set excluded;"
                        + " public void choose(java.util.List) {"
                        + " s.Chooser r0; java.util.List r1;"
                        + " java.util.Set $r2; " + predicate + " $r3;"
                        + " " + stream + " $r4, $r5; " + collector + " $r6;"
                        + " java.lang.Object $r7; java.util.List $r8;"
                        + " int $i0; java.lang.IllegalStateException $r9;"
                        + " r0 := @this: s.Chooser;"
                        + " r1 := @parameter0: java.util.List;"
                        + " $r2 = r0.<s.Chooser: java.util.Set excluded>;"
                        + " $r3 = staticinvoke <" + lambda + ": " + predicate
                        + " bootstrap$(java.util.Set)>($r2);"
                        + " $r4 = interfaceinvoke r1.<java.util.List: "
                        + stream + " stream()>();"
                        + " $r5 = interfaceinvoke $r4.<" + stream + ": "
                        + stream + " filter(" + predicate + ")>($r3);"
                        + " $r6 = staticinvoke <java.util.stream.Collectors: "
                        + collector + " toList()>();"
                        + " $r7 = interfaceinvoke $r5.<" + stream
                        + ": java.lang.Object collect(" + collector
                        + ")>($r6); $r8 = (java.util.List) $r7;"
                        + " $i0 = interfaceinvoke $r8.<java.util.List:"
                        + " int size()>(); if $i0 > 0 goto label1;"
                        + " $r9 = new java.lang.IllegalStateException;"
                        + " throw $r9; label1: return; } }",
                "application public class " + lambda + " extends"
                        + " java.lang.Object implements " + predicate
                        + " { java.util.Set cap0;"
                        + " public void <init>(java.util.Set) { " + lambda
                        + " r0; java.util.Set r1; r0 := @this: " + lambda
                        + "; r1 := @parameter0: java.util.Set;"
                        + " specialinvoke r0.<java.lang.Object: void"
                        + " <init>()>(); r0.<" + lambda + ": java.util.Set"
                        + " cap0> = r1; return; }"
                        + " public static " + predicate + " bootstrap$("
                        + "java.util.Set) { java.util.Set r0; " + lambda
                        + " $r1; r0 := @parameter0: java.util.Set;"
                        + " $r1 = new " + lambda + "; specialinvoke $r1.<"
                        + lambda + ": void <init>(java.util.Set)>(r0);"
                        + " return $r1; }"
                        + " public boolean test(java.lang.Object) { " + lambda
                        + " r0; java.lang.Object r2; java.util.Set $r1;"
                        + " boolean $z0; r0 := @this: " + lambda + ";"
                        + " r2 := @parameter0: java.lang.Object;"
                        + " $r1 = r0.<" + lambda + ": java.util.Set cap0>;"
                        + " $z0 = interfaceinvoke $r1.<java.util.Set: boolean"
                        + " contains(java.lang.Object)>(r2); return $z0; } }");
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", "s.Chooser", "choose",
                        "(Ljava/util/List;)V",
                        "<s.Chooser: void choose(java.util.List)>",
                        "java.lang.IllegalStateException", 0));
    }
}
