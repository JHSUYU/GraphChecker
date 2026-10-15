package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.G;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §4.3: which reads are configuration, under which key, minted
 * in which shape, with which domain.
 */
public class ConfigRootsTest {
    private static final String CONF = "org.apache.hadoop.conf.Configuration";
    private static final String MANAGER = "t.Manager";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aConfigurationIsReadAtOneFieldOrAtItsGetterReturns() {
        Map<String, List<String>> writers = new LinkedHashMap<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        scene(writers, edges);
        ConfigRoots roots = ConfigRoots.of(edges, writers);
        String getInt = "<" + CONF + ": int getInt(java.lang.String,int)>";
        Object[][] rows = {
            {"a field its constructor stores from a getter, a boolean",
                "CONFIG:k.ordered boolean [,]", source(roots.field(
                        field("boolean ordered")))},
            {"a clamp keeps the key; the default and a compared literal "
                    + "+-1 are its domain", "CONFIG:k.limit int [5,11]",
                source(roots.field(field("int limit")))},
            {"a clamp bounds the domain: Math.max(v, 1) is never 0",
                "CONFIG:k.low int [1,4]", source(roots.field(
                        field("int low")))},
            {"no floor at 0: a comparison with 0 flips at -1",
                "CONFIG:k.debt int [-1,5]", source(roots.field(
                        field("int debt")))},
            {"a constant stored after the configuration (if (f <= 0) f = 1)"
                    + " leaves the field no root", "null false true",
                source(roots.field(field("int san"))) + " "
                        + roots.fields().containsKey(field("int san")) + " "
                        + roots.configField(field("int san"))},
            {"a second writer storing anything else is no configuration",
                "null", source(roots.field(field("int counter")))},
            {"a view's literal is part of the root, past the initializer's"
                    + " constant", "CONFIG:k.legacy==true boolean [,]",
                source(roots.field(field("boolean legacy")))},
            {"a key a field holds is minted at the field, not its getter",
                "null", source(roots.call(run(), 3,
                        "<t.Manager: boolean legacy(" + CONF + ")>"))},
            {"the getter call a field's writer stores is the field's read: "
                    + "no root, no gap", "null", source(roots.call(
                        "<t.Manager: void <init>(" + CONF + ")>", 3, "<"
                        + CONF + ": boolean getBoolean(java.lang.String,"
                        + "boolean)>"))},
            {"a key no field holds is minted at each getter return of its"
                    + " shape, whatever its default",
                "CONFIG:k.only int [3,7] CONFIG:k.only int [3,7]",
                source(roots.call(run(), 4, getInt)) + " "
                        + source(roots.call(run(), 8, getInt))},
            {"a read of the key under another type is read concretely",
                "null", source(roots.call(run(), 9, "<" + CONF
                        + ": long getLong(java.lang.String,long)>"))},
            {"a key no literal names is no root", "null",
                source(roots.call(run(), 7, getInt))},
            {"two views of one key: the first by site is the root",
                "CONFIG:k.mode==a boolean [,] null",
                source(roots.call(run(), 10, "<t.Manager: boolean isA("
                        + CONF + ")>")) + " " + source(roots.call(run(), 11,
                        "<t.Manager: boolean isB(" + CONF + ")>"))},
            {"a wrapper's clamp bounds its domain; the getter in its body is"
                    + " its own read", "CONFIG:k.w int [2,2] null",
                source(roots.call(run(), 12, "<t.Manager: int limitOf("
                        + CONF + ")>")) + " " + source(roots.call(
                        "<t.Manager: int limitOf(" + CONF + ")>", 1,
                        getInt))},
            {"a wrapper's own validation rides beside the static hull, which"
                    + " it clips only where a run's reading passes it",
                "CONFIG:k.min int [1,6] [2,] by <t.Manager: int minOf("
                        + CONF + ")>#u2", source(roots.field(field(
                        "int min"))) + " " + roots.field(field("int min"))
                        .valid},
            {"a validation one return bypasses bounds nothing: every path"
                    + " to the value's return must pass it",
                "CONFIG:k.cap int [1,5] [,]", source(roots.field(field(
                        "int cap"))) + " " + roots.field(field("int cap"))
                        .valid},
            {"a getter called on a subclass is the catalog's",
                "CONFIG:k.sub int [2,2]", source(roots.call(run(), 5,
                        "<org.apache.hadoop.hdfs.HdfsConfiguration: int "
                                + "getInt(java.lang.String,int)>"))},
            {"every configuration field of the slice, declared or not",
                "[true, false]", Arrays.asList(roots.configField(field(
                        "boolean ordered")), roots.configField(field(
                        "int counter"))).toString()},
            {"what no root mints is named, by reason and site",
                "[CONFIG_FIELD_OVERWRITTEN@<t.Manager: void <init>("
                        + CONF + ")>#u19, CONFIG_READ_CONCRETE@" + run()
                        + "#u3, CONFIG_KEY_UNRESOLVED@" + run() + "#u7,"
                        + " CONFIG_READ_CONCRETE@" + run() + "#u9,"
                        + " CONFIG_READ_CONCRETE@" + run() + "#u11]",
                gaps(roots)},
            {"beside a root the demand left unchosen, a concrete read is no"
                    + " gap", "[CONFIG_FIELD_OVERWRITTEN@<t.Manager: void"
                    + " <init>(" + CONF + ")>#u19, CONFIG_KEY_UNRESOLVED@"
                    + run() + "#u7, CONFIG_READ_CONCRETE@" + run() + "#u9]",
                gaps(roots.limitedTo(Collections.singleton(
                        "CONFIG:k.only")))},
            {"each root's reads its plant leaves, over the whole scope: the"
                    + " getter's other shape; a field's own reads planted,"
                    + " its stored getter call its own; a key read at no"
                    + " plant (a hook's field) is no root",
                "[CONFIG:k.limit " + field("int limit") + " [], CONFIG:k.only "
                        + run() + "#u4 [" + run() + "#u9]]",
                keyRows(roots.keyRows(new java.util.HashSet<>(Arrays.asList(
                        "CONFIG:k.only", "CONFIG:k.limit",
                        "CONFIG:k.ordered")), Collections.singleton(
                        "<t.Manager: void check()>#u1")))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static String gaps(ConfigRoots roots) {
        List<String> found = new ArrayList<>();
        for (Map<String, Object> gap : roots.gaps()) {
            found.add(gap.get("reason") + "@" + gap.get("siteId"));
        }
        return found.toString();
    }

    private static String keyRows(List<com.google.gson.JsonObject> rows) {
        List<String> found = new ArrayList<>();
        for (com.google.gson.JsonObject row : rows) {
            found.add(row.get("sourceId").getAsString() + " "
                    + row.get("mintedAt").getAsString() + " "
                    + row.get("concreteReads").toString().replace("\"", ""));
        }
        return found.toString();
    }

    private static String source(ConfigRoots.Source source) {
        return source == null ? "null" : source.sourceId + " "
                + source.javaType + " [" + source.domainMin + ","
                + source.domainMax + "]";
    }

    private static String field(String declared) {
        return "<" + MANAGER + ": " + declared + ">";
    }

    private static String run() {
        return "<" + MANAGER + ": void run(" + CONF + ")>";
    }

    /**
     * {@code t.Manager}'s constructor stores {@code ordered}, {@code limit}
     * and {@code low} (clamped), {@code counter} (which {@code bump} also
     * counts), {@code legacy} (initialized false, then a wrapper's answer)
     * and {@code san} (then set to 1 where it is not positive) from a {@code
     * Configuration}, {@code setDebt} stores {@code debt}; {@code check}
     * compares {@code limit} with 10, {@code checkLow} {@code low} with 3,
     * {@code checkDebt} {@code debt} with 0; {@code run} calls the wrappers
     * ({@code legacy}, the views {@code isA} and {@code isB}, the clamp {@code
     * limitOf}) and the getters: {@code k.only} with two defaults and as a
     * {@code long}, a key no literal names, one through {@code
     * HdfsConfiguration}.
     */
    private static void scene(Map<String, List<String>> writers,
                              List<Map<String, Object>> edges) {
        String conf = CONF + " r1; r0 := @this: " + MANAGER
                + "; r1 := @parameter0: " + CONF + ";";
        String max = "staticinvoke <java.lang.Math: int max(int,int)>";
        String store = " r0.<" + MANAGER + ": ";
        StringBuilder checks = new StringBuilder();
        for (Object[] check : new Object[][] {{"check", "limit", 10},
                {"checkCap", "cap", 4}, {"checkLow", "low", 3},
                {"checkDebt", "debt", 0}, {"checkMin", "min", 5}}) {
            checks.append(compare((String) check[0], (String) check[1],
                    (Integer) check[2], edges));
        }
        JimpleScene.load(JimpleScene.OBJECT,
                "public class java.lang.String extends java.lang.Object {"
                        + " public native boolean equals(java.lang.Object);"
                        + " }",
                "public class java.lang.Math extends java.lang.Object {"
                        + " public static native int max(int, int); }",
                "public class " + CONF + " extends java.lang.Object {"
                        + " public native boolean getBoolean(java.lang.String,"
                        + " boolean); public native int getInt("
                        + "java.lang.String, int); public native long getLong("
                        + "java.lang.String, long); public native"
                        + " java.lang.String get(java.lang.String); }",
                "public class " + HDFS + " extends " + CONF + " { }",
                "application public class " + MANAGER + " extends"
                        + " java.lang.Object { boolean ordered; int limit;"
                        + " int counter; boolean legacy; int low; int san;"
                        + " int debt; int min; int cap;"
                        + view("legacy", "k.legacy", "true")
                        + view("isA", "k.mode", "a")
                        + view("isB", "k.mode", "b")
                        + " public static int limitOf(" + CONF + ") { " + CONF
                        + " r0; int $i0, $i1; r0 := @parameter0: " + CONF
                        + "; $i0 = " + getInt("r0", "\"k.w\"", "0") + "; $i1 = "
                        + max + "($i0, 2); return $i1; }"
                        // A wrapper that throws on a value below 2 before it
                        // returns it.
                        + " public static int minOf(" + CONF + ") { " + CONF
                        + " r0; int $i0; java.lang.RuntimeException $r1;"
                        + " r0 := @parameter0: " + CONF + "; $i0 = "
                        + getInt("r0", "\"k.min\"", "1") + ";"
                        + " if $i0 >= 2 goto label1;"
                        + " $r1 = new java.lang.RuntimeException; throw $r1;"
                        + " label1: return $i0; }"
                        // A wrapper whose check of a value below 3 one return
                        // bypasses.
                        + " public static int capOf(" + CONF + ") { " + CONF
                        + " r0; int $i0; java.lang.RuntimeException $r1;"
                        + " r0 := @parameter0: " + CONF + "; $i0 = "
                        + getInt("r0", "\"k.cap\"", "1") + ";"
                        + " if $i0 < 0 goto label2; if $i0 >= 3 goto label1;"
                        + " $r1 = new java.lang.RuntimeException; throw $r1;"
                        + " label1: return $i0; label2: return $i0; }"
                        + " public void <init>(" + CONF + ") { " + MANAGER
                        + " r0; " + CONF + " r1; boolean $z0; int $i0, $i1,"
                        + " $i2; boolean $z1; int $i3, $i4, $i5, $i6;"
                        + " r0 := @this: " + MANAGER + "; r1 := @parameter0: "
                        + CONF + ";" + store + "boolean legacy> = 0;"
                        + " $z0 = virtualinvoke r1.<" + CONF + ": boolean"
                        + " getBoolean(java.lang.String,boolean)>("
                        + "\"k.ordered\", 0);" + store + "boolean ordered>"
                        + " = $z0; $i0 = " + getInt("r1", "\"k.limit\"", "5")
                        + "; $i1 = " + max + "($i0, 1);" + store
                        + "int limit> = $i1; $i2 = " + getInt("r1",
                        "\"k.counter\"", "0") + ";" + store + "int counter>"
                        + " = $i2; $z1 = staticinvoke " + view("legacy")
                        + "(r1);" + store + "boolean legacy> = $z1; $i3 = "
                        + getInt("r1", "\"k.low\"", "0") + "; $i4 = " + max
                        + "($i3, 1);" + store + "int low> = $i4; $i5 = "
                        + getInt("r1", "\"k.san\"", "5") + ";" + store
                        + "int san> = $i5; $i6 = r0." + field("int san")
                        + "; if $i6 > 0 goto label1;" + store
                        + "int san> = 1; label1: return; }"
                        + " public void bump() { " + MANAGER + " r0;"
                        + " int $i0, $i1; r0 := @this: " + MANAGER + ";"
                        + " $i0 = r0." + field("int counter") + ";"
                        + " $i1 = $i0 + 1;" + store + "int counter> = $i1;"
                        + " return; }"
                        + " public void setDebt(" + CONF + ") { " + MANAGER
                        + " r0; int $i0; " + conf + " $i0 = " + getInt("r1",
                        "\"k.debt\"", "5") + ";" + store + "int debt> = $i0;"
                        + " return; }"
                        + " public void setMin(" + CONF + ") { " + MANAGER
                        + " r0; int $i0; " + conf + " $i0 = staticinvoke <"
                        + MANAGER + ": int minOf(" + CONF + ")>(r1);" + store
                        + "int min> = $i0; return; }"
                        + " public void setCap(" + CONF + ") { " + MANAGER
                        + " r0; int $i0; " + conf + " $i0 = staticinvoke <"
                        + MANAGER + ": int capOf(" + CONF + ")>(r1);" + store
                        + "int cap> = $i0; return; }" + checks
                        + " public void run(" + CONF + ") { " + MANAGER
                        + " r0; " + CONF + " r1; boolean $z0; int $i0; " + HDFS
                        + " $r2; int $i1; java.lang.String $r3; int $i2, $i3;"
                        + " long $l0; boolean $z1, $z2; int $i4;"
                        + " r0 := @this: " + MANAGER + "; r1 := @parameter0: "
                        + CONF + "; $r2 = (" + HDFS + ") r1;"
                        + " $z0 = staticinvoke " + view("legacy") + "(r1);"
                        + " $i0 = " + getInt("r1", "\"k.only\"", "3") + ";"
                        + " $i1 = virtualinvoke $r2." + SUB_GET_INT
                        + "(\"k.sub\", 2); $r3 = virtualinvoke r1." + GET
                        + "(\"k.name\"); $i2 = " + getInt("r1", "$r3", "0")
                        + "; $i3 = " + getInt("r1", "\"k.only\"", "7") + ";"
                        + " $l0 = virtualinvoke r1." + GET_LONG
                        + "(\"k.only\", 3L); $z1 = staticinvoke "
                        + view("isA") + "(r1); $z2 = staticinvoke "
                        + view("isB") + "(r1); $i4 = staticinvoke " + LIMIT_OF
                        + "(r1); return; } }",
                "public class java.lang.RuntimeException extends"
                        + " java.lang.Object { }");
        String initSig = "<" + MANAGER + ": void <init>(" + CONF + ")>";
        writers.put(field("boolean ordered"),
                Collections.singletonList(initSig + "#u4"));
        writers.put(field("int limit"),
                Collections.singletonList(initSig + "#u7"));
        writers.put(field("boolean legacy"),
                Arrays.asList(initSig + "#u2", initSig + "#u11"));
        writers.put(field("int low"),
                Collections.singletonList(initSig + "#u14"));
        writers.put(field("int san"),
                Arrays.asList(initSig + "#u16", initSig + "#u19"));
        writers.put(field("int counter"), Arrays.asList(initSig + "#u9",
                "<" + MANAGER + ": void bump()>#u3"));
        for (String set : new String[] {"Debt", "Min", "Cap"}) {
            writers.put(field("int " + set.toLowerCase()),
                    Collections.singletonList("<" + MANAGER + ": void set"
                            + set + "(" + CONF + ")>#u3"));
        }
        String checkSig = "<" + MANAGER + ": void check()>";
        for (String read : new String[]{"boolean ordered", "int counter",
                "boolean legacy", "int san"}) {
            edges.add(edge("field_read", field(read), checkSig + "::x",
                    checkSig, 1, null));
        }
        String runSig = run();
        Object[][] calls = {{3, view("legacy"), "$z0"}, {4, GET_INT, "$i0"},
            {5, SUB_GET_INT, "$i1"}, {7, GET_INT, "$i2"}, {8, GET_INT, "$i3"},
            {9, GET_LONG, "$l0"}, {10, view("isA"), "$z1"},
            {11, view("isB"), "$z2"}, {12, LIMIT_OF, "$i4"}};
        for (Object[] call : calls) {
            edges.add(edge("call_return", call[1] + ".return",
                    runSig + "::" + call[2], runSig, (Integer) call[0],
                    (String) call[1]));
        }
        edges.add(edge("call_return", GET_INT + ".return",
                LIMIT_OF + "::$i0", LIMIT_OF, 1, GET_INT));
        String getBoolean = "<" + CONF + ": boolean getBoolean("
                + "java.lang.String,boolean)>";
        edges.add(edge("call_return", getBoolean + ".return",
                initSig + "::$z0", initSig, 3, getBoolean));
    }

    private static final String HDFS =
            "org.apache.hadoop.hdfs.HdfsConfiguration";
    private static final String GET_INT = "<" + CONF + ": int getInt("
            + "java.lang.String,int)>";
    private static final String SUB_GET_INT = "<" + HDFS + ": int getInt("
            + "java.lang.String,int)>";
    private static final String GET_LONG = "<" + CONF + ": long getLong("
            + "java.lang.String,long)>";
    private static final String GET = "<" + CONF + ": java.lang.String get("
            + "java.lang.String)>";
    private static final String LIMIT_OF = "<" + MANAGER + ": int limitOf("
            + CONF + ")>";

    /** {@code receiver.getInt(key, otherwise)}. */
    private static String getInt(String receiver, String key,
                                 String otherwise) {
        return "virtualinvoke " + receiver + "." + GET_INT + "(" + key + ", "
                + otherwise + ")";
    }

    /** The signature of the view {@code name}. */
    private static String view(String name) {
        return "<" + MANAGER + ": boolean " + name + "(" + CONF + ")>";
    }

    /** {@code static boolean <name>(Configuration c)}: {@code
     *  "<literal>".equals(c.get("<key>"))}. */
    private static String view(String name, String key, String literal) {
        return " public static boolean " + name + "(" + CONF + ") { " + CONF
                + " r0; java.lang.String $r1; boolean $z0;"
                + " java.lang.String $r2; r0 := @parameter0: " + CONF + ";"
                + " $r1 = virtualinvoke r0." + GET + "(\"" + key + "\");"
                + " $r2 = \"" + literal + "\"; $z0 = virtualinvoke $r2."
                + "<java.lang.String: boolean equals(java.lang.Object)>($r1);"
                + " return $z0; }";
    }

    /** {@code void <name>()}: {@code if (this.<field> > bound) bump()}, its
     *  read and its guard in the slice. */
    private static String compare(String name, String read, int bound,
                                  List<Map<String, Object>> edges) {
        String signature = "<" + MANAGER + ": void " + name + "()>";
        String local = signature + "::$i0";
        edges.add(edge("field_read", field("int " + read), local,
                signature, 1, null));
        edges.add(edge("guard_dependency", local, signature + "#u2",
                signature, 2, null));
        return " public void " + name + "() { " + MANAGER + " r0; int $i0;"
                + " r0 := @this: " + MANAGER + "; $i0 = r0." + field("int "
                + read) + "; if $i0 <= " + bound + " goto label1;"
                + " virtualinvoke r0.<" + MANAGER + ": void bump()>();"
                + " label1: return; }";
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String method,
                                            int unitIndex, String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        edge.put("method", method);
        edge.put("unitIndex", unitIndex);
        if (invoke != null) edge.put("invoke", invoke);
        return edge;
    }
}
